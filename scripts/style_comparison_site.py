#!/usr/bin/env python3
"""Post-process the Verso multi-page comparison output into a single-page
dashboard whose visual shape matches the existing live `site/comparison/`
(warm-parchment theme, expandable rows), but whose code blocks are
**Verso-rendered** (full bodies, hover info, cross-refs).

Inputs:
  - Verso multi-page HTML tree produced by `lake exe comparison`
    (default: comparison-build/_out/html-multi)
  - paper-statements.json (row metadata: section, prose, kind)
  - extracted.json (`@[informal]` decls with paperRef, kind, status)

Output (default: comparison-dashboard/):
  comparison-dashboard/
    index.html                   — single-page dashboard
    book.css, verso-vars.css     — copied from Verso output so styles resolve
    -verso-data/, -verso-search/ — copied so hover JS + search work
    entries/                     — the Verso multi-page tree, copied in as-is
                                   so cross-reference links from code blocks
                                   (e.g. `σ.slicing`) still resolve.

Reuses `load_and_join`, `catchword`, `prose_preview`, `source_url` from the
existing `generate_comparison.py`. The only rendering change is
`render_lean_panel`: instead of regex-tokenizing `signature`, it injects the
matching Verso `<code class="hl lean block">` HTML blocks lifted from the
entry page for this paperRef.

Requires: beautifulsoup4.
"""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
import sys
from pathlib import Path

from bs4 import BeautifulSoup

# Reuse the existing dashboard's joining + helpers.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_comparison import (  # type: ignore
    PAGE_TEMPLATE,
    SECTION_TITLES,
    catchword,
    load_and_join,
    prose_preview,
    render_attribute,
    source_url,
)


# ─────────────────────────────────────────────────────────────────────────────
# Verso entry-page location
# ─────────────────────────────────────────────────────────────────────────────

def ref_to_page_slug(ref: str) -> str:
    """Mirror Verso's directory-name slug for a `#` heading.

    Verso encodes `.` as `___` and spaces as `-`, then surrounds with a
    version of the heading; for our generator, entry headings are literally
    the `ref` with optional ` — {kind}` suffix. We look up by prefix later so
    only the ref portion needs encoding.
    """
    return ref.replace(".", "___").replace(" ", "-")


def find_entry_page(multi_root: Path, section_num: str, ref: str) -> Path | None:
    """Resolve the per-entry Verso HTML file for (section_num, ref).

    The section dir looks like `___{n}-___-Section-Title`; the entry dir
    like `{Kind-prefix}{encoded-ref}{...}`. We match by whichever entry dir
    has a slug-form containing `ref_to_page_slug(ref)`.
    """
    prefix = f"___{section_num}-___-"
    section_dirs = [d for d in multi_root.iterdir()
                    if d.is_dir() and d.name.startswith(prefix)]
    if not section_dirs:
        return None
    section_dir = section_dirs[0]
    ref_slug = ref_to_page_slug(ref)
    for entry_dir in section_dir.iterdir():
        if entry_dir.is_dir() and ref_slug in entry_dir.name:
            page = entry_dir / "index.html"
            if page.exists():
                return page
    return None


# ─────────────────────────────────────────────────────────────────────────────
# Extract Verso-rendered code blocks from an entry page
# ─────────────────────────────────────────────────────────────────────────────

# ─────────────────────────────────────────────────────────────────────────────
# Recover the true decl keyword from source
# ─────────────────────────────────────────────────────────────────────────────
#
# `extracted.json`'s `declKind` field can say "axiom" for decls that are in
# fact `theorem` in the source. This happens because `extract_decls` loads
# the project env via `importModules`, and Lean 4's module system resolves
# unexposed theorem bodies to their signature-only (axiom) form in the
# `.olean`. The decl keyword in the source file is ground truth — read it.

_LEAN_KEYWORDS = {
    "theorem", "lemma", "def", "abbrev", "opaque", "axiom",
    "structure", "class", "instance", "inductive",
    "example", "noncomputable",  # noncomputable is a modifier, stripped below
}

_ATTR_LINE_RE = re.compile(r"^\s*@\[.*?\]\s*$")


def true_decl_kind(source_path: str, start_line: int,
                   project_root: Path) -> str | None:
    """Return the first Lean declaration keyword at or after
    `source_path:start_line`, stepping over docstrings (`/-- … -/`),
    attribute lines (`@[...]`), and leading modifiers (`noncomputable`,
    `private`, etc.).

    `findDeclarationRanges?` reports the *start* of the declaration as the
    first docstring / attribute line above the keyword, not the keyword
    itself — so a forward scan is needed.  Returns `None` if nothing is
    found within ~30 lines.
    """
    if not source_path or not start_line:
        return None
    abs_path = project_root / source_path
    try:
        with abs_path.open() as f:
            lines = f.readlines()
    except OSError:
        return None
    skip_modifiers = {
        "noncomputable", "private", "protected", "public",
        "meta", "partial", "unsafe", "scoped", "local",
    }
    i = max(0, start_line - 1)
    in_block_comment = False
    n = min(i + 30, len(lines))
    while i < n:
        line = lines[i].strip()
        i += 1
        # Handle `/-- … -/` docstrings that may span multiple lines.
        if in_block_comment:
            if "-/" in line:
                in_block_comment = False
                rest = line.split("-/", 1)[1].strip()
                if not rest:
                    continue
                line = rest
            else:
                continue
        if line.startswith("/-"):
            if "-/" in line[2:]:
                line = line.split("-/", 1)[1].strip()
                if not line:
                    continue
            else:
                in_block_comment = True
                continue
        if not line or line.startswith("--"):
            continue
        # Skip an entire `@[...]` attribute line (single-line form).
        if _ATTR_LINE_RE.match(line) or line.startswith("@["):
            # Attributes can wrap; but if the closing `]` is on this line,
            # the attribute is done. Otherwise consume until we find one.
            if "]" not in line:
                while i < n and "]" not in lines[i]:
                    i += 1
                i += 1  # consume the line with `]`
            continue
        tokens = line.split()
        for tok in tokens:
            if tok in skip_modifiers:
                continue
            if tok in _LEAN_KEYWORDS:
                return tok
            # Non-keyword at the declaration slot — give up on this line.
            break
    return None


_MAIN_RE = re.compile(r"<main[\s>].*?</main>", re.DOTALL)
_CODE_BLOCK_RE = re.compile(
    r'(<code class="hl lean block"[^>]*>)(.*?)(</code>)', re.DOTALL
)
_HREF_RE = re.compile(r'href="([^"]+)"')
_ID_RE = re.compile(r'\sid="([^"]+)"')
_A_WITH_HREF_RE = re.compile(
    r'<a\s+(?P<pre>[^>]*?)href="(?P<href>[^"]+)"(?P<post>[^>]*?)>'
    r'(?P<inner>.*?)</a>',
    re.DOTALL,
)

# A single whitespace-only `<span class="inter-text">…</span>` (holds source
# whitespace between Verso tokens).
_INTERTEXT_WS_RE = re.compile(
    r'<span class="inter-text"[^>]*>\s*</span>', re.DOTALL
)

# The leading `/-- … -/` docstring Verso emits as a single
# `<span class="doc-comment token">…</span>`.
_LEAD_DOCCOMMENT_RE = re.compile(
    r'^\s*<span class="doc-comment token"[^>]*>.*?</span>\s*'
    r'(?:<span class="inter-text"[^>]*>\s*</span>\s*)*',
    re.DOTALL,
)

# `@[informal …]` attribute: matches from an `@[` unknown-token span through
# the next `]` unknown-token span at the top level. Attribute string args
# contain no `]`, so non-greedy matching is safe.
_INFORMAL_ATTR_RE = re.compile(
    r'<span class="unknown token"[^>]*>@\[</span>'
    r'.*?'
    r'<span class="[^"]*keyword[^"]*token[^"]*"[^>]*>informal</span>'
    r'.*?'
    r'<span class="unknown token"[^>]*>\]</span>\s*'
    r'(?:<span class="inter-text"[^>]*>\s*</span>\s*)*',
    re.DOTALL,
)


def _strip_metadata(inner: str) -> str:
    """Drop the leading `/-- … -/` docstring and the `@[informal …]` attribute
    from a code block's inner HTML.  Both are metadata that duplicate info
    shown in the dashboard's row header + code-head badge, so they add
    visual noise without carrying information.  Any `<span class="inter-text">`
    whitespace/newlines between the metadata blocks are also absorbed so the
    surviving content starts cleanly at `def`/`theorem`/etc.

    Applied post-extraction so the raw Verso output is untouched — flip this
    off by commenting out the call site if a user ever wants the metadata
    visible.
    """
    inner = _LEAD_DOCCOMMENT_RE.sub("", inner, count=1)
    inner = _INFORMAL_ATTR_RE.sub("", inner, count=1)
    # Absorb any remaining pure-whitespace inter-text spans at the very start.
    while True:
        new = _INTERTEXT_WS_RE.sub("", inner, count=1)
        if new == inner or not new.startswith("<span") or "inter-text" not in new[:80]:
            break
        inner = new
    return inner.lstrip()


def extract_code_blocks_raw(entry_page: Path) -> list[str]:
    """Return each `<code class="hl lean block">…</code>` verbatim from the
    entry page's `<main>`, with leading `/-- … -/` docstring and
    `@[informal …]` attribute stripped.  Uses byte-exact regex slicing
    because BS4's `html.parser` normalizes leading whitespace inside
    `<span>` text nodes, destroying Verso's source indentation encoded as
    `<span class="inter-text">\\n    </span>`.
    """
    text = entry_page.read_text()
    main_match = _MAIN_RE.search(text)
    if main_match is None:
        return []
    results: list[str] = []
    for m in _CODE_BLOCK_RE.finditer(main_match.group(0)):
        open_tag, inner, close_tag = m.group(1), m.group(2), m.group(3)
        results.append(open_tag + _strip_metadata(inner) + close_tag)
    return results


def rewrite_code_block_hrefs(block: str,
                             in_dashboard_ids: set[str]) -> str:
    """Rewrite `<a href>` URLs inside a code block.

    Strategy:
      * `#frag` / `http(s):` / `mailto:` → left alone.
      * Verso cross-ref whose fragment is also an `id` somewhere in the
        dashboard → collapse to `#frag` so the click stays in-page (the
        crossref click handler opens the owning row before scrolling).
      * Verso cross-ref to a decl NOT in the dashboard (only exists in the
        multi-page tree, e.g. `existsComplexManifoldOnConnectedComponent`)
        → unwrap the `<a>` tag entirely. The inner `<span>` styling is
        preserved; the dangling link to a disconnected Verso page is dropped.
    """
    def rewrite(m: re.Match) -> str:
        href = m.group("href")
        if href.startswith(("http://", "https://", "#", "mailto:")):
            return m.group(0)
        _path, _, frag = href.partition("#")
        if frag and frag in in_dashboard_ids:
            pre = m.group("pre")
            post = m.group("post")
            inner = m.group("inner")
            return f'<a {pre}href="#{frag}"{post}>{inner}</a>'
        # No in-dashboard target — strip the <a> wrapper, keep inner markup.
        return m.group("inner")
    return _A_WITH_HREF_RE.sub(rewrite, block)


def collect_ids(block: str) -> list[str]:
    """Pull every `id="…"` from a code block."""
    return _ID_RE.findall(block)


# ─────────────────────────────────────────────────────────────────────────────
# Row renderer (dashboard-style, with Verso-rendered code blocks)
# ─────────────────────────────────────────────────────────────────────────────

MATHLIB_DOCS_BASE = "https://leanprover-community.github.io/mathlib4_docs"


def is_external_decl(decl: dict, project_prefix: str) -> bool:
    """True when the decl lives outside the current project — e.g. a
    `#informal_external` pointer to a mathlib constant.  Detected by
    `moduleName` not starting with the project prefix."""
    module = decl.get("moduleName", "")
    return bool(module) and not module.startswith(project_prefix)


def render_external_panel(decl: dict) -> str:
    """Link-out panel for a `#informal_external` decl.  No Verso rendering —
    the upstream source lives outside BS's shadow project (mathlib,
    typically), so we surface the decl name + a link to the mathlib docs
    page rather than trying to mirror its code."""
    name = decl["declName"]
    module = decl.get("moduleName", "Mathlib")
    kind = decl.get("declKind", "")
    docs_url = f"{MATHLIB_DOCS_BASE}/{module.replace('.', '/')}.html#{name}"
    safe_name = html.escape(name)
    safe_module = html.escape(module)
    safe_kind = html.escape(kind)
    safe_url = html.escape(docs_url)
    source_label = "Mathlib" if module.startswith("Mathlib.") else "upstream"
    return f'''
<div class="lean-panel external-panel">
  <div class="code-head">
    <span class="decl">{safe_name} <span class="kind">{safe_kind}</span></span>
    <a href="{safe_url}" target="_blank" rel="noopener">view in {source_label} ↗</a>
  </div>
  <div class="external-note">
    Formalized upstream as <code>{safe_name}</code> in <code>{safe_module}</code>.
  </div>
</div>
'''


def render_lean_panel_verso(decl: dict, paper_ref: str, repo_url: str,
                            code_html: str | None,
                            project_root: Path) -> str:
    """Dashboard-styled lean panel whose body is a Verso `<code>` block.

    The panel deliberately omits the `@[informal "…"]` attribute badge and
    the leading docstring the original `generate_comparison.py` used to show
    — paperRef is already in the row's `c-ref` column, paperComment is
    redundant, and the docstring (when present) has been stripped from the
    embedded Verso block by `_strip_metadata`.

    Kind classification: prefer the real source keyword (`theorem`/`def`/…)
    over `extracted.json`'s `declKind` when they disagree. Lean 4's module
    system resolves unexposed theorem bodies to their signature-only (axiom)
    form in `.olean`s, and `extract_decls` classifies off `env.find?`, so
    legitimate theorems can leak through tagged as `"axiom"`. Reading the
    source gives ground truth.
    """
    decl_name = html.escape(decl["declName"])
    sf = decl.get("sourceFile", "")
    line = decl.get("startLine", "")
    kind_from_source = true_decl_kind(sf, line, project_root) if isinstance(line, int) else None
    kind = html.escape(kind_from_source or decl.get("declKind", ""))
    url = source_url(repo_url, decl)
    if code_html:
        # Verso's <code class="hl lean block"> already handles whitespace
        # (white-space: pre + display: block via extracted CSS), so we do NOT
        # wrap it in <pre> — the dashboard's `.codeblock pre { white-space:
        # pre-wrap }` rule would otherwise collapse the inter-text spans.
        body_html = code_html
    else:
        body_html = f'<pre><span class="tk-ident">{decl_name}</span></pre>'
    return f'''
<div class="lean-panel">
  <div class="code-head">
    <span class="decl">{decl_name} <span class="kind">{kind}</span></span>
    <a href="{html.escape(url)}" target="_blank" rel="noopener">view source ↗</a>
  </div>
  <div class="codeblock verso-codeblock">{body_html}</div>
</div>
'''


def render_row(row: dict, code_blocks_by_name: dict[str, str],
               repo_url: str, project_root: Path,
               project_prefix: str) -> str:
    ref = catchword(row["paperRef"])
    section = html.escape(row.get("section", ""))
    prose = html.escape(row["prose"])
    preview = html.escape(prose_preview(row["prose"]))
    status = row["status"]
    decls = row["declarations"]
    lines_range = ""
    if decls:
        start = min(d.get("startLine", 10**9) for d in decls)
        end = max(d.get("endLine", d.get("startLine", 0)) for d in decls)
        lines_range = f"L{start}" if start == end else f"L{start}–L{end}"

    if decls:
        panels = "".join(
            render_external_panel(d) if is_external_decl(d, project_prefix)
            else render_lean_panel_verso(d, row["paperRef"], repo_url,
                                         code_blocks_by_name.get(d["declName"]),
                                         project_root)
            for d in decls
        )
    else:
        panels = '<div class="lean-empty">Not yet formalized in this project.</div>'

    return f'''
<li class="entry s-{status}">
  <div class="head">
    <div class="c-ref">{html.escape(ref)}</div>
    <div class="c-status"><span class="pill s-{status}">{status}</span></div>
    <div class="c-preview">{preview}</div>
    <div class="c-line">{lines_range}</div>
    <div class="c-caret">›</div>
  </div>
  <div class="detail">
    <div class="detail-inner">
      <div>
        <span class="lbl">{section}</span>
        <p class="prose">{prose}</p>
      </div>
      <div class="lean-panels">{panels}</div>
    </div>
  </div>
</li>
'''


# ─────────────────────────────────────────────────────────────────────────────
# Supplementary <head> contents for Verso assets
# ─────────────────────────────────────────────────────────────────────────────

# Only load Verso's JS (tippy, popper for hover tooltips) + katex (math) +
# tippy's border CSS. We deliberately do NOT load `book.css` or `verso-vars.css`
# — those set page-level body/layout rules that clobber the dashboard's
# parchment theme. Code-highlighting CSS is extracted from an entry page's
# inline <style> block instead (see extract_hl_css).
VERSO_HEAD_JS = """
<script src="-verso-data/popper.min.js"></script>
<script src="-verso-data/tippy-bundle.umd.min.js"></script>
<link rel="stylesheet" href="-verso-data/tippy-border.css">
<link rel="stylesheet" href="-verso-data/katex/katex.css">
<script defer src="-verso-data/katex/katex.js"></script>
<script defer src="-verso-data/katex/math.js"></script>
"""

# Map Verso's code-color variables onto the dashboard's parchment palette so
# `.hl.lean .keyword` / `.const` / `.var` etc. pick up accent / blue / italic
# colors instead of bare black. These mirror the old `tk-*` classes in the
# live dashboard.
DASHBOARD_VERSO_VARS = """
<style>
:root {{
  --verso-code-color: var(--fg, #1b1b1b);
  --verso-code-keyword-color: var(--accent, #2c6742);
  --verso-code-keyword-weight: 500;
  --verso-code-const-color: #1d3f6e;
  --verso-code-var-color: var(--fg-mid, #4a4840);
  --verso-code-font-family: "JetBrains Mono", monospace;
  --verso-text-color: var(--fg, #1b1b1b);
}}
.codeblock.verso-codeblock {{
  padding: 12px 14px;
  font-family: "JetBrains Mono", monospace;
  font-size: 12.25px; line-height: 1.55; color: var(--fg);
  /* The existing dashboard .codeblock wrapper sets no whitespace rule;
     the inner <code class="hl lean block"> brings its own white-space:pre. */
  overflow-x: auto;
}}
.codeblock.verso-codeblock code.hl.lean.block {{
  display: block; white-space: pre; background: transparent;
  padding: 0; margin: 0;
}}
.codeblock.verso-codeblock .unknown {{ color: var(--fg-mid, #4a4840); }}
.codeblock.verso-codeblock .literal.string {{ color: #6e3a7a; }}
.codeblock.verso-codeblock .doc-comment {{
  color: var(--fg-faint, #b0ab9a); font-style: italic;
}}
/* Verso's cross-ref links inside code: keep them subtle. */
.codeblock.verso-codeblock a {{
  color: inherit; text-decoration: none;
  border-bottom: 1px dotted rgba(44,103,66,0.35);
}}
.codeblock.verso-codeblock a:hover {{
  border-bottom-color: var(--accent, #2c6742);
}}
/* New code-head slot: fully-qualified decl name + declKind pill.
   `.code-head` defaults to uppercase tracking; override to a readable mono
   style for the decl name. */
.code-head .decl {{
  font-family: "JetBrains Mono", monospace; font-weight: 500;
  font-size: 11.5px; color: var(--fg-mid); text-transform: none;
  letter-spacing: -0.01em; overflow: hidden; text-overflow: ellipsis;
  white-space: nowrap; min-width: 0; flex: 1 1 auto;
}}
.code-head .decl .kind {{
  color: var(--fg-faint); font-weight: 400; font-style: italic;
  margin-left: 6px;
}}
/* External (upstream / mathlib) panels: compact link-out rather than a
   code block.  The formalization lives outside the current project — we
   surface the decl name and a docs link instead of mirroring the source. */
.external-panel .external-note {{
  font-size: 13.5px; line-height: 1.5; color: var(--fg-mid);
  background: var(--bg-code); border: 1px solid var(--rule);
  padding: 10px 14px;
}}
.external-panel .external-note code {{
  font-family: "JetBrains Mono", monospace; font-size: 11.5px;
  color: var(--fg); background: var(--bg-row-alt);
  padding: 1px 6px; border: 1px solid var(--rule);
}}
.external-panel .code-head .decl .kind {{
  color: #1d3f6e; font-style: normal; font-weight: 500;
  text-transform: uppercase; letter-spacing: 0.08em; font-size: 9.5px;
  border: 1px solid rgba(29, 63, 110, 0.35);
  padding: 1px 6px 0; border-radius: 2px; margin-left: 8px;
}}
</style>
"""


def extract_hl_css(multi_root: Path) -> str:
    """Pull the `.hl.lean`/`.hover` CSS from any entry page's inline <style>.

    Verso emits this style block per page; its content is identical across
    pages. We grab it from the first entry we can find and strip the outer
    `<style>` tags.
    """
    for entry_page in multi_root.rglob("index.html"):
        if entry_page == multi_root / "index.html":
            continue
        soup = BeautifulSoup(entry_page.read_text(), "html.parser")
        style = soup.find("style")
        if style and style.string and ".hl.lean" in style.string:
            return f"<style>{style.string}</style>"
    return ""


def extract_hover_script(multi_root: Path) -> str:
    """Pull Verso's inline hover-init script from an entry page.

    Verso emits a ~400-line <script> near the end of each page that:
      * fetches -verso-docs.json,
      * wires `data-verso-hover` tokens to tippy tooltips,
      * manages binding highlights and the `onload` lifecycle.

    It's identical across entry pages. We grab it verbatim and inline it
    into the dashboard (the -verso-docs.json fetch is relative and works
    because we copy the JSON alongside index.html).
    """
    for entry_page in multi_root.rglob("index.html"):
        if entry_page == multi_root / "index.html":
            continue
        soup = BeautifulSoup(entry_page.read_text(), "html.parser")
        for script in soup.find_all("script"):
            text = script.string or ""
            if "window.onload" in text and "tippy" in text and "verso-docs" in text:
                return f"<script>{text}</script>"
    return ""


# Click handler for in-dashboard cross-references. Code-block anchors like
# `<a href="#CategoryTheory___Foo">…</a>` land inside a `.detail` panel that
# is `display: none` until its `li.entry` has the `open` class. Without this
# handler, clicking a cross-ref appends `#…` to the URL but scroll targets a
# hidden element (no-op). This also closes other entries to mirror the
# existing row-toggle behaviour.
CROSSREF_CLICK_SCRIPT = """
<script>
(function() {{
  document.addEventListener('click', (ev) => {{
    const a = ev.target.closest('.codeblock.verso-codeblock a[href^="#"]');
    if (!a) return;
    const id = a.getAttribute('href').slice(1);
    if (!id) return;
    const target = document.getElementById(id);
    if (!target) return;
    ev.preventDefault();
    const entry = target.closest('li.entry');
    if (entry) {{
      document.querySelectorAll('li.entry.open').forEach(x => {{
        if (x !== entry) x.classList.remove('open');
      }});
      entry.classList.add('open');
    }}
    // Scroll after the detail panel has been made visible.
    requestAnimationFrame(() => {{
      target.scrollIntoView({{ block: 'center', behavior: 'smooth' }});
      target.classList.add('xref-flash');
      setTimeout(() => target.classList.remove('xref-flash'), 1200);
    }});
    history.replaceState(null, '', '#' + id);
  }});
}})();
</script>
<style>
@keyframes xref-flash-kf {{
  from {{ background-color: rgba(161, 77, 43, 0.45); }}
  to   {{ background-color: transparent; }}
}}
.xref-flash {{ animation: xref-flash-kf 1s ease-out; }}
</style>
"""


def patch_page_template(template: str, hl_css: str, hover_script: str) -> str:
    """Inject Verso's code-highlighting CSS (in <head>) and its hover-init
    script plus a cross-ref click handler (at end of <body>) into the
    dashboard template.

    The dashboard's `PAGE_TEMPLATE` is a `str.format` template, so literal
    CSS/JS braces inside any injected content must be escaped as `{{`/`}}`.
    `VERSO_HEAD_JS` has none; `DASHBOARD_VERSO_VARS` and the crossref
    helpers have them escaped already; the freshly-extracted `hl_css` and
    `hover_script` both need doubling.
    """
    def esc(s: str) -> str:
        return s.replace("{", "{{").replace("}", "}}")

    head_inject = VERSO_HEAD_JS + DASHBOARD_VERSO_VARS + esc(hl_css)
    out = template.replace("</head>", head_inject + "\n</head>", 1)
    body_inject = (esc(hover_script) if hover_script else "") + CROSSREF_CLICK_SCRIPT
    out = out.replace("</body>", body_inject + "\n</body>", 1)
    return out


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--paper", required=True, help="Path to paper-statements.json")
    ap.add_argument("--extracted", required=True, help="Path to extract_decls JSON")
    ap.add_argument("--multi-html", required=True,
                    help="Verso multi-page HTML root (comparison-build/_out/html-multi)")
    ap.add_argument("--output", default="comparison-dashboard",
                    help="Output directory")
    ap.add_argument("--repo-url", default="https://github.com/mattrobball/BridgelandStability")
    ap.add_argument("--project-root", default=".",
                    help="Path to the Lean project root (for reading decl "
                         "sources to recover true keyword when extracted.json "
                         "misclassifies sorry'd/unexposed theorems as `axiom`)")
    ap.add_argument("--project-prefix", default="BridgelandStability",
                    help="Module-name prefix identifying local decls; any "
                         "decl whose moduleName is outside this prefix is "
                         "treated as external (e.g. mathlib) and rendered as "
                         "a link-out panel instead of a Verso code block.")
    ap.add_argument("--copy-entries", action="store_true",
                    help="(Deprecated) Copy the Verso multi-page tree into "
                         "OUTPUT/entries/. No longer needed — out-of-dashboard "
                         "cross-references are now unwrapped to plain <span>, "
                         "so the entries copy serves no purpose. Left in place "
                         "for backward-compat with older invocations.")
    args = ap.parse_args()

    paper_doc = json.loads(Path(args.paper).read_text())
    source_title = paper_doc.get("_meta", {}).get("source", {}).get(
        "title", "Stability conditions on triangulated categories"
    )

    rows = load_and_join(args.paper, args.extracted)

    # Upstream `extract_decls` can emit multiple entries for the same
    # `declName` when Lean 4's module system lets two `.lean` files claim
    # the same constant (e.g. `Spec.lean` + `NumericalStabilityManifold.lean`
    # both declaring `existsComplexManifoldOnConnectedComponent`). Every such
    # duplicate shares the same `startLine` from `findDeclarationRanges?` —
    # correct for one `sourceFile`, bogus for the other (past EOF). Dedupe
    # by `declName`, preferring the entry whose `(sourceFile, startLine)`
    # actually points inside the file.
    project_root_path = Path(args.project_root).resolve()
    def line_in_file(d: dict) -> bool:
        sf = d.get("sourceFile") or ""
        ln = d.get("startLine")
        if not sf or not isinstance(ln, int):
            return False
        try:
            with (project_root_path / sf).open() as f:
                return ln <= sum(1 for _ in f)
        except OSError:
            return False

    for row in rows:
        by_name: dict[str, dict] = {}
        order: list[str] = []
        for d in row["declarations"]:
            name = d.get("declName", "")
            if not name:
                continue
            if name not in by_name:
                order.append(name)
                by_name[name] = d
                continue
            # Same-name duplicate: prefer the entry whose source line is
            # actually inside its file.
            if line_in_file(d) and not line_in_file(by_name[name]):
                by_name[name] = d
        row["declarations"] = [by_name[n] for n in order]

    # Two-pass extraction:
    #   pass 1 — pull code blocks verbatim from each Verso entry page and
    #            collect every `id="…"` across all blocks so we know which
    #            cross-ref anchors are present in this dashboard.
    #   pass 2 — rewrite each block's `<a href>` attributes, collapsing
    #            to `#frag` when the target id is in-dashboard, else
    #            prefixing with `entries/` (copied multi-page tree).
    multi_root = Path(args.multi_html)
    raw_by_name: dict[str, str] = {}
    missing_entry: list[tuple[str, str]] = []

    statements_by_ref = {s["ref"]: s for s in paper_doc.get("statements", [])}

    for row in rows:
        decls = row["declarations"]
        if not decls:
            continue
        ref = row["paperRef"]
        stmt = statements_by_ref.get(ref, {})
        section_num = str(stmt.get("section", ""))
        page = find_entry_page(multi_root, section_num, ref) if section_num else None
        if page is None:
            missing_entry.append((ref, section_num or "?"))
            continue
        blocks = extract_code_blocks_raw(page)
        # Positional pairing: Verso emits one block per `@[informal]` decl
        # in the order `Informal.getEntriesFor` returns them.
        for decl, block in zip(decls, blocks):
            raw_by_name[decl["declName"]] = block

    in_dashboard_ids: set[str] = set()
    for block in raw_by_name.values():
        in_dashboard_ids.update(collect_ids(block))

    code_blocks_by_name: dict[str, str] = {
        name: rewrite_code_block_hrefs(block, in_dashboard_ids)
        for name, block in raw_by_name.items()
    }

    # ── Assemble output directory ───────────────────────────────────────────
    out_dir = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Copy Verso data dirs only — `book.css`/`verso-vars.css` are intentionally
    # omitted so Verso's page-level layout doesn't clobber our parchment theme.
    # The `.hl.lean` styling is inlined via `extract_hl_css` below.
    for name in ("-verso-data", "-verso-search"):
        src = multi_root / name
        if src.exists():
            dst = out_dir / name
            if dst.exists():
                shutil.rmtree(dst)
            shutil.copytree(src, dst, dirs_exist_ok=False)

    # `-verso-docs.json` is fetched by the hover-init script to populate
    # tippy tooltips for every `data-verso-hover` ID in the DOM. Without it
    # the fetch 404s and no tooltips ever attach.
    docs_json = multi_root / "-verso-docs.json"
    if docs_json.exists():
        shutil.copy2(docs_json, out_dir / "-verso-docs.json")

    if args.copy_entries:
        dst_entries = out_dir / "entries"
        if dst_entries.exists():
            shutil.rmtree(dst_entries)
        shutil.copytree(multi_root, dst_entries)

    # ── Render the single dashboard page ─────────────────────────────────────
    n_total = len(rows)
    n_complete = sum(1 for r in rows if r["status"] == "complete")
    n_incomplete = sum(1 for r in rows if r["status"] == "incomplete")
    n_missing = sum(1 for r in rows if r["status"] == "missing")

    rows_html = "\n".join(render_row(r, code_blocks_by_name, args.repo_url,
                                     project_root_path, args.project_prefix)
                          for r in rows)

    subtitle = (
        "Every numbered result from "
        f"<em>{html.escape(source_title)}</em>"
        " by Tom Bridgeland (2007), joined with "
        "<code>@[informal]</code>-tagged Lean declarations rendered via "
        "Verso + SubVerso. Click any row to expand."
    )

    hl_css = extract_hl_css(multi_root)
    hover_script = extract_hover_script(multi_root)
    patched_template = patch_page_template(PAGE_TEMPLATE, hl_css, hover_script)

    html_out = patched_template.format(
        source_title=html.escape(source_title),
        source_title_html=html.escape(source_title),
        subtitle=subtitle,
        n_total=n_total,
        n_complete=n_complete,
        n_incomplete=n_incomplete,
        n_missing=n_missing,
        rows=rows_html,
    )

    out_path = out_dir / "index.html"
    out_path.write_text(html_out)

    matched_code = len(code_blocks_by_name)
    print(f"wrote {out_path} ({out_path.stat().st_size:,} bytes)")
    print(f"  {n_total} rows · complete={n_complete} · "
          f"incomplete={n_incomplete} · missing={n_missing}")
    print(f"  {matched_code} Verso-rendered code blocks embedded")
    if missing_entry:
        print(f"  missing Verso entry page for: "
              f"{', '.join(f'{r} (§{s})' for r, s in missing_entry[:5])}"
              + (" …" if len(missing_entry) > 5 else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
