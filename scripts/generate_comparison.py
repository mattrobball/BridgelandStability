#!/usr/bin/env python3
"""Generate a comparison dashboard joining paper statements with Lean declarations.

Reads:
  paper-statements.json  — paper side (ref, kind, section, prose)
  extracted.json          — Lean side (from lake exe extract_decls)

Joins on paperRef. Rows with zero matching declarations render as "missing".

Writes:
  <output>/index.html  (single self-contained file; Google Fonts via <link>)
"""

from __future__ import annotations

import argparse
import html
import json
import re
from collections import defaultdict
from pathlib import Path


# ─────────────────────────────────────────────────────────────────────────────
# Lean tokenizer
# ─────────────────────────────────────────────────────────────────────────────

LEAN_KEYWORDS = {
    "theorem", "lemma", "def", "abbrev", "structure", "class", "instance",
    "inductive", "example", "noncomputable", "mutual", "partial",
    "namespace", "section", "end", "variable", "variables", "open", "import",
    "export", "universe", "universes",
    "where", "extends", "deriving", "fun", "λ", "let", "in",
    "if", "then", "else", "match", "with", "do", "return",
    "by", "from",
    "protected", "private", "local", "scoped", "attribute",
    "Prop", "Type", "Sort",
}

LEAN_SYMBOLS = {
    "→", "↦", "⟶", "↪", "↠", "⟹", "⟸", "⇒", "⇐",
    "∀", "∃", "¬", "∧", "∨", "∈", "∉", "⊂", "⊃", "⊆", "⊇",
    "≤", "≥", "≠", "≈", "≃", "≅", "∘", "⋆", "·", "•",
    "⊢", "⊣", "⊤", "⊥",
}

ASCII_OPS = [":=", "=>", "->", "<-", "::", "..", "?=", "!=", "<=", ">="]

_SYMBOL_CLASS = "[" + re.escape("".join(LEAN_SYMBOLS)) + "]"
_ASCII_OPS_RE = "|".join(re.escape(op) for op in ASCII_OPS)

_TOKEN_RE = re.compile(
    r"""
      (?P<block_comment> /-[\s\S]*?-/ )
    | (?P<line_comment>  --[^\n]* )
    | (?P<attribute>     @\[ [^\]]* \] )
    | (?P<string>        " (?: [^"\\] | \\. )* " )
    | (?P<number>        \b (?: 0x[0-9a-fA-F]+ | \d+ (?: \. \d+ )? ) \b )
    | (?P<ascii_op>      """ + _ASCII_OPS_RE + r""" )
    | (?P<symbol>        """ + _SYMBOL_CLASS + r""" )
    | (?P<word>          (?: [A-Za-z_] | [α-ωΑ-Ω𝒜-𝒵ℕℤℚℝℂℙ] )
                         (?: [A-Za-z0-9_'] | [₀-₉⁰-⁹ₐ-ₜ] | \. [A-Za-z_] )* )
    | (?P<brace>         [(){}\[\]⟨⟩⟦⟧] )
    | (?P<punct>         [,.;:|'+\-*/=<>~^&!?] )
    | (?P<space>         [\ \t]+ )
    | (?P<newline>       \n )
    """,
    re.VERBOSE,
)


def _looks_like_type_name(word: str) -> bool:
    tail = word.rsplit(".", 1)[-1]
    if not tail:
        return False
    return tail[0].isupper() or tail[0] in "𝒜𝒟ℕℤℚℝℂℙ"


def tokenize_lean(source: str) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    pos = 0
    for m in _TOKEN_RE.finditer(source):
        if m.start() != pos:
            out.append(("raw", source[pos:m.start()]))
        kind = m.lastgroup or "raw"
        text = m.group()
        if kind == "word":
            if text in LEAN_KEYWORDS:
                kind = "keyword"
            elif _looks_like_type_name(text):
                kind = "type"
            else:
                kind = "ident"
        out.append((kind, text))
        pos = m.end()
    if pos < len(source):
        out.append(("raw", source[pos:]))
    return out


def render_lean(source: str) -> str:
    parts: list[str] = []
    for kind, text in tokenize_lean(source):
        escaped = html.escape(text)
        if kind in ("space", "newline", "raw"):
            parts.append(escaped)
        else:
            parts.append(f'<span class="tk-{kind}">{escaped}</span>')
    return "".join(parts)


# ─────────────────────────────────────────────────────────────────────────────
# Data loading and joining
# ─────────────────────────────────────────────────────────────────────────────

SECTION_TITLES = {
    "1": "Introduction",
    "2": "Stability functions on abelian categories",
    "3": "t-structures and slicings",
    "4": "Quasi-abelian categories",
    "5": "Stability conditions",
    "6": "The space of stability conditions",
    "7": "Deformations of stability conditions",
    "8": "More on the space of stability conditions",
    "9": "Stability conditions on curves",
}


def load_and_join(paper_path: str, extracted_path: str) -> list[dict]:
    paper = json.loads(Path(paper_path).read_text())
    extracted = json.loads(Path(extracted_path).read_text())

    by_ref: dict[str, list[dict]] = defaultdict(list)
    for decl in extracted:
        ref = decl.get("paperRef")
        if ref:
            by_ref[ref].append(decl)

    rows = []
    for stmt in paper["statements"]:
        ref = stmt["ref"]
        decls = by_ref.get(ref, [])

        if decls:
            has_complete = any(
                d.get("paperStatus", "incomplete") == "complete" for d in decls
            )
            status = "complete" if has_complete else "incomplete"
        else:
            status = "missing"

        section_num = stmt.get("section", "")
        section_title = SECTION_TITLES.get(section_num, "")
        section_display = f"§{section_num}. {section_title}" if section_title else f"§{section_num}"

        rows.append({
            "paperRef": ref,
            "kind": stmt.get("kind", ""),
            "section": section_display,
            "prose": stmt.get("prose", ""),
            "status": status,
            "declarations": decls,
        })

    return rows


# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────

def catchword(paper_ref: str) -> str:
    return (
        paper_ref.replace("Definition ", "Def ")
                 .replace("Theorem ", "Thm ")
                 .replace("Lemma ", "Lem ")
                 .replace("Proposition ", "Prop ")
                 .replace("Corollary ", "Cor ")
                 .replace("Remark ", "Rem ")
    )


def source_url(repo_url: str, decl: dict) -> str:
    sf = decl.get("sourceFile", "")
    line = decl.get("startLine", 1)
    return f'{repo_url}/blob/main/{sf}#L{line}'


def prose_preview(prose: str, max_len: int = 80) -> str:
    text = prose.replace("\n", " ").strip()
    if len(text) <= max_len:
        return text
    return text[:max_len].rsplit(" ", 1)[0] + " …"


# ─────────────────────────────────────────────────────────────────────────────
# Page template
# ─────────────────────────────────────────────────────────────────────────────

PAGE_TEMPLATE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{source_title} · Comparison Index</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Public+Sans:ital,wght@0,300;0,400;0,500;0,600;0,700;1,400&family=JetBrains+Mono:ital,wght@0,400;0,500;1,400&display=swap" rel="stylesheet">
<style>
:root {{
  --bg:          #fbfaf6;
  --bg-row:      #fbfaf6;
  --bg-row-alt:  #f5f3ec;
  --bg-row-hover:#f0eee5;
  --bg-row-open: #f4f1e6;
  --bg-detail:   #f8f6ee;
  --bg-code:     #ffffff;
  --rule:        #e7e3d4;
  --rule-strong: #d6d0bb;
  --fg:          #1b1b1b;
  --fg-mid:      #4a4840;
  --fg-dim:      #817c6e;
  --fg-faint:    #b0ab9a;
  --accent:      #2c6742;
  --accent-soft: #4b8a5f;
  --warn:        #9a5518;
  --st-complete-fg: #2c6742;
  --st-complete-bd: rgba(44,103,66,0.40);
  --st-complete-bg: rgba(44,103,66,0.06);
  --st-incomplete-fg: #9a5518;
  --st-incomplete-bd: rgba(154,85,24,0.40);
  --st-incomplete-bg: rgba(154,85,24,0.06);
  --st-missing-fg:  #8a2e2a;
  --st-missing-bd:  rgba(138,46,42,0.40);
  --st-missing-bg:  rgba(138,46,42,0.06);
}}
* {{ box-sizing: border-box; }}
html, body {{
  margin: 0; padding: 0;
  background: var(--bg); color: var(--fg);
  font-family: "Public Sans", system-ui, sans-serif;
  font-size: 15px; line-height: 1.5;
  -webkit-font-smoothing: antialiased;
}}
a {{
  color: var(--accent); text-decoration: none;
  border-bottom: 1px solid rgba(44,103,66,0.3);
  transition: color 120ms ease, border-color 120ms ease;
}}
a:hover {{ color: var(--fg); border-bottom-color: currentColor; }}
.wrap {{ max-width: 1180px; margin: 0 auto; padding: 56px 36px 120px; }}

.masthead {{ margin-bottom: 40px; padding-bottom: 24px; border-bottom: 1px solid var(--rule-strong); }}
.masthead .kicker {{
  font-size: 11px; font-weight: 600; text-transform: uppercase;
  letter-spacing: 0.16em; color: var(--fg-dim); margin-bottom: 14px;
}}
.masthead .kicker .dot {{ color: var(--accent); margin: 0 6px; }}
.masthead h1 {{ font-weight: 600; font-size: 32px; line-height: 1.15; margin: 0 0 6px; color: var(--fg); }}
.masthead h1 em {{ font-weight: 500; font-style: italic; color: var(--fg-mid); }}
.masthead .sub {{ font-size: 14.5px; color: var(--fg-dim); line-height: 1.55; margin: 0; }}
.masthead .sub code {{
  font-family: "JetBrains Mono", monospace; font-size: 12.5px;
  color: var(--fg-mid); background: var(--bg-row-alt); padding: 1px 6px; border: 1px solid var(--rule);
}}
.masthead .meta-line {{
  display: flex; gap: 24px; margin-top: 14px;
  font-size: 12px; color: var(--fg-dim); font-variant-numeric: tabular-nums;
}}
.masthead .meta-line .k {{
  text-transform: uppercase; letter-spacing: 0.1em; font-weight: 600;
  color: var(--fg-faint); margin-right: 6px;
}}

ul.index {{ list-style: none; padding: 0; margin: 0; border-top: 1px solid var(--rule-strong); }}
ul.index > li.entry {{ border-bottom: 1px solid var(--rule); transition: background 140ms ease; }}
li.entry:nth-child(even) {{ background: var(--bg-row-alt); }}
li.entry:hover:not(.open) {{ background: var(--bg-row-hover); }}
li.entry.open {{ background: var(--bg-row-open); border-bottom-color: var(--rule-strong); }}

.head {{
  display: grid;
  grid-template-columns: 96px 132px 1fr 52px 20px;
  column-gap: 18px; align-items: baseline;
  padding: 14px 18px; cursor: pointer; user-select: none;
}}
.c-ref {{ font-weight: 600; font-size: 14px; color: var(--fg); font-variant-numeric: tabular-nums; }}
.c-status {{ line-height: 1; }}
.c-status .pill {{
  display: inline-block; font-size: 10px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.1em;
  padding: 3px 8px 2px; border: 1px solid; border-radius: 2px;
  line-height: 1.35; white-space: nowrap;
}}
.c-status .pill.s-complete   {{ color: var(--st-complete-fg); border-color: var(--st-complete-bd); background: var(--st-complete-bg); }}
.c-status .pill.s-incomplete {{ color: var(--st-incomplete-fg); border-color: var(--st-incomplete-bd); background: var(--st-incomplete-bg); }}
.c-status .pill.s-missing    {{ color: var(--st-missing-fg); border-color: var(--st-missing-bd); background: var(--st-missing-bg); }}
.c-preview {{
  font-size: 14px; color: var(--fg-mid); min-width: 0;
  overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
}}
.c-line {{
  font-family: "JetBrains Mono", monospace; font-size: 12px;
  color: var(--fg-dim); text-align: right; font-variant-numeric: tabular-nums;
}}
.c-caret {{
  color: var(--fg-faint); text-align: center; font-size: 11px; line-height: 1;
  transition: transform 180ms ease, color 180ms ease;
  font-family: "JetBrains Mono", monospace;
}}
li.entry.open .c-caret {{ transform: rotate(90deg); color: var(--accent); }}

.detail {{ display: none; padding: 4px 18px 22px; }}
li.entry.open .detail {{ display: block; }}
.detail-inner {{
  padding-top: 14px; border-top: 1px dashed var(--rule-strong);
  display: flex; flex-direction: column; gap: 22px; min-width: 0;
}}
.detail .lbl {{
  display: block; font-size: 10px; font-weight: 700;
  text-transform: uppercase; letter-spacing: 0.14em;
  color: var(--fg-faint); margin-bottom: 10px;
}}
.detail .prose {{ font-size: 15px; line-height: 1.62; color: var(--fg); margin: 0; }}
.lean-panels {{ display: flex; flex-direction: column; gap: 18px; min-width: 0; }}
.lean-panel + .lean-panel {{ padding-top: 14px; border-top: 1px dashed var(--rule); }}
.lean-empty {{
  padding: 16px 18px; border: 1px dashed var(--st-missing-bd);
  background: var(--st-missing-bg); color: var(--st-missing-fg);
  font-size: 13.5px; font-style: italic; text-align: center; border-radius: 2px;
}}
.lean-empty::before {{ content: "∅  "; font-style: normal; margin-right: 4px; opacity: 0.8; }}

.codeblock {{
  background: var(--bg-code); border: 1px solid var(--rule);
  padding: 14px 16px; min-width: 0; overflow: hidden;
}}
.codeblock pre {{
  margin: 0; font-family: "JetBrains Mono", monospace;
  font-size: 12.5px; line-height: 1.6; color: var(--fg);
  white-space: pre-wrap; overflow-wrap: break-word;
}}
.code-head {{
  display: flex; justify-content: space-between; align-items: baseline;
  gap: 12px; margin-bottom: 10px;
  font-size: 10.5px; font-weight: 600; text-transform: uppercase;
  letter-spacing: 0.14em; color: var(--fg-faint);
}}
.code-head .attr {{
  font-family: "JetBrains Mono", monospace; font-weight: 500;
  font-size: 11px; color: var(--accent); text-transform: none; letter-spacing: -0.01em;
}}
.code-head a {{
  font-weight: 500; text-transform: none; letter-spacing: 0; font-size: 12px;
  border-bottom: 1px solid rgba(44,103,66,0.4);
}}
.code-foot {{
  display: flex; justify-content: space-between; align-items: baseline;
  margin-top: 8px; font-family: "JetBrains Mono", monospace;
  font-size: 10.5px; color: var(--fg-faint); gap: 14px;
}}
.code-foot .decl {{ overflow: hidden; text-overflow: ellipsis; white-space: nowrap; min-width: 0; }}

.tk-keyword    {{ color: var(--accent); font-weight: 500; }}
.tk-type       {{ color: #1d3f6e; }}
.tk-symbol     {{ color: var(--warn); }}
.tk-ascii_op   {{ color: var(--warn); }}
.tk-attribute  {{ color: #6e3a7a; font-style: italic; }}
.tk-number     {{ color: #6e3a7a; }}
.tk-string     {{ color: #6e3a7a; }}
.tk-line_comment, .tk-block_comment {{ color: var(--fg-faint); font-style: italic; }}
.tk-brace      {{ color: var(--fg-mid); }}
.tk-punct      {{ color: var(--fg-mid); }}
.tk-ident      {{ color: var(--fg); }}

footer.colophon {{
  margin-top: 64px; padding-top: 20px; border-top: 1px solid var(--rule);
  display: flex; justify-content: space-between; gap: 16px;
  font-size: 11.5px; color: var(--fg-faint); font-variant-numeric: tabular-nums;
}}
footer.colophon .mark {{ text-transform: uppercase; letter-spacing: 0.1em; color: var(--accent); font-weight: 600; }}

@media (max-width: 760px) {{
  .wrap {{ padding: 40px 22px 80px; }}
  .head {{ grid-template-columns: 88px 1fr 18px; column-gap: 12px; padding: 12px 14px; row-gap: 4px; }}
  .c-status {{ grid-column: 1; grid-row: 2; }}
  .c-preview {{ grid-row: 1 / span 1; }}
  .c-line {{ display: none; }}
  .c-caret {{ grid-column: 3; grid-row: 1; }}
  .detail {{ padding: 4px 14px 20px; }}
  .masthead h1 {{ font-size: 26px; }}
  .masthead .meta-line {{ flex-wrap: wrap; gap: 10px 20px; }}
}}
</style>
</head>
<body>
<div class="wrap">

  <header class="masthead">
    <div class="kicker">lean-informal <span class="dot">·</span> comparison index</div>
    <h1><em>{source_title_html}</em></h1>
    <p class="sub">{subtitle}</p>
    <div class="meta-line">
      <span><span class="k">entries</span>{n_total}</span>
      <span><span class="k">complete</span>{n_complete}</span>
      <span><span class="k">incomplete</span>{n_incomplete}</span>
      <span><span class="k">missing</span>{n_missing}</span>
    </div>
  </header>

  <ul class="index">
    {rows}
  </ul>

  <footer class="colophon">
    <span>click any row to expand</span>
    <span class="mark">BridgelandStability</span>
  </footer>

</div>
<script>
(function() {{
  const entries = document.querySelectorAll('li.entry');
  entries.forEach(li => {{
    li.querySelector('.head').addEventListener('click', () => {{
      li.classList.toggle('open');
    }});
  }});
}})();
</script>
</body>
</html>
"""


# ─────────────────────────────────────────────────────────────────────────────
# Row rendering
# ─────────────────────────────────────────────────────────────────────────────

def render_attribute(paper_ref: str, paper_comment: str | None) -> str:
    ref = html.escape(paper_ref)
    if paper_comment:
        return f'@[informal "{ref}" "{html.escape(paper_comment)}"]'
    return f'@[informal "{ref}"]'


def render_lean_panel(decl: dict, paper_ref: str, repo_url: str) -> str:
    decl_name = html.escape(decl["declName"])
    kind = html.escape(decl.get("declKind", ""))
    sf = decl.get("sourceFile", "")
    line = decl.get("startLine", "")
    url = source_url(repo_url, decl)
    attr_text = render_attribute(paper_ref, decl.get("paperComment"))
    sig = decl.get("signature")
    if sig:
        lean_html = render_lean(sig)
    else:
        lean_html = f'<span class="tk-ident">{decl_name}</span>'

    return f'''
<div class="lean-panel">
  <div class="code-head">
    <span class="attr">{attr_text}</span>
    <a href="{html.escape(url)}" target="_blank" rel="noopener">view source ↗</a>
  </div>
  <div class="codeblock"><pre>{lean_html}</pre></div>
  <div class="code-foot">
    <span class="decl">{decl_name} · <em>{kind}</em></span>
    <span>{html.escape(sf)}:{line}</span>
  </div>
</div>
'''


def render_row(row: dict, repo_url: str) -> str:
    ref = catchword(row["paperRef"])
    section = html.escape(row.get("section", ""))
    prose = html.escape(row["prose"])
    preview = html.escape(prose_preview(row["prose"]))
    status = row["status"]
    decls = row.get("declarations", [])

    line_display = ""
    if decls:
        line_display = str(decls[0].get("startLine", ""))
        if len(decls) > 1:
            line_display = ""

    if decls:
        panels_html = "".join(
            render_lean_panel(decl, row["paperRef"], repo_url) for decl in decls
        )
    else:
        panels_html = '<div class="lean-empty">Not yet formalized in this project.</div>'

    return f'''
<li class="entry">
  <div class="head">
    <span class="c-ref">{html.escape(ref)}</span>
    <span class="c-status"><span class="pill s-{status}">{html.escape(status)}</span></span>
    <span class="c-preview">{preview}</span>
    <span class="c-line">{html.escape(line_display)}</span>
    <span class="c-caret">›</span>
  </div>
  <div class="detail">
    <div class="detail-inner">
      <div class="prose-block">
        <span class="lbl">{section} · paper statement</span>
        <p class="prose">{prose}</p>
      </div>
      <div class="lean-panels">{panels_html}</div>
    </div>
  </div>
</li>
'''


def render_page(rows: list[dict], source_title: str, repo_url: str) -> str:
    n_total = len(rows)
    n_complete = sum(1 for r in rows if r["status"] == "complete")
    n_incomplete = sum(1 for r in rows if r["status"] == "incomplete")
    n_missing = sum(1 for r in rows if r["status"] == "missing")

    subtitle = (
        "Paper statements from <em>" + html.escape(source_title) + "</em>"
        " by Tom Bridgeland (2007), joined with "
        "<code>@[informal]</code>-tagged Lean declarations. Click any row to expand."
    )

    rows_html = "\n".join(render_row(row, repo_url) for row in rows)

    return PAGE_TEMPLATE.format(
        source_title=html.escape(source_title),
        source_title_html=html.escape(source_title),
        subtitle=subtitle,
        n_total=n_total,
        n_complete=n_complete,
        n_incomplete=n_incomplete,
        n_missing=n_missing,
        rows=rows_html,
    )


# ─────────────────────────────────────────────────────────────────────────────
# main
# ─────────────────────────────────────────────────────────────────────────────

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--paper", required=True, help="Path to paper-statements.json")
    p.add_argument("--extracted", required=True, help="Path to extractor output JSON")
    p.add_argument("--output", default="comparison-out", help="Output directory")
    p.add_argument("--repo-url", default="https://github.com/mattrobball/BridgelandStability")
    args = p.parse_args()

    paper = json.loads(Path(args.paper).read_text())
    source_title = paper.get("_meta", {}).get("source", {}).get(
        "title", "Stability conditions on triangulated categories"
    )

    rows = load_and_join(args.paper, args.extracted)

    out_dir = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "index.html"
    out_path.write_text(render_page(rows, source_title, args.repo_url))
    print(f"wrote {out_path} ({out_path.stat().st_size:,} bytes, {len(rows)} rows)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
