#!/usr/bin/env python3
"""Generate the Coverage & Fidelity dashboard as a self-contained HTML page.

Reads:
  - artifacts/coverage-data.json  (per-declaration status, summary, notes)
  - informalizations.json         (optional — supplies source file + line
                                   numbers for links into GitHub)

Writes:
  - <output>/index.html           (single self-contained file, no external
                                   assets at runtime)

The dashboard is designed for mathematicians who do not read Lean. It
favours natural language summaries of each paper declaration, hides Lean
identifiers behind collapsibles, and uses clear status categories with
optional "notes" that explain every fidelity gap.
"""

from __future__ import annotations

import argparse
import html
import json
import os
import re
import sys
from collections import Counter
from typing import Any


# ── Status metadata ────────────────────────────────────────────────────────

STATUS_ORDER = [
    "complete",
    "generalized",
    "stronger_hyp",
    "partial",
    "statement_only",
    "missing",
]

STATUS_LABEL = {
    "complete": "Complete",
    "generalized": "Generalized",
    "stronger_hyp": "Stronger hypotheses",
    "partial": "Partial",
    "statement_only": "Statement only",
    "missing": "Not formalized",
}

STATUS_GLYPH = {
    "complete": "\u25cf",          # solid dot
    "generalized": "\u25c6",       # solid diamond
    "stronger_hyp": "\u25b2",      # solid triangle
    "partial": "\u25d0",           # half-filled circle
    "statement_only": "\u25cb",    # hollow circle
    "missing": "\u00d7",           # cross
}


KIND_LABEL = {
    "definition": "Definition",
    "lemma": "Lemma",
    "proposition": "Proposition",
    "theorem": "Theorem",
    "corollary": "Corollary",
}


# ── Light-weight inline math rendering ────────────────────────────────────

_MATH_RE = re.compile(r"\$([^$\n]+)\$")


def render_text(text: str) -> str:
    """Escape HTML and turn `$...$` spans into italic math-styled spans.

    This is intentionally minimal: we want the summaries to read as prose,
    and full KaTeX would require external assets at runtime. The goal is
    just to visually separate short inline math from surrounding text.
    """
    if text is None:
        return ""
    out: list[str] = []
    idx = 0
    for m in _MATH_RE.finditer(text):
        out.append(html.escape(text[idx:m.start()]))
        out.append(f"<span class=\"math\">{html.escape(m.group(1))}</span>")
        idx = m.end()
    out.append(html.escape(text[idx:]))
    return "".join(out)


# ── Informalizations lookup ───────────────────────────────────────────────

def load_informal_index(path: str | None) -> dict[str, dict]:
    if not path or not os.path.exists(path):
        return {}
    with open(path) as f:
        data = json.load(f)
    if isinstance(data, list):
        return {e["declName"]: e for e in data if e.get("declName")}
    return {}


def github_source_url(
    repo_url: str,
    branch: str,
    entry: dict | None,
) -> str | None:
    if not entry:
        return None
    src = entry.get("sourceFile")
    line = entry.get("startLine")
    if not src:
        return None
    base = repo_url.rstrip("/")
    if line:
        return f"{base}/blob/{branch}/{src}#L{line}"
    return f"{base}/blob/{branch}/{src}"


def api_docs_url(decl: str | None) -> str | None:
    if not decl:
        return None
    # Placeholder: the deployed API docs live under /api/ in the same site.
    # doc-gen4 uses flat slugs. We link relative to the site root.
    return f"../api/find/?pattern={decl}"


# ── HTML emitters ─────────────────────────────────────────────────────────

CSS = """
:root {
  --bg:            #fbf9f4;
  --bg-soft:       #f5f1e6;
  --surface:       #ffffff;
  --rule:          #e7e0cd;
  --rule-strong:   #d5cdb4;
  --text:          #23232a;
  --muted:         #6e6a60;
  --dim:           #948f82;
  --accent:        #39486b;
  --math:          #5b4a85;
  --link:          #2e4c7a;
  --link-hover:    #1c3358;
  --shadow:        0 1px 0 rgba(30,25,10,0.04), 0 1px 3px rgba(30,25,10,0.06);
  --shadow-strong: 0 2px 8px rgba(30,25,10,0.08);
  --radius:        6px;

  /* status palette: muted, earthy, paper-friendly */
  --s-complete-bg:       #e6efdd;
  --s-complete-fg:       #2c5a36;
  --s-complete-ring:     #b4cd9b;

  --s-generalized-bg:    #dcece9;
  --s-generalized-fg:    #215a5c;
  --s-generalized-ring:  #9bc4c0;

  --s-stronger-bg:       #f4e6c8;
  --s-stronger-fg:       #73491b;
  --s-stronger-ring:     #dbc088;

  --s-partial-bg:        #f6e1cd;
  --s-partial-fg:        #743910;
  --s-partial-ring:      #e2b185;

  --s-statement-bg:      #dfe4ef;
  --s-statement-fg:      #384266;
  --s-statement-ring:    #a6b0cd;

  --s-missing-bg:        #efd9d5;
  --s-missing-fg:        #723733;
  --s-missing-ring:      #cf9c95;
}

* { box-sizing: border-box; }

html, body {
  margin: 0;
  padding: 0;
  background: var(--bg);
  color: var(--text);
  font-family: "Inter", -apple-system, "Segoe UI", "Helvetica Neue", Arial, sans-serif;
  font-size: 16px;
  line-height: 1.55;
  -webkit-font-smoothing: antialiased;
}

a {
  color: var(--link);
  text-decoration: none;
  border-bottom: 1px solid rgba(46, 76, 122, 0.25);
  transition: border-color 120ms ease, color 120ms ease;
}
a:hover {
  color: var(--link-hover);
  border-bottom-color: currentColor;
}

/* ── Page chrome ───────────────────────────────────────────────── */

.page {
  max-width: 1040px;
  margin: 0 auto;
  padding: 48px 32px 96px;
}

header.masthead {
  display: grid;
  grid-template-columns: 1fr auto;
  gap: 32px;
  align-items: end;
  padding-bottom: 24px;
  border-bottom: 1px solid var(--rule-strong);
  margin-bottom: 40px;
}
header.masthead .title {
  font-family: "Iowan Old Style", "Charter", "Georgia", "Times New Roman", serif;
  font-size: 34px;
  font-weight: 600;
  line-height: 1.15;
  letter-spacing: -0.01em;
  margin: 0 0 6px;
  color: #1a1a20;
}
header.masthead .subtitle {
  color: var(--muted);
  font-size: 15px;
  max-width: 54ch;
}
header.masthead .paper-ref {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-style: italic;
  color: var(--muted);
  font-size: 14px;
  text-align: right;
  max-width: 22ch;
  line-height: 1.4;
}
header.masthead .paper-ref a { color: var(--muted); border-bottom-color: rgba(110,106,96,0.3); }
header.masthead .paper-ref a:hover { color: var(--link-hover); }

/* ── Introduction ──────────────────────────────────────────────── */

.intro {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-size: 17.5px;
  line-height: 1.65;
  color: #2c2c32;
  max-width: 66ch;
  margin: 0 0 36px;
}
.intro p { margin: 0 0 14px; }
.intro .math { color: var(--math); }

/* ── Legend / filters ─────────────────────────────────────────── */

.legend {
  background: var(--surface);
  border: 1px solid var(--rule);
  border-radius: var(--radius);
  box-shadow: var(--shadow);
  padding: 18px 22px 20px;
  margin: 0 0 40px;
}
.legend h2 {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-size: 14px;
  font-weight: 600;
  letter-spacing: 0.08em;
  text-transform: uppercase;
  color: var(--muted);
  margin: 0 0 14px;
}
.legend-items {
  display: flex;
  flex-wrap: wrap;
  gap: 10px 14px;
}
.legend-item {
  display: inline-flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
  user-select: none;
  font-size: 14px;
  padding: 6px 12px 6px 10px;
  border-radius: 999px;
  border: 1px solid transparent;
  background: transparent;
  transition: background 120ms ease, border-color 120ms ease, opacity 120ms ease;
  position: relative;
}
.legend-item .count {
  font-variant-numeric: tabular-nums;
  color: var(--dim);
  font-size: 12.5px;
}
.legend-item[aria-pressed="false"] { opacity: 0.45; }
.legend-item:hover { background: var(--bg-soft); }

/* Legend hover tooltip explaining each status. */
.legend-item .defn {
  position: absolute;
  left: 0;
  top: calc(100% + 8px);
  width: 290px;
  background: #2a2a30;
  color: #f6f3ea;
  border-radius: 6px;
  padding: 10px 12px;
  font-size: 12.5px;
  line-height: 1.5;
  opacity: 0;
  pointer-events: none;
  transform: translateY(-2px);
  transition: opacity 120ms ease, transform 120ms ease;
  box-shadow: var(--shadow-strong);
  z-index: 20;
}
.legend-item:hover .defn,
.legend-item:focus-visible .defn {
  opacity: 1;
  transform: translateY(0);
}

/* ── Status chip (shared) ─────────────────────────────────────── */

.chip {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  font-size: 12.5px;
  font-weight: 500;
  letter-spacing: 0.01em;
  padding: 3px 10px;
  border-radius: 999px;
  border: 1px solid transparent;
  white-space: nowrap;
}
.chip .glyph { font-size: 10px; line-height: 1; }

.chip.s-complete       { background: var(--s-complete-bg);    color: var(--s-complete-fg);    border-color: var(--s-complete-ring); }
.chip.s-generalized    { background: var(--s-generalized-bg); color: var(--s-generalized-fg); border-color: var(--s-generalized-ring); }
.chip.s-stronger_hyp   { background: var(--s-stronger-bg);    color: var(--s-stronger-fg);    border-color: var(--s-stronger-ring); }
.chip.s-partial        { background: var(--s-partial-bg);     color: var(--s-partial-fg);     border-color: var(--s-partial-ring); }
.chip.s-statement_only { background: var(--s-statement-bg);   color: var(--s-statement-fg);   border-color: var(--s-statement-ring); }
.chip.s-missing        { background: var(--s-missing-bg);     color: var(--s-missing-fg);     border-color: var(--s-missing-ring); }

/* ── Sections ─────────────────────────────────────────────────── */

.section {
  margin: 0 0 44px;
}
.section-head {
  display: grid;
  grid-template-columns: 80px 1fr;
  gap: 24px;
  align-items: baseline;
  padding-bottom: 10px;
  margin-bottom: 22px;
  border-bottom: 1px solid var(--rule);
}
.section-head .sec-num {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-size: 38px;
  font-weight: 500;
  color: var(--rule-strong);
  letter-spacing: -0.02em;
  line-height: 1;
  text-align: right;
  font-variant-numeric: lining-nums;
}
.section-head .sec-title {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-size: 22px;
  font-weight: 600;
  margin: 0 0 4px;
  color: #1f1f25;
  letter-spacing: -0.005em;
}
.section-head .sec-blurb {
  color: var(--muted);
  font-size: 14.5px;
  max-width: 62ch;
}

/* ── Entry cards ──────────────────────────────────────────────── */

.entries {
  display: flex;
  flex-direction: column;
  gap: 14px;
  margin-left: 104px;
}
.entries::before {
  /* unused; spacing handled by grid */
  content: none;
}

.entry {
  background: var(--surface);
  border: 1px solid var(--rule);
  border-radius: var(--radius);
  box-shadow: var(--shadow);
  padding: 18px 22px;
  transition: opacity 140ms ease, transform 140ms ease, box-shadow 140ms ease;
}
.entry[hidden] { display: none !important; }
.entry.headline {
  border-color: var(--rule-strong);
  box-shadow: var(--shadow-strong);
}
.entry.headline::before {
  content: "Headline result";
  display: inline-block;
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-size: 11px;
  font-weight: 600;
  letter-spacing: 0.12em;
  text-transform: uppercase;
  color: var(--accent);
  margin-bottom: 6px;
}

.entry-head {
  display: flex;
  align-items: baseline;
  flex-wrap: wrap;
  gap: 10px 14px;
  margin-bottom: 10px;
}
.entry-head .paper-id {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-size: 13px;
  font-weight: 600;
  letter-spacing: 0.03em;
  color: var(--accent);
  background: var(--bg-soft);
  border: 1px solid var(--rule);
  padding: 3px 10px;
  border-radius: 4px;
  white-space: nowrap;
}
.entry-head .title {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-size: 19px;
  font-weight: 600;
  color: #1f1f25;
  line-height: 1.25;
  flex: 1 1 auto;
  min-width: 12ch;
}
.entry-head .title .math { color: var(--math); font-style: italic; }
.entry-head .chip { margin-left: auto; }

.summary {
  margin: 0 0 10px;
  color: #31313a;
  font-size: 15.5px;
  max-width: 68ch;
}
.summary .math { color: var(--math); font-style: italic; }

.note {
  display: grid;
  grid-template-columns: 16px 1fr;
  gap: 10px;
  margin-top: 10px;
  padding: 10px 14px;
  background: #f9f5ea;
  border-left: 3px solid var(--rule-strong);
  border-radius: 0 4px 4px 0;
  color: #4a4436;
  font-size: 13.5px;
  line-height: 1.55;
}
.note .glyph {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-style: italic;
  font-weight: 700;
  color: var(--accent);
  text-align: center;
  font-size: 14px;
  padding-top: 1px;
}
.note .math { color: var(--math); font-style: italic; }

details.lean {
  margin-top: 12px;
  font-size: 13px;
  color: var(--muted);
  border-top: 1px dashed var(--rule);
  padding-top: 10px;
}
details.lean > summary {
  list-style: none;
  cursor: pointer;
  display: inline-flex;
  align-items: center;
  gap: 6px;
  color: var(--muted);
  user-select: none;
  transition: color 120ms ease;
}
details.lean > summary::-webkit-details-marker { display: none; }
details.lean > summary::before {
  content: "\\25b8";  /* ▸ */
  display: inline-block;
  font-size: 10px;
  transition: transform 120ms ease;
  color: var(--dim);
}
details.lean[open] > summary::before {
  transform: rotate(90deg);
}
details.lean > summary:hover { color: var(--text); }
details.lean > summary .label {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-style: italic;
  font-size: 13px;
  letter-spacing: 0.01em;
}

.lean-body {
  margin-top: 10px;
  display: grid;
  grid-template-columns: 92px 1fr;
  row-gap: 6px;
  column-gap: 14px;
  font-size: 13px;
  color: var(--muted);
}
.lean-body dt {
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-style: italic;
  color: var(--dim);
}
.lean-body dd {
  margin: 0;
  overflow-wrap: anywhere;
}
.lean-body .code {
  font-family: "SF Mono", "JetBrains Mono", "Menlo", "Consolas", monospace;
  font-size: 12.5px;
  color: #2a2a32;
  background: var(--bg-soft);
  padding: 1px 6px;
  border-radius: 3px;
  border: 1px solid var(--rule);
}
.lean-body .links {
  display: flex;
  flex-wrap: wrap;
  gap: 6px 14px;
  margin-top: 4px;
}
.lean-body .links a {
  font-size: 12.5px;
}

.missing-body {
  margin-top: 10px;
  font-size: 13px;
  font-style: italic;
  color: var(--dim);
}

/* ── Footer ───────────────────────────────────────────────────── */

footer.colophon {
  margin-top: 64px;
  padding-top: 20px;
  border-top: 1px solid var(--rule);
  color: var(--dim);
  font-size: 12.5px;
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  gap: 12px;
  font-family: "Iowan Old Style", "Charter", "Georgia", serif;
  font-style: italic;
}

/* ── Responsive ───────────────────────────────────────────────── */

@media (max-width: 760px) {
  .page { padding: 32px 18px 64px; }
  header.masthead {
    grid-template-columns: 1fr;
    gap: 10px;
    align-items: start;
  }
  header.masthead .paper-ref { text-align: left; }
  .section-head {
    grid-template-columns: 1fr;
    gap: 4px;
  }
  .section-head .sec-num { text-align: left; font-size: 28px; }
  .entries { margin-left: 0; }
}
"""


JS = """
(function () {
  const items = document.querySelectorAll('.legend-item');
  const entries = document.querySelectorAll('.entry');
  const active = new Set();

  items.forEach((btn) => {
    active.add(btn.dataset.status);
    btn.setAttribute('aria-pressed', 'true');
    btn.addEventListener('click', () => {
      const s = btn.dataset.status;
      if (active.has(s)) {
        active.delete(s);
        btn.setAttribute('aria-pressed', 'false');
      } else {
        active.add(s);
        btn.setAttribute('aria-pressed', 'true');
      }
      if (active.size === 0) {
        // clicking the last active chip reselects all — avoid an empty view
        items.forEach((b) => { active.add(b.dataset.status); b.setAttribute('aria-pressed', 'true'); });
      }
      entries.forEach((el) => {
        el.hidden = !active.has(el.dataset.status);
      });
      document.querySelectorAll('.section').forEach((sec) => {
        const visible = sec.querySelectorAll('.entry:not([hidden])').length;
        sec.hidden = visible === 0;
      });
    });
  });
})();
"""


def chip_html(status: str) -> str:
    label = STATUS_LABEL[status]
    glyph = STATUS_GLYPH[status]
    return (
        f'<span class="chip s-{status}">'
        f'<span class="glyph" aria-hidden="true">{glyph}</span>{label}'
        f'</span>'
    )


def legend_html(counts: dict[str, int], legend: dict[str, str]) -> str:
    parts = ['<div class="legend-items" role="group" aria-label="Filter by status">']
    for status in STATUS_ORDER:
        count = counts.get(status, 0)
        defn = html.escape(legend.get(status, ""))
        parts.append(
            f'<button type="button" class="legend-item chip s-{status}" '
            f'data-status="{status}" aria-pressed="true">'
            f'<span class="glyph" aria-hidden="true">{STATUS_GLYPH[status]}</span>'
            f'{STATUS_LABEL[status]}'
            f'<span class="count">({count})</span>'
            f'<span class="defn" role="tooltip">{defn}</span>'
            f'</button>'
        )
    parts.append("</div>")
    return "".join(parts)


def entry_html(
    entry: dict,
    informal_index: dict[str, dict],
    repo_url: str,
    branch: str,
) -> str:
    status = entry["status"]
    headline = " headline" if entry.get("headline") else ""
    title_html = render_text(entry["title"])
    summary_html = render_text(entry.get("summary", ""))

    paper_id = html.escape(entry["id"])

    head = [
        f'<div class="entry-head">',
        f'  <span class="paper-id" title="Reference to {html.escape(entry.get("kind", "").title())} in the paper">{paper_id}</span>',
        f'  <span class="title">{title_html}</span>',
        f'  {chip_html(status)}',
        f'</div>',
    ]

    body = [f'<p class="summary">{summary_html}</p>']

    if entry.get("note"):
        body.append(
            '<div class="note">'
            '<span class="glyph" aria-hidden="true">!</span>'
            f'<div>{render_text(entry["note"])}</div>'
            '</div>'
        )

    decl = entry.get("lean_decl")
    if decl:
        info = informal_index.get(decl)
        short = decl.split(".")[-1]
        module = entry.get("lean_module") or (info.get("moduleName") if info else None)
        src_url = github_source_url(repo_url, branch, info)
        api_url = api_docs_url(decl)

        links: list[str] = []
        if src_url:
            links.append(f'<a href="{html.escape(src_url)}" target="_blank" rel="noopener">Lean source</a>')
        if api_url:
            links.append(f'<a href="{html.escape(api_url)}">API docs</a>')

        lean_body = ['<dl class="lean-body">']
        lean_body.append('<dt>declaration</dt>')
        lean_body.append(f'<dd><span class="code">{html.escape(short)}</span></dd>')
        lean_body.append('<dt>full name</dt>')
        lean_body.append(f'<dd><span class="code">{html.escape(decl)}</span></dd>')
        if module:
            lean_body.append('<dt>module</dt>')
            lean_body.append(f'<dd><span class="code">{html.escape(module)}</span></dd>')
        if links:
            lean_body.append('<dt>links</dt>')
            lean_body.append(f'<dd><span class="links">{" ".join(links)}</span></dd>')
        lean_body.append('</dl>')

        body.append(
            '<details class="lean">'
            '<summary><span class="label">Show Lean declaration</span></summary>'
            + "".join(lean_body)
            + '</details>'
        )
    elif status == "missing":
        body.append(
            '<p class="missing-body">No Lean declaration in the repository yet.</p>'
        )

    return (
        f'<article class="entry{headline}" data-status="{status}" data-id="{paper_id}">'
        + "".join(head)
        + "".join(body)
        + '</article>'
    )


def section_html(
    section: dict,
    entries: list[dict],
    informal_index: dict[str, dict],
    repo_url: str,
    branch: str,
) -> str:
    head = (
        '<header class="section-head">'
        f'<div class="sec-num">\u00a7{html.escape(section["section"])}</div>'
        f'<div>'
        f'<h2 class="sec-title">{render_text(section["title"])}</h2>'
        f'<p class="sec-blurb">{render_text(section.get("blurb", ""))}</p>'
        f'</div>'
        '</header>'
    )
    body = (
        '<div class="entries">'
        + "".join(
            entry_html(e, informal_index, repo_url, branch)
            for e in entries
        )
        + '</div>'
    )
    return f'<section class="section" data-section="{html.escape(section["section"])}">{head}{body}</section>'


def build_html(data: dict, informal_index: dict[str, dict], repo_url: str, branch: str) -> str:
    meta = data.get("_meta", {})
    sections = data.get("sections", [])
    entries = data.get("entries", [])
    legend = meta.get("status_legend", {})

    counts = Counter(e["status"] for e in entries)
    total = sum(counts.values())
    headline_counts = ", ".join(
        f"{counts.get(s, 0)} {STATUS_LABEL[s].lower()}"
        for s in STATUS_ORDER
        if counts.get(s, 0)
    )

    by_section: dict[str, list[dict]] = {}
    for e in entries:
        by_section.setdefault(e["section"], []).append(e)

    section_html_parts = [
        section_html(sec, by_section.get(sec["section"], []), informal_index, repo_url, branch)
        for sec in sections
        if by_section.get(sec["section"])
    ]

    paper_ref_bits: list[str] = []
    if meta.get("paper_url"):
        paper_ref_bits.append(
            f'<a href="{html.escape(meta["paper_url"])}" target="_blank" rel="noopener">'
            f'{html.escape(meta.get("paper_title", "paper"))}</a>'
        )
    else:
        paper_ref_bits.append(html.escape(meta.get("paper_title", "paper")))
    if meta.get("paper_author"):
        paper_ref_bits.append(html.escape(meta["paper_author"]))
    if meta.get("paper_year"):
        paper_ref_bits.append(str(meta["paper_year"]))
    if meta.get("paper_arxiv"):
        paper_ref_bits.append(f'arXiv:{html.escape(meta["paper_arxiv"])}')

    intro = (
        '<section class="intro">'
        '<p>This dashboard is a mathematician-facing summary of the '
        '<em>BridgelandStability</em> Lean&nbsp;4 formalization. Each row is a numbered '
        'declaration from Bridgeland\u2019s paper, stated in natural language, labelled '
        'with a clear <em>status</em>, and \u2014 when something was formalized \u2014 linked '
        'to its Lean realization through a collapsible. The intent is that you can '
        'read the whole page without ever opening a <span class="math">.lean</span> file.</p>'
        f'<p>The current state: {html.escape(str(total))} paper declarations tracked &mdash; {html.escape(headline_counts)}.</p>'
        '<p>Every status carries a precise meaning; hover the chips in the legend '
        'below for definitions. Where the Lean statement departs from the paper\u2019s '
        '(stronger hypotheses, a generalization, or a partial proof), you will find a '
        'small <em>note</em> under the summary explaining exactly where and why.</p>'
        '</section>'
    )

    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Coverage &amp; Fidelity &mdash; BridgelandStability</title>
<meta name="description" content="Mathematician-facing coverage dashboard for the BridgelandStability Lean 4 formalization.">
<style>{CSS}</style>
</head>
<body>
<div class="page">
  <header class="masthead">
    <div>
      <h1 class="title">Coverage &amp; Fidelity</h1>
      <p class="subtitle">A per-result map of the <em>BridgelandStability</em> Lean&nbsp;4 formalization &mdash; written for mathematicians, with the Lean hidden behind collapsibles.</p>
    </div>
    <div class="paper-ref">{" &middot; ".join(paper_ref_bits)}</div>
  </header>
  {intro}
  <section class="legend" aria-label="Status legend and filters">
    <h2>Status &middot; click to filter &middot; hover for definitions</h2>
    {legend_html(counts, legend)}
  </section>
  {"".join(section_html_parts)}
  <footer class="colophon">
    <div>Data: <code>artifacts/coverage-data.json</code> &middot; audited against <code>artifacts/informal-audit.md</code>.</div>
    <div>Generated by <code>scripts/generate_dashboard.py</code>.</div>
  </footer>
</div>
<script>{JS}</script>
</body>
</html>
"""


# ── CLI ───────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--data", default="artifacts/coverage-data.json",
                    help="Path to coverage-data.json (default: %(default)s)")
    ap.add_argument("--informalizations", default="informalizations.json",
                    help="Path to informalizations.json (for source links)")
    ap.add_argument("--output", default="artifacts/dashboard-preview",
                    help="Output directory (will be created if missing)")
    ap.add_argument("--repo-url", default="https://github.com/mattrobball/BridgelandStability",
                    help="Base GitHub URL for Lean source links")
    ap.add_argument("--branch", default="main",
                    help="Git branch for source links (default: %(default)s)")
    args = ap.parse_args()

    with open(args.data) as f:
        data = json.load(f)

    informal_index = load_informal_index(args.informalizations)
    html_text = build_html(data, informal_index, args.repo_url, args.branch)

    os.makedirs(args.output, exist_ok=True)
    out_path = os.path.join(args.output, "index.html")
    with open(out_path, "w") as f:
        f.write(html_text)

    print(f"wrote {out_path} ({len(html_text):,} bytes, {len(data.get('entries', []))} entries)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
