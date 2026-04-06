#!/usr/bin/env python3
"""Post-process Verso HTML for informal exposition pages.

Restructures the DOM so that:
  1. Source docstring <p> tags inside .namedocs > .text are removed
     (our informal prose lives OUTSIDE the namedocs block)
  2. The .namedocs block's internal structure is preserved intact
     (signature, constructor, extends, fields — all Verso hover/linking works)
  3. A refined stylesheet is injected for the informal exposition aesthetic

Works on any Verso {docstring}-generated page regardless of whether the
declaration has a source docstring or not.

Usage:
    python3 style_informal.py <html-dir>
    python3 style_informal.py <single-file.html>

Requires: beautifulsoup4
"""
import sys
from pathlib import Path
from bs4 import BeautifulSoup, Tag, Comment


# ── Stylesheet ──────────────────────────────────────────────────────────────

INFORMAL_CSS = """\
/* ── Informal Exposition Overrides ────────────────────────────────────── */

@import url('https://fonts.googleapis.com/css2?family=Source+Serif+4:ital,opsz,wght@0,8..60,300;0,8..60,400;0,8..60,600;0,8..60,700;1,8..60,300;1,8..60,400&family=Fira+Code:wght@400;500&display=swap');

:root {
  /* Typography */
  --inf-text: 'Source Serif 4', 'Iowan Old Style', 'Palatino Linotype', Palatino, Georgia, serif;
  --inf-code: 'Fira Code', 'JetBrains Mono', ui-monospace, monospace;
  --inf-heading: 'Source Serif 4', Georgia, serif;

  /* Palette — warm parchment tones */
  --inf-bg: #faf8f4;
  --inf-ink: #2c2416;
  --inf-muted: #6b5e4f;
  --inf-rule: #d4cabb;
  --inf-accent: #8b4513;
  --inf-card-bg: #ffffff;
  --inf-card-border: #d4cabb;
  --inf-badge-bg: #f0ebe0;
  --inf-badge-ink: #6b5e4f;
  --inf-sig-bg: #fdfcfa;

  /* Override Verso defaults */
  --verso-text-font-family: var(--inf-text);
  --verso-structure-font-family: var(--inf-heading);
  --verso-code-font-family: var(--inf-code);
  --verso-toc-background-color: var(--inf-bg);
}

/* ── Page background ── */
body {
  background: var(--inf-bg);
  color: var(--inf-ink);
}

/* ── Prose paragraphs (our informal text) ── */
.informal-prose {
  font-family: var(--inf-text);
  font-size: 1.05rem;
  line-height: 1.7;
  color: var(--inf-ink);
  margin: 0.4em 0 0.2em;
}
.informal-prose em, .informal-prose .proof-exposition, .informal-prose .term-exposition {
  color: var(--inf-muted);
}

/* ── Declaration sections ── */
.decl-section {
  margin: 2rem 0;
  padding-bottom: 1.5rem;
  border-bottom: 1px solid var(--inf-rule);
}
.decl-section:last-child {
  border-bottom: none;
}

/* ── Declaration headings ── */
.decl-section > h3 {
  font-family: var(--inf-heading);
  font-weight: 600;
  font-size: 1.25rem;
  color: var(--inf-accent);
  margin-bottom: 0.5rem;
  letter-spacing: -0.01em;
}

/* ── Namedocs card ── */
.namedocs {
  border: 1px solid var(--inf-card-border) !important;
  border-radius: 0.4rem !important;
  background: var(--inf-card-bg);
  box-shadow: 0 1px 3px rgba(0,0,0,0.04);
}

/* Kind badge */
.namedocs .label {
  font-family: var(--inf-code) !important;
  font-size: 0.7rem !important;
  font-weight: 500;
  text-transform: uppercase;
  letter-spacing: 0.06em;
  background: var(--inf-badge-bg) !important;
  color: var(--inf-badge-ink) !important;
  border: 1px solid var(--inf-card-border) !important;
  border-radius: 3px !important;
  padding: 0.1rem 0.5rem 0.2rem !important;
}

/* Signature block */
.namedocs .signature {
  font-family: var(--inf-code) !important;
  font-size: 0.88rem;
  line-height: 1.55;
  background: var(--inf-sig-bg);
  padding: 0.6rem 1rem !important;
  margin: 0.5rem var(--verso--box-padding) 0 !important;
  border-radius: 0.25rem;
  overflow-x: auto;
}

/* Structure details (Constructor / Extends / Fields) */
.namedocs > .text h1 {
  font-family: var(--inf-heading);
  font-size: 0.85rem;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.05em;
  color: var(--inf-muted);
  border-bottom: 1px solid var(--inf-rule);
  padding-bottom: 0.3rem;
  margin-top: 1rem;
  margin-bottom: 0.5rem;
}

/* Subdoc field signatures */
.namedocs .subdocs .name-and-type {
  font-family: var(--inf-code);
  font-size: 0.82rem;
  line-height: 1.5;
}

/* Extends list */
.namedocs .extends li {
  font-family: var(--inf-code);
  font-size: 0.85rem;
}

/* Extends checkbox → triangle toggle */
.namedocs .extends input[type="checkbox"] {
  position: absolute;
  opacity: 0;
  width: 0;
  height: 0;
}
.namedocs .extends label {
  cursor: pointer;
  position: relative;
  padding-left: 1.2em;
}
.namedocs .extends label::before {
  content: '▸';
  position: absolute;
  left: 0;
  font-size: 0.8em;
  color: var(--inf-muted);
  transition: transform 0.15s ease;
}
.namedocs .extends input[type="checkbox"]:checked + label::before {
  content: '▾';
}

/* ── Title page ── */
.titlepage h1 {
  font-family: var(--inf-heading);
  font-weight: 700;
  font-size: 1.6rem;
  color: var(--inf-ink);
  letter-spacing: -0.02em;
}

/* ── Section headings ── */
h2 {
  font-family: var(--inf-heading);
  font-weight: 600;
  font-size: 1.35rem;
  color: var(--inf-ink);
  border-bottom: 2px solid var(--inf-rule);
  padding-bottom: 0.35rem;
}

/* ── Permalink widget ── */
.permalink-widget {
  opacity: 0.3;
  transition: opacity 0.15s;
}
.permalink-widget:hover, .namedocs:hover .permalink-widget {
  opacity: 0.7;
}

/* ── KaTeX ── */
.katex { font-size: 1em; }

/* ── Alignment table ── */
table.informal-alignment {
  width: 100%;
  border-collapse: collapse;
  font-family: var(--inf-text);
  font-size: 0.9rem;
  margin: 1.5rem 0;
}
table.informal-alignment th {
  background: var(--inf-badge-bg);
  color: var(--inf-muted);
  font-weight: 600;
  text-align: left;
  padding: 0.4rem 0.6rem;
  border-bottom: 2px solid var(--inf-rule);
}
table.informal-alignment td {
  padding: 0.35rem 0.6rem;
  border-bottom: 1px solid var(--inf-rule);
  vertical-align: top;
}
table.informal-alignment code {
  font-family: var(--inf-code);
  font-size: 0.82rem;
}
"""


# ── DOM surgery ─────────────────────────────────────────────────────────────

def strip_source_docstrings(soup: BeautifulSoup) -> int:
    """Remove source docstring <p> tags from inside .namedocs > .text.

    These are always the leading <p> children before the first <h1>
    (Constructor / Extends / Fields).  Declarations without source
    docstrings simply have no <p> children there — nothing to remove.

    Returns count of removed elements.
    """
    count = 0
    for namedocs in soup.find_all("div", class_="namedocs"):
        text_div = namedocs.find("div", class_="text", recursive=False)
        if not text_div:
            continue
        # Collect <p> children that appear before the first <h1>
        to_remove = []
        for child in text_div.children:
            if not isinstance(child, Tag):
                continue
            if child.name == 'h1':
                break  # stop at first structural heading
            if child.name == 'p':
                to_remove.append(child)
        for p in to_remove:
            p.decompose()
            count += 1
    return count


def wrap_decl_sections(soup: BeautifulSoup) -> int:
    """Add .decl-section class to sections that contain a declaration
    (h3 heading + namedocs block), for styling hooks."""
    count = 0
    for section in soup.find_all("section"):
        h3 = section.find("h3", recursive=False)
        nd = section.find("div", class_="namedocs", recursive=False)
        if h3 and nd:
            existing = section.get("class", [])
            if "decl-section" not in existing:
                section["class"] = existing + ["decl-section"]
                count += 1
    return count



def inject_stylesheet(soup: BeautifulSoup) -> None:
    """Replace or inject the informal stylesheet into <head>."""
    head = soup.find("head")
    if not head:
        return

    # Remove old override link if present
    for link in head.find_all("link", rel="stylesheet"):
        href = link.get("href", "")
        if "informal-overrides" in href:
            link.decompose()

    # Remove old inline informal styles
    for style in head.find_all("style"):
        if style.string and "informal-prose" in style.string:
            style.decompose()

    # Inject new stylesheet inline (no external file dependency)
    style = soup.new_tag("style")
    style.string = INFORMAL_CSS
    head.append(style)


def inject_alignment_table(soup: BeautifulSoup, json_path: Path) -> bool:
    """Inject the @[informal] alignment table into the root page.

    Looks for <!--INFORMAL-TABLE--> marker comment in the HTML.
    If not found, appends the table after the "Contributing" heading.
    """
    if not json_path.exists():
        return False

    import json
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from informal_table import build_rows, render_markdown

    entries = json.loads(json_path.read_text())
    # informalizations.json uses paperRef (nullable); filter to tagged only
    tagged = [e for e in entries if e.get("paperRef")]
    if not tagged:
        return False

    rows = build_rows(tagged)
    if not rows:
        return False

    # Build HTML table
    table_tag = soup.new_tag("table", attrs={"class": "informal-alignment"})
    thead = soup.new_tag("thead")
    tr = soup.new_tag("tr")
    for col in ["Paper", "Lean declaration", "File", "Notes"]:
        th = soup.new_tag("th")
        th.string = col
        tr.append(th)
    thead.append(tr)
    table_tag.append(thead)

    tbody = soup.new_tag("tbody")
    for _, ref, name, f, note in rows:
        tr = soup.new_tag("tr")
        for val in [ref, name, f, note]:
            td = soup.new_tag("td")
            if val in (name, f):
                code = soup.new_tag("code")
                code.string = val
                td.append(code)
            else:
                td.string = val
            tr.append(td)
        tbody.append(tr)
    table_tag.append(tbody)

    # Find insertion point: after the "Paper Alignment" heading
    inserted = False
    for h1 in soup.find_all(["h1", "h2"]):
        text = h1.get_text(strip=True)
        if "Paper Alignment" in text:
            # Insert after the paragraph(s) following this heading
            sibling = h1.find_next_sibling()
            while sibling and sibling.name == "p":
                sibling = sibling.find_next_sibling()
            if sibling:
                sibling.insert_before(table_tag)
            else:
                h1.parent.append(table_tag)
            inserted = True
            break

    if not inserted:
        # Fallback: look for the section containing "Paper Alignment"
        for section in soup.find_all("section"):
            text = section.get_text(strip=True)[:50]
            if "Paper Alignment" in text:
                section.append(table_tag)
                inserted = True
                break

    return inserted


def process_file(path: Path, site_root: Path, json_path: Path | None = None) -> bool:
    """Process one HTML file.  Returns True if modified."""
    html = path.read_text()
    soup = BeautifulSoup(html, "html.parser")

    # Skip non-HTML pages (search assets, etc.)
    if not soup.find("head"):
        return False

    removed = 0
    wrapped = 0

    # DOM surgery only on pages with namedocs (declaration pages)
    if soup.find("div", class_="namedocs"):
        removed = strip_source_docstrings(soup)
        wrapped = wrap_decl_sections(soup)

    # Inject alignment table on root page
    table_injected = False
    if json_path and path.name == "index.html" and path.parent == site_root:
        table_injected = inject_alignment_table(soup, json_path)

    # Inject CSS on ALL pages for consistent styling
    inject_stylesheet(soup)

    path.write_text(str(soup))
    rel = path.relative_to(site_root)
    if removed or wrapped or table_injected:
        parts = []
        if removed:
            parts.append(f"removed {removed} docstrings")
        if wrapped:
            parts.append(f"marked {wrapped} sections")
        if table_injected:
            parts.append("injected alignment table")
        print(f"  {rel}: {', '.join(parts)}")
    return True


# ── Entry point ─────────────────────────────────────────────────────────────

def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <html-dir-or-file> [--json <informalizations.json>]")
        sys.exit(1)

    target = Path(sys.argv[1])
    json_path = None
    if "--json" in sys.argv:
        idx = sys.argv.index("--json")
        if idx + 1 < len(sys.argv):
            json_path = Path(sys.argv[idx + 1])

    if target.is_file():
        process_file(target, target.parent, json_path)
    elif target.is_dir():
        files = sorted(target.rglob("*.html"))
        processed = 0
        for f in files:
            if process_file(f, target, json_path):
                processed += 1
        print(f"Processed {processed}/{len(files)} HTML files")
    else:
        print(f"Not found: {target}")
        sys.exit(1)


if __name__ == "__main__":
    main()
