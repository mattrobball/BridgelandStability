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

/* Bold section labels on landing page — act as visual dividers */
.titlepage > p > strong:only-child {
  display: block;
  font-family: var(--inf-heading);
  font-size: 1.15rem;
  font-weight: 600;
  color: var(--inf-accent);
  letter-spacing: -0.01em;
  margin-top: 1.5rem;
  padding-top: 1rem;
  border-top: 1px solid var(--inf-rule);
}
.titlepage > p:first-of-type > strong:only-child {
  border-top: none;
  margin-top: 0;
  padding-top: 0;
}

/* ── Hide duplicate docstring entries in sidebar TOC ──
   Verso's {docstring} creates a TOC entry with the full qualified name
   alongside the heading entry with the short name — hide the former. */
#toc .split-toc li:has(> a > code) {
  display: none;
}

/* ── Prevent ugly wrapping of long declaration names in sidebar TOC ── */
#toc .split-toc .header a {
  word-break: break-all;
  font-size: 0.82rem;
  line-height: 1.35;
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
  border-collapse: separate;
  border-spacing: 0;
  font-family: var(--inf-text);
  font-size: 0.88rem;
  line-height: 1.5;
  margin: 2rem 0;
  border: 1px solid var(--inf-card-border);
  border-radius: 0.4rem;
  overflow: hidden;
}
table.informal-alignment thead {
  position: sticky;
  top: 0;
  z-index: 1;
}
table.informal-alignment th {
  background: var(--inf-badge-bg);
  color: var(--inf-muted);
  font-family: var(--inf-heading);
  font-weight: 600;
  font-size: 0.75rem;
  letter-spacing: 0.06em;
  text-transform: uppercase;
  text-align: left;
  padding: 0.6rem 0.8rem;
  border-bottom: 2px solid var(--inf-rule);
  white-space: nowrap;
}
table.informal-alignment td {
  padding: 0.5rem 0.8rem;
  border-bottom: 1px solid color-mix(in srgb, var(--inf-rule) 50%, transparent);
  vertical-align: baseline;
}
table.informal-alignment tbody tr:last-child td {
  border-bottom: none;
}
table.informal-alignment tbody tr:hover {
  background: color-mix(in srgb, var(--inf-badge-bg) 40%, transparent);
}
/* Paper ref column — compact, serif */
table.informal-alignment td:first-child {
  white-space: nowrap;
  color: var(--inf-accent);
  font-weight: 500;
  font-variant-numeric: tabular-nums;
}
/* Declaration column — monospace, linked */
table.informal-alignment code {
  font-family: var(--inf-code);
  font-size: 0.8rem;
  background: none;
  padding: 0;
}
table.informal-alignment a {
  color: var(--inf-ink);
  text-decoration: none;
  border-bottom: 1px solid transparent;
  transition: border-color 0.15s;
}
table.informal-alignment a:hover {
  border-bottom-color: var(--inf-accent);
}
/* Responsive: stack on narrow viewports */
@media (max-width: 640px) {
  table.informal-alignment,
  table.informal-alignment thead,
  table.informal-alignment tbody,
  table.informal-alignment tr,
  table.informal-alignment td,
  table.informal-alignment th {
    display: block;
  }
  table.informal-alignment thead { display: none; }
  table.informal-alignment tr {
    padding: 0.6rem 0.8rem;
    border-bottom: 1px solid var(--inf-rule);
  }
  table.informal-alignment td {
    padding: 0.15rem 0;
    border: none;
  }
  table.informal-alignment td:first-child {
    font-size: 0.82rem;
    margin-bottom: 0.15rem;
  }
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


def inject_alignment_table(soup: BeautifulSoup, json_path: Path, site_base: str = "") -> bool:
    """Inject the @[informal] alignment table into the landing page.

    Declarations link to their Verso doc pages via the find/ endpoint.
    """
    if not json_path.exists():
        return False

    import json
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from informal_table import build_rows

    entries = json.loads(json_path.read_text())
    tagged = [e for e in entries if e.get("paperRef")]
    if not tagged:
        return False

    rows = build_rows(tagged)
    if not rows:
        return False

    # Build HTML table — two columns: Paper, Declaration (linked)
    table_tag = soup.new_tag("table", attrs={"class": "informal-alignment"})
    thead = soup.new_tag("thead")
    tr = soup.new_tag("tr")
    for col in ["Paper", "Lean declaration"]:
        th = soup.new_tag("th")
        th.string = col
        tr.append(th)
    thead.append(tr)
    table_tag.append(thead)

    tbody = soup.new_tag("tbody")
    for _, ref, short_name, full_name in rows:
        tr = soup.new_tag("tr")
        # Paper ref
        td_ref = soup.new_tag("td")
        td_ref.string = ref
        tr.append(td_ref)
        # Declaration name, linked to Verso find/ endpoint
        td_decl = soup.new_tag("td")
        link = soup.new_tag("a", href=f"{site_base}find/?domain=Verso.Genre.Manual.doc&name={full_name}")
        code = soup.new_tag("code")
        code.string = short_name
        link.append(code)
        td_decl.append(link)
        tr.append(td_decl)
        tbody.append(tr)
    table_tag.append(tbody)

    # Find insertion point: after "Paper alignment" heading/label and its paragraph
    inserted = False
    # Search headings first, then bold labels (for non-heading section markers)
    candidates = list(soup.find_all(["h1", "h2", "h3"]))
    candidates += list(soup.find_all("strong"))
    for tag in candidates:
        if "Paper alignment" in tag.get_text(strip=True):
            # If inside a <p>, anchor from the <p>
            anchor = tag if tag.name != "strong" else (tag.parent if tag.parent and tag.parent.name == "p" else tag)
            # Skip one description paragraph after the anchor
            sibling = anchor.find_next_sibling()
            if sibling and sibling.name == "p":
                sibling = sibling.find_next_sibling()
            if sibling:
                sibling.insert_before(table_tag)
            else:
                anchor.parent.append(table_tag)
            inserted = True
            break

    return inserted


# ── Chapter stub detection and link rewriting ──────────────────────────────

def detect_stubs(site_root: Path) -> dict[str, dict]:
    """Scan site for chapter stub pages and extract navigation info.

    A stub is an index.html that has a section-toc but no namedocs
    (i.e. no declaration content — just a listing page).
    Excludes the root index.html.

    Returns dict mapping stub relative URL (e.g. "Slicing/") to:
      - first_child: href of the first child page
      - prev: href from the stub's own prev-next nav (the page before this stub)
    """
    stubs = {}
    for html_path in sorted(site_root.rglob("*.html")):
        if html_path.name != "index.html":
            continue
        if html_path.parent == site_root:
            continue
        soup = BeautifulSoup(html_path.read_text(), "html.parser")
        toc_ol = soup.find("ol", class_="section-toc")
        has_namedocs = soup.find("div", class_="namedocs")
        if not toc_ol or has_namedocs:
            continue

        # This is a stub — extract first child link
        first_link = toc_ol.find("a", href=True)
        if not first_link:
            continue

        # Extract the stub's own prev/next labels and hrefs
        prev_href = None
        prev_title = None
        next_title = None
        for nav in soup.find_all("nav", class_="prev-next-buttons"):
            prev_a = nav.find("a", rel="prev")
            if prev_a and prev_a.get("href"):
                prev_href = prev_a["href"]
                prev_title = prev_a.get("title", "")
            next_a = nav.find("a", rel="next")
            if next_a:
                next_title = next_a.get("title", "")
            break

        # Also grab the title for the first child from the section-toc
        first_child_title = first_link.get_text(separator=" ", strip=True) if first_link else ""

        rel = str(html_path.parent.relative_to(site_root)) + "/"
        stubs[rel] = {
            "first_child": first_link["href"],
            "first_child_title": first_child_title,
            "prev": prev_href,
            "prev_title": prev_title,
        }
    return stubs


def rewrite_nav_links(soup: BeautifulSoup, stubs: dict[str, dict]) -> int:
    """Rewrite prev/next and TOC links to skip chapter stubs.

    All Verso pages use ``<base href="...">`` pointing to site root,
    so all hrefs are already site-root-relative.

    Returns count of rewritten links.
    """
    count = 0

    def href_to_stub_key(href: str) -> str | None:
        """Extract stub key from an href, or None if it doesn't match a stub."""
        clean = href.split("#")[0]
        if clean and not clean.endswith("/"):
            clean += "/"
        return clean if clean in stubs else None

    def update_button_label(a_tag, new_title: str) -> None:
        """Update the visible label and title attribute of a nav button."""
        if new_title:
            a_tag["title"] = new_title
            where = a_tag.find("span", class_="where")
            if where:
                where.string = new_title

    # Rewrite prev/next buttons
    for nav in soup.find_all("nav", class_="prev-next-buttons"):
        for a in nav.find_all("a", href=True):
            key = href_to_stub_key(a["href"])
            if not key:
                continue
            stub_info = stubs[key]
            is_prev = a.get("rel") == ["prev"]
            is_next = a.get("rel") == ["next"]
            if is_next:
                # Skip stub, go to its first child
                a["href"] = stub_info["first_child"]
                update_button_label(a, stub_info.get("first_child_title"))
                count += 1
            elif is_prev and stub_info.get("prev"):
                # Skip stub, go to what was before the stub
                a["href"] = stub_info["prev"]
                update_button_label(a, stub_info.get("prev_title"))
                count += 1

    # Rewrite TOC sidebar links that point to stubs
    toc_nav = soup.find("nav", id="toc")
    if toc_nav:
        for a in toc_nav.find_all("a", href=True):
            key = href_to_stub_key(a["href"])
            if key:
                a["href"] = stubs[key]["first_child"]
                count += 1

    return count


def add_stub_redirect(soup: BeautifulSoup, first_child_href: str) -> None:
    """Add a JS redirect to a chapter stub page (fallback for direct URL access)."""
    script = soup.new_tag("script")
    script.string = f'window.location.replace("{first_child_href}");'
    head = soup.find("head")
    if head:
        head.append(script)


def process_file(path: Path, site_root: Path, json_path: Path | None = None,
                 stubs: dict[str, dict] | None = None) -> bool:
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

    # Root page: suppress inline Contents section
    if path.name == "index.html" and path.parent == site_root:
        for h2 in soup.find_all("h2"):
            if h2.get_text(strip=True) == "Contents":
                section = h2.find_parent("section")
                if section:
                    section.decompose()
                else:
                    toc = h2.find_next_sibling("ol", class_="section-toc")
                    if toc:
                        toc.decompose()
                    h2.decompose()
                break

    table_injected = False
    if json_path and path.name == "index.html" and path.parent == site_root:
        table_injected = inject_alignment_table(soup, json_path)

    # Rewrite navigation links to skip chapter stubs
    nav_rewritten = 0
    is_stub = False
    if stubs:
        nav_rewritten = rewrite_nav_links(soup, stubs)

        # If this page IS a stub, add redirect to first child
        rel_dir = str(path.parent.relative_to(site_root)) + "/" if path.parent != site_root else ""
        page_key = rel_dir + path.name if path.name != "index.html" else rel_dir
        if page_key in stubs:
            add_stub_redirect(soup, stubs[page_key]["first_child"])
            is_stub = True

    # Inject CSS on ALL pages for consistent styling
    inject_stylesheet(soup)

    path.write_text(str(soup))
    rel = path.relative_to(site_root)
    if removed or wrapped or table_injected or nav_rewritten or is_stub:
        parts = []
        if removed:
            parts.append(f"removed {removed} docstrings")
        if wrapped:
            parts.append(f"marked {wrapped} sections")
        if table_injected:
            parts.append("injected alignment table")
        if nav_rewritten:
            parts.append(f"rewrote {nav_rewritten} nav links")
        if is_stub:
            parts.append("stub redirect")
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
        # Pass 1: detect chapter stubs and extract their navigation info
        stubs = detect_stubs(target)
        if stubs:
            print(f"Detected {len(stubs)} chapter stubs: {', '.join(stubs.keys())}")

        # Pass 2: process all HTML files with stub-skipping
        files = sorted(target.rglob("*.html"))
        processed = 0
        for f in files:
            if process_file(f, target, json_path, stubs=stubs):
                processed += 1
        print(f"Processed {processed}/{len(files)} HTML files")
    else:
        print(f"Not found: {target}")
        sys.exit(1)


if __name__ == "__main__":
    main()
