#!/usr/bin/env python3
"""Split a single-page Verso HTML manual into multi-page output.

Preserves the sidebar TOC and header chrome on every page.
The first section (Overview) becomes the landing page.
"""
import sys, re
from pathlib import Path


def slugify(s):
    return re.sub(r'[^a-z0-9]+', '-', s.lower()).strip('-')


def split_html(html_dir):
    html_path = Path(html_dir) / 'index.html'
    html = html_path.read_text()

    head_match = re.search(r'(<head[\s\S]*?</head>)', html)
    if not head_match:
        print("No <head> found")
        return
    head = head_match.group(1)

    # Extract the page chrome: header + TOC sidebar + content wrapper opening
    # This is everything between <body> and the first top-level <section>
    body_start = html.find('<body>') + len('<body>')
    first_section = re.search(r'<section>\s*\n\s*<h2\s', html)
    if not first_section:
        print("No sections found")
        return
    chrome_before = html[body_start:first_section.start()]

    # Extract post-content chrome (closing tags after last section)
    last_section_end = html.rfind('</section>')
    if last_section_end < 0:
        print("No closing </section> found")
        return
    last_section_end += len('</section>')
    chrome_after = html[last_section_end:html.rfind('</body>')]

    # Find all top-level sections
    section_starts = [m.start() for m in re.finditer(r'<section>\s*\n\s*<h2\s', html)]
    if len(section_starts) < 2:
        print(f"Only {len(section_starts)} section(s), nothing to split")
        return

    sections = []
    for i, start in enumerate(section_starts):
        end = section_starts[i + 1] if i + 1 < len(section_starts) else last_section_end
        chunk = html[start:end]

        title_match = re.search(r'<h2[^>]*>([\s\S]*?)</h2>', chunk)
        title = re.sub(r'<[^>]+>', '', title_match.group(1)).strip() if title_match else f'section-{i}'
        title = title.replace('\U0001f517', '').strip()
        title = re.sub(r'^\d+\.\s*', '', title)

        # Strip Verso's prev-next nav, section-toc, and its heading (old unsplit links)
        chunk = re.sub(r'<nav class="prev-next-buttons">[\s\S]*?</nav>', '', chunk)
        chunk = re.sub(r'<h2[^>]*>\s*Contents[\s\S]*?</h2>\s*<ol class="section-toc">[\s\S]*?</ol>', '', chunk)
        chunk = re.sub(r'<ol class="section-toc">[\s\S]*?</ol>', '', chunk)
        sections.append({'title': title, 'slug': slugify(title), 'html': chunk})

    print(f"Found {len(sections)} sections")

    # Extract the manual title from the original header
    manual_title_match = re.search(r'<a[^>]*class="header-title"[^>]*><h1>\s*(.*?)\s*</h1>', html, re.DOTALL)
    manual_title = re.sub(r'<[^>]+>', '', manual_title_match.group(1)).strip() if manual_title_match else sections[0]['title']

    # Generate a placeholder badge if one doesn't exist (CI generates the real one)
    badge_dir = Path(html_dir) / 'badge'
    badge_dir.mkdir(exist_ok=True)
    badge_svg = badge_dir / 'comparator.svg'
    if not badge_svg.exists():
        badge_svg.write_text(
            '<svg xmlns="http://www.w3.org/2000/svg" width="140" height="20">'
            '<rect width="140" height="20" rx="3" fill="#555"/>'
            '<g fill="#fff" text-anchor="middle" font-family="sans-serif" font-size="11">'
            '<text x="70" y="14">comparator: local</text></g></svg>'
        )

    # Save original
    (Path(html_dir) / 'index-full.html').write_text(html)

    def fix_paths_for_subpage(h):
        """Set <base href="../"> so all relative paths resolve from root.
        No explicit ../ prefixes needed — base handles it."""
        h = re.sub(r'<base href="[^"]*">', '<base href="../">', h)
        return h

    # Simpler approach: extract original TOC table rows and rebuild with our slugs
    toc_rows = []
    for i, sect in enumerate(sections):
        toc_rows.append(
            f'<tr class="numbered"><td class="num">{i+1}.</td>'
            f'<td><a href="{{prefix}}{sect["slug"]}/">{sect["title"]}</a></td></tr>'
        )
    toc_table = ''.join(toc_rows)

    # Extract inline scripts from the body (between </head><body> and first section)
    # These include the TOC toggle JS, Tippy init, SubVerso hover code
    body_start = html.find('<body>') + len('<body>')
    pre_section = html[body_start:first_section.start()]
    inline_scripts = ''.join(re.findall(r'(<script>[\s\S]*?</script>)', pre_section))

    # The burger toggle that shows/hides the sidebar
    burger = (
        '<label for="toggle-toc" id="toggle-toc-click">'
        '<span class="line line1"></span>'
        '<span class="line line2"></span>'
        '<span class="line line3"></span>'
        '</label>'
    )

    def build_toc(is_subpage=False, current_slug=''):
        """Build TOC. On sub-pages, <base href="../"> is set so all hrefs
        are relative to the site root — use slug/ directly, ./ for root."""
        rows = []
        for i, sect in enumerate(sections):
            cls = 'numbered current' if sect['slug'] == current_slug else 'numbered'
            if i == 0:
                href = './'  # Overview = site root
            else:
                href = f'{sect["slug"]}/'
            rows.append(
                f'<tr class="{cls}"><td class="num">{i+1}.</td>'
                f'<td><a href="{href}">{sect["title"]}</a></td></tr>'
            )
        return (
            '<nav id="toc">'
            '<input type="checkbox" id="toggle-toc">'
            '<div class="first">'
            f'<a href="./" class="toc-title"><h1>{manual_title}</h1></a>'
            '<div class="split-tocs"><div class="split-toc book">'
            '<div class="title">'
            '<label for="--split-toc-toggle" class="toggle-split-toc">'
            '<input type="checkbox" class="toggle-split-toc" id="--split-toc-toggle" checked="checked">'
            '</label>'
            '<span>Table of Contents</span></div>'
            '<table>' + ''.join(rows) + '</table>'
            '</div></div></div></nav>'
        )

    # Build a map of anchor IDs to page slugs for cross-page link rewriting.
    # After splitting, href="#some-id" may point to an anchor on a different page.
    # We rewrite those to "slug/#some-id" so they resolve correctly.
    id_to_slug = {}
    for sect in sections:
        for m in re.finditer(r'id="([^"]+)"', sect['html']):
            anchor_id = m.group(1)
            # Overview (first section) is at root
            id_to_slug[anchor_id] = sections[0]['slug'] if sect is sections[0] else sect['slug']

    def rewrite_cross_links(page_html, page_slug, is_subpage=False):
        """Rewrite fragment-only links.
        On sub-pages with <base href="../">, ALL #fragment links resolve from
        the root, not the current page. So even same-page links need an
        explicit slug/ prefix to route back to the current page."""
        def rewrite(m):
            href = m.group(1)
            if not href.startswith('#'):
                return m.group(0)
            anchor = href[1:]
            target_slug = id_to_slug.get(anchor)
            if target_slug is None:
                if is_subpage:
                    # Unknown anchor on sub-page: add explicit self-reference
                    return f'href="{page_slug}/#{anchor}"'
                return m.group(0)
            # All sub-page links need explicit slug/ due to <base href="../">
            if is_subpage:
                return f'href="{target_slug}/#{anchor}"'
            # Landing page: same-page fragments are fine, cross-page need slug
            if target_slug == page_slug:
                return m.group(0)
            return f'href="{target_slug}/#{anchor}"'
        return re.sub(r'href="(#[^"]*)"', rewrite, page_html)

    # Create sub-pages for all sections except the first (Overview = landing)
    for i, sect in enumerate(sections):
        if i == 0:
            continue  # Overview becomes the landing page
        page_dir = Path(html_dir) / sect['slug']
        page_dir.mkdir(exist_ok=True)
        sub_head = fix_paths_for_subpage(head)
        # Set per-page title for browser tabs
        sub_head = re.sub(
            r'<title>[^<]*</title>',
            f'<title>{sect["title"]} — {manual_title}</title>',
            sub_head
        )
        sub_toc = build_toc(is_subpage=True, current_slug=sect['slug'])
        page = (
            f'<!DOCTYPE html>\n<html>\n{sub_head}\n<body>\n'
            f'<header><div class="header-logo-wrapper"></div>'
            f'<div class="header-title-wrapper">'
            f'<a href="./" class="header-title"><h1>{manual_title}</h1></a>'
            f'</div></header>\n'
            f'{burger}'
            f'<div class="with-toc">\n'
            f'<div class="toc-backdrop" onclick="document.getElementById(\'toggle-toc-click\')?.click()"></div>\n'
            f'{sub_toc}\n'
            f'<main><div class="content-wrapper">\n'
            f'{sect["html"]}\n'
            f'</div></main></div>\n{inline_scripts}\n</body>\n</html>'
        )
        page = rewrite_cross_links(page, sect['slug'], is_subpage=True)
        (page_dir / 'index.html').write_text(page)
        print(f"  {sect['slug']}/index.html ({len(sect['html'])} bytes)")

    # Landing page = Overview section with full chrome
    overview = sections[0]
    landing_toc = build_toc(is_subpage=False, current_slug=overview['slug'])
    landing = (
        f'<!DOCTYPE html>\n<html>\n{head}\n<body>\n'
        f'<header><div class="header-logo-wrapper"></div>'
        f'<div class="header-title-wrapper">'
        f'<a href="" class="header-title"><h1>{manual_title}</h1></a>'
        f'</div></header>\n'
        f'{burger}'
        f'<div class="with-toc">\n'
        f'<div class="toc-backdrop" onclick="document.getElementById(\'toggle-toc-click\')?.click()"></div>\n'
        f'{landing_toc}\n'
        f'<main><div class="content-wrapper">\n'
        f'{overview["html"]}\n'
        f'</div></main></div>\n{inline_scripts}\n</body>\n</html>'
    )
    landing = rewrite_cross_links(landing, overview['slug'])
    html_path.write_text(landing)
    print(f"  index.html (Overview landing, {len(overview['html'])} bytes)")


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <html-dir>")
        sys.exit(1)
    split_html(sys.argv[1])
