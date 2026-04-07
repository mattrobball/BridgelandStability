#!/usr/bin/env python3
"""Package doc-gen4 output for deployment.

Usage:
    python3 scripts/package_api_docs.py <doc-dir> <output-dir>

Copies BridgelandStability docs + infrastructure files, filters the
navbar and declaration data to BS only, and rewrites external package
links to point at https://leanprover-community.github.io/mathlib4_docs/.
"""

import json
import re
import shutil
import sys
from pathlib import Path

MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs"

EXTERNAL_PKGS = (
    r'Mathlib|Init|Lean|Lake|Batteries|Std|Aesop|Qq|Plausible'
    r'|ImportGraph|LeanSearchClient|ProofWidgets'
)

LINK_RE = re.compile(
    r'href="(\.\./)*\.?/?' + r'(' + EXTERNAL_PKGS + r')([/.])'
)

ROOT_FILES = [
    "index.html", "navbar.html", "404.html", "style.css", "favicon.svg",
    "search.html", "search.js", "declaration-data.js", "nav.js",
    "color-scheme.js", "expand-nav.js", "how-about.js", "jump-src.js",
    "mathjax-config.js", "instances.js", "importedBy.js",
    "foundational_types.html", "tactics.html",
    "references.html", "references.bib",
]


def copy_files(doc_dir: Path, out_dir: Path):
    """Copy BS docs + infrastructure to output."""
    out_dir.mkdir(parents=True, exist_ok=True)

    # BS module docs
    shutil.copytree(doc_dir / "BridgelandStability", out_dir / "BridgelandStability")
    shutil.copy2(doc_dir / "BridgelandStability.html", out_dir)

    # Root files
    for f in ROOT_FILES:
        src = doc_dir / f
        if src.exists():
            shutil.copy2(src, out_dir)

    # Declarations + find
    shutil.copytree(doc_dir / "declarations", out_dir / "declarations")
    if (doc_dir / "find").exists():
        shutil.copytree(doc_dir / "find", out_dir / "find")

    # Source links
    src_dir = doc_dir / "src" / "BridgelandStability"
    if src_dir.exists():
        (out_dir / "src").mkdir(exist_ok=True)
        shutil.copytree(src_dir, out_dir / "src" / "BridgelandStability")


def filter_navbar(out_dir: Path):
    """Remove non-BS entries from navbar."""
    from bs4 import BeautifulSoup

    path = out_dir / "navbar.html"
    soup = BeautifulSoup(path.read_text(), "html.parser")
    # Remove "General documentation" section (index, foundational types, tactics)
    for h3 in soup.find_all("h3"):
        if "General documentation" in h3.get_text():
            sibling = h3.find_next_sibling()
            while sibling and sibling.name != "h3":
                next_sib = sibling.find_next_sibling()
                sibling.decompose()
                sibling = next_sib
            h3.decompose()
            break

    # Filter module list to BS only
    module_list = soup.find("div", class_="module_list")
    if module_list:
        for d in module_list.find_all("details", class_="nav_sect", recursive=False):
            if "BridgelandStability" not in d.get("data-path", ""):
                d.decompose()
    path.write_text(str(soup))


def filter_declarations(out_dir: Path):
    """Filter declaration data to BS only."""
    path = out_dir / "declarations" / "declaration-data.bmp"
    orig = json.loads(path.read_text())
    filtered = {
        "declarations": {
            k: v for k, v in orig["declarations"].items()
            if "BridgelandStability" in v.get("docLink", "")
        },
        "instances": {},
        "instancesFor": {},
        "modules": {
            k: v for k, v in orig.get("modules", {}).items()
            if k.startswith("BridgelandStability")
        },
    }
    path.write_text(json.dumps(filtered, separators=(",", ":")))
    return len(filtered["declarations"]), len(filtered["modules"])


def rewrite_links(out_dir: Path) -> int:
    """Rewrite relative links to external packages."""
    count = 0
    for html in out_dir.rglob("*.html"):
        text = html.read_text()
        new_text = LINK_RE.sub(
            lambda m: f'href="{MATHLIB_DOCS}/{m.group(2)}{m.group(3)}',
            text,
        )
        if new_text != text:
            html.write_text(new_text)
            count += 1
    return count


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <doc-dir> <output-dir>")
        sys.exit(1)

    doc_dir = Path(sys.argv[1])
    out_dir = Path(sys.argv[2])

    if out_dir.exists():
        shutil.rmtree(out_dir)

    print(f"Copying BS docs from {doc_dir}...")
    copy_files(doc_dir, out_dir)

    print("Filtering navbar...")
    filter_navbar(out_dir)

    print("Filtering declarations...")
    decls, mods = filter_declarations(out_dir)
    print(f"  {decls} declarations, {mods} modules")

    print("Rewriting external links...")
    count = rewrite_links(out_dir)
    print(f"  Rewrote {count} files")

    size = sum(f.stat().st_size for f in out_dir.rglob("*") if f.is_file())
    print(f"Output: {out_dir} ({size / 1024 / 1024:.1f} MB)")


if __name__ == "__main__":
    main()
