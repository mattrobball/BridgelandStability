#!/usr/bin/env python3
"""Rewrite doc-gen4 links to point external deps at upstream hosted docs.

Usage:
    python3 scripts/rewrite_doc_links.py <doc-dir>

Rewrites relative links in BridgelandStability HTML docs so that
references to Mathlib, Init, Lean, Batteries, etc. point to
https://leanprover-community.github.io/mathlib4_docs/ instead of
local relative paths.
"""

import re
import sys
from pathlib import Path

MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs"

EXTERNAL_PKGS = (
    r'Mathlib|Init|Lean|Lake|Batteries|Std|Aesop|Qq|Plausible'
    r'|ImportGraph|LeanSearchClient|ProofWidgets'
)

# Matches: href="../.././Mathlib/Foo.html" or href="./Init.html"
RELATIVE_RE = re.compile(
    r'href="(\.\./)*\.?/?' + r'(' + EXTERNAL_PKGS + r')([/.])'
)


def rewrite_file(path: Path) -> bool:
    text = path.read_text()
    new_text = RELATIVE_RE.sub(
        lambda m: f'href="{MATHLIB_DOCS}/{m.group(2)}{m.group(3)}',
        text,
    )
    if new_text != text:
        path.write_text(new_text)
        return True
    return False


def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <doc-dir>")
        sys.exit(1)

    doc_dir = Path(sys.argv[1])
    if not doc_dir.is_dir():
        print(f"Not a directory: {doc_dir}")
        sys.exit(1)

    count = 0
    for html in doc_dir.rglob("*.html"):
        if rewrite_file(html):
            count += 1

    print(f"Rewrote links in {count} files")


if __name__ == "__main__":
    main()
