#!/usr/bin/env python3
"""Patch the README informal-alignment table from the JSON export.

Usage:
    lake build checkInformal
    python3 scripts/generate_readme_table.py
"""

import json
import sys
from pathlib import Path

from informal_table import build_rows, render_markdown

ROOT = Path(__file__).resolve().parent.parent
JSON = ROOT / "artifacts" / "formal_informal_alignments.json"
README = ROOT / "README.md"
BEGIN = "<!-- BEGIN INFORMAL TABLE -->"
END = "<!-- END INFORMAL TABLE -->"


def main():
    entries = json.loads(JSON.read_text())
    table = render_markdown(build_rows(entries))

    readme = README.read_text()
    start, end = readme.find(BEGIN), readme.find(END)
    if start == -1 or end == -1:
        sys.exit(f"Missing {BEGIN} / {END} markers in README.md")

    new = readme[: start + len(BEGIN)] + "\n" + table + readme[end:]
    README.write_text(new)
    print(f"Updated README.md ({len(build_rows(entries))} entries)")


if __name__ == "__main__":
    main()
