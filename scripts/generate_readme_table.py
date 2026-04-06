#!/usr/bin/env python3
"""Patch the README informal-alignment table from the JSON export.

Usage:
    lake build checkInformal
    python3 scripts/generate_readme_table.py [--check]
"""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
JSON = ROOT / "artifacts" / "formal_informal_alignments.json"
README = ROOT / "README.md"
BEGIN = "<!-- BEGIN INFORMAL TABLE -->"
END = "<!-- END INFORMAL TABLE -->"


def sort_key(ref: str) -> tuple[int, int]:
    m = re.search(r"(\d+)\.(\d+)", ref)
    sec, sub = (int(m.group(1)), int(m.group(2))) if m else (0, 0)
    return (100, sub) if sec == 1 else (sec, sub)  # headline results last


def main():
    entries = json.loads(JSON.read_text())

    # deduplicate by (paperRef, declName)
    seen, rows = set(), []
    for e in entries:
        key = (e["paperRef"], e["declName"])
        if key in seen:
            continue
        seen.add(key)
        # module → relative file path
        mod = e["moduleName"]
        prefix = "BridgelandStability."
        rel = mod.removeprefix(prefix).replace(".", "/") + ".lean"
        # short display name
        name = e["declName"].removeprefix("CategoryTheory.Triangulated.")
        note = e.get("comment", "")
        rows.append((sort_key(e["paperRef"]), e["paperRef"], name, rel, note))

    rows.sort()
    header = "| Paper | Lean declaration | File | Notes |"
    sep = "|-------|-----------------|------|-------|"
    lines = [header, sep] + [
        f"| {ref} | `{name}` | `{f}` | {note} |"
        for _, ref, name, f, note in rows
    ]
    table = "\n".join(lines) + "\n"

    readme = README.read_text()
    start, end = readme.find(BEGIN), readme.find(END)
    if start == -1 or end == -1:
        sys.exit(f"Missing {BEGIN} / {END} markers in README.md")

    new = readme[: start + len(BEGIN)] + "\n" + table + readme[end:]

    if "--check" in sys.argv:
        if new != readme:
            sys.exit("README table is stale. Run: python3 scripts/generate_readme_table.py")
        print(f"OK ({len(rows)} entries)")
    else:
        README.write_text(new)
        print(f"Updated README.md ({len(rows)} entries)")


if __name__ == "__main__":
    main()
