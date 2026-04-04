#!/usr/bin/env python3
"""Find declarations needing prose work.

Usage:
    python3 scripts/find_missing_prose.py informalizations.json

Reports entries grouped by category:
  - Empty prose (new declarations needing initial write)
  - Needs review (signature changed since prose was written)
  - Has @[informal] tag but no prose (paper-aligned declarations)
"""

import json
import sys
from collections import defaultdict


def main():
    if len(sys.argv) < 2:
        print("Usage: find_missing_prose.py <informalizations.json>", file=sys.stderr)
        sys.exit(1)

    with open(sys.argv[1]) as f:
        data = json.load(f)

    empty = [e for e in data if not e.get("prose")]
    needs_review = [e for e in data if e.get("needsReview")]
    tagged_no_prose = [e for e in data
                       if e.get("paperRef") and not e.get("prose")]

    total_issues = len(empty) + len(needs_review)

    if total_issues == 0 and not tagged_no_prose:
        print("All entries have prose and are up to date.")
        return

    if empty:
        print(f"## Empty prose ({len(empty)} declarations)\n")
        by_mod = defaultdict(list)
        for e in empty:
            by_mod[e["moduleName"]].append(e)
        for mod in sorted(by_mod):
            entries = by_mod[mod]
            print(f"### {mod} ({len(entries)})")
            for e in entries:
                doc = ""
                if e.get("docstring"):
                    doc = f"  (has docstring)"
                print(f"  - [{e['declKind']}] `{e['declName']}`{doc}")
            print()

    if needs_review:
        print(f"## Needs review ({len(needs_review)} declarations)\n")
        print("Signature or body changed since prose was written.\n")
        by_mod = defaultdict(list)
        for e in needs_review:
            by_mod[e["moduleName"]].append(e)
        for mod in sorted(by_mod):
            entries = by_mod[mod]
            print(f"### {mod} ({len(entries)})")
            for e in entries:
                print(f"  - [{e['declKind']}] `{e['declName']}`")
            print()

    if tagged_no_prose:
        print(f"## @[informal] tagged but no prose ({len(tagged_no_prose)})\n")
        for e in tagged_no_prose:
            print(f"  - `{e['declName']}` ← {e['paperRef']}")
        print()

    print(f"---")
    print(f"Total: {len(empty)} empty, {len(needs_review)} needs review, "
          f"{len(tagged_no_prose)} tagged without prose")


if __name__ == "__main__":
    main()
