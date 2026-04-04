#!/usr/bin/env python3
"""Apply prose patches to informalizations.json.

Usage:
    python3 scripts/apply_patches.py patch1.json patch2.json ...

Each patch file is a list of objects with fields:
  - declName (required)
  - prose (required)
  - proofExposition (optional)
  - termExposition (optional)
"""

import json
import sys


def main():
    if len(sys.argv) < 2:
        print("Usage: apply_patches.py patch1.json [patch2.json ...]", file=sys.stderr)
        sys.exit(1)

    with open("informalizations.json") as f:
        data = json.load(f)

    by_name = {d["declName"]: i for i, d in enumerate(data)}
    applied = 0
    skipped = 0

    for patch_file in sys.argv[1:]:
        with open(patch_file) as f:
            patches = json.load(f)
        for patch in patches:
            name = patch["declName"]
            if name not in by_name:
                print(f"  SKIP (not found): {name}", file=sys.stderr)
                skipped += 1
                continue
            idx = by_name[name]
            entry = data[idx]
            if patch.get("prose"):
                entry["prose"] = patch["prose"]
            if patch.get("proofExposition") is not None:
                entry["proofExposition"] = patch["proofExposition"]
            if patch.get("termExposition") is not None:
                entry["termExposition"] = patch["termExposition"]
            applied += 1

    with open("informalizations.json", "w") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
        f.write("\n")

    print(f"Applied {applied} patches, skipped {skipped}.", file=sys.stderr)


if __name__ == "__main__":
    main()
