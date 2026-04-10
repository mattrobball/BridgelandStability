#!/usr/bin/env python3
"""Merge extracted declarations with existing prose database.

Usage:
    python3 scripts/merge_prose.py --extracted extracted.json --existing informalizations.json

Reads the extracted declarations (from `lake build extractDecls`) and merges
with the existing prose JSON. Preserves prose for matched declarations, adds
stubs for new ones, and writes stale entries to a separate file.

Uses contentHash to detect when a declaration's signature/body has changed,
marking those entries as needsReview so prose can be updated.
"""

import argparse
import json
import sys


def merge(extracted: list[dict], existing: list[dict]) -> tuple[list[dict], list[dict], dict]:
    existing_by_name = {e["declName"]: e for e in existing}
    stats = {"kept": 0, "changed": 0, "added": 0, "stale": 0}
    merged = []
    seen = set()

    for ext in extracted:
        name = ext["declName"]
        seen.add(name)

        if name in existing_by_name:
            old = existing_by_name[name]
            entry = {
                "declName": name,
                "declKind": ext["declKind"],
                "moduleName": ext["moduleName"],
                "docstring": ext.get("docstring"),
                "contentHash": ext.get("contentHash"),
                "depHashes": ext.get("depHashes"),
                "paperRef": ext.get("paperRef"),
                "paperComment": ext.get("paperComment"),
                "sourceFile": ext.get("sourceFile"),
                "startLine": ext.get("startLine"),
                "endLine": ext.get("endLine"),
                "prose": old.get("prose", ""),
                "proofExposition": old.get("proofExposition"),
                "termExposition": old.get("termExposition"),
            }
            old_hash = old.get("contentHash")
            new_hash = ext.get("contentHash")
            if old_hash is not None and new_hash is not None and old_hash != new_hash:
                entry["needsReview"] = True
                stats["changed"] += 1
            else:
                stats["kept"] += 1
            merged.append(entry)
        else:
            entry = {
                "declName": name,
                "declKind": ext["declKind"],
                "moduleName": ext["moduleName"],
                "docstring": ext.get("docstring"),
                "contentHash": ext.get("contentHash"),
                "depHashes": ext.get("depHashes"),
                "paperRef": ext.get("paperRef"),
                "paperComment": ext.get("paperComment"),
                "sourceFile": ext.get("sourceFile"),
                "startLine": ext.get("startLine"),
                "endLine": ext.get("endLine"),
                "prose": "",
                "proofExposition": None,
                "termExposition": None,
            }
            stats["added"] += 1
            merged.append(entry)

    stale = []
    for old in existing:
        if old["declName"] not in seen:
            stats["stale"] += 1
            stale.append(old)

    return merged, stale, stats


def main():
    parser = argparse.ArgumentParser(description="Merge extracted declarations with existing prose")
    parser.add_argument("--extracted", required=True, help="Path to extracted.json")
    parser.add_argument("--existing", required=True, help="Path to existing informalizations.json")
    parser.add_argument("--output", help="Output path (default: overwrite --existing)")
    parser.add_argument("--stale-output", default="informalizations-stale.json",
                        help="Path for stale entries (default: informalizations-stale.json)")
    args = parser.parse_args()

    with open(args.extracted) as f:
        extracted = json.load(f)
    with open(args.existing) as f:
        existing = json.load(f)

    merged, stale, stats = merge(extracted, existing)

    output_path = args.output or args.existing
    with open(output_path, "w") as f:
        json.dump(merged, f, indent=2, ensure_ascii=False)
        f.write("\n")

    if stale:
        with open(args.stale_output, "w") as f:
            json.dump(stale, f, indent=2, ensure_ascii=False)
            f.write("\n")

    print(f"Merge complete:", file=sys.stderr)
    print(f"  Kept (unchanged):     {stats['kept']:>5}", file=sys.stderr)
    print(f"  Signature changed:    {stats['changed']:>5}", file=sys.stderr)
    print(f"  Added (new):          {stats['added']:>5}", file=sys.stderr)
    print(f"  Stale (removed):      {stats['stale']:>5}", file=sys.stderr)
    print(f"  Total output:         {len(merged):>5}", file=sys.stderr)
    if stale:
        print(f"  Stale written to: {args.stale_output}", file=sys.stderr)


if __name__ == "__main__":
    main()
