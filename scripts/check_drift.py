#!/usr/bin/env python3
"""Check @[informal]-tagged declarations for drift.

Usage:
    python3 scripts/check_drift.py --extracted extracted.json --baseline informalizations.json

Compares contentHash and depHashes for declarations with a paperRef.
Output format matches the legacy #check_informal command so existing CI
comment/label logic works unchanged.
"""

import argparse
import json
import sys


def check_drift(extracted: list[dict], baseline: list[dict]) -> tuple[list[str], int]:
    baseline_by_name = {e["declName"]: e for e in baseline}
    issues: list[str] = []
    informal_count = 0

    for ext in extracted:
        paper_ref = ext.get("paperRef")
        if not paper_ref:
            continue
        informal_count += 1
        name = ext["declName"]
        old = baseline_by_name.get(name)
        if old is None:
            issues.append(
                f'@[informal "{paper_ref}"] on {name}: new declaration (not in baseline)'
            )
            continue

        old_hash = old.get("contentHash")
        new_hash = ext.get("contentHash")
        if old_hash is not None and new_hash is not None and old_hash != new_hash:
            issues.append(
                f'@[informal "{paper_ref}"] on {name}: '
                f"declaration changed (hash {old_hash} \u2192 {new_hash})"
            )

        old_raw = old.get("depHashes")
        new_raw = ext.get("depHashes")
        if old_raw is not None and new_raw is not None:
            old_deps = {d["name"]: d["hash"] for d in old_raw if isinstance(d, dict)}
            new_deps = {d["name"]: d["hash"] for d in new_raw if isinstance(d, dict)}

            for dep_name, new_dep_hash in new_deps.items():
                old_dep_hash = old_deps.get(dep_name)
                if old_dep_hash is None:
                    issues.append(
                        f'@[informal "{paper_ref}"] on {name}: '
                        f"new dependency {dep_name}"
                    )
                elif old_dep_hash != new_dep_hash:
                    issues.append(
                        f'@[informal "{paper_ref}"] on {name}: '
                        f"dependency {dep_name} changed "
                        f"(hash {old_dep_hash} \u2192 {new_dep_hash})"
                    )

            for dep_name in old_deps:
                if dep_name not in new_deps:
                    issues.append(
                        f'@[informal "{paper_ref}"] on {name}: '
                        f"dependency {dep_name} no longer exists"
                    )

    return issues, informal_count


def main():
    parser = argparse.ArgumentParser(
        description="Check @[informal]-tagged declarations for drift"
    )
    parser.add_argument("--extracted", required=True, help="Path to freshly extracted JSON")
    parser.add_argument("--baseline", required=True, help="Path to baseline informalizations.json")
    args = parser.parse_args()

    with open(args.extracted) as f:
        extracted = json.load(f)
    with open(args.baseline) as f:
        baseline = json.load(f)

    issues, informal_count = check_drift(extracted, baseline)

    for issue in issues:
        print(issue)

    if issues:
        print(f"{len(issues)} issue(s) found across {informal_count} informal entries.")
    else:
        print(f"All {informal_count} informal entries are consistent.")


if __name__ == "__main__":
    main()
