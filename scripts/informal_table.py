"""Build the @[informal] paper-alignment table from export JSON entries.

Each entry must have: declName, moduleName, paperRef, comment.
"""

import re


def sort_key(ref: str) -> tuple[int, int]:
    m = re.search(r"(\d+)\.(\d+)", ref)
    sec, sub = (int(m.group(1)), int(m.group(2))) if m else (0, 0)
    return (100, sub) if sec == 1 else (sec, sub)  # headline results last


def build_rows(entries: list[dict], prefix: str = "BridgelandStability.") -> list[tuple]:
    """Deduplicate and sort entries. Returns [(sort_key, paperRef, name, file, comment)]."""
    seen, rows = set(), []
    for e in entries:
        ref = e.get("paperRef")
        if not ref:
            continue
        decl = e["declName"]
        key = (ref, decl)
        if key in seen:
            continue
        seen.add(key)
        mod = e["moduleName"]
        rel = mod.removeprefix(prefix).replace(".", "/") + ".lean"
        name = decl.removeprefix("CategoryTheory.Triangulated.")
        note = e.get("comment") or ""
        rows.append((sort_key(ref), ref, name, rel, note))
    rows.sort()
    return rows


def render_markdown(rows: list[tuple]) -> str:
    header = "| Paper | Lean declaration | File | Notes |"
    sep = "|-------|-----------------|------|-------|"
    lines = [header, sep] + [
        f"| {ref} | `{name}` | `{f}` | {note} |"
        for _, ref, name, f, note in rows
    ]
    return "\n".join(lines) + "\n"
