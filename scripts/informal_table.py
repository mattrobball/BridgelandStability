"""Build the @[informal] paper-alignment table from export JSON entries.

Each entry must have: declName, moduleName, paperRef.
"""

import re


def sort_key(ref: str) -> tuple[int, int]:
    m = re.search(r"(\d+)\.(\d+)", ref)
    sec, sub = (int(m.group(1)), int(m.group(2))) if m else (0, 0)
    return (0, sub) if sec == 1 else (sec, sub)  # headline results first


# Paper refs where the formalization is split across multiple declarations
# and no single one is complete — omit from the summary table.
PARTIAL_REFS = {"Lemma 3.4", "Proposition 5.3"}

# When multiple declarations share a paper ref, prefer this one.
PREFERRED_DECL = {
    "Theorem 1.2": "CategoryTheory.Triangulated.centralChargeIsLocalHomeomorphOnConnectedComponents",
    "Definition 5.7": "CategoryTheory.Triangulated.StabilityCondition.WithClassMap",
}


def build_rows(entries: list[dict], prefix: str = "BridgelandStability.") -> list[tuple]:
    """Deduplicate and sort entries. Returns [(sort_key, paperRef, shortName, fullName)].

    One declaration per paper reference. Partial formalizations are omitted.
    """
    # Group by paper ref
    by_ref: dict[str, list[dict]] = {}
    for e in entries:
        ref = e.get("paperRef")
        if not ref or ref in PARTIAL_REFS:
            continue
        by_ref.setdefault(ref, []).append(e)

    rows = []
    for ref, candidates in by_ref.items():
        # Pick preferred declaration if specified, else first
        preferred = PREFERRED_DECL.get(ref)
        entry = None
        if preferred:
            entry = next((e for e in candidates if e["declName"] == preferred), None)
        if entry is None:
            entry = candidates[0]
        decl = entry["declName"]
        short = decl.removeprefix("CategoryTheory.Triangulated.").removeprefix("CategoryTheory.")
        rows.append((sort_key(ref), ref, short, decl))
    rows.sort()
    return rows


def render_markdown(rows: list[tuple]) -> str:
    header = "| Paper | Lean declaration |"
    sep = "|-------|-----------------|"
    lines = [header, sep] + [
        f"| {ref} | `{name}` |"
        for _, ref, name, _full in rows
    ]
    return "\n".join(lines) + "\n"
