#!/usr/bin/env python3
"""Generate Verso {docstring}-based informal exposition files from JSON.

Reads informalizations.json and produces a unified Verso manual:
  - InformalDocs/<path>.lean   (one per source module — leaf pages)
  - InformalDocs/<Group>.lean  (one per top-level group — chapter pages)
  - InformalDocs/Root.lean     (root manual composing all chapters)
  - InformalMain.lean          (single manualMain entry point)
  - lakefile.toml              (project config)
"""

import json
import os
import re
import argparse
from collections import defaultdict


# ── Chapter ordering (mathematical dependency) ──────────────────────────────

CHAPTER_ORDER = [
    "PostnikovTower",
    "GrothendieckGroup",
    "EulerForm",
    "ExtensionClosure",
    "QuasiAbelian",
    "TStructure",
    "IntervalCategory",
    "StabilityFunction",
    "Slicing",
    "NumericalStability",
    "NumericalStabilityManifold",
    "HeartEquivalence",
    "StabilityCondition",
    "Deformation",
]


# ── Prose sanitization ──────────────────────────────────────────────────────

def sanitize_prose(text: str) -> str:
    """Convert prose text to Verso-safe markup.

    - Converts $...$ LaTeX to $`...` Verso math
    - Escapes Verso-special chars (_, [, ], `) outside math spans
    """
    # Split on $...$ boundaries, preserving delimiters
    # Even indices are outside math, odd indices are inside math
    parts = re.split(r'(\$\$?.+?\$\$?)', text)
    result = []
    for i, part in enumerate(parts):
        if i % 2 == 1:
            # Math span — convert to Verso syntax
            if part.startswith("$$"):
                inner = part[2:-2]
                result.append(f"$$`{inner}`")
            else:
                inner = part[1:-1]
                result.append(f"$`{inner}`")
        else:
            # Outside math — escape Verso-special chars, but preserve
            # backtick code spans (`...`) which Verso renders as inline code
            def _escape_non_code(segment: str) -> str:
                segment = segment.replace("_", " ")
                segment = segment.replace("*", "\\*")
                segment = segment.replace("[", "(")
                segment = segment.replace("]", ")")
                segment = segment.replace("{", "(")
                segment = segment.replace("}", ")")
                return segment

            # Split on `...` code spans, preserve them intact
            code_parts = re.split(r'(`[^`]+`)', part)
            escaped = []
            for j, cp in enumerate(code_parts):
                if j % 2 == 1:
                    # Inside backticks — keep as-is (Verso inline code)
                    escaped.append(cp)
                else:
                    escaped.append(_escape_non_code(cp))
            result.append("".join(escaped))
    return "".join(result)


# ── Naming helpers ──────────────────────────────────────────────────────────

def short_title(decl_name: str) -> str:
    """Extract a short title from a fully-qualified name."""
    parts = decl_name.split(".")
    drop = {"CategoryTheory", "Triangulated", "Limits", "Abelian"}
    filtered = [p for p in parts if p not in drop]
    if not filtered:
        filtered = parts
    return filtered[-1]


def module_to_path(module_name: str, prefix: str) -> str:
    """Convert 'BridgelandStability.Slicing.Basic' to 'InformalDocs/Slicing/Basic.lean'."""
    parts = module_name.split(".")
    prefix_parts = prefix.split(".")
    if parts[: len(prefix_parts)] == prefix_parts:
        parts = parts[len(prefix_parts):]
    if not parts:
        parts = ["Root"]
    return os.path.join("InformalDocs", *parts[:-1], parts[-1] + ".lean")


def doc_module_name(module_name: str, prefix: str) -> str:
    """Convert 'BridgelandStability.Slicing.Basic' to 'InformalDocs.Slicing.Basic'."""
    parts = module_name.split(".")
    prefix_parts = prefix.split(".")
    if parts[: len(prefix_parts)] == prefix_parts:
        parts = parts[len(prefix_parts):]
    if not parts:
        parts = ["Root"]
    return "InformalDocs." + ".".join(parts)


def human_title(module_name: str, prefix: str) -> str:
    """Convert 'BridgelandStability.Slicing.Basic' to 'Slicing: Basic'."""
    parts = module_name.split(".")
    prefix_parts = prefix.split(".")
    if parts[: len(prefix_parts)] == prefix_parts:
        parts = parts[len(prefix_parts):]
    if not parts:
        return prefix
    if len(parts) == 1:
        return parts[0]
    return f"{parts[0]}: {'.'.join(parts[1:])}"


def group_modules(by_module: dict, prefix: str) -> dict[str, list[str]]:
    """Group module names by their top-level component after stripping prefix.

    Returns dict: group_name -> sorted list of full module names.
    """
    groups: dict[str, list[str]] = defaultdict(list)
    prefix_parts = prefix.split(".")
    for mod in by_module:
        parts = mod.split(".")
        if parts[: len(prefix_parts)] == prefix_parts:
            remainder = parts[len(prefix_parts):]
        else:
            remainder = parts
        group = remainder[0] if remainder else mod
        groups[group].append(mod)
    # Sort modules within each group
    for g in groups:
        groups[g].sort()
    return dict(groups)


def ordered_groups(groups: dict[str, list[str]]) -> list[tuple[str, list[str]]]:
    """Return groups in mathematical dependency order."""
    result = []
    seen = set()
    for name in CHAPTER_ORDER:
        if name in groups:
            result.append((name, groups[name]))
            seen.add(name)
    # Append any groups not in the predefined order (alphabetically)
    for name in sorted(groups):
        if name not in seen:
            result.append((name, groups[name]))
    return result


# ── Leaf doc generation (unchanged) ─────────────────────────────────────────

def issue_url(repo_url: str, decl_name: str, module_name: str,
              source_file: str | None, start_line: int | None,
              paper_ref: str | None) -> str:
    """Build a GitHub new-issue URL with pre-filled metadata."""
    from urllib.parse import quote
    short = decl_name.rsplit(".", 1)[-1]
    title = f"Review: {short}"
    source = f"{source_file}:{start_line}" if source_file and start_line else "unavailable"
    ref_line = f"**Paper:** {paper_ref}" if paper_ref else ""
    body = "\n".join(filter(None, [
        f"**Declaration:** `{decl_name}`",
        f"**Module:** `{module_name}`",
        f"**Source:** {source}",
        ref_line,
        "",
        "---",
        "",
        "**Describe the issue:**",
        "",
    ]))
    return f"{repo_url}/issues/new?title={quote(title)}&body={quote(body)}&labels=exposition-review"


def generate_doc_file(module_name: str, entries: list, prefix: str,
                      repo_url: str | None = None) -> str:
    """Generate a single Verso doc .lean file for one module."""
    lines = []
    lines.append(f"import {module_name}")
    lines.append("import VersoManual")
    lines.append("")
    lines.append("open Verso.Genre Manual")
    lines.append("")
    lines.append("set_option verso.docstring.allowMissing true")
    lines.append("")
    title = human_title(module_name, prefix)
    lines.append(f'#doc (Manual) "{title}" =>')
    lines.append("%%%")
    lines.append("htmlSplit := .never")
    lines.append("%%%")
    lines.append("")

    # Pre-compute heading titles, disambiguating duplicates
    raw_titles = [short_title(e["declName"]) for e in entries]
    title_counts: dict[str, int] = {}
    for t in raw_titles:
        title_counts[t] = title_counts.get(t, 0) + 1
    # For duplicates, use more of the qualified name until unique
    heading_titles = []
    for entry, raw in zip(entries, raw_titles):
        if title_counts[raw] > 1:
            parts = entry["declName"].split(".")
            drop = {"CategoryTheory", "Triangulated", "Limits", "Abelian"}
            filtered = [p for p in parts if p not in drop]
            # Try increasing suffix lengths until unique
            for n in range(2, len(filtered) + 1):
                candidate = ".".join(filtered[-n:])
                if sum(1 for e2 in entries
                       if ".".join([p for p in e2["declName"].split(".")
                                    if p not in drop][-n:]) == candidate) == 1:
                    break
            heading_titles.append(candidate if len(filtered) >= 2 else raw)
        else:
            heading_titles.append(raw)

    for entry, heading in zip(entries, heading_titles):
        decl_name = entry["declName"]
        prose = entry.get("prose", "")
        proof_expo = entry.get("proofExposition")
        term_expo = entry.get("termExposition")
        paper_ref = entry.get("paperRef")
        paper_comment = entry.get("paperComment")

        # Escape underscores in headings — Verso treats _ as emphasis
        st_safe = heading.replace("_", "\\_")
        lines.append(f"# {st_safe}")
        lines.append("")

        # Paper alignment badge
        if paper_ref:
            badge = f"**\\[{paper_ref}\\]**"
            if paper_comment:
                safe_comment = sanitize_prose(paper_comment)
                badge += f" {safe_comment}"
            lines.append(badge)
            lines.append("")

        if prose:
            safe_prose = " ".join(prose.split())
            safe_prose = safe_prose.replace("**", "")
            safe_prose = sanitize_prose(safe_prose)
            lines.append(safe_prose)
            lines.append("")

        if proof_expo:
            safe_proof = " ".join(proof_expo.split())
            safe_proof = sanitize_prose(safe_proof)
            lines.append(f"Proof: {safe_proof}")
            lines.append("")

        if term_expo:
            safe_term = " ".join(term_expo.split())
            safe_term = sanitize_prose(safe_term)
            lines.append(f"Construction: {safe_term}")
            lines.append("")
            lines.append("")

        lines.append("{docstring " + decl_name + "}")
        lines.append("")

        # Issue link
        if repo_url:
            url = issue_url(
                repo_url, decl_name, module_name,
                entry.get("sourceFile"), entry.get("startLine"),
                paper_ref,
            )
            lines.append(f"Something wrong, better idea? [Suggest a change]({url})")
            lines.append("")

    return "\n".join(lines)


# ── Chapter doc generation (NEW) ────────────────────────────────────────────

def generate_chapter_file(group_name: str, module_names: list[str], prefix: str) -> str:
    """Generate a chapter .lean file that includes all leaf modules in a group.

    No ``# heading`` — the ``#doc`` title serves as the chapter name in the TOC.
    Adding a heading would create an extra empty intermediate page when Verso splits.
    """
    doc_mods = [doc_module_name(m, prefix) for m in module_names]

    lines = []
    lines.append("import VersoManual")
    for dm in doc_mods:
        lines.append(f"import {dm}")
    lines.append("")
    lines.append("open Verso.Genre Manual")
    lines.append("")
    lines.append(f'#doc (Manual) "{group_name}" =>')
    lines.append("")
    for dm in doc_mods:
        lines.append(f"{{include 0 {dm}}}")
        lines.append("")
    return "\n".join(lines)


# ── Root doc generation (NEW) ───────────────────────────────────────────────

def _build_includes(
    chapter_groups: list[tuple[str, list[str]]],
    direct_leaves: list[tuple[str, str]],
) -> list[tuple[str, str]]:
    """Build the ordered list of (import_name, include_name) for chapter pages."""
    all_includes = []
    chapter_set = {g for g, _ in chapter_groups}
    leaf_set = {g: dm for g, dm in direct_leaves}

    for name in CHAPTER_ORDER:
        if name in chapter_set:
            all_includes.append((f"InformalDocs.{name}", f"InformalDocs.{name}"))
        elif name in leaf_set:
            all_includes.append((leaf_set[name], leaf_set[name]))
    for g, _ in chapter_groups:
        if (f"InformalDocs.{g}", f"InformalDocs.{g}") not in all_includes:
            all_includes.append((f"InformalDocs.{g}", f"InformalDocs.{g}"))
    for g, dm in direct_leaves:
        if (dm, dm) not in all_includes:
            all_includes.append((dm, dm))
    return all_includes


def generate_chapters_file(
    chapter_groups: list[tuple[str, list[str]]],
    direct_leaves: list[tuple[str, str]],
) -> str:
    """Generate Chapters.lean — all chapter includes on a single page."""
    all_includes = _build_includes(chapter_groups, direct_leaves)

    lines = []
    lines.append("import VersoManual")
    for imp, _ in all_includes:
        lines.append(f"import {imp}")
    lines.append("")
    lines.append("open Verso.Genre Manual")
    lines.append("")
    lines.append("set_option maxHeartbeats 800000")
    lines.append("")
    lines.append('#doc (Manual) "Chapters" =>')
    lines.append("")
    lines.append(
        "The chapters below follow the mathematical dependency order of the formalization."
    )
    lines.append("")
    for _, inc in all_includes:
        lines.append(f"{{include 0 {inc}}}")
        lines.append("")
    return "\n".join(lines)


def generate_root_file(
    chapter_groups: list[tuple[str, list[str]]],
    direct_leaves: list[tuple[str, str]],
    total_entries: int,
) -> str:
    """Generate Root.lean — landing page with intro, contributing, and paper alignment."""
    lines = []
    lines.append("import VersoManual")
    lines.append("import InformalDocs.Chapters")
    lines.append("")
    lines.append("open Verso.Genre Manual")
    lines.append("")
    lines.append('#doc (Manual) "Bridgeland Stability Conditions" =>')
    lines.append("")
    lines.append(
        "Inspired by Douglas's work on \\`Π\\`-stability in string theory, "
        "Bridgeland stability conditions allow one to extract a complex manifold "
        "from a triangulated category. A stability condition pairs a central charge "
        "--- a group homomorphism from the Grothendieck group to the complex numbers "
        "--- with a slicing of the category into semistable objects of each phase. "
        "Bridgeland's main theorem is that the space of all such conditions is itself "
        "a complex manifold, with local charts given by the central charge."
    )
    lines.append("")
    lines.append(
        "This site documents a machine-checked proof of that theorem, formalized "
        "in Lean 4 using Mathlib. All Lean code is written by AI agents guided by "
        "human mathematicians --- no human writes proof scripts. The formalization "
        "covers Sections 2--7 of Bridgeland's "
        "*Stability conditions on triangulated categories* (Annals of Mathematics, 2007), "
        "working in the class-map generality of Bayer--Macr\\`i--Stellari and "
        "Bayer--Lahoz--Macr\\`i--Nuer--Perry--Stellari."
    )
    lines.append("")
    lines.append(
        "Why trust a proof written by AI? Two independent checks. First, every "
        "logical step is verified by Lean's kernel --- a small, fixed type checker "
        "that accepts or rejects proofs regardless of how they were produced. The "
        "kernel guarantees the arguments are correct. Second, the "
        "[Comparator Manual](comparator/) lists the definitions the result "
        "depends on, paired with their informal mathematical meanings, so you can "
        "audit whether the formal statements faithfully capture the mathematics."
    )
    lines.append("")
    lines.append(
        "Each declaration is paired with an informal description and, where "
        "available, a proof sketch. Passing the type checker is necessary but not "
        "sufficient: the formalization aims for Mathlib quality, with correct "
        "abstractions, reusable lemmas, and proofs that could survive code review "
        "and upstreaming. If you see a mathematical inaccuracy, a missing "
        "generalization, a cleaner definition, or --- if you know Lean --- a better "
        "proof strategy, each declaration has a link to open an issue. Describe what "
        "you think should happen and start a discussion. Once we figure out what "
        "needs to change, AI agents will do the rest."
    )
    lines.append("")
    lines.append("# Paper Alignment")
    lines.append("")
    lines.append(
        "The table below lists every definition, lemma, and theorem from "
        "the paper that has a formal analog tagged with `@\\[informal\\]`."
    )
    lines.append("")
    lines.append("{include 0 InformalDocs.Chapters}")
    lines.append("")
    return "\n".join(lines)


# ── Main entry point (NEW) ─────────────────────────────────────────────────

def generate_main() -> str:
    """Generate InformalMain.lean — single manualMain call."""
    return """\
import VersoManual
import InformalDocs.Root

open Verso.Genre Manual

def main := manualMain (%doc InformalDocs.Root)
"""


def generate_lakefile(source_path: str, verso_rev: str) -> str:
    """Generate lakefile.toml."""
    return f"""name = "BridgelandInformal"
version = "0.1.0"

[[require]]
name = "verso"
git = "https://github.com/leanprover/verso"
rev = "{verso_rev}"

[[require]]
name = "BridgelandStability"
path = "{source_path}"

[[lean_lib]]
name = "InformalDocs"

[[lean_exe]]
name = "informal"
root = "InformalMain"
"""


# ── CLI ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Generate Verso docstring-based docs")
    parser.add_argument("--json", required=True, help="Path to informalizations.json")
    parser.add_argument("--output", required=True, help="Output directory (bridgeland-informal/)")
    parser.add_argument(
        "--source-path",
        default="../bridgeland-extract",
        help="Relative path from output to source project (for lakefile)",
    )
    parser.add_argument(
        "--prefix",
        default="BridgelandStability",
        help="Root module prefix to strip",
    )
    parser.add_argument(
        "--verso-rev",
        default="v4.29.0",
        help="Verso git revision",
    )
    parser.add_argument(
        "--repo-url",
        default=None,
        help="GitHub repo URL for issue/source links",
    )
    args = parser.parse_args()

    with open(args.json) as f:
        entries = json.load(f)
    print(f"Loaded {len(entries)} entries from {args.json}")

    by_module = defaultdict(list)
    for entry in entries:
        by_module[entry["moduleName"]].append(entry)
    print(f"Found {len(by_module)} modules")

    # ── Leaf docs (one per module) ──
    for module_name, mod_entries in sorted(by_module.items()):
        # Sort by source line when available, then alphabetically as fallback
        mod_entries.sort(key=lambda e: (e.get("startLine") or 999999, e["declName"]))
        rel_path = module_to_path(module_name, args.prefix)
        out_path = os.path.join(args.output, rel_path)
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        content = generate_doc_file(module_name, mod_entries, args.prefix, args.repo_url)
        with open(out_path, "w") as f:
            f.write(content)
        print(f"  {rel_path} ({len(mod_entries)} entries)")

    # ── Chapter docs (one per group) ──
    # Single-component modules (e.g. BridgelandStability.ExtensionClosure) have
    # their leaf at InformalDocs/ExtensionClosure.lean — same path as the chapter
    # would get.  For these, skip the chapter and include the leaf directly in Root.
    groups = group_modules(by_module, args.prefix)
    sorted_groups = ordered_groups(groups)
    prefix_parts = args.prefix.split(".")

    # Partition into groups that need chapters vs direct includes
    chapter_groups = []   # (group_name, module_names) — get a chapter file
    direct_leaves = []    # (group_name, doc_module_name) — included directly in Root

    for group_name, module_names in sorted_groups:
        if len(module_names) == 1:
            mod = module_names[0]
            remainder = mod.split(".")[len(prefix_parts):]
            if len(remainder) == 1:
                # Single-component module — leaf path collides with chapter path
                direct_leaves.append((group_name, doc_module_name(mod, args.prefix)))
                continue
        chapter_groups.append((group_name, module_names))

    print(f"\nGenerating {len(chapter_groups)} chapter files ({len(direct_leaves)} direct leaves):")
    for group_name, module_names in chapter_groups:
        content = generate_chapter_file(group_name, module_names, args.prefix)
        chapter_path = os.path.join(args.output, "InformalDocs", f"{group_name}.lean")
        with open(chapter_path, "w") as f:
            f.write(content)
        print(f"  InformalDocs/{group_name}.lean ({len(module_names)} modules)")
    for group_name, dm in direct_leaves:
        print(f"  (direct) {dm}")

    # ── Chapters doc ──
    chapters_content = generate_chapters_file(chapter_groups, direct_leaves)
    chapters_path = os.path.join(args.output, "InformalDocs", "Chapters.lean")
    with open(chapters_path, "w") as f:
        f.write(chapters_content)
    print(f"  InformalDocs/Chapters.lean")

    # ── Root doc ──
    root_content = generate_root_file(chapter_groups, direct_leaves, len(entries))
    root_path = os.path.join(args.output, "InformalDocs", "Root.lean")
    with open(root_path, "w") as f:
        f.write(root_content)
    print(f"  InformalDocs/Root.lean")

    # ── InformalMain.lean ──
    main_content = generate_main()
    main_path = os.path.join(args.output, "InformalMain.lean")
    with open(main_path, "w") as f:
        f.write(main_content)
    print(f"  InformalMain.lean")

    # ── lakefile.toml ──
    lakefile_content = generate_lakefile(args.source_path, args.verso_rev)
    lakefile_path = os.path.join(args.output, "lakefile.toml")
    with open(lakefile_path, "w") as f:
        f.write(lakefile_content)
    print(f"  lakefile.toml")

    print(f"\nGenerated {len(by_module)} leaf docs + {len(sorted_groups)} chapters + Root + InformalMain + lakefile")


if __name__ == "__main__":
    main()
