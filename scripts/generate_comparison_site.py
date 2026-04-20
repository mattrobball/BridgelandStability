#!/usr/bin/env python3
"""Generate a Verso shadow project for the paper-vs-Lean comparison dashboard.

Reads paper-statements.json (left column: paper prose) and extracted.json
(right column: `@[informal "paperRef"]`-tagged Lean declarations), writes a
Verso manual shadow project to OUTPUT, which `lake exe comparison` can then
build to HTML via Verso + SubVerso.

Outputs:
  OUTPUT/ComparisonDocs/Index.lean   — the dashboard, one section per paper entry
  OUTPUT/ComparisonMain.lean         — manualMain entry point
  OUTPUT/lakefile.toml               — depends on verso + BridgelandStability

The generator writes Verso-markdown strings only — no Lean parsing on the
Python side. Per-decl highlighting is handled inside Verso via the
`{informalByRef (paperRef := "...")}` code-block expander provided by the
`informal` Lean package (Informal.VersoBlock).
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path


# Reuse prose-sanitization from scripts/generate_site.py by running it as
# a sibling module. Keeping this file self-contained by duplicating the
# function is fine too; this is a few lines.
def sanitize_prose(text: str) -> str:
    """Convert prose text to Verso-safe markup.

    - Converts $...$ LaTeX to $`...` Verso math
    - Escapes Verso-special chars ([, ], {, }, *) outside math / code spans
    - Replaces _ with space (Verso treats _ as emphasis and paper prose does
      not need it)
    """
    parts = re.split(r'(\$\$?.+?\$\$?)', text)
    out: list[str] = []
    for i, part in enumerate(parts):
        if i % 2 == 1:
            if part.startswith("$$"):
                inner = part[2:-2]
                out.append(f"$$`{inner}`")
            else:
                inner = part[1:-1]
                out.append(f"$`{inner}`")
            continue

        def _escape_non_code(seg: str) -> str:
            seg = seg.replace("_", " ")
            seg = seg.replace("*", "\\*")
            seg = seg.replace("[", "(")
            seg = seg.replace("]", ")")
            seg = seg.replace("{", "(")
            seg = seg.replace("}", ")")
            return seg

        code_parts = re.split(r'(`[^`]+`)', part)
        buf: list[str] = []
        for j, cp in enumerate(code_parts):
            buf.append(cp if j % 2 == 1 else _escape_non_code(cp))
        out.append("".join(buf))

    return "".join(out)


def _heading_slug(ref: str) -> str:
    """Turn a paper ref like 'Theorem 1.2' into a Verso heading tag slug."""
    return re.sub(r"[^a-zA-Z0-9]+", "-", ref).strip("-").lower()


def render_section(section_num: str, section_title: str,
                   entries: list[dict], informal_by_ref: dict[str, list[dict]],
                   project_path: str) -> str:
    """Generate one ComparisonDocs/Section{N}.lean file for one paper section.

    The per-section split keeps each generated `.c` file small — a single
    36-entry file produced a 41k-line `.c` that segfaulted clang.
    """
    lines: list[str] = []
    lines.append("import BridgelandStability")
    lines.append("import Informal.VersoBlock")
    lines.append("import VersoManual")
    lines.append("")
    lines.append("open Verso.Genre Manual")
    lines.append("open Informal.VersoBlock")
    lines.append("")
    lines.append(f'set_option verso.exampleProject "{project_path}"')
    lines.append("set_option maxHeartbeats 2000000")
    lines.append("")
    title = f"§{section_num} — {section_title}"
    lines.append(f'#doc (Manual) "{title}" =>')
    lines.append("")

    for entry in entries:
        ref = entry["ref"]
        kind = entry.get("kind", "")
        prose = entry.get("prose", "")

        section_heading = f"{ref}" + (f" — {kind}" if kind else "")
        lines.append(f"# {sanitize_prose(section_heading)}")
        lines.append("")
        if prose:
            lines.append(sanitize_prose(prose))
            lines.append("")
        if ref in informal_by_ref:
            lines.append(f'```informalByRef (paperRef := "{ref}")')
            lines.append("```")
            lines.append("")
        else:
            lines.append("_Not yet formalized in this project._")
            lines.append("")

    return "\n".join(lines)


def render_root(section_nums: list[str], section_titles: dict[str, str],
                source_title: str, repo_url: str | None,
                project_path: str) -> str:
    """Generate ComparisonDocs/Root.lean — composes every per-section file."""
    lines: list[str] = []
    lines.append("import VersoManual")
    for n in section_nums:
        lines.append(f"import ComparisonDocs.Section{n}")
    lines.append("")
    lines.append("open Verso.Genre Manual")
    lines.append("")
    lines.append(f'set_option verso.exampleProject "{project_path}"')
    lines.append("set_option maxHeartbeats 2000000")
    lines.append("")
    title = f"{source_title} — Comparison Index"
    lines.append(f'#doc (Manual) "{title}" =>')
    lines.append("")
    if repo_url:
        lines.append(f"[GitHub repository]({repo_url})")
        lines.append("")
    lines.append(
        "Every numbered result from the paper, paired with its Lean formalization "
        "(when one exists). The left-hand prose is the paper statement; each code "
        "block is the `@[informal]`-tagged Lean declaration, rendered by Verso + "
        "SubVerso directly from the formalization source."
    )
    lines.append("")
    for n in section_nums:
        lines.append(f"{{include 0 ComparisonDocs.Section{n}}}")
        lines.append("")
    return "\n".join(lines)


def render_main() -> str:
    """Generate ComparisonMain.lean."""
    return (
        "import VersoManual\n"
        "import ComparisonDocs.Root\n"
        "\n"
        "open Verso.Genre Manual\n"
        "\n"
        "def main := manualMain (%doc ComparisonDocs.Root)\n"
    )


def render_lakefile(source_path: str, verso_rev: str, informal_rev: str) -> str:
    """Generate lakefile.toml for the shadow project.

    Requires the same `verso` rev as the main informal site; takes
    `BridgelandStability` by path (which itself pulls `informal` with the
    `Informal.VersoBlock` module baked in). No separate `informal` require
    needed — BridgelandStability's lakefile transitively provides it.
    """
    return (
        'name = "BridgelandComparison"\n'
        'version = "0.1.0"\n'
        '\n'
        '[[require]]\n'
        'name = "verso"\n'
        'git = "https://github.com/leanprover/verso"\n'
        f'rev = "{verso_rev}"\n'
        '\n'
        '[[require]]\n'
        'name = "BridgelandStability"\n'
        f'path = "{source_path}"\n'
        '\n'
        '[[lean_lib]]\n'
        'name = "ComparisonDocs"\n'
        '\n'
        '[[lean_exe]]\n'
        'name = "comparison"\n'
        'root = "ComparisonMain"\n'
    )


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--paper", required=True,
                   help="Path to paper-statements.json")
    p.add_argument("--extracted", required=True,
                   help="Path to extract_decls output JSON")
    p.add_argument("--output", default="comparison-build",
                   help="Output directory for the shadow project")
    p.add_argument("--source-path", default="..",
                   help="Relative path from OUTPUT to BridgelandStability root "
                        "(for the lakefile `path` require)")
    p.add_argument("--prefix", default="BridgelandStability",
                   help="Root module prefix (unused in v1, for forward compat)")
    p.add_argument("--verso-rev", default="v4.29.0",
                   help="Verso git revision for the shadow project's lakefile")
    p.add_argument("--informal-rev", default="main",
                   help="lean-informal git revision (unused in v1; BS provides "
                        "the transitive dep)")
    p.add_argument("--repo-url", default=None,
                   help="Repo URL for the landing blurb")
    args = p.parse_args()

    paper_doc = json.loads(Path(args.paper).read_text())
    meta = paper_doc.get("_meta", {})
    source_title = meta.get("source", {}).get("title", "Paper")
    section_titles: dict[str, str] = meta.get("sections", {})
    statements = paper_doc.get("statements", [])

    extracted = json.loads(Path(args.extracted).read_text())
    informal_by_ref: dict[str, list[dict]] = defaultdict(list)
    for decl in extracted:
        ref = decl.get("paperRef")
        if ref:
            informal_by_ref[ref].append(decl)

    # Group statements by their paper section. Each section becomes one
    # generated file so a single `.c` translation unit stays small enough
    # for clang to compile.
    by_section: dict[str, list[dict]] = defaultdict(list)
    for s in statements:
        key = str(s.get("section", "misc"))
        by_section[key].append(s)
    section_nums = sorted(by_section.keys(),
                          key=lambda k: (int(k) if k.isdigit() else 1_000_000, k))

    out = Path(args.output)
    (out / "ComparisonDocs").mkdir(parents=True, exist_ok=True)

    for num in section_nums:
        title = section_titles.get(num, f"Section {num}")
        section_lean = render_section(num, title, by_section[num], informal_by_ref,
                                      project_path=args.source_path)
        (out / "ComparisonDocs" / f"Section{num}.lean").write_text(section_lean)

    root_lean = render_root(section_nums, section_titles, source_title, args.repo_url,
                            project_path=args.source_path)
    (out / "ComparisonDocs" / "Root.lean").write_text(root_lean)

    (out / "ComparisonMain.lean").write_text(render_main())

    (out / "lakefile.toml").write_text(
        render_lakefile(args.source_path, args.verso_rev, args.informal_rev)
    )

    n_paper = len(statements)
    n_informal = sum(len(v) for v in informal_by_ref.values())
    n_matched = sum(1 for e in statements if e["ref"] in informal_by_ref)
    print(f"wrote {out}/ComparisonDocs/{{Root, Section{','.join(section_nums)}}}.lean, "
          f"ComparisonMain.lean, lakefile.toml")
    print(f"  {n_paper} paper entries across {len(section_nums)} sections, "
          f"{n_matched} with Lean decls, {n_informal} informal-tagged decls total")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
