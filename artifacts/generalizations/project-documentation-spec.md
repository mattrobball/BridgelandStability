# Design Spec: Project Documentation System

## Status: Design phase

## Requirements

### Primary audience: Mathematicians
- Paper-style mathematical exposition is the default view
- Lean source is secondary — shown alongside but not dominating
- No assumption that the reader knows Lean syntax

### Core features
1. **Paired natural language + Lean statements** — each definition/theorem
   shows both the paper-style formulation and the Lean type signature
2. **Collapsible proofs** — proofs hidden by default, expandable on click
   (Isabelle's keep/drop/fold model)
3. **Dependency graph** — interactive, color-coded by formalization status
   (proved/in-progress/not-started), clickable nodes
4. **One-click "Create Issue" button** per declaration — opens a GitHub issue
   pre-filled with declaration name, file, line number, and a template for
   the mathematician to describe the problem. AI agents (Claude/Codex) can
   then be tasked with resolving the issue.

### Non-requirements (for now)
- Full API docs (doc-gen4 handles this separately)
- Interactive proof state display (Alectryon-style — desirable but not v1)
- PDF output (web-first)

---

## Landscape survey

### What exists in the Lean ecosystem

| Tool | Architecture | Strengths | Weaknesses |
|------|-------------|-----------|------------|
| **leanblueprint** | LaTeX → plasTeX → HTML | Proven (PFR, LTE); dependency graph; LaTeX natural for math | plasTeX rendering quirks; no collapsible proofs; manual `\uses{}` annotations; no issue buttons |
| **LeanArchitect** | Lean `@[blueprint]` → auto-extracted LaTeX | Eliminates manual `\uses{}`; complements leanblueprint | Still outputs through plasTeX; `extractAll` doesn't properly register nodes (bug we found) |
| **Verso** | Lean-native Markdown → HTML/PDF | Best Lean code rendering; proof states; type-checked refs | No dependency graphs; rapidly changing; not designed for blueprint-style tracking |
| **doc-gen4** | Lake → static HTML API docs | Auto-generated; comprehensive | API reference, not mathematical exposition |
| **LeanDepViz** | Lean → JSON/DOT/SVG | Multiple output formats; interactive | Standalone viz, not a doc system |

### What exists elsewhere

| Tool | Architecture | Key pattern to steal |
|------|-------------|---------------------|
| **Alectryon** (Coq) | Source → SerAPI → JSON → HTML | CSS-only proof state toggles; per-sentence display control |
| **Isabelle docs** | `.thy` with LaTeX antiquotations → PDF | `keep`/`drop`/`fold` tag system for proof regions; type-checked references |
| **Docusaurus** | MDX → React → static HTML | Custom React components (`<CollapsibleProof>`, `<CreateIssueButton>`); plugin ecosystem |
| **mdBook** | Markdown → HTML | Clean, fast, simple sidebar navigation |
| **Quarto** | `.qmd` → Pandoc → HTML/PDF | Scientific publishing quality; engine extensions |

### Dependency graph options

The community standard is **Graphviz layout + D3.js rendering** (used by
leanblueprint/plastexdepgraph). Color-coded rectangles (defs) and ellipses
(theorems), click-to-focus, zoom/pan. This works and should be reused.

---

## GitHub Issue Button (implementation)

GitHub supports pre-filled issues via URL parameters:

```
https://github.com/OWNER/REPO/issues/new?
  title=Declaration: Namespace.declName&
  body=**Declaration:** `Namespace.declName`%0A
       **File:** `BridgelandStability/Foo.lean:42`%0A%0A
       **Describe the issue:**%0A&
  labels=blueprint-review
```

Pure HTML — no backend needed. Any build system with declaration metadata
(name, file, line) can generate these links. The metadata is available from
LeanArchitect's JSON output or direct Lake environment queries.

---

## Architectural options

### Option A: Extend leanblueprint (lowest risk, fastest ship)

Keep the existing pipeline. Add:
- `<details>`/`<summary>` CSS for collapsible proofs (plasTeX postprocessor)
- "Create Issue" links via JS injection reading declaration metadata
- LeanArchitect for auto `\uses{}` (fix the `blueprintExt` registration bug)

**Ship time:** Days. **Ceiling:** Low — plasTeX limits interactivity.

### Option B: LeanArchitect JSON → custom static site (medium risk, highest flexibility)

Extract structured data from LeanArchitect into JSON:
```json
{
  "declarations": [
    {
      "name": "CategoryTheory.Triangulated.Slicing",
      "kind": "structure",
      "module": "BridgelandStability.Slicing.Defs",
      "file": "BridgelandStability/Slicing/Defs.lean",
      "line": 79,
      "docstring": "A slicing P of D consists of...",
      "leanSignature": "structure Slicing where ...",
      "proof": null,
      "uses": ["HNFiltration", "PostnikovTower"],
      "usedBy": ["StabilityCondition", "IntervalCat"],
      "status": "proved"
    }
  ]
}
```

Render with a lightweight static site generator (Docusaurus, Astro, or even
plain HTML + JS) with:
- **`<MathStatement>`** — renders LaTeX description + Lean signature side-by-side
- **`<CollapsibleProof>`** — `<details>` with the Lean proof, collapsed by default
- **`<CreateIssueButton>`** — generates GitHub issue link from declaration metadata
- **`<DependencyGraph>`** — D3.js interactive graph consuming the JSON

**Ship time:** Weeks. **Ceiling:** High — full control over UX.

### Option C: Verso (long-term bet)

Wait for Verso to stabilize. Write docs in Verso's Lean-native format. Extend
with dependency graph and issue button via Lean metaprogramming.

**Ship time:** Months (waiting on upstream). **Ceiling:** Highest if Verso
adds dependency graph support.

---

## Recommendation

**Do Option A now, build toward Option B.**

1. Fix the LeanArchitect `blueprintExt` registration bug (done locally).
2. Get the full blueprint rendering working with all 68 modules.
3. Add `<details>`-based collapsible proofs and issue buttons as post-processing.
4. In parallel, design the JSON schema for Option B and start extracting structured
   data from LeanArchitect.
5. Watch Verso — if it adds dependency graphs, re-evaluate.

The JSON-first approach (Option B) is the right medium-term architecture because
it **decouples data extraction from rendering**. Any frontend can consume the
JSON: Docusaurus today, Verso tomorrow, a custom React app next year. The
LeanArchitect extraction + `ExtractDeps` metaprogram already produce most of
the data; the missing piece is a clean JSON export format.

---

## References

- leanblueprint: https://github.com/PatrickMassot/leanblueprint
- LeanArchitect: https://github.com/hanwenzhu/LeanArchitect
- Verso: https://github.com/leanprover/verso
- Alectryon: https://github.com/cpitclaudel/alectryon
- Isabelle Document Preparation: https://isabelle.in.tum.de/library/Doc/Isar_Ref/Document_Preparation.html
- Docusaurus: https://docusaurus.io
- d3-graphviz: https://github.com/magjac/d3-graphviz
- Tao on PFR+Blueprint: https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/
- GitHub pre-filled issues: https://docs.github.com/en/issues/tracking-your-work-with-issues/using-issues/creating-an-issue
