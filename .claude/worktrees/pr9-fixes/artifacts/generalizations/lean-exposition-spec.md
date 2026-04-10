# lean-exposition: Design Spec

## Status: Draft — verified feasible on current toolchain

## One-sentence summary

A Lean 4 executable that walks a compiled project's environment and emits a
static site — mathematician-facing, with paired math/code, collapsible proofs,
interactive dependency graph, and one-click GitHub issue creation — built on
Verso's `Manual` genre and SubVerso's code highlighting.

---

## Proven foundation

**FormalFrontier/Sutherland-NumberTheory-verso** is a live example of exactly
this pattern: a Lean 4 project that uses Verso + Mathlib to produce a static
documentation site via `lake exe`. Deployed at
`formalfrontier.github.io/Sutherland-NumberTheory-verso/`.

Their architecture:
```
Main.lean (config + manualMain)
  → lake exe sutherland-nt
  → _out/html-multi/
  → GitHub Pages
```

Their stack: Verso `v4.29.0-rc8`, Mathlib, custom CSS/JS injected via config.
CI is `lake build && lake exe && deploy` — fast, no Python, no plasTeX.

Their limitation: all prose is hand-authored in Verso's DSL. We want to
auto-generate declaration cards from the environment.

---

## Toolchain verification

| Component | Available? | Details |
|---|---|---|
| Verso | Yes | Tag `v4.29.0-rc6` matches our `leanprover/lean4:v4.29.0-rc6` exactly |
| `Verso.Output.Html` | Yes | `text`, `tag`, `seq` constructors with `Html.asString` serializer |
| SubVerso highlighting | Yes | Comes with Verso; `Highlighted` type with JSON export |
| `Verso.Genre.Manual` | Yes | Multi-page static site genre with `manualMain` entry point |
| Lean core verso docstrings | Yes | `Lean.DocString.*` — parse verso syntax, convert to markdown |
| Environment walking | Yes | `importModules`, `env.find?`, `getModuleIdxFor?`, etc. |
| `findDocString?` | Yes | In core — extracts docstrings (plain string or verso AST) |
| `Expr.getUsedConstants` | Yes | Dependency computation (already used in `ExtractDeps.lean`) |
| `ppExpr` | Yes | Pretty-print types for display |
| Mathlib compatibility | Yes | Sutherland project proves Verso + Mathlib coexist |

### What does NOT exist (corrections from earlier drafts)

- ~~`Lean.Widget.Html`~~ — does not exist in Lean core
- ~~ProofWidgets `Html.toString`~~ — no static serialization; infoview-only
- ~~Verso in Lean core~~ — Verso is a **separate Lake package**, not built-in.
  Core has verso *docstring parsing* (`Lean.DocString.*`) but not the `Html`
  type or site generation.

---

## Architecture

Two possible approaches, both proven:

### Approach A: Verso Manual genre (recommended)

Use Verso's `Manual` genre with `manualMain`, like Sutherland-NT does. The
executable writes Verso document trees that `manualMain` renders to HTML.

```
┌─────────────────┐
│  Lean 4 Project │
│  (compiled)     │
└────────┬────────┘
         │ importModules
         ▼
┌─────────────────────────────────────────┐
│          lake exe exposition            │
│                                         │
│  1. Walk environment (declarations,     │
│     docstrings, dependencies, modules)  │
│                                         │
│  2. Build Verso Manual document tree    │
│     programmatically (not hand-authored │
│     — generated from environment data)  │
│                                         │
│  3. manualMain renders to HTML with     │
│     SubVerso highlighting, navigation,  │
│     cross-references, custom CSS/JS     │
│                                         │
│  4. Outputs _out/html-multi/            │
└────────┬────────────────────────────────┘
         │
         ▼
    _out/html-multi/ → GitHub Pages
```

**Pros:** Get Verso's full rendering pipeline (navigation, cross-refs, search,
themes, multi-page) for free. Proven pattern (Sutherland-NT). Custom CSS/JS
for dependency graph and issue buttons via `extraCss`/`extraJs` config.

**Cons:** Must learn Verso's document AST to generate programmatically. The
`Manual` genre may impose structure we don't want.

### Approach B: Raw `Verso.Output.Html` + `asString`

Use Verso only as an HTML library. Build `Html` trees directly, serialize
with `asString`, write files to disk. Full control over page structure.

```
┌─────────────────┐
│  Lean 4 Project │
│  (compiled)     │
└────────┬────────┘
         │ importModules
         ▼
┌─────────────────────────────────────────┐
│          lake exe exposition            │
│                                         │
│  1. Walk environment                    │
│  2. Highlight code via SubVerso         │
│  3. Build Html trees directly           │
│  4. Html.asString → write to disk       │
└────────┬────────────────────────────────┘
         │
         ▼
    site/ directory → GitHub Pages
```

**Pros:** No framework constraints. Full control. Simpler dependency (just
`Verso.Output.Html`, not the full genre system).

**Cons:** Must build navigation, cross-refs, page layout from scratch.
Reimplements what Verso's Manual genre already does.

### Recommendation

**Start with Approach A.** The `Manual` genre gives navigation, multi-page
output, themes, and cross-references for free. The Sutherland-NT project
proves it works. The auto-generation part (building the document tree from
the environment instead of hand-authoring) is the novel contribution — the
rendering is commodity.

If the `Manual` genre proves too constraining, fall back to Approach B. The
`Html` type and `asString` are available either way.

---

## What we auto-generate (the novel part)

Existing Verso projects (Sutherland-NT, PhysLean Notes, Lean Reference Manual)
are all **hand-authored**: a human writes prose in Verso's DSL and manually
includes Lean code blocks.

Our tool **programmatically generates** the document tree from the compiled
environment:

1. **Walk `env.constants`** filtered by module prefix (like `ExtractDeps`)
2. **For each declaration**, extract:
   - Fully qualified name, kind (def/theorem/structure/class/instance)
   - Docstring via `findDocString?` (rendered as markdown/KaTeX)
   - Type signature via `ppExpr` (highlighted via SubVerso)
   - Proof text for theorems (read from source file via `DeclarationRanges`)
   - Dependencies via `Expr.getUsedConstants` (filtered to project)
   - Sorry status via checking for `sorryAx` in constants
3. **Group by module**, order by source position
4. **Build Verso document tree** with:
   - One part/chapter per module group (Foundations, Deformation, etc.)
   - One section per module
   - Declaration cards with docstring + Lean signature + collapsible proof
   - Dependency links as cross-references
   - Issue button URLs as HTML anchors

---

## Page structure

### Index

- Project name, paper reference, description
- Progress dashboard: proved / sorry / axiom counts by module
- Navigation to module pages and dependency graph

### Module pages

For each declaration:

```
┌──────────────────────────────────────────────────┐
│ Definition: Slicing                   [📋 Issue] │
│                                                  │
│ A slicing P of D consists of full additive       │
│ subcategories P(φ) ⊂ D for each φ ∈ ℝ, ...      │
│ (docstring, rendered with KaTeX)                 │
│                                                  │
│ ┌─ Lean ───────────────────────────────────────┐ │
│ │ structure Slicing where                      │ │
│ │   P : ℝ → ObjectProperty C                  │ │
│ │   shift_iff : ...                            │ │
│ │   hom_vanishing : ...                        │ │
│ │   hn_exists : ...                            │ │
│ └──────────────────────────────────────────────┘ │
│ (SubVerso-highlighted)                           │
│                                                  │
│ Depends on: HNFiltration · PostnikovTower        │
│ Used by: StabilityCondition · IntervalCat        │
└──────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────┐
│ Theorem: phiPlus_unique               [📋 Issue] │
│                                                  │
│ The highest phase φ⁺(E) is well-defined.         │
│                                                  │
│ ┌─ Lean signature ────────────────────────────┐  │
│ │ theorem phiPlus_unique ...                  │  │
│ └─────────────────────────────────────────────┘  │
│                                                  │
│ ▶ Proof (click to expand)                        │
│ ┌─ <details> ────────────────────────────────┐   │
│ │ by                                         │   │
│ │   intro F₁ F₂ h₁ h₂                       │   │
│ │   exact uniqueness_of_hn_phases ...        │   │
│ └────────────────────────────────────────────┘   │
└──────────────────────────────────────────────────┘
```

### Dependency graph (`/graph/`)

D3.js + Graphviz WASM. The Lean program emits a JSON blob inline:
```html
<script>const graphData = { nodes: [...], edges: [...] }</script>
```

- Rectangles = defs/structures, ellipses = theorems
- Green = proved, red = sorry
- Click node → panel with info + issue button
- Filter by module, kind, status

---

## Issue button

Each declaration card has a 📋 link:

```
https://github.com/{repo}/issues/new?
  title=Review: {short_name}&
  body=**Declaration:** `{full_name}`%0A
       **Module:** `{module}`%0A
       **Source:** [{file}:{line}]({permalink})%0A
       **Status:** {proved|sorry}%0A%0A
       ---%0A%0A
       **Describe the issue:**%0A%0A&
  labels=exposition-review
```

Pure HTML. A Claude Code scheduled trigger can monitor the label.

---

## Build pipeline

```bash
lake exe cache get
lake build BridgelandStability
lake exe exposition          # emits _out/html-multi/ or site/
# deploy to GitHub Pages
```

CI time: ~90s build + ~30s site generation = **~2 minutes**.

---

## Existing code we reuse

- **`ExtractDeps.lean`** — dependency computation via `Expr.getUsedConstants`,
  module filtering, auto-generated declaration filtering. Already in the repo.
- **`Checkdecls.lean`** — environment loading pattern (`importModules`,
  workspace loading). Already in the repo.
- **Verso `v4.29.0-rc6`** — `Manual` genre, `manualMain`, `Html.asString`,
  SubVerso highlighting. Proven with Mathlib (Sutherland-NT).

---

## Resolved design questions

### 1. `manualMain` accepts programmatic document trees (CONFIRMED)

```lean
def manualMain (text : Part Manual) (options : List String)
    (config : RenderConfig := {}) ... : IO UInt32
```

`Part Manual` is a plain struct: `title`, `titleString`, `metadata`,
`content : Array (Block Manual)`, `subParts : Array (Part Manual)`. The
`#doc (Manual)` macro is just sugar that produces a `Part Manual` value.
We build the tree directly — no elaboration required.

### 2. SubVerso highlighting is heavyweight (DEFER TO v2)

There is no `String → Highlighted` function. SubVerso requires the full
Lean frontend pipeline (parse → import → elaborate → InfoTrees →
`highlightFrontendResult` in `TermElabM`). The `subverso-extract-mod` CLI
does this, but it re-elaborates the entire module.

**v1 decision:** Use `ppExpr` for type signatures (plain text) and source
file reading for proof text, rendered in `<pre><code>` with CSS-based
keyword highlighting. This avoids the SubVerso heavyweight pipeline.

**v2:** Either shell out to `subverso-extract-mod` per module (consume
JSON) or replicate its frontend pattern inline. This gives full syntax
highlighting with hover info.

### 3. Separate repo (DECIDED)

The tool lives in its own repo, usable by any Lean 4 project. It runs in
CI as `lake exe exposition` — added as a Lake dependency or invoked as a
separate step. This project is the first consumer.

### 4. Module grouping from directory structure (DECIDED)

Chapters are derived from the first path component after the project root:
`Deformation/*` → "Deformation Theory", `Slicing/*` → "Slicings", etc.
No config file needed — the project's file organization IS the document
structure.

### 5. Docstrings as-is (DECIDED)

v1 renders whatever docstrings exist. Undocumented declarations get a card
with just the Lean signature and no prose. This is honest and creates
visible pressure to add docstrings.

### 6. Name (OPEN)

Candidates: `lean-exposition`, `lean-atlas`, `lean-folio`, `formalink`.

---

## v1 scope

**In:**
- Environment walker collecting all project declarations with metadata
- Verso `Manual` genre for multi-page site with navigation
- `ppExpr` for type signatures + source file reading for proof text
- CSS keyword highlighting for Lean code (v1 — no SubVerso)
- KaTeX for docstring math (client-side `<script>` tag)
- Declaration cards: docstring + signature + collapsible proof (`<details>`)
- Dependency graph page (D3.js + inline JSON from environment walk)
- Issue buttons (pre-filled GitHub issue URLs)
- Custom CSS (clean, mathematician-friendly, Sutherland-NT as reference)
- GitHub Actions workflow: `lake build && lake exe && deploy`

**v2:**
- SubVerso syntax highlighting with hover info / go-to-definition
- Hand-authored Verso prose sections that `{include}` auto-generated cards
- Interactive proof states (Alectryon-style per-tactic goals)
- Full-text search (Pagefind)
- PDF output

---

## References

- Verso: https://github.com/leanprover/verso (tag `v4.29.0-rc6`)
- SubVerso: https://github.com/leanprover/subverso
- Sutherland-NT (proven example): https://github.com/FormalFrontier/Sutherland-NumberTheory-verso
- Sutherland-NT site: https://formalfrontier.github.io/Sutherland-NumberTheory-verso/
- PhysLean Notes (Verso site): https://notes.physlean.com/
- Tao Analysis I (Verso + formalization): https://github.com/teorth/analysis
- Verso Manual genre: used by the Lean Reference Manual
- `ExtractDeps.lean`: already in this repo, dependency computation
- `Checkdecls.lean`: already in this repo, environment loading pattern
