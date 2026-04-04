# Plan: Unified Exposition Site

## Context

Three data layers exist for the BridgelandStability formalization, currently rendered by separate tools:

1. **Comparator/TFB** — lean-exposition renders trusted formalization base + dependency graph
2. **Informal prose** — bridgeland-informal renders `informalizations.json` prose via `{docstring}` blocks
3. **Paper alignment** — `@[informal]` tags + audit map declarations to Bridgeland paper sections

Goal: one site with all three layers, full SubVerso hover info (including declaration bodies), generated in CI.

## Architecture

A unified Verso project (extending the bridgeland-informal approach) that combines:
- `{docstring}` blocks for signatures with hover (cheap, env lookup only)
- ` ```anchor ` blocks for declaration bodies with hover (pre-computed highlighted JSON)
- Prose from `informalizations.json` as running text
- Paper alignment badges from `@[informal]` environment extension
- Comparator results as a separate chapter

### Why this approach

- `{docstring}` is fast (~10s build in bridgeland-informal today) but can't show bodies
- ` ```anchor ` shows full source with hover from pre-computed JSON — no re-elaboration during Verso build
- lean-exposition is too resource-intensive to scale to all 1128 declarations
- Shadow copy with anchor injection is needed for ` ```anchor ` but can be done efficiently (preserve `.lake`, only update source files)

## Verso directive reference

| Directive | Hover? | Shows body? | Cost | Import needed? |
|-----------|--------|-------------|------|----------------|
| `{docstring}` | Yes | No (signature only) | Cheap (env lookup) | Yes |
| ` ```module/anchor ` | Yes | Yes (full source) | Medium (pre-computed JSON) | No (external) |
| ` ```lean ` | Yes | Yes | Expensive (re-elaborates) | N/A |
| ` ```signature ` | Yes | No | Partial | No |

## Pipeline

```
1. lake build BridgelandStability                    (oleans, ~15 min cold / instant cached)
2. lake build +BridgelandStability.*:highlighted     (SubVerso JSON per module, one-time)
3. scripts/make_shadow.py                            (copy source, inject ANCHOR markers)
4. scripts/generate_unified_docs.py                  (generate Verso files from informalizations.json
                                                      using {docstring} + ```anchor``` + prose + badges)
5. cd unified-site && lake build site                (Verso reads pre-computed JSON, ~30s)
6. python3 scripts/style_site.py _out/               (CSS post-processing)
```

Steps 1-2 are the expensive part but only run when code changes. Steps 3-6 are fast.

## Components

### 1. Shadow copy with anchor injection (`scripts/make_shadow.py`)

- Copy `BridgelandStability/` source files to `shadow/BridgelandStability/`
- For each declaration in `informalizations.json`, inject `-- ANCHOR: DeclName` before and `-- ANCHOR_END: DeclName` after, using `sourceFile`/`startLine`/`endLine` from `extracted.json`
- Preserve `.lake/` between runs (only update changed `.lean` files)
- Copy `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`

### 2. Pre-build highlighted facets

```bash
cd shadow && lake build +BridgelandStability.Slicing.Defs:highlighted
# ... for each module
```

This produces `.lake/build/highlighted/BridgelandStability/Slicing/Defs.json` with full `Highlighted` data. Only needs rebuilding when source changes.

### 3. Unified doc generator (`scripts/generate_unified_docs.py`)

Extends `generate_docstring_docs.py` from bridgeland-informal. For each declaration, generates:

```lean
## DeclarationName

[prose from informalizations.json]                          ← mathematician-facing description

Proof: [proofExposition]                                    ← proof strategy (theorems)
Construction: [termExposition]                              ← construction (defs/structures)

{docstring Fully.Qualified.Name}                            ← signature with hover

:::keepEnv
```anchor (project := "shadow") (module := BridgelandStability.Module)
-- ANCHOR: DeclName
```                                                          ← full body with hover
:::
```

Paper alignment (if `@[informal]` tagged):
- Badge rendered as text: `**[Theorem 7.1]** comment text`

### 4. Comparator chapter

A separate chapter in the unified site showing:
- Comparator verification status (pass/fail)
- TFB declaration list
- Paper coverage table (which paper sections are formalized, which are missing)

Data sources: `comparator.json` results + `@[informal]` entries + audit data.

This chapter can use `{docstring}` only (no bodies needed for the coverage table).

### 5. Site structure

```
Root
├── Overview (intro, stats, comparator badge)
├── Paper Alignment (organized by paper section number)
│   ├── Definitions (2.1, 2.2, 2.3, 3.3, ...)
│   ├── Propositions & Lemmas
│   ├── Theorems (1.2, 7.1)
│   └── Coverage gaps
├── Chapters (by module group, mathematical order)
│   ├── PostnikovTower
│   ├── GrothendieckGroup
│   ├── ...
│   └── Deformation
└── Trusted Formalization Base
```

### 6. Lakefile for unified site

```toml
name = "BridgelandUnified"

[[require]]
name = "verso"
git = "https://github.com/leanprover/verso"
rev = "v4.29.0"

[[require]]
name = "BridgelandStability"
path = "../bridgeland-extract"

[[lean_lib]]
name = "UnifiedDocs"

[[lean_exe]]
name = "site"
root = "UnifiedMain"
```

### 7. CI workflow

```yaml
steps:
  - build BridgelandStability
  - build highlighted facets (cached between runs)
  - make shadow copy with anchors
  - generate unified Verso files
  - build Verso site
  - deploy to GitHub Pages
```

## Key files

```
bridgeland-extract/
  scripts/
    make_shadow.py              # NEW: shadow copy + anchor injection
    generate_unified_docs.py    # NEW: extends generate_docstring_docs.py
    style_site.py               # NEW: CSS post-processing (from style_informal.py)
  informalizations.json         # existing prose database
  extracted.json                # existing declaration metadata with source ranges

unified-site/                   # NEW: or extend bridgeland-informal/
  UnifiedDocs/
    Root.lean
    PaperAlignment.lean
    {Chapter}/*.lean
  UnifiedMain.lean
  lakefile.toml
```

## What gets retired

- `bridgeland-informal/` as a separate project — absorbed into unified site
- lean-exposition's shadow/comparator manual rendering — replaced by the unified site's comparator chapter

## Verification

1. `make_shadow.py` correctly injects anchors at declaration boundaries
2. `lake build +Module:highlighted` produces valid JSON in shadow
3. Generated Verso files build without errors (~30s)
4. Declarations render with hover info on both signature and body
5. Prose, proof exposition, and paper badges display correctly
6. Comparator chapter shows TFB status
7. CI workflow completes and deploys

## Open questions

- Does the `:highlighted` Lake facet exist for SubVerso in the current toolchain (v4.29.0)?
- How long does building highlighted facets take for 67 modules?
- Can ` ```anchor ` blocks coexist with `{docstring}` blocks for the same declaration in one page?
- Should the unified site live in `bridgeland-extract` or as a separate repo?
