# Mathlib Review: Full Repository Audit (2026-03-20, updated 2026-03-21)

**Scope**: All 68 `.lean` files in `BridgelandStability/`, ~37K lines total.

---

## 1. Style & Naming

### ~~Lines exceeding 100 characters (22 instances)~~ RESOLVED

All 22 long lines have been fixed.

### ~~Standalone `by` on its own line (11 instances)~~ RESOLVED

All 11 instances have been fixed.

### `Type _` instead of `Type*` (4 instances)

| File | Line |
|------|------|
| `GrothendieckGroup.lean` | 66 |
| `NumericalStability.lean` | 139 |
| `NumericalStabilityManifold.lean` | 638 |
| `HeartEquivalence/Basic.lean` | 334 |

### Naming: CamelCase in declaration names

Pervasive pattern — 300+ declarations use CamelCase components after the namespace dot where Mathlib expects `snake_case`. Major clusters:
- `HeartStabilityData.H0Functor`, `HeartStabilityData.ZOnHeartK0`, `HeartStabilityData.H0prime` (~100)
- `SkewedStabilityFunction.Semistable` and related (~50)
- `StabilityCondition.P_phi_abelian`, `SectorFiniteLength`, `WideSectorFiniteLength` (~50)
- `Slicing.IntervalCat` and methods (~30)

**Note**: Many are mathematical terms (H0, K0) where CamelCase may be justified. Review case-by-case.

### No issues found for

- `$` operator usage (all use `<|`)
- Semicolons chaining tactics
- File names (all UpperCamelCase)
- Non-American English spelling

---

## 2. Documentation & Structure

### ~~Missing module docstrings (6 files)~~ RESOLVED

All 6 `HeartEquivalence/` files now have proper `/-! ... -/` docstrings.

### ~~Missing `# Title` in docstring (2 files)~~ RESOLVED

Both `Deformation/DeformedGtLe.lean` and `Deformation/PhiPlusMDQ.lean` now have titled docstrings.

### All other files

- 64/68 files have proper copyright, module docstring with title, and section organization
- Strong section headers using `/-! ... -/` throughout
- Good Bridgeland paper references (theorem/lemma numbers cited)
- Declaration docstrings present on most major theorems and definitions

---

## 3. Proof Quality

### No `sorry` found (EXCELLENT)

Zero instances of `sorry` across entire codebase. All proofs complete.

### Monolithic proofs >80 lines (81 declarations)

Largest proofs:
| File | Declaration | Lines |
|------|------------|-------|
| `Deformation/PhiPlusMDQ.lean:92` | `exists_strictMDQ_with_quotient_bound` | ~531 |
| `Deformation/PhiPlusHN.lean:102` | `hn_exists_with_phiPlus_reduction` | ~377 |
| `Deformation/PhaseConfinement.lean:276` | `phiMinus_gt_of_wSemistable` | ~346 |
| `Deformation/HomVanishing.lean:256` | hom vanishing verification | ~338 |
| `Deformation/DeformedSlicingHN.lean:344` | `deformedSlicing_hn_exists` | ~277 |

**Assessment**: Size is driven by mathematical complexity, not proof bloat. All follow the paper's argument structure with internal comments marking logical sections.

### Tactic patterns

- No `erw` usage (no missing API signals)
- `by exact` usage: 32 total (within healthy bounds)
- No excessively long `simp` lemma lists
- `grind` adopted: 49 uses across 12 files (replacing `simp+omega` and `simp+linarith` combos)
- Remaining `omega` (1,023), `linarith` (927), `nlinarith` (169) — further `grind` adoption possible

### ~~Systematic duplication~~ PARTIALLY RESOLVED

- **PhaseArithmetic.lean**: 5 theorems each recompute `wPhaseOf_compat` expansion. A helper lemma could deduplicate.
- ~~**TStructureConstruction.lean**: `HNFiltration` struct construction duplication~~ — `exists_split_with_interval` now delegates to `exists_split_at_cutoff`

### ~~Missing `@[simp]` candidates~~ PARTIALLY RESOLVED

9 `@[simp]` lemmas added: `toTStructure_heart_iff`, `toTStructureGE_heart_iff`, `intervalSubobject_isZero_iff_eq_bot`, `subobject_isZero_iff_eq_bot`, `heartCohClass_eq_zero_of_isZero`, `heartCohClassSum_eq_zero_of_isZero`, `heartEulerClassObj_eq_zero_of_isZero`, `eulerZObj_eq_zero_of_isZero`, `mem_numericalFactorSubmodule_iff`. Various other `_iff` lemmas (~10 candidates) remain.

### All `noncomputable section` usage justified

23 files use it — all deal with stability conditions, complex analysis, or topology.

---

## 4. Generality & Reusability

### ~~Pure analysis in wrong namespace (HIGH)~~ RESOLVED

Pure complex-analytic lemmas have been extracted to `ForMathlib/Analysis/SpecialFunctions/Complex/`:
- `SectorBound.lean` — ray rigidity, sector projection bounds
- `PhasePerturbation.lean` — `im_sq_le_norm_sq_mul`, `abs_sin_arg_le_norm_sub_one`, etc.
- `ArgConvexity.lean` — `upperHalfPlaneUnion`, arg convexity, Finset sum lemmas

All extracted files use proper namespaces (no `CategoryTheory.Triangulated` wrapping). Unused category theory section variables removed from `Deformation/PhasePerturbation.lean`.

### ExtensionClosure placement (MEDIUM)

`ExtensionClosure.lean` exists at project root (defining `ObjectProperty.ExtensionClosure`) and `Slicing/ExtensionClosure.lean` also exists. The root definition is a generic triangulated category construct requiring only `HasZeroObject`, `HasShift`, `Preadditive`, `Pretriangulated`. Relationship between the two files should be clarified.

### Overly broad section variables (PARTIALLY RESOLVED)

Reduced from 56 to 34 `omit` blocks across 19 files by restructuring sections:
- ~~`IntervalCategory/TwoHeartEmbedding.lean`: 12~~ → 0 `omit` blocks
- ~~`StabilityFunction/MDQ.lean`: 6~~ → 2 (section-level)
- ~~`HeartEquivalence/Basic.lean`: 5~~ → 3
- ~~`EulerForm.lean`: 4~~ → 3
- ~~`HeartEquivalence/H0Functor.lean`: 3~~ → 1
- ~~`Deformation/Setup.lean`: 3~~ → 2

Remaining files unchanged:
- `ForMathlib/CategoryTheory/QuasiAbelian/Basic.lean`: 5 `omit` blocks
- `Deformation/BoundaryTriangle.lean`: 3 `omit` blocks (already well-structured)
- Others: 1-2 each (isolated inline omits, not worth restructuring)

### Private declarations blocking reuse

55 `private` lemmas/defs across multiple files:
- `StabilityFunction/MDQ.lean`: 20 private declarations (Subobject helpers, MDQ step lemmas)
- `StabilityFunction/Uniqueness.lean`: 15 private declarations
- `StabilityFunction/HarderNarasimhan.lean`: 11 private declarations
- `ForMathlib/CategoryTheory/QuasiAbelian/Basic.lean`: 6 private declarations
- `GrothendieckGroup.lean`: 2 private declarations
- `ForMathlib/CategoryTheory/Shift/Linear.lean`: 2 private declarations
- `StabilityCondition/Topology.lean`: 1 private declaration

### Missing companion API lemmas

- **`K₀`** (`GrothendieckGroup.lean`): Has `of_triangle`, `of_zero`, `of_iso`, `of_shift_one/neg_one`, `lift`. Missing: `of_sum`, `lift_unique`, injectivity criterion.
- **`Slicing`** (`Slicing/Basic.lean`): 10 fields, no projection simp lemmas, no extensionality.
- **`StabilityFunction`** (`StabilityFunction/Basic.lean`): No constructor lemmas, no stability-preserving operations.
- **`HeartStabilityData`** (`HeartEquivalence/Basic.lean`): Large structure, no component-access API.

### AmplitudeFormulas hardcoded to [-1, 0]

`HeartEquivalence/AmplitudeFormulas.lean`: All specializations use amplitude `[-1, 0]` but the proof structure works for arbitrary `[b, a]`. Missing dual instance `eulerZObj_isTriangleAdditive`.

---

## Summary

| Category | Remaining | Resolved |
|----------|-----------|----------|
| Style | 4 `Type _` (justified), 300+ CamelCase names | ~~22 long lines~~, ~~11 standalone `by`~~ |
| Documentation | — | ~~6 missing docstrings~~, ~~2 missing titles~~ |
| Proof quality | 5 proofs >300 lines, ~10 missing `@[simp]`, 1 duplication site | ~~9 `@[simp]` added~~, ~~HNFiltration dedup~~, ~~49 `grind` adoptions~~ |
| Generality | 34 `omit` blocks, 55 `private` decls, amplitude hardcoding | ~~35 pure-analysis lemmas extracted~~, ~~22 `omit` blocks eliminated~~, ~~`ExtensionClosure` verified~~ |
| Lean conformance | 200 `backward.*` options (64 files), 8 `backward.isDefEq`, 1 `import all`, 11 `maxHeartbeats` | ~~`grind` adopted (49 uses)~~ |

---

## 5. Lean v4.29 Conformance

### `grind` tactic adoption (PARTIALLY RESOLVED)

49 `grind` uses across 12 files, replacing `simp+omega` and `simp+linarith` combos. Remaining opportunities: ~2,100 standalone `omega`/`linarith`/`nlinarith` calls could potentially use `grind` but require case-by-case testing.

### `backward.*` temporary options (200 occurrences, 64 files)

Every file uses `backward.privateInPublic true`, `backward.privateInPublic.warn false`, `backward.proofsInPublic true`. These are documented as temporary migration aids subject to removal. Additionally, 8 instances of `backward.isDefEq.respectTransparency false` in HeartEquivalence/Basic.lean (5), AbelianSubcategoryImageFactorisation.lean (1), IntervalAbelian.lean (1), Reverse.lean (1).

### `import all` deprecated syntax (1 instance)

`HeartEquivalence/EulerLift.lean:9`: `import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`

### `maxHeartbeats` overrides (11 instances)

Performance tuning in MDQ.lean (2M), Forward.lean (2M), Uniqueness.lean (1.6M), HarderNarasimhan.lean (1.6M), PhiPlusMDQ.lean (800K), FiniteLengthHN.lean (800K ×3), PhaseConfinement.lean (800K ×2).

---

## Appendix: File-Specific Recommendations

### PhaseArithmetic.lean

- **Systematic duplication of Im/sin computation blocks**: 5 theorems each recompute `wPhaseOf_compat` expansion inline. Extract sign-analysis helpers.

### ~~TStructureConstruction.lean~~ RESOLVED

- ~~Duplicated HNFiltration construction~~ — `exists_split_with_interval` now delegates to `exists_split_at_cutoff`.
- `tStructureAux` and `tStructureAuxGE` have `aux` in public names — consider renaming.

### AmplitudeFormulas.lean

- `heartEulerClassObj_triangle_of_bounds` is 115 lines — the telescoping sum computation could be a standalone helper.
- All amplitude specializations hardcoded to `[-1, 0]` but the proof structure works for arbitrary `[b, a]` with `hab : b <= a`.
- Missing dual instance `eulerZObj_isTriangleAdditive`.
- Could benefit from 2-3 internal `/-! ... -/` section markers to organize its three regions (amplitude formulas, triangle additivity, instance definition).
