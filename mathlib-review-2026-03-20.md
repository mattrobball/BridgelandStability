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
- `linarith` frequency appropriate for phase-bound arithmetic (29 uses in PhaseConfinement alone)

### Systematic duplication

- **PhaseArithmetic.lean**: 5 theorems (`wPhaseOf_seesaw`, `_strict`, `_dual`, `_lt_of_add_le_lt`, `_lt_of_add_le_gt`) each recompute `wPhaseOf_compat` expansion. A helper lemma could deduplicate.
- **TStructureConstruction.lean**: Manual `HNFiltration` struct construction duplicated between `exists_split_with_interval` and `exists_split_at_cutoff`

### ~~Missing `@[simp]` candidates~~ RESOLVED

`toTStructure_heart_iff`, `toTStructureGE_heart_iff`, and `intervalSubobject_isZero_iff_eq_bot` now have `@[simp]`. Various other `_iff` lemmas across the codebase (~15 candidates) remain unannotated.

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

### Overly broad section variables

Many files declare `[IsTriangulated C]` at section level then use `omit` repeatedly (56 total `omit` blocks across 20 files):
- `IntervalCategory/TwoHeartEmbedding.lean`: 12 `omit` blocks
- `StabilityFunction/MDQ.lean`: 6 `omit` blocks
- `ForMathlib/CategoryTheory/QuasiAbelian/Basic.lean`: 5 `omit` blocks
- `HeartEquivalence/Basic.lean`: 5 `omit` blocks
- `EulerForm.lean`: 4 `omit` blocks
- `HeartEquivalence/H0Functor.lean`: 3 `omit` blocks
- `Deformation/BoundaryTriangle.lean`: 3 `omit` blocks
- `Deformation/Setup.lean`: 3 `omit` blocks

Suggests section variables should be restructured.

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
| Style | 4 `Type _`, 300+ CamelCase names | ~~22 long lines~~, ~~11 standalone `by`~~ |
| Documentation | — | ~~6 missing docstrings~~, ~~2 missing titles~~ |
| Proof quality | 5 proofs >300 lines, ~15 missing `@[simp]`, 2 duplication sites | ~~3 `@[simp]` candidates~~ |
| Generality | 56 `omit` blocks, 55 `private` decls, `ExtensionClosure` placement, amplitude hardcoding | ~~35 pure-analysis lemmas extracted~~ |

---

## Appendix: File-Specific Recommendations

### PhaseArithmetic.lean

- **Systematic duplication of Im/sin computation blocks**: `wPhaseOf_seesaw`, `wPhaseOf_seesaw_strict`, `wPhaseOf_seesaw_dual`, `wPhaseOf_lt_of_add_le_lt`, `wPhaseOf_lt_of_add_le_gt` each recompute the `wPhaseOf_compat` expansion inline. Extract a helper like `wPhaseOf_expand_eq` stating `w = ||w|| * exp(i*pi * wPhaseOf(w, alpha))` and reference it in all five proofs.
- `im_pos_of_phase_above`, `im_neg_of_phase_below` are pure polar-form facts about `m * exp(i*pi*phi) * exp(-i*pi*psi)`. The core R-computation could be extracted as a standalone lemma.

### TStructureConstruction.lean

- **Duplicated `HNFiltration` struct construction** between `exists_split_with_interval` and `exists_split_at_cutoff`. Both manually build `GXorig : HNFiltration C s.P X` by copying all fields and adjusting `phi := fun j => GX.phi j + t`. Extract `HNFiltration.phaseShiftCoordinates` helper.
- `tStructureAux` and `tStructureAuxGE` have `aux` in public names — consider renaming to `tStructure_exists_triangle` or similar.

### AmplitudeFormulas.lean

- `heartEulerClassObj_triangle_of_bounds` is 115 lines — the telescoping sum computation could be a standalone helper.
- All amplitude specializations hardcoded to `[-1, 0]` but the proof structure works for arbitrary `[b, a]` with `hab : b <= a`.
- Missing dual instance `eulerZObj_isTriangleAdditive`.
- Could benefit from 2-3 internal `/-! ... -/` section markers to organize its three regions (amplitude formulas, triangle additivity, instance definition).
