# Mathlib Review: Full Repository Audit (2026-03-20)

**Scope**: All 64 `.lean` files in `BridgelandStability/`, ~37K lines total.

---

## 1. Style & Naming

### Lines exceeding 100 characters (22 instances)

| File | Line(s) |
|------|---------|
| `StabilityCondition/LocalHomeomorphism.lean` | 341 |
| `StabilityCondition/ConnectedComponent.lean` | 221, 223 |
| `HeartEquivalence/Basic.lean` | 461, 568, 621, 649 |
| `HeartEquivalence/H0Homological.lean` | 788 |
| `Deformation/IntervalSelection.lean` | 951 |
| `Deformation/MaximalDestabilizingQuotient.lean` | 125, 521 |
| `Deformation/StrictShortExactSequence.lean` | 39 |
| `Deformation/MaximalDestabilizingQuotientKernel.lean` | 184, 541 |
| `EulerForm.lean` | 541, 549 |
| `IntervalCategory/Basic.lean` | 99 |
| `IntervalCategory/FiniteLength.lean` | 601 |
| `StabilityFunction/MDQ.lean` | 291, 358, 477, 766 |

### Standalone `by` on its own line (11 instances)

| File | Line(s) |
|------|---------|
| `Strict.lean` | 160, 164 |
| `Deformation/BoundaryTriangle.lean` | 71 |
| `HeartEquivalence/H0Homological.lean` | 104, 586, 604 |
| `HeartEquivalence/AmplitudeFormulas.lean` | 76, 103 |
| `HeartEquivalence/Reverse.lean` | 685 |
| `Deformation/PhaseConfinement.lean` | 795, 887 |

### `Type _` instead of `Type*` (4 instances)

| File | Line |
|------|------|
| `NumericalStability.lean` | 139 |
| `GrothendieckGroup.lean` | 66 |
| `NumericalStabilityManifold.lean` | 616 |
| `HeartEquivalence/Basic.lean` | 333 |

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

### Missing module docstrings (6 files)

All in `HeartEquivalence/`:
- `EulerLift.lean`
- `Forward.lean`
- `H0Functor.lean`
- `H0Homological.lean`
- `PureAdditivity.lean`
- `Reverse.lean`

### Missing `# Title` in docstring (2 files)

- `Deformation/DeformedGtLe.lean`
- `Deformation/PhiPlusMDQ.lean`

### All other files

- 56/64 files have proper copyright, module docstring with title, and section organization
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

### Missing `@[simp]` candidates

- `Slicing/TStructureConstruction.lean`: `toTStructure_heart_iff`, `toTStructureGE_heart_iff`
- `Deformation/IntervalSelection.lean`: `intervalSubobject_isZero_iff_eq_bot`
- Various `_iff` lemmas across the codebase (~15 candidates)

### All `noncomputable section` usage justified

23 files use it — all deal with stability conditions, complex analysis, or topology.

---

## 4. Generality & Reusability

### Pure analysis in wrong namespace (HIGH)

Pure complex-analytic lemmas in `CategoryTheory.Triangulated`:
- **`StabilityFunction/Basic.lean`** (lines 60-259): 27 lemmas about `upperHalfPlaneUnion`, `arg` convexity. Zero category theory dependency.
- **`Deformation/PhasePerturbation.lean`**: 8 lemmas (`im_sq_le_norm_sq_mul`, `abs_sin_arg_le_norm_sub_one`, `sum_mem_upperHalfPlane`, etc.). All pure `Complex`/`Real` analysis.
- **Unused section variables**: Both files declare `(C : Type u) [Category.{v} C] ...` that no theorem in the file uses.

### Misplaced generic definition (MEDIUM)

`Deformation/ExtensionClosure.lean` defines `ObjectProperty.ExtensionClosure` — a generic triangulated category construct requiring only `HasZeroObject`, `HasShift`, `Preadditive`, `Pretriangulated`. Not deformation-specific. Should be at top level or in `Slicing/`.

### Overly broad section variables

Many files declare `[IsTriangulated C]` at section level then use `omit [IsTriangulated C]` repeatedly:
- `IntervalCategory/TwoHeartEmbedding.lean`: 9 `omit` blocks
- `HeartEquivalence/H0Functor.lean`: 3 `omit` blocks
- `Deformation/BoundaryTriangle.lean`: 3 `omit` blocks

Suggests section variables should be restructured.

### Private declarations blocking reuse (4 files)

- `StabilityFunction/Basic.lean`: `private lemma cross_*` (arg convexity helpers)
- `EulerForm.lean`: `private lemma finsum_*` (alternating sum identity)
- `Slicing/Basic.lean`: `private lemma chain_hom_eq_zero_of_gt`
- `Slicing/Phase.lean`: Some helper lemmas

### Missing companion API lemmas

- **`K₀`** (`GrothendieckGroup.lean`): Has `of_triangle`, `of_zero`, `of_iso`, `of_shift_one/neg_one`, `lift`. Missing: `of_sum`, `lift_unique`, injectivity criterion.
- **`Slicing`** (`Slicing/Basic.lean`): 10 fields, no projection simp lemmas, no extensionality.
- **`StabilityFunction`** (`StabilityFunction/Basic.lean`): No constructor lemmas, no stability-preserving operations.
- **`HeartStabilityData`** (`HeartEquivalence/Basic.lean`): Large structure, no component-access API.

### AmplitudeFormulas hardcoded to [-1, 0]

`HeartEquivalence/AmplitudeFormulas.lean`: All specializations use amplitude `[-1, 0]` but the proof structure works for arbitrary `[b, a]`. Missing dual instance `eulerZObj_isTriangleAdditive`.

---

## Summary

| Category | Critical | Medium | Low |
|----------|----------|--------|-----|
| Style (line length, `by` placement, `Type _`) | 22 lines >100 chars | 11 standalone `by`, 4 `Type _` | — |
| Naming (CamelCase) | 300+ CamelCase names | — | — |
| Documentation | — | 6 missing module docstrings | 2 missing titles |
| Proof quality | 0 sorries | 5 proofs >300 lines | 15 missing `@[simp]` |
| Generality | 35 pure-analysis lemmas in wrong namespace | `ExtensionClosure` misplaced, ~15 `omit` blocks | 4 files with `private` |

---

## Appendix: File-Specific Recommendations (from targeted review)

These are more granular findings from a focused review of the 5 most recently changed files.

### PhaseArithmetic.lean

- **Systematic duplication of Im/sin computation blocks**: `wPhaseOf_seesaw`, `wPhaseOf_seesaw_strict`, `wPhaseOf_seesaw_dual`, `wPhaseOf_lt_of_add_le_lt`, `wPhaseOf_lt_of_add_le_gt` each recompute the `wPhaseOf_compat` expansion inline (lines ~360-580). Extract a helper like `wPhaseOf_expand_eq` stating `w = ||w|| * exp(i*pi * wPhaseOf(w, alpha))` and reference it in all five proofs.
- `im_pos_of_phase_above`, `im_neg_of_phase_below` are pure polar-form facts about `m * exp(i*pi*phi) * exp(-i*pi*psi)`. The core R-computation could be extracted as a standalone lemma.
- Section headers use `###` instead of `##` inside `/-! ... -/` (4 instances at lines ~31, 145, 258, 347).

### TStructureConstruction.lean

- **Duplicated `HNFiltration` struct construction** between `exists_split_with_interval` (lines 483-495) and `exists_split_at_cutoff` (lines 540-552). Both manually build `GXorig : HNFiltration C s.P X` by copying all fields and adjusting `phi := fun j => GX.phi j + t`. Extract `HNFiltration.phaseShiftCoordinates` helper.
- `tStructureAux` and `tStructureAuxGE` have `aux` in public names — consider renaming to `tStructure_exists_triangle` or similar.
- Missing `@[simp]` on `toTStructure_heart_iff` and `toTStructureGE_heart_iff` (lines 427-438).

### AmplitudeFormulas.lean

- `by` on its own line at lines 76 and 103 (should be at end of preceding line).
- `heartEulerClassObj_triangle_of_bounds` is 115 lines (line 215) — the telescoping sum computation could be a standalone helper.
- All amplitude specializations hardcoded to `[-1, 0]` but the proof structure works for arbitrary `[b, a]` with `hab : b <= a`.
- Missing dual instance `eulerZObj_isTriangleAdditive`.
- Could benefit from 2-3 internal `/-! ... -/` section markers to organize its three regions (amplitude formulas, triangle additivity, instance definition).

### PhasePerturbation.lean

- All 8 theorems are pure complex analysis with zero category theory dependency, but live in `CategoryTheory.Triangulated` namespace with unused section variables `(C : Type u) [Category.{v} C] ...`.
- Missing companion lemmas: `im_sq_le_norm_sq_mul` stated in one direction only; an equality characterization could be useful.

### FirstStrictSES.lean

- Well-structured, no major issues.
- The well-founded induction in `exists_first_strictShortExact_of_not_semistable_of_strictArtinian` (lines 166-258, 93 lines) faithfully follows the paper's descent argument — monolithicity is justified.
