# Audit: `Slicing.IntervalCat` and Interval Subcategory Infrastructure

## 1. Core Definitions

### `intervalProp` (the membership predicate)

File: `BridgelandStability/Slicing/Defs.lean`, line 200.

```lean
def Slicing.intervalProp (s : Slicing C) (a b : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E), ∀ i, a < F.φ i ∧ F.φ i < b
```

This is P((a,b)) from Bridgeland Definition 4.1: an object belongs to the interval
subcategory if it is zero, or it admits an HN filtration whose phases all lie in the
**open** interval (a, b).

### `IntervalCat` (the full subcategory)

File: `BridgelandStability/IntervalCategory/Basic.lean`, line 77.

```lean
abbrev Slicing.IntervalCat (s : Slicing C) (a b : ℝ) :=
  (s.intervalProp C a b).FullSubcategory
```

This is the full subcategory of C on objects satisfying `intervalProp`. It uses Mathlib's
`ObjectProperty.FullSubcategory`, so morphisms are just morphisms in C between qualifying
objects.

### Two-heart embeddings

File: `BridgelandStability/IntervalCategory/TwoHeartEmbedding.lean`, lines 120 and 140.

```lean
abbrev Slicing.IntervalCat.toLeftHeart (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤ ((s.phaseShift C a).toTStructure).heart.FullSubcategory

abbrev Slicing.IntervalCat.toRightHeart (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤ ((s.phaseShift C (b - 1)).toTStructureGE).heart.FullSubcategory
```

Both are fully faithful additive functors. The left heart P((a, a+1]) controls kernels
(via `toTStructure`); the right heart P([b-1, b)) controls cokernels (via
`toTStructureGE`). This asymmetry is why P((a,b)) is quasi-abelian but generally not
abelian.

## 2. API Catalog

### Files in `BridgelandStability/IntervalCategory/`

| File | Key declarations |
|------|-----------------|
| `Basic.lean` | `IntervalCat`, `IntervalCat.ι`, `intervalProp_of_isZero`, `intervalProp_containsZero`, `isZero_of_obj_isZero`, `intervalFiniteLength`, `intervalProp_of_semistable`, `intervalProp_mono`, `IntervalCat.inclusion`, `intervalProp_closedUnderIso`, `intervalProp_stableUnderRetracts`, `intervalProp_biprod`, `intervalProp_closedUnderFiniteProducts`, `intervalCat_hasFiniteProducts`, `intervalHom_eq_zero` |
| `TwoHeartEmbedding.lean` | `gtProp_of_intervalProp`, `leProp_of_intervalProp`, `intervalProp_implies_leftHeart`, `intervalProp_implies_rightHeart`, `toLeftHeart` (full + faithful), `toRightHeart` (full + faithful), `intervalProp_implies_rightWindow`, `phiPlus_le_of_semistable_triangle`, `phiMinus_ge_of_semistable_triangle`, `phiPlus_lt_of_triangle_with_leProp`, `phiMinus_gt_of_triangle_with_gtProp` |
| `QuasiAbelian.lean` | `intervalCat_hasKernel`, `intervalCat_hasKernels`, `intervalCat_hasCokernel`, `intervalCat_hasCokernels`, `toRightHeartCokernelIso`, `toLeftHeartKernelIso` |
| `Strictness.lean` | `mono_toRightHeart_of_strictMono`, `strictMono_of_mono_toRightHeart`, `toLeftHeartKernelIso` (construction), `epi_toLeftHeart_of_strictEpi`, `strictEpi_of_epi_toLeftHeart` |
| `FiniteLength.lean` | `toLeftHeart_additive`, `toRightHeart_additive`, `toLeftHeart_preservesKernel`, `toRightHeart_preservesCokernel`, `intervalCat_hasBinaryBiproducts`, `intervalCat_hasEqualizers`, `intervalCat_hasCoequalizers`, `intervalCat_hasFiniteCoproducts`, `intervalCat_hasPullbacks`, `intervalCat_hasPushouts`, `toLeftHeart_preservesFiniteLimits`, `toRightHeart_preservesFiniteColimits`, `finite_subobject_of_leftHeart`, `comp_strictEpi`, `comp_strictMono`, **`intervalCat_quasiAbelian`**, `IsLocallyFinite`, `strictMono_strictEpi_of_shortExact_toLeftRightHearts`, `strictMono_strictEpi_of_distTriang` |

### Closure properties of `intervalProp`

- Closed under isomorphisms (`intervalProp_closedUnderIso`)
- Stable under retracts (`intervalProp_stableUnderRetracts`)
- Closed under binary biproducts (`intervalProp_biprod`)
- Closed under finite products (`intervalProp_closedUnderFiniteProducts`)
- Extension-closed: if A, B in P((a,b)) and A -> E -> B -> A[1] is distinguished, then E in P((a,b)) (`intervalProp_of_triangle`, in `Slicing/ExtensionClosure.lean`)
- Monotone in interval: (a,b) subset (a',b') implies P((a,b)) subset P((a',b')) (`intervalProp_mono`)
- Contains all semistable objects of matching phase (`intervalProp_of_semistable`)
- Contains the zero object (`intervalProp_containsZero`)

### Quasi-abelian structure (requires `b - a <= 1`)

The quasi-abelian instance is at `BridgelandStability/IntervalCategory/FiniteLength.lean`,
line 210:

```lean
noncomputable instance Slicing.intervalCat_quasiAbelian (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] :
    QuasiAbelian (s.IntervalCat C a b)
```

This is the custom `QuasiAbelian` class from
`BridgelandStability/ForMathlib/CategoryTheory/QuasiAbelian/Basic.lean`, line 278:

```lean
class QuasiAbelian : Prop where
  pullback_strictEpi : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    IsStrictEpi g → IsStrictEpi (pullback.fst f g)
  pushout_strictMono : ∀ {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y),
    IsStrictMono f → IsStrictMono (pushout.inr f g)
```

Following Schneiders (1999). This class lives entirely in ForMathlib and has no Mathlib
counterpart yet.

### Strict morphisms

- `IsStrict f`: `coimageImageComparison f` is an isomorphism
- `IsStrictMono f`: mono + strict
- `IsStrictEpi f`: epi + strict
- `StrictSubobject`: subobjects represented by strict monomorphisms
- `IsStrictArtinianObject`, `IsStrictNoetherianObject`: ACC/DCC on strict subobjects

### Finite length / local finiteness

```lean
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  intervalFinite : ∃ η : ℝ, ∃ hη : 0 < η, ∃ hη' : η < 1 / 2, ∀ t : ℝ,
    ...
    ∀ (E : s.IntervalCat C a b),
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E
```

The deformation theorem extracts `ε₀ < 1/8` from `η < 1/2`, ensuring 8ε₀ < 1 so
all working intervals satisfy the width constraint.

## 3. Mathematical Generalization Analysis

### Why open intervals?

The definition `intervalProp` uses strict inequalities: `a < F.φ i ∧ F.φ i < b`. This
is mathematically essential for Bridgeland's framework:

1. **Hom-vanishing at endpoints.** The slicing axiom `hom_vanishing` requires `φ₂ < φ₁`
   (strict). If we allowed phases equal to `a` or `b`, the hom-vanishing theorem
   `intervalHom_eq_zero` (which requires `b₂ ≤ a₁`, hence phases of B strictly below
   phases of A) would fail at the boundary.

2. **Extension-closure.** The extension-closure theorem `intervalProp_of_triangle`
   recovers open-interval membership from `phiPlus < b` and `phiMinus > a` (both
   strict). Closed endpoints would create edge cases where the triangle argument does
   not yield the right containment.

3. **Paper fidelity.** Bridgeland Definition 4.1 uses P((a,b)) with open intervals
   throughout. The half-open intervals P((a, a+1]) and P([b-1, b)) appear only as
   **hearts of t-structures**, not as interval subcategories subject to the quasi-abelian
   theory.

### Could it be [a,b] or (a,b]?

**No, not without changing the mathematics.** The two-heart embedding relies on:
- Left heart = P((a, a+1]) (half-open), controlling kernels
- Right heart = P([b-1, b)) (half-open), controlling cokernels

These are honest abelian hearts of t-structures, and their half-openness is intrinsic to
the t-structure formalism (the heart is `le 0 ∩ ge 0`, which gives one strict and one
non-strict inequality in terms of phases).

The open interval P((a,b)) sits inside both hearts when `b - a ≤ 1`:
- (a, b) ⊆ (a, a+1] because b ≤ a+1
- (a, b) ⊆ [b-1, b) because a ≥ b-1

A closed interval [a,b] would not sit inside P((a, a+1]) because `a` is not strictly
greater than `a`. A half-open interval (a,b] would lose the right-heart containment.

### Where does `b - a ≤ 1` come from?

This constraint is **mathematically essential**, not an artifact of the formalization.

The shift axiom of a slicing says `P(φ)[1] = P(φ+1)`. The hom-vanishing axiom gives
`Hom(P(φ₁), P(φ₂)) = 0` for `φ₂ < φ₁`. Together, these mean that objects with phases
more than 1 apart can interact through the shift functor, potentially leaving the
interval subcategory.

Concretely, the two-heart embedding requires:
- `(a, b) ⊆ (a, a+1]` needs `b ≤ a+1`, i.e., `b - a ≤ 1`
- `(a, b) ⊆ [b-1, b)` needs `a ≥ b-1`, i.e., `b - a ≤ 1`

Both conditions reduce to the same constraint. Without it, kernels computed in the left
heart would not land back in P((a,b)), breaking the preabelian structure.

The paper uses this constraint implicitly: Bridgeland's Lemma 4.3 assumes "thin"
intervals, meaning width at most 1. The deformation theorem (Section 7) works with
intervals of width `8ε₀ < 1`, well within this bound.

## 4. Mathlib Comparison

### What exists in Mathlib

- **`TStructure`** (`Mathlib.CategoryTheory.Triangulated.TStructure.Basic`): the basic
  definition with `le`/`ge` predicates indexed by integers.
- **`TStructure.heart`** (`Mathlib.CategoryTheory.Triangulated.TStructure.Heart`):
  defined as `t.le 0 ⊓ t.ge 0`, an `ObjectProperty C`. Comes with a `Heart` typeclass
  for identifying the heart with a given category.
- **`TStructure.Heart`** typeclass: packages a fully faithful additive functor from an
  abstract heart category H into C.
- **`ObjectProperty.FullSubcategory`**: used throughout for subcategories defined by
  predicates.
- **`ObjectProperty.tStructure`** (`Mathlib.CategoryTheory.Triangulated.TStructure.Induced`):
  induced t-structure on a full subcategory satisfying `ObjectProperty.IsTriangulated`.

### What does NOT exist in Mathlib

- **Slicings.** No definition of slicing (real-indexed refinement of t-structures).
- **Quasi-abelian categories.** No `QuasiAbelian` class. The entire theory of strict
  morphisms, strict subobjects, strict Artinian/Noetherian objects is in ForMathlib.
- **Interval subcategories.** No concept of P((a,b)) or any real-parameterized
  subcategory construction.
- **Stability conditions.** No Bridgeland stability conditions.
- **Heart abelianity.** The TODO in Heart.lean says "Show that the heart is an abelian
  category" -- this project provides `heartFullSubcategoryAbelian` in
  `BridgelandStability/TStructure/HeartAbelian.lean`.

### Upstream potential

1. **`QuasiAbelian` class + strict morphism theory**: completely independent of
   Bridgeland. Candidate for direct Mathlib PR. Follows Schneiders (1999).

2. **Heart abelianity**: the project's `heartFullSubcategoryAbelian` proves what
   Mathlib's Heart.lean has as a TODO. High-value upstream target.

3. **`IntervalCat` itself**: deeply coupled to the Slicing definition, which has no
   Mathlib counterpart. Not upstreamable until Mathlib has slicings.

4. **Strict Artinian/Noetherian objects**: defined in ForMathlib, could be upstreamed
   alongside the quasi-abelian class.

## 5. Downstream Usage

The `IntervalCat` infrastructure is heavily used in the deformation theorem (Section 7):
720 occurrences of `IntervalCat` across 17 files in `BridgelandStability/Deformation/`.

Key consumers:
- `Setup.lean`: extracts ε₀ from local finiteness, constructs working interval categories
- `IntervalSelection.lean`: 147 occurrences -- subobject lifting, strict subobject
  lattice operations, finite-length induction within thin intervals
- `StrictShortExactSequence.lean`: 112 occurrences -- strict SES construction from
  distinguished triangles in P((a,b))
- `MaximalDestabilizingQuotientKernel.lean`: 68 occurrences -- MDQ kernel containment
- `Pullback.lean`: 64 occurrences -- pullback of strict epimorphisms
- `PhiPlusHN.lean`, `PhiPlusMDQ.lean`: HN existence and phase refinement within intervals

The entire deformation argument works inside `P((t - 4ε₀, t + 4ε₀))` for various
centers `t`, with width `8ε₀ < 1` ensuring the quasi-abelian structure is available.

## 6. Summary of Findings

The `IntervalCat` infrastructure is mathematically sound and faithful to Bridgeland's
paper:

- **Open intervals are essential**: boundary behavior of hom-vanishing and the two-heart
  embedding require strict inequalities.
- **`b - a ≤ 1` is a mathematical requirement**: it ensures both heart embeddings exist,
  giving the preabelian (and hence quasi-abelian) structure.
- **The API is comprehensive**: closure properties, two-heart embeddings, kernel/cokernel
  computation, strictness transfer, quasi-abelian instance, finite-length conditions.
- **The quasi-abelian class is Mathlib-ready**: it lives in ForMathlib with no dependency
  on slicings or Bridgeland-specific material.
- **No generalization is needed or appropriate**: the open interval and width constraint
  are both dictated by the mathematics, not by formalization convenience.
