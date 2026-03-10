/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.StabilityCondition
import Mathlib.CategoryTheory.Triangulated.StabilityFunction
import Mathlib.CategoryTheory.Triangulated.IntervalCategory
import Mathlib.CategoryTheory.Triangulated.TStructure.HeartAbelian

/-!
# Heart Equivalence and Blueprint Scaffolding

This file captures the definitions and theorem statements from the Bridgeland
stability conditions blueprint (§§3–5) that are not yet present in the branch.
All nontrivial proofs are left as `sorry` to create a complete scaffolding.

## Contents

### §3 — t-structures and slicings

* `Slicing.toTStructure_bounded`: the t-structure from a slicing is bounded
  (Lemma 3.2 / Node 3.2a).
* `Slicing.toTStructure_heart_iff`: the heart of the slicing-induced t-structure
  is exactly the half-open interval `P((0, 1])` (Node 3.5b).

### §5 — Stability conditions

* `StabilityCondition.P_phi_abelian`: each phase subcategory `P(φ)` is abelian
  (Lemma 5.2).
* `StabilityCondition.stabilityFunctionOnPhase`: the central charge restricted
  to `P(φ)` gives a stability function on that abelian category.
* `HeartStabilityData`: a bounded t-structure with an HN stability function on
  its heart (one side of Proposition 5.3).
* `StabilityCondition.toHeartStabilityData`: extract heart data (Prop 5.3a).
* `HeartStabilityData.toStabilityCondition`: construct σ from heart data (5.3b).
* `StabilityCondition.roundtrip`, `HeartStabilityData.roundtrip`:
  inverse lemmas (Proposition 5.3c).

### §7 — Deformation infrastructure

* `TStructure.heart_shortExact_triangle`: SES in the heart lifts to a
  distinguished triangle (bridge between abelian and triangulated).

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals 2007
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ## §3: t-structures from slicings

`Slicing.toTStructure_bounded` and `Slicing.toTStructure_heart_iff` are now proved
in `Slicing.lean` (near the `toTStructure` definition) to avoid import cycles.
-/

/-! ## §5: Stability conditions — Lemma 5.2 and Proposition 5.3 -/

section Lemma52

variable [IsTriangulated C]

/-- **Lemma 5.2 / P(φ) is abelian.**
For each phase `φ`, the full subcategory `P(φ)` of `σ`-semistable objects of
phase `φ` (plus the zero object) is an abelian category.

The proof embeds `P(φ)` fully faithfully into the abelian heart `P((φ-1, φ])`,
then shows that for any morphism `f` in `P(φ)`, its kernel and cokernel in the
heart still lie in `P(φ)`. This uses Lemma 3.4 (triangle phase bounds) applied
to the short exact sequences `0 → ker f → A → im f → 0` and
`0 → im f → B → coker f → 0`. Since all terms have phases confined to `{φ}`,
the phase bounds force the kernel and cokernel into `P(φ)`.

The abelian structure on `P(φ)` is then inherited from the heart via the
closure under kernels and cokernels. -/
def StabilityCondition.P_phi_abelian
    (σ : StabilityCondition C) (φ : ℝ) :
    Abelian (σ.slicing.P φ).FullSubcategory := by
  sorry

/-- **Stability function restricted to P(φ).**
The central charge `Z` of a stability condition, restricted to `σ`-semistable
objects of phase `φ`, defines a stability function on the abelian category
`P(φ)`.

The `Zobj` field sends `E : P(φ)` to `σ.Z (K₀.of C (ι E))`, where `ι` is
the inclusion `P(φ) ↪ C`. Additivity follows from `K₀.of_shortExact_P_phi`;
the upper half plane condition follows from the compatibility axiom of `σ`. -/
def StabilityCondition.stabilityFunctionOnPhase
    (σ : StabilityCondition C) (φ : ℝ) :
    @StabilityFunction (σ.slicing.P φ).FullSubcategory _
      (σ.P_phi_abelian C φ) := by
  letI : Abelian (σ.slicing.P φ).FullSubcategory := σ.P_phi_abelian C φ
  exact {
    Zobj := fun E => σ.Z (K₀.of C ((σ.slicing.P φ).ι.obj E))
    map_zero' := fun X hX => by sorry
    additive := fun S hS => by sorry
    upper := fun E hE => by sorry }

/-- **HasHN for the restricted stability function on P(φ).**
The stability function on `P(φ)` has the Harder-Narasimhan property, since
`P(φ)` has finite length (from local finiteness of `σ`) and
`hasHN_of_finiteLength` applies. -/
theorem StabilityCondition.stabilityFunctionOnPhase_hasHN
    (σ : StabilityCondition C) (φ : ℝ) :
    @StabilityFunction.HasHNProperty (σ.slicing.P φ).FullSubcategory _
      (σ.P_phi_abelian C φ) (σ.stabilityFunctionOnPhase C φ) := by
  sorry

end Lemma52

section Proposition53

variable [IsTriangulated C]

/-- **Heart stability data (Proposition 5.3).**
This structure bundles a bounded t-structure with a stability function on its
heart that has the Harder-Narasimhan property. It represents one side of the
equivalence in Bridgeland's Proposition 5.3.

The heart `t.heart.FullSubcategory` is abelian by
`heartFullSubcategoryAbelian`. -/
structure HeartStabilityData where
  /-- The t-structure on `C`. -/
  t : TStructure C
  /-- The t-structure is bounded. -/
  bounded : t.IsBounded
  /-- The abelian structure on the heart, default from `heartFullSubcategoryAbelian`. -/
  hAbelian : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  /-- The stability function on the heart. -/
  Z : @StabilityFunction t.heart.FullSubcategory _ hAbelian
  /-- The stability function has the HN property. -/
  hasHN : @StabilityFunction.HasHNProperty t.heart.FullSubcategory _ hAbelian Z

/-- **Proposition 5.3a / forward direction.**
Every stability condition `σ` determines heart stability data:
1. The t-structure is `σ.slicing.toTStructure`.
2. Boundedness follows from the HN filtration axiom.
3. The stability function on the heart `P((0, 1])` is the restriction of `Z`.
4. The HN property follows from local finiteness + `hasHN_of_finiteLength`.

The key identification is that semistable objects of phase `φ ∈ (0, 1]` in the
heart are exactly the objects of `P(φ)`, and the slicing's HN filtration of a
heart object is exactly an HN filtration in the sense of
`StabilityFunction`. -/
def StabilityCondition.toHeartStabilityData
    (σ : StabilityCondition C) : HeartStabilityData C where
  t := σ.slicing.toTStructure
  bounded := σ.slicing.toTStructure_bounded C
  Z := by sorry
  hasHN := by sorry

/-- **Proposition 5.3b / reverse direction.**
Heart stability data determines a stability condition:
1. Define `P(φ)` for `φ ∈ (0, 1]` as the semistable objects of phase `φ` in
   the heart's stability function.
2. Extend by shifts: `P(φ + n) := P(φ)[n]` for `n ∈ ℤ`.
3. The central charge `Z : K₀ C →+ ℂ` is constructed by lifting the heart's
   `Zobj` through boundedness (every K₀ class decomposes into heart classes).
4. Hom-vanishing uses heart orthogonality (shifts of heart objects in different
   degrees have no morphisms) and phase monotonicity for semistable objects.
5. HN existence uses the bounded t-structure decomposition + the heart's HN
   property on each cohomology piece.
6. Compatibility with `Z` is direct from the construction.
7. Local finiteness follows from the HN property + finite length. -/
def HeartStabilityData.toStabilityCondition
    (h : HeartStabilityData C) : StabilityCondition C := by
  sorry

/-- **Proposition 5.3c / left inverse.**
Starting from a stability condition `σ`, extracting heart data, and
reconstructing a stability condition yields back `σ`. -/
theorem StabilityCondition.roundtrip
    (σ : StabilityCondition C) :
    (σ.toHeartStabilityData C).toStabilityCondition C = σ := by
  sorry

/-- **Proposition 5.3c / right inverse.**
Starting from heart stability data, constructing a stability condition, and
extracting heart data yields back the original data. -/
theorem HeartStabilityData.roundtrip
    (h : HeartStabilityData C) :
    (h.toStabilityCondition C).toHeartStabilityData C = h := by
  sorry

end Proposition53

/-! ## §5: Lemma 5.2 consequences — P(φ) closure properties

### FALSE: P(φ) is NOT closed under subobjects in the heart

**Counterexample** (elliptic curve, standard stability condition `Z(E) = -deg(E) + i·rank(E)`):
Take `F` = semistable rank 2 bundle of degree 2 on an elliptic curve `E`.
Then `F ∈ P(3/4)` (since `arg(Z(F)) = arg(-2 + 2i) = 3π/4`).
A nonzero section `O_E → F` gives a sub-line-bundle `O_E ↪ F` in the heart `Coh(E)`.
But `O_E ∈ P(1/2)` (since `arg(Z(O_E)) = arg(i) = π/2`), so `O_E ∉ P(3/4)`.

**Why the see-saw argument fails**: For the triangle `A → E → Q → A⟦1⟧` with `E ∈ P(φ)`:
- `φ⁺(A) ≤ φ` (from `phiPlus_triangle_le`), so `Im(Z(A) · rot) ≤ 0`
- `φ⁻(Q) ≥ φ` (from `phiMinus_triangle_le`), so `Im(Z(Q) · rot) ≥ 0`
- Sum `= Im(Z(E) · rot) = 0` — but the terms have **opposite signs**, so sum `= 0`
  does NOT force each to be zero.

Compare with `P_phi_of_heart_triangle` (in `Deformation.lean`), which IS correct: it
requires BOTH `K` and `Q` to have phases `≤ φ` (and `> φ - 1`), ensuring same-sign
terms in the sum. -/

section PhaseSubcategoryProperties

variable [IsTriangulated C]

-- NOTE: The theorems `P_phi_closed_under_subobjects_in_heart` and
-- `P_phi_closed_under_quotients_in_heart` that were previously here are
-- MATHEMATICALLY FALSE and have been deleted. See the section comment above
-- for a counterexample.
--
-- The correct results for P(φ) closure are:
-- 1. `P_phi_of_heart_triangle` (Deformation.lean): if BOTH K and Q have
--    phases in (φ-1, φ], then K ∈ P(φ) and Q ∈ P(φ).
-- 2. For Bridgeland's arguments (Lemma 7.6, 7.7), the quasi-abelian
--    structure of P((a,b)) is needed. Strict subobjects in the quasi-abelian
--    category DO stay in the interval, but arbitrary heart-subobjects do NOT
--    stay in P(φ).

end PhaseSubcategoryProperties

/-! ## §7: Deformation infrastructure — heart SES bridge -/

section DeformationInfrastructure

variable [IsTriangulated C]

omit [IsTriangulated C] in
set_option backward.isDefEq.respectTransparency false in
/-- **Heart SES to distinguished triangle.**
Given a short exact sequence in the abelian heart (as objects and morphisms
in the ambient category `C` that lie in the heart), there is a distinguished
triangle extending it.

This is the fundamental bridge between abelian exact sequences in the heart
and triangulated exact triangles in the ambient category. It is used in
Lemma 7.6 (small-gap hom-vanishing) to translate kernel/image/cokernel
decompositions into phase bound arguments. -/
theorem TStructure.heart_shortExact_triangle
    (t : TStructure C) {A B Q : C}
    (hA : t.heart A) (hB : t.heart B) (hQ : t.heart Q)
    (f : A ⟶ B) (g : B ⟶ Q) (hfg : f ≫ g = 0)
    (hmono : Mono f) (hepi : Epi g)
    (hexact : ∀ {W : C} (α : W ⟶ B), α ≫ g = 0 →
      ∃ (β : W ⟶ A), β ≫ f = α) :
    ∃ (h : Q ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  -- Work in the heart abelian subcategory (letI for transparent instance reduction)
  letI := t.hasHeartFullSubcategory
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  let A' : t.heart.FullSubcategory := ⟨A, hA⟩
  let B' : t.heart.FullSubcategory := ⟨B, hB⟩
  let Q' : t.heart.FullSubcategory := ⟨Q, hQ⟩
  let f' : A' ⟶ B' := ObjectProperty.homMk f
  let g' : B' ⟶ Q' := ObjectProperty.homMk g
  -- g' is epi in the heart (faithful inclusion preserves the epi test)
  haveI : Epi g' := ⟨fun {Z} h₁ h₂ hh ↦ by
    ext; exact (cancel_epi g).mp (by
      simpa [ObjectProperty.FullSubcategory.comp_hom] using
        congr_arg InducedCategory.Hom.hom hh)⟩
  -- Get a distinguished triangle from the epi g' via the heart's abelian structure
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (heart_hι t) (heart_admissible t) g'
  -- hT : Triangle.mk (ι.map i) (ι.map g') δ ∈ distTriang C
  -- Factor ι.map i through f via hexact (i ≫ g' = 0 from the triangle)
  have h_ig : (ι.map i) ≫ g = 0 := by
    have := comp_distTriang_mor_zero₁₂ _ hT
    -- this : ι.map i ≫ ι.map g' = 0; ι.map g' =_def g
    change (ι.map i) ≫ g = 0 at this; exact this
  obtain ⟨β_hom, hβ_hom⟩ := hexact _ h_ig
  let β : K ⟶ A' := ObjectProperty.homMk β_hom
  have hβf : β ≫ f' = i := ι.map_injective (by
    rw [Functor.map_comp]; change β_hom ≫ f = ι.map i; exact hβ_hom)
  -- i is a kernel of g' in the heart (from the distinguished triangle)
  have hKer :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang (heart_hι t) i g' δ hT
  -- f' ≫ g' = 0 in the heart
  have hfg' : f' ≫ g' = 0 := ι.map_injective (by
    rw [Functor.map_comp, Functor.map_zero]; change f ≫ g = 0; exact hfg)
  -- Lift f' through the kernel i to get γ : A' ⟶ K with γ ≫ i = f'
  let γ : A' ⟶ K := hKer.lift (KernelFork.ofι f' hfg')
  have hγi : γ ≫ i = f' := Fork.IsLimit.lift_ι hKer
  -- β and γ are mutually inverse (both are kernel maps for g')
  have hβγ : β ≫ γ = 𝟙 K :=
    Fork.IsLimit.hom_ext hKer (by simp [hγi, hβf])
  have hγβ : γ ≫ β = 𝟙 A' := by
    haveI : Mono f' := ⟨fun {Z} h₁ h₂ hh ↦ by
      ext; exact (cancel_mono f).mp (by
        simpa [ObjectProperty.FullSubcategory.comp_hom] using
          congr_arg InducedCategory.Hom.hom hh)⟩
    rw [← cancel_mono f', Category.assoc, hβf, hγi, Category.id_comp]
  -- Construct the isomorphism K ≅ A' in the heart
  let eKA : K ≅ A' :=
    { hom := β, inv := γ, hom_inv_id := hβγ, inv_hom_id := hγβ }
  -- Transport the distinguished triangle via eKA
  -- T = Triangle.mk (ι.map i) (ι.map g') δ ∈ distTriang C
  -- T' = Triangle.mk f g h with h = δ ≫ (shiftFunctor C (1 : ℤ)).map (ι.map β)
  -- iso: T' ≅ T given by (ι.mapIso eKA.symm, id, id)
  refine ⟨δ ≫ ((shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)), ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (ι.mapIso eKA.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · -- comm₁: f ≫ 𝟙 = (ι.map γ) ≫ (ι.map i)
    simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom,
      Triangle.mk_mor₁]
    -- After simp: f = ι.map eKA.inv ≫ t.ιHeart.map i
    -- eKA.inv = γ and t.ιHeart = ι (via let), so:
    change f = ι.map γ ≫ ι.map i
    rw [← Functor.map_comp, hγi]; rfl
  · -- comm₂: g ≫ 𝟙 = 𝟙 ≫ (ι.map g')
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl
  · -- comm₃: (δ ≫ F.map (ι.map β)) ≫ F.map (ι.map γ) = 𝟙 ≫ δ
    simp only [Iso.refl_hom, Category.id_comp, Triangle.mk_mor₃, Functor.mapIso_hom,
      Iso.symm_hom]
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp, ← ι.map_comp, hβγ,
      ι.map_id, Functor.map_id, Category.comp_id]

end DeformationInfrastructure

end CategoryTheory.Triangulated
