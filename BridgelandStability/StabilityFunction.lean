/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Simple
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Order.Minimal
import Mathlib.Data.Fintype.Lattice

/-!
# Stability Functions on Abelian Categories

We define stability functions on abelian categories following Bridgeland (2007), §2.
A stability function assigns to each nonzero object of an abelian category a complex
number in the semi-closed upper half plane `H ∪ ℝ₋`, and is additive on short exact
sequences.

## Main definitions

* `CategoryTheory.upperHalfPlaneUnion`: the set `{im > 0} ∪ {im = 0 ∧ re < 0}` in `ℂ`
* `CategoryTheory.StabilityFunction`: a stability function on an abelian category
* `CategoryTheory.StabilityFunction.phase`: the phase of an object, in `(0, 1]` when nonzero
* `CategoryTheory.StabilityFunction.IsSemistable`: semistability predicate
* `CategoryTheory.AbelianHNFiltration`: HN filtration as a chain of subobjects
* `CategoryTheory.StabilityFunction.HasHNProperty`: every nonzero object admits an HN filtration

## Main results

* `CategoryTheory.StabilityFunction.hasHN_of_finiteLength`: **Proposition 2.4** (Bridgeland).
  If every object has finite length, then any stability function has the HN property.
* `CategoryTheory.StabilityFunction.hn_unique`: **Proposition 2.3** (Bridgeland).
  The number of factors in the HN filtration is unique.

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007, §2
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex Real

universe v u

namespace CategoryTheory

/-! ### The semi-closed upper half plane -/

/-- Bridgeland's semi-closed upper half plane: the strict upper half plane together with
the negative real axis. This is `{z ∈ ℂ | im z > 0} ∪ {z ∈ ℂ | im z = 0 ∧ re z < 0}`.

For `z` in this set, `Complex.arg z ∈ (0, π]`, so the phase `(1/π) · arg(z)` lies in `(0, 1]`.
This matches Bridgeland's Definition 2.1: `H = {r · exp(iπφ) : r > 0, 0 < φ ≤ 1}`. -/
def upperHalfPlaneUnion : Set ℂ :=
  {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ z.re < 0}

lemma upperHalfPlaneUnion_ne_zero {z : ℂ} (hz : z ∈ upperHalfPlaneUnion) : z ≠ 0 := by
  rcases hz with him | ⟨him, hre⟩
  · exact ne_of_apply_ne im (ne_of_gt him)
  · exact ne_of_apply_ne re (ne_of_lt hre)

lemma arg_pos_of_mem_upperHalfPlaneUnion {z : ℂ} (hz : z ∈ upperHalfPlaneUnion) :
    0 < arg z := by
  rcases hz with him | ⟨him, hre⟩
  · have h1 : 0 ≤ arg z := arg_nonneg_iff.mpr him.le
    have h2 : arg z ≠ 0 := by
      intro h0
      exact him.ne' (arg_eq_zero_iff.mp h0).2
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  · have hzeq : z = ↑z.re := Complex.ext rfl (by simp [him])
    rw [hzeq, arg_ofReal_of_neg hre]
    exact Real.pi_pos

lemma im_nonneg_of_mem_upperHalfPlaneUnion {z : ℂ} (hz : z ∈ upperHalfPlaneUnion) :
    0 ≤ z.im := by
  rcases hz with him | ⟨him, _⟩
  · exact him.le
  · exact him.symm ▸ le_refl _

lemma mem_upperHalfPlaneUnion_of_add {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ upperHalfPlaneUnion) (h₂ : z₂ ∈ upperHalfPlaneUnion) :
    z₁ + z₂ ∈ upperHalfPlaneUnion := by
  have hi₁ := im_nonneg_of_mem_upperHalfPlaneUnion h₁
  have hi₂ := im_nonneg_of_mem_upperHalfPlaneUnion h₂
  simp only [upperHalfPlaneUnion, Set.mem_union, Set.mem_setOf_eq, Complex.add_im, Complex.add_re]
  by_cases h₁' : 0 < z₁.im
  · left; linarith
  · by_cases h₂' : 0 < z₂.im
    · left; linarith
    · right
      have him₁ : z₁.im = 0 := le_antisymm (not_lt.mp h₁') hi₁
      have him₂ : z₂.im = 0 := le_antisymm (not_lt.mp h₂') hi₂
      have hre₁ : z₁.re < 0 := by
        rcases h₁ with h | ⟨_, h_re⟩
        · exact absurd him₁ (ne_of_gt h)
        · exact h_re
      have hre₂ : z₂.re < 0 := by
        rcases h₂ with h | ⟨_, h_re⟩
        · exact absurd him₂ (ne_of_gt h)
        · exact h_re
      exact ⟨by linarith, by linarith⟩

/-! ### Arg convexity for sums in the upper half plane

The key analytical ingredient for stability function theory: if `z₁` and `z₂` are
in the semi-closed upper half plane, then `arg(z₁ + z₂)` lies between `arg z₁` and
`arg z₂`.

The proof uses the "cross product" method: the 2D cross product
`z₁.re * z₂.im - z₁.im * z₂.re` determines the ordering of `arg z₁` and `arg z₂`
in the upper half plane. The algebraic identities
`(z₁+z₂).re * z₂.im - (z₁+z₂).im * z₂.re = z₁.re * z₂.im - z₁.im * z₂.re` and
`z₁.re * (z₁+z₂).im - z₁.im * (z₁+z₂).re = z₁.re * z₂.im - z₁.im * z₂.re`
(the self-terms cancel) then give both bounds. -/

/-- The "cross product" `z₁.re * z₂.im - z₁.im * z₂.re` equals
`‖z₁‖ * ‖z₂‖ * sin(arg z₂ - arg z₁)`. -/
private lemma cross_eq_norm_mul_sin (z₁ z₂ : ℂ) :
    z₁.re * z₂.im - z₁.im * z₂.re =
      ‖z₁‖ * ‖z₂‖ * Real.sin (arg z₂ - arg z₁) := by
  rw [← norm_mul_cos_arg z₁, ← norm_mul_sin_arg z₁,
      ← norm_mul_cos_arg z₂, ← norm_mul_sin_arg z₂, Real.sin_sub]
  ring

/-- If `arg z₁ ≤ arg z₂` (with both in the closed upper half plane), then
the cross product `z₁.re * z₂.im - z₁.im * z₂.re` is nonneg. -/
private lemma cross_nonneg_of_arg_le {z₁ z₂ : ℂ}
    (him₁ : 0 ≤ z₁.im) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (h : arg z₁ ≤ arg z₂) :
    0 ≤ z₁.re * z₂.im - z₁.im * z₂.re := by
  have hnn : 0 < ‖z₁‖ * ‖z₂‖ := mul_pos (norm_pos_iff.mpr hz₁) (norm_pos_iff.mpr hz₂)
  rw [cross_eq_norm_mul_sin, mul_nonneg_iff_right_nonneg_of_pos hnn]
  exact sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr h)
    (by linarith [arg_le_pi z₂, arg_nonneg_iff.mpr him₁])

/-- If the cross product is nonneg and both args are positive (in the open upper half plane
or negative real axis), then `arg z₁ ≤ arg z₂`. -/
private lemma arg_le_of_cross_nonneg {z₁ z₂ : ℂ}
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (harg₂ : 0 < arg z₂)
    (hcross : 0 ≤ z₁.re * z₂.im - z₁.im * z₂.re) :
    arg z₁ ≤ arg z₂ := by
  have hnn : 0 < ‖z₁‖ * ‖z₂‖ := mul_pos (norm_pos_iff.mpr hz₁) (norm_pos_iff.mpr hz₂)
  rw [cross_eq_norm_mul_sin, mul_nonneg_iff_right_nonneg_of_pos hnn] at hcross
  by_contra h
  push_neg at h
  have hlt : arg z₂ - arg z₁ < 0 := sub_neg.mpr h
  have hge : -π < arg z₂ - arg z₁ := by linarith [arg_le_pi z₁]
  exact absurd hcross (not_le.mpr (sin_neg_of_neg_of_neg_pi_lt hlt hge))

/-- Strict version: if `arg z₁ < arg z₂` (with both in the closed upper half plane), then
the cross product is strictly positive. -/
private lemma cross_pos_of_arg_lt {z₁ z₂ : ℂ}
    (harg₁ : 0 < arg z₁) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (h : arg z₁ < arg z₂) :
    0 < z₁.re * z₂.im - z₁.im * z₂.re := by
  have hnn : 0 < ‖z₁‖ * ‖z₂‖ := mul_pos (norm_pos_iff.mpr hz₁) (norm_pos_iff.mpr hz₂)
  rw [cross_eq_norm_mul_sin]
  exact mul_pos hnn (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr h)
    (by linarith [arg_le_pi z₂]))

/-- Strict version: if the cross product is positive and both args are positive (in the UHP),
then `arg z₁ < arg z₂`. -/
private lemma arg_lt_of_cross_pos {z₁ z₂ : ℂ}
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (harg₂ : 0 < arg z₂)
    (hcross : 0 < z₁.re * z₂.im - z₁.im * z₂.re) :
    arg z₁ < arg z₂ := by
  have hnn : 0 < ‖z₁‖ * ‖z₂‖ := mul_pos (norm_pos_iff.mpr hz₁) (norm_pos_iff.mpr hz₂)
  rw [cross_eq_norm_mul_sin] at hcross
  -- hcross : 0 < ‖z₁‖ * ‖z₂‖ * sin(arg z₂ - arg z₁)
  have hsin : 0 < Real.sin (arg z₂ - arg z₁) := by
    rcases (mul_pos_iff.mp hcross).elim id (fun ⟨h1, h2⟩ ↦ absurd h1 (not_lt.mpr hnn.le)) with
      ⟨_, h⟩
    exact h
  by_contra h
  push_neg at h
  rcases h.eq_or_lt with heq | hlt
  · rw [heq, sub_self, Real.sin_zero] at hsin; exact lt_irrefl _ hsin
  · have : Real.sin (arg z₂ - arg z₁) < 0 :=
      sin_neg_of_neg_of_neg_pi_lt (sub_neg.mpr hlt) (by linarith [arg_le_pi z₁])
    linarith

/-- **Strict see-saw**: if `z₁, z₂ ∈ UHP \ {0}` with `arg z₁ ≠ arg z₂`, then
`arg(z₁ + z₂) < max(arg z₁, arg z₂)` (strict inequality). -/
private lemma arg_add_lt_max {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ upperHalfPlaneUnion) (h₂ : z₂ ∈ upperHalfPlaneUnion)
    (hne : arg z₁ ≠ arg z₂) :
    arg (z₁ + z₂) < max (arg z₁) (arg z₂) := by
  have hz₁ := upperHalfPlaneUnion_ne_zero h₁
  have hz₂ := upperHalfPlaneUnion_ne_zero h₂
  have hs_mem := mem_upperHalfPlaneUnion_of_add h₁ h₂
  have hs_ne := upperHalfPlaneUnion_ne_zero hs_mem
  have him₁ := im_nonneg_of_mem_upperHalfPlaneUnion h₁
  have him₂ := im_nonneg_of_mem_upperHalfPlaneUnion h₂
  have harg₁ := arg_pos_of_mem_upperHalfPlaneUnion h₁
  have harg₂ := arg_pos_of_mem_upperHalfPlaneUnion h₂
  set cp := z₁.re * z₂.im - z₁.im * z₂.re
  rcases hne.lt_or_gt with h | h
  · rw [max_eq_right h.le]
    apply arg_lt_of_cross_pos hs_ne hz₂ harg₂
    show 0 < (z₁ + z₂).re * z₂.im - (z₁ + z₂).im * z₂.re
    have : (z₁ + z₂).re * z₂.im - (z₁ + z₂).im * z₂.re = cp := by
      simp only [Complex.add_re, Complex.add_im, cp]; ring
    rw [this]
    exact cross_pos_of_arg_lt harg₁ hz₁ hz₂ h
  · rw [max_eq_left h.le]
    apply arg_lt_of_cross_pos hs_ne hz₁ harg₁
    show 0 < (z₁ + z₂).re * z₁.im - (z₁ + z₂).im * z₁.re
    have : (z₁ + z₂).re * z₁.im - (z₁ + z₂).im * z₁.re = -cp := by
      simp only [Complex.add_re, Complex.add_im, cp]; ring
    rw [this]
    have : 0 < z₂.re * z₁.im - z₂.im * z₁.re :=
      cross_pos_of_arg_lt harg₂ hz₂ hz₁ h
    linarith

/-- For `z₁, z₂` in the upper half plane union, `arg(z₁ + z₂) ≤ max(arg z₁, arg z₂)`.

This is the key analytical ingredient for the phase "see-saw" lemma: the phase of the
middle term of a short exact sequence is bounded by the phases of the outer terms.

The proof: WLOG `arg z₁ ≤ arg z₂`. Show `arg(z₁+z₂) ≤ arg z₂` by checking
`0 ≤ (z₁+z₂).re * z₂.im - (z₁+z₂).im * z₂.re`, which simplifies to the cross product
`z₁.re * z₂.im - z₁.im * z₂.re ≥ 0`, known from the WLOG hypothesis. -/
lemma arg_add_le_max {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ upperHalfPlaneUnion) (h₂ : z₂ ∈ upperHalfPlaneUnion) :
    arg (z₁ + z₂) ≤ max (arg z₁) (arg z₂) := by
  have hz₁ := upperHalfPlaneUnion_ne_zero h₁
  have hz₂ := upperHalfPlaneUnion_ne_zero h₂
  have hs_mem := mem_upperHalfPlaneUnion_of_add h₁ h₂
  have hs_ne := upperHalfPlaneUnion_ne_zero hs_mem
  have him₁ := im_nonneg_of_mem_upperHalfPlaneUnion h₁
  have him₂ := im_nonneg_of_mem_upperHalfPlaneUnion h₂
  have hims := im_nonneg_of_mem_upperHalfPlaneUnion hs_mem
  have harg₁ := arg_pos_of_mem_upperHalfPlaneUnion h₁
  have harg₂ := arg_pos_of_mem_upperHalfPlaneUnion h₂
  set cp := z₁.re * z₂.im - z₁.im * z₂.re
  rcases le_total (arg z₁) (arg z₂) with h | h
  · -- Case arg z₁ ≤ arg z₂: show arg(z₁+z₂) ≤ arg z₂ = max
    rw [max_eq_right h]
    -- Suffices: 0 ≤ cross((z₁+z₂), z₂), which simplifies to cp
    apply arg_le_of_cross_nonneg hs_ne hz₂ harg₂
    show 0 ≤ (z₁ + z₂).re * z₂.im - (z₁ + z₂).im * z₂.re
    have : (z₁ + z₂).re * z₂.im - (z₁ + z₂).im * z₂.re = cp := by
      simp only [Complex.add_re, Complex.add_im, cp]; ring
    rw [this]
    exact cross_nonneg_of_arg_le him₁ hz₁ hz₂ h
  · -- Case arg z₂ ≤ arg z₁: show arg(z₁+z₂) ≤ arg z₁ = max
    rw [max_eq_left h]
    -- Suffices: 0 ≤ cross((z₁+z₂), z₁), which simplifies to -cp
    apply arg_le_of_cross_nonneg hs_ne hz₁ harg₁
    show 0 ≤ (z₁ + z₂).re * z₁.im - (z₁ + z₂).im * z₁.re
    have : (z₁ + z₂).re * z₁.im - (z₁ + z₂).im * z₁.re = -cp := by
      simp only [Complex.add_re, Complex.add_im, cp]; ring
    rw [this]
    have hcp : 0 ≤ z₂.re * z₁.im - z₂.im * z₁.re :=
      cross_nonneg_of_arg_le him₂ hz₂ hz₁ h
    linarith

/-- For `z₁, z₂` in the upper half plane union, `min(arg z₁, arg z₂) ≤ arg(z₁ + z₂)`.

The dual bound to `arg_add_le_max`. The same cross product identity gives both
bounds simultaneously. -/
lemma min_arg_le_arg_add {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ upperHalfPlaneUnion) (h₂ : z₂ ∈ upperHalfPlaneUnion) :
    min (arg z₁) (arg z₂) ≤ arg (z₁ + z₂) := by
  have hz₁ := upperHalfPlaneUnion_ne_zero h₁
  have hz₂ := upperHalfPlaneUnion_ne_zero h₂
  have hs_mem := mem_upperHalfPlaneUnion_of_add h₁ h₂
  have hs_ne := upperHalfPlaneUnion_ne_zero hs_mem
  have him₁ := im_nonneg_of_mem_upperHalfPlaneUnion h₁
  have him₂ := im_nonneg_of_mem_upperHalfPlaneUnion h₂
  have hims := im_nonneg_of_mem_upperHalfPlaneUnion hs_mem
  have hargs := arg_pos_of_mem_upperHalfPlaneUnion hs_mem
  set cp := z₁.re * z₂.im - z₁.im * z₂.re
  rcases le_total (arg z₁) (arg z₂) with h | h
  · -- Case arg z₁ ≤ arg z₂: show arg z₁ = min ≤ arg(z₁+z₂)
    rw [min_eq_left h]
    -- Suffices: 0 ≤ cross(z₁, z₁+z₂), which simplifies to cp
    apply arg_le_of_cross_nonneg hz₁ hs_ne hargs
    show 0 ≤ z₁.re * (z₁ + z₂).im - z₁.im * (z₁ + z₂).re
    have : z₁.re * (z₁ + z₂).im - z₁.im * (z₁ + z₂).re = cp := by
      simp only [Complex.add_re, Complex.add_im, cp]; ring
    rw [this]
    exact cross_nonneg_of_arg_le him₁ hz₁ hz₂ h
  · -- Case arg z₂ ≤ arg z₁: show arg z₂ = min ≤ arg(z₁+z₂)
    rw [min_eq_right h]
    -- Suffices: 0 ≤ cross(z₂, z₁+z₂), which simplifies to -cp
    apply arg_le_of_cross_nonneg hz₂ hs_ne hargs
    show 0 ≤ z₂.re * (z₁ + z₂).im - z₂.im * (z₁ + z₂).re
    have : z₂.re * (z₁ + z₂).im - z₂.im * (z₁ + z₂).re = -cp := by
      simp only [Complex.add_re, Complex.add_im, cp]; ring
    rw [this]
    have hcp : 0 ≤ z₂.re * z₁.im - z₂.im * z₁.re :=
      cross_nonneg_of_arg_le him₂ hz₂ hz₁ h
    linarith

/-! ### Stability functions -/

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A stability function on an abelian category `A` assigns to each object a complex number
such that nonzero objects map into the semi-closed upper half plane, and the assignment
is additive on short exact sequences (Bridgeland, Definition 2.1).

We use an object-level function `Zobj : A → ℂ` rather than a K₀-level homomorphism,
since the Grothendieck group `K₀` in the current formalization is defined only for
pretriangulated categories, not abelian categories. -/
structure StabilityFunction (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The central charge on objects. -/
  Zobj : A → ℂ
  /-- The zero object maps to zero. -/
  map_zero' : ∀ (X : A), IsZero X → Zobj X = 0
  /-- Additivity on short exact sequences: `Z(B) = Z(A) + Z(C)` for `0 → A → B → C → 0`. -/
  additive : ∀ (S : ShortComplex A), S.ShortExact → Zobj S.X₂ = Zobj S.X₁ + Zobj S.X₃
  /-- Every nonzero object maps into the semi-closed upper half plane. -/
  upper : ∀ (E : A), ¬IsZero E → Zobj E ∈ upperHalfPlaneUnion

/-! ### Phase -/

namespace StabilityFunction

variable (Z : StabilityFunction A)

/-- The phase of an object `E`, defined as `(1/π) · arg(Z(E))`.
For a nonzero object, `Z(E) ∈ upperHalfPlaneUnion` implies `arg(Z(E)) ∈ (0, π]`,
so the phase lies in `(0, 1]`. For a zero object, the phase is `0`. -/
def phase (E : A) : ℝ :=
  (1 / Real.pi) * arg (Z.Zobj E)

lemma phase_pos (E : A) (hE : ¬IsZero E) : 0 < Z.phase E := by
  unfold phase
  exact mul_pos (div_pos one_pos Real.pi_pos)
    (arg_pos_of_mem_upperHalfPlaneUnion (Z.upper E hE))

lemma phase_le_one (E : A) : Z.phase E ≤ 1 := by
  unfold phase
  rw [div_mul_eq_mul_div, one_mul]
  exact div_le_one_of_le₀ (arg_le_pi (Z.Zobj E)) (le_of_lt Real.pi_pos)

lemma phase_mem_Ioc (E : A) (hE : ¬IsZero E) :
    Z.phase E ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨Z.phase_pos E hE, Z.phase_le_one E⟩

/-! ### Semistability -/

/-- An object `E` of an abelian category is *semistable* with respect to a stability
function `Z` if it is nonzero and for every nonzero subobject `A ↪ E`, the phase of
`A` is at most the phase of `E` (Bridgeland, Definition 2.2). -/
def IsSemistable (E : A) : Prop :=
  ¬IsZero E ∧ ∀ (B : Subobject E), ¬IsZero (B : A) →
    Z.phase (B : A) ≤ Z.phase E

/-- An object is *stable* if it is nonzero and every nonzero proper subobject has
strictly smaller phase. -/
def IsStable (E : A) : Prop :=
  ¬IsZero E ∧ ∀ (B : Subobject E), ¬IsZero (B : A) →
    B ≠ ⊤ → Z.phase (B : A) < Z.phase E

/-- A nonzero object that is not semistable has a destabilizing subobject: a nonzero
subobject with strictly larger phase. -/
lemma exists_destabilizing_of_not_semistable (E : A) (hE : ¬IsZero E)
    (hns : ¬Z.IsSemistable E) :
    ∃ (B : Subobject E), ¬IsZero (B : A) ∧ Z.phase E < Z.phase (B : A) := by
  simp only [IsSemistable, not_and_or, not_forall, not_le, exists_prop] at hns
  rcases hns with hns | ⟨B, hB_nz, hB_phase⟩
  · exact absurd hE hns
  · exact ⟨B, hB_nz, hB_phase⟩

/-! ### Phase see-saw -/

/-- **Phase see-saw (upper bound)**: For a short exact sequence `0 → A → B → C → 0`
with `A, C` nonzero, the phase of `B` is at most the maximum of the phases of `A` and `C`.
This follows from `Z(B) = Z(A) + Z(C)` and `arg_add_le_max`. -/
lemma phase_le_max_of_shortExact (S : ShortComplex A) (hse : S.ShortExact)
    (hA : ¬IsZero S.X₁) (hC : ¬IsZero S.X₃) :
    Z.phase S.X₂ ≤ max (Z.phase S.X₁) (Z.phase S.X₃) := by
  unfold phase
  have hadd : Z.Zobj S.X₂ = Z.Zobj S.X₁ + Z.Zobj S.X₃ := Z.additive S hse
  rw [hadd]
  have h₁ := Z.upper S.X₁ hA
  have h₃ := Z.upper S.X₃ hC
  have harg := arg_add_le_max h₁ h₃
  calc (1 / Real.pi) * arg (Z.Zobj S.X₁ + Z.Zobj S.X₃)
      ≤ (1 / Real.pi) * max (arg (Z.Zobj S.X₁)) (arg (Z.Zobj S.X₃)) := by
        apply mul_le_mul_of_nonneg_left harg (div_nonneg one_pos.le Real.pi_pos.le)
    _ = max ((1 / Real.pi) * arg (Z.Zobj S.X₁)) ((1 / Real.pi) * arg (Z.Zobj S.X₃)) := by
        rw [mul_max_of_nonneg _ _ (div_nonneg one_pos.le Real.pi_pos.le)]

/-- **Phase see-saw (lower bound)**: For a short exact sequence `0 → A → B → C → 0`
with `A, C` nonzero, the phase of `B` is at least the minimum of the phases of `A` and `C`.
This follows from `Z(B) = Z(A) + Z(C)` and `min_arg_le_arg_add`. -/
lemma min_phase_le_of_shortExact (S : ShortComplex A) (hse : S.ShortExact)
    (hA : ¬IsZero S.X₁) (hC : ¬IsZero S.X₃) :
    min (Z.phase S.X₁) (Z.phase S.X₃) ≤ Z.phase S.X₂ := by
  unfold phase
  have hadd : Z.Zobj S.X₂ = Z.Zobj S.X₁ + Z.Zobj S.X₃ := Z.additive S hse
  rw [hadd]
  have h₁ := Z.upper S.X₁ hA
  have h₃ := Z.upper S.X₃ hC
  have harg := min_arg_le_arg_add h₁ h₃
  calc min ((1 / Real.pi) * arg (Z.Zobj S.X₁)) ((1 / Real.pi) * arg (Z.Zobj S.X₃))
      = (1 / Real.pi) * min (arg (Z.Zobj S.X₁)) (arg (Z.Zobj S.X₃)) := by
        rw [mul_min_of_nonneg _ _ (div_nonneg one_pos.le Real.pi_pos.le)]
    _ ≤ (1 / Real.pi) * arg (Z.Zobj S.X₁ + Z.Zobj S.X₃) := by
        apply mul_le_mul_of_nonneg_left harg (div_nonneg one_pos.le Real.pi_pos.le)

/-! ### Z and phase invariance under isomorphisms -/

/-- `Z` sends isomorphic objects to the same value. Uses additivity on the
short exact sequence `0 → E → F → 0` induced by the isomorphism. -/
lemma Zobj_eq_of_iso {E F : A} (e : E ≅ F) : Z.Zobj E = Z.Zobj F := by
  have hS : (ShortComplex.mk e.hom (cokernel.π e.hom) (by simp)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel e.hom) inferInstance inferInstance
  have hadd := Z.additive _ hS
  have hcok : IsZero (cokernel e.hom) := isZero_cokernel_of_epi e.hom
  rw [Z.map_zero' _ hcok, add_zero] at hadd
  exact hadd.symm

/-- Phase is invariant under isomorphisms. -/
lemma phase_eq_of_iso {E F : A} (e : E ≅ F) : Z.phase E = Z.phase F := by
  unfold phase; rw [Z.Zobj_eq_of_iso e]

/-- In an abelian category, for any morphism `f`, the short complex
`X →f→ Y →cokernel.π→ cokernel f` is exact. If `f` is mono, it is short exact. -/
private lemma shortExact_of_mono {X Y : A} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (by simp)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f) inferInstance inferInstance

/-- `IsSemistable` is invariant under isomorphisms. -/
lemma isSemistable_of_iso {X Y : A} (e : X ≅ Y) (h : Z.IsSemistable X) :
    Z.IsSemistable Y := by
  refine ⟨fun hY ↦ h.1 (hY.of_iso e), fun B hB ↦ ?_⟩
  -- B : Subobject Y. Transport to a subobject of X via e.
  have hBX : ¬IsZero ((Subobject.mk (B.arrow ≫ e.inv)) : A) := by
    intro hZ
    exact hB (hZ.of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv)).symm)
  have hle := h.2 (Subobject.mk (B.arrow ≫ e.inv)) hBX
  rw [Z.phase_eq_of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv))] at hle
  rwa [Z.phase_eq_of_iso e] at hle

/-! ### Subobject lifting and bot/top helpers -/

/-- A subobject is zero iff it equals ⊥. -/
lemma subobject_isZero_iff_eq_bot {E : A} (B : Subobject E) :
    IsZero (B : A) ↔ B = ⊥ := by
  constructor
  · intro hZ
    have : B.arrow = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rwa [← Subobject.mk_arrow B, Subobject.mk_eq_bot_iff_zero]
  · intro h
    subst h
    exact (isZero_zero A).of_iso Subobject.botCoeIsoZero

/-- A nonzero subobject is not ⊥. -/
lemma subobject_ne_bot_of_not_isZero {E : A} {B : Subobject E}
    (h : ¬IsZero (B : A)) : B ≠ ⊥ :=
  fun h' ↦ h ((subobject_isZero_iff_eq_bot B).mpr h')

/-- ⊥ as a subobject is zero. -/
lemma subobject_not_isZero_of_ne_bot {E : A} {B : Subobject E}
    (h : B ≠ ⊥) : ¬IsZero (B : A) :=
  fun hZ ↦ h ((subobject_isZero_iff_eq_bot B).mp hZ)

/-- In a nontrivial category, ⊤ ≠ ⊥ as subobjects of a nonzero object. -/
lemma subobject_top_ne_bot_of_not_isZero {E : A} (hE : ¬IsZero E) :
    (⊤ : Subobject E) ≠ ⊥ := by
  intro h
  apply hE
  have hZ : IsZero ((⊤ : Subobject E) : A) := (subobject_isZero_iff_eq_bot _).mpr h
  exact hZ.of_iso (asIso (⊤ : Subobject E).arrow).symm

/-- `ofLE ⊥ S h` is the zero morphism (since the source is a zero object). -/
lemma Subobject.ofLE_bot {E : A} (S : Subobject E) (h : ⊥ ≤ S) :
    Subobject.ofLE ⊥ S h = 0 :=
  zero_of_source_iso_zero _ Subobject.botCoeIsoZero

/-- The cokernel of `ofLE ⊥ S _` is isomorphic to `(S : A)`. -/
def Subobject.cokernelBotIso {E : A} (S : Subobject E) (h : ⊥ ≤ S) :
    cokernel (Subobject.ofLE ⊥ S h) ≅ (S : A) := by
  have : Subobject.ofLE ⊥ S h = 0 := Subobject.ofLE_bot S h
  rw [this]
  exact cokernelZeroIsoTarget

/-- Given B : Subobject E and C : Subobject (B : A), lift C to a subobject of E
by composing the arrows. -/
private def liftSub {E : A} (B : Subobject E) (C : Subobject (B : A)) :
    Subobject E :=
  Subobject.mk (C.arrow ≫ B.arrow)

omit [Abelian A] in
/-- The lifted subobject is below B. -/
private lemma liftSub_le {E : A} (B : Subobject E) (C : Subobject (B : A)) :
    liftSub B C ≤ B := by
  have h := Subobject.mk_le_mk_of_comm C.arrow
    (show C.arrow ≫ B.arrow = C.arrow ≫ B.arrow from rfl)
  rwa [Subobject.mk_arrow] at h

/-- The phase of the lifted subobject equals the phase of C. -/
private lemma phase_liftSub {E : A} (B : Subobject E) (C : Subobject (B : A)) :
    Z.phase (liftSub B C : A) = Z.phase (C : A) :=
  Z.phase_eq_of_iso (Subobject.underlyingIso _)

/-- Lifting ⊥ gives ⊥. -/
private lemma liftSub_bot {E : A} (B : Subobject E) :
    liftSub B ⊥ = ⊥ := by
  apply (Subobject.mk_eq_bot_iff_zero).mpr
  simp [Subobject.bot_arrow]

/-- Lifting a nonzero subobject gives a nonzero subobject. -/
private lemma liftSub_ne_bot {E : A} (B : Subobject E)
    (C : Subobject (B : A)) (hC : C ≠ ⊥) :
    liftSub B C ≠ ⊥ := by
  intro h
  apply hC
  rw [← subobject_isZero_iff_eq_bot] at h ⊢
  exact h.of_iso (Subobject.underlyingIso (C.arrow ≫ B.arrow)).symm

/-! ### Simple objects are semistable -/

/-- A simple object is semistable: its only nonzero subobject is `⊤ ≅ E` itself,
so the phase condition `φ(B) ≤ φ(E)` holds trivially. -/
lemma simple_isSemistable {E : A} (hS : Simple E) : Z.IsSemistable E := by
  refine ⟨Simple.not_isZero E, fun B hB ↦ ?_⟩
  have : IsSimpleOrder (Subobject E) := (simple_iff_subobject_isSimpleOrder E).mp hS
  rcases IsSimpleOrder.eq_bot_or_eq_top B with h | h
  · exact absurd ((subobject_isZero_iff_eq_bot B).mpr h) hB
  · rw [h]; exact le_of_eq (Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow))

/-! ### Max phase and MDS construction -/

/-- Among all nonzero subobjects of a nonzero object with finite subobject lattice,
there exists one with maximal phase. -/
lemma exists_maxPhase_subobject (E : A) (hE : ¬IsZero E)
    [hFin : Finite (Subobject E)] :
    ∃ M : Subobject E, M ≠ ⊥ ∧
      ∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A) := by
  have hne : ∃ B : Subobject E, B ≠ ⊥ :=
    ⟨⊤, subobject_top_ne_bot_of_not_isZero hE⟩
  haveI : Nonempty {B : Subobject E // B ≠ ⊥} :=
    ⟨⟨⊤, subobject_top_ne_bot_of_not_isZero hE⟩⟩
  haveI : Finite {B : Subobject E // B ≠ ⊥} := Finite.of_injective
    (fun x ↦ (x : Subobject E)) Subtype.val_injective
  obtain ⟨⟨M, hM⟩, hmax⟩ := Finite.exists_max (fun (x : {B : Subobject E // B ≠ ⊥}) ↦
    Z.phase ((x : Subobject E) : A))
  exact ⟨M, hM, fun B hB ↦ hmax ⟨B, hB⟩⟩

/-- If `M` has maximal phase among all nonzero subobjects of `E`, then `M` is
semistable as an object. This is because any destabilizing subobject of `(M : A)`
lifts to a nonzero subobject of `E` with higher phase, contradicting maximality. -/
lemma maxPhase_isSemistable {E : A} {M : Subobject E} (hM : M ≠ ⊥)
    (hmax : ∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A)) :
    Z.IsSemistable (M : A) := by
  refine ⟨subobject_not_isZero_of_ne_bot hM, fun C hC ↦ ?_⟩
  -- C : Subobject (M : A). Lift to a subobject of E via liftSub.
  have hC_ne : C ≠ ⊥ := subobject_ne_bot_of_not_isZero hC
  have hL := liftSub_ne_bot M C hC_ne
  calc Z.phase (C : A)
      = Z.phase (liftSub M C : A) := (Z.phase_liftSub M C).symm
    _ ≤ Z.phase (M : A) := hmax (liftSub M C) hL

/-- The max-phase subobject `M` is not `⊤` when `E` is not semistable and `M ≠ ⊤`,
which happens when `φ(M) > φ(E)`. Since `φ(⊤) = φ(E)` (via the iso `⊤ ≅ E`),
`φ(M) > φ(E)` implies `M ≠ ⊤`. -/
lemma maxPhase_ne_top_of_not_semistable {E : A}
    (hns : ¬Z.IsSemistable E) :
    ∀ M : Subobject E, M ≠ ⊥ →
      (∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A)) →
      M ≠ ⊤ := by
  intro M hM hmax hMtop
  apply hns
  have hMS := Z.maxPhase_isSemistable hM hmax
  subst hMtop
  exact Z.isSemistable_of_iso (asIso (⊤ : Subobject E).arrow) hMS

end StabilityFunction

/-! ### Harder-Narasimhan filtrations (abelian setting) -/

/-- A Harder-Narasimhan filtration of a nonzero object `E` in an abelian category,
with respect to a stability function `Z`.

This is a finite chain of subobjects `0 = E₀ < E₁ < ⋯ < Eₙ = E` with:
- `n ≥ 1` factors
- the phases are strictly decreasing
- each factor `Eᵢ₊₁/Eᵢ` is semistable with phase `φ i`

The semistability condition connects the chain to the stability function `Z`:
the `i`-th factor (successive quotient) is semistable and has phase `φ i`.
We encode this via `factor_semistable` and `factor_phase`, where the factor
objects are obtained as cokernels of the successive inclusion maps. -/
structure AbelianHNFiltration (Z : StabilityFunction A) (E : A) where
  /-- The number of semistable factors. -/
  n : ℕ
  hn : 0 < n
  /-- The chain of subobjects, strictly monotone. -/
  chain : Fin (n + 1) → Subobject E
  chain_strictMono : StrictMono chain
  chain_bot : chain ⟨0, Nat.zero_lt_succ _⟩ = ⊥
  chain_top : chain ⟨n, n.lt_succ_iff.mpr le_rfl⟩ = ⊤
  /-- The phases of the semistable quotients, in strictly decreasing order. -/
  φ : Fin n → ℝ
  φ_anti : StrictAnti φ
  /-- The phase of each factor equals the given phase. -/
  factor_phase : ∀ (j : Fin n),
    Z.phase (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
      (le_of_lt (chain_strictMono j.castSucc_lt_succ)))) = φ j
  /-- Each successive quotient is semistable. -/
  factor_semistable : ∀ (j : Fin n),
    Z.IsSemistable (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
      (le_of_lt (chain_strictMono j.castSucc_lt_succ))))

/-- A stability function has the Harder-Narasimhan property if every nonzero object
admits a Harder-Narasimhan filtration (Bridgeland, Proposition 2.4). -/
def StabilityFunction.HasHNProperty (Z : StabilityFunction A) : Prop :=
  ∀ (E : A), ¬IsZero E → Nonempty (AbelianHNFiltration Z E)

/-! ### Pullback infrastructure for HN proof -/

/-- In an abelian category, precomposing by an epi doesn't change the image subobject. -/
private lemma imageSubobject_epi_comp {X Y Z : A} (g : X ⟶ Y) [Epi g] (f : Y ⟶ Z) :
    imageSubobject (g ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le g f)
  have h_le := imageSubobject_comp_le g f
  haveI : Mono (Subobject.ofLE _ _ h_le) := by
    apply (mono_comp_iff_of_mono _ (imageSubobject f).arrow).mp
    rw [Subobject.ofLE_arrow]; infer_instance
  haveI : Epi (Subobject.ofLE _ _ h_le) := imageSubobject_comp_le_epi_of_epi g f
  haveI := isIso_of_mono_of_epi (Subobject.ofLE _ _ h_le)
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ h_le))
    (by rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow])

/-- For epi `p` in an abelian category, `pullbackπ p B` is epi. -/
private lemma epi_pullbackπ_of_epi {X Y : A} (p : X ⟶ Y) [Epi p] (B : Subobject Y) :
    Epi (Subobject.pullbackπ p B) := by
  rw [← (Subobject.isPullback p B).isoPullback_hom_fst]; infer_instance

/-- For epi `p` in an abelian category, `(Subobject.pullback p).obj` is injective. -/
private lemma pullback_obj_injective_of_epi {X Y : A} (p : X ⟶ Y) [Epi p] :
    Function.Injective (Subobject.pullback p).obj := by
  intro B₁ B₂ h
  haveI := epi_pullbackπ_of_epi p B₁
  haveI := epi_pullbackπ_of_epi p B₂
  calc B₁ = imageSubobject (Subobject.pullbackπ p B₁ ≫ B₁.arrow) := by
          rw [imageSubobject_epi_comp, imageSubobject_mono, Subobject.mk_arrow]
    _ = imageSubobject (((Subobject.pullback p).obj B₁).arrow ≫ p) := by
          rw [(Subobject.isPullback p B₁).w]
    _ = imageSubobject (((Subobject.pullback p).obj B₂).arrow ≫ p) := by rw [h]
    _ = imageSubobject (Subobject.pullbackπ p B₂ ≫ B₂.arrow) := by
          rw [← (Subobject.isPullback p B₂).w]
    _ = B₂ := by rw [imageSubobject_epi_comp, imageSubobject_mono, Subobject.mk_arrow]

/-- The subobject `M ≤ (pullback p).obj ⊥` when `M.arrow ≫ p = 0`. This is used to show
that pullback along the cokernel projection maps every subobject above the kernel. -/
private lemma le_pullback_bot_of_comp_eq_zero {X Y : A} {M : Subobject X}
    (p : X ⟶ Y) (hMp : M.arrow ≫ p = 0) :
    M ≤ (Subobject.pullback p).obj ⊥ := by
  have hpb := Subobject.isPullback p (⊥ : Subobject Y)
  have hpb_zero : ((Subobject.pullback p).obj ⊥).arrow ≫ p = 0 := by
    have := hpb.w
    simp only [Subobject.bot_arrow, comp_zero] at this
    rw [this]
  exact Subobject.le_of_comm
    (hpb.isLimit.lift (PullbackCone.mk (0 : (M : A) ⟶ _) M.arrow (by simp [hMp])))
    (hpb.isLimit.fac _ WalkingCospan.right)

/-- For epi `cokernel.π M.arrow`, every subobject of the target pulls back to a
subobject of the source that is `≥ M`, hence `≠ ⊥` when `M ≠ ⊥`. -/
private lemma pullback_cokernel_ne_bot {E : A} {M : Subobject E}
    (hM : M ≠ ⊥) (B : Subobject (cokernel M.arrow)) :
    (Subobject.pullback (cokernel.π M.arrow)).obj B ≠ ⊥ := by
  intro h
  have hle : M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ :=
    le_pullback_bot_of_comp_eq_zero _ (cokernel.condition M.arrow)
  have hle' : M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B :=
    le_trans hle ((Subobject.pullback (cokernel.π M.arrow)).monotone bot_le)
  rw [h] at hle'
  exact hM (eq_bot_iff.mpr hle')

/-- **Cardinality decrease**: `Nat.card (Subobject Q) < Nat.card (Subobject E)` where
`Q = cokernel M.arrow` for a proper nonzero subobject `M`. -/
private lemma card_subobject_cokernel_lt {E : A} {M : Subobject E}
    (hM_ne_bot : M ≠ ⊥) [hFin : Finite (Subobject E)] :
    Nat.card (Subobject (cokernel M.arrow)) < Nat.card (Subobject E) := by
  haveI := Fintype.ofFinite (Subobject E)
  haveI : Finite (Subobject (cokernel M.arrow)) := by
    exact Finite.of_injective _ (pullback_obj_injective_of_epi (cokernel.π M.arrow))
  haveI := Fintype.ofFinite (Subobject (cokernel M.arrow))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem
    (Subobject.pullback (cokernel.π M.arrow)).obj
    (pullback_obj_injective_of_epi _)
    (by simp only [Set.mem_range, not_exists]
        exact fun B ↦ pullback_cokernel_ne_bot hM_ne_bot B)

/-- The pullback of `⊥` along `cokernel.π M.arrow` equals `M` as a subobject of `E`. -/
private lemma pullback_cokernel_bot_eq {E : A} (M : Subobject E) :
    (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ = M := by
  apply le_antisymm
  · set P := (Subobject.pullback (cokernel.π M.arrow)).obj ⊥
    have hP : P.arrow ≫ cokernel.π M.arrow = 0 := by
      have := (Subobject.isPullback (cokernel.π M.arrow)
        (⊥ : Subobject (cokernel M.arrow))).w
      simp only [Subobject.bot_arrow, comp_zero] at this; rw [this]
    have hker : kernelSubobject (cokernel.π M.arrow) = M := by
      have := (ShortComplex.mk M.arrow (cokernel.π M.arrow)
        (cokernel.condition M.arrow)).exact_iff_image_eq_kernel.mp
        (ShortComplex.exact_cokernel M.arrow)
      rw [imageSubobject_mono, Subobject.mk_arrow] at this; exact this.symm
    rw [← hker]
    exact Subobject.le_of_comm
      (factorThruKernelSubobject _ P.arrow hP)
      (factorThruKernelSubobject_comp_arrow _ _ _)
  · exact le_pullback_bot_of_comp_eq_zero _ (cokernel.condition M.arrow)

-- Subobject.pullback_top already exists in Mathlib

/-- For epi `p`, `(Subobject.pullback p).obj` is strictly monotone. -/
private lemma pullback_obj_strictMono_of_epi {X Y : A} (p : X ⟶ Y) [Epi p] :
    StrictMono (Subobject.pullback p).obj :=
  (Subobject.pullback p).monotone.strictMono_of_injective
    (pullback_obj_injective_of_epi p)

/-- Among all nonzero subobjects with maximal phase, there exists one that is maximal
in the subobject ordering. The third condition says every subobject strictly above `M`
has strictly lower phase, preventing equal-phase subobjects from being larger. -/
private lemma exists_maxPhase_maximal_subobject (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) [hFin : Finite (Subobject E)] :
    ∃ M : Subobject E, M ≠ ⊥ ∧
      (∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A)) ∧
      (∀ B : Subobject E, M < B → Z.phase (B : A) < Z.phase (M : A)) := by
  obtain ⟨M₀, hM₀_ne, hM₀_max⟩ := Z.exists_maxPhase_subobject E hE
  set S := {B : Subobject E | B ≠ ⊥ ∧ Z.phase (B : A) = Z.phase (M₀ : A)}
  have hS_ne : S.Nonempty := ⟨M₀, hM₀_ne, rfl⟩
  have hS_fin : S.Finite := Set.toFinite _
  obtain ⟨M, ⟨hM_ne, hM_phase⟩, hM_max_in_S⟩ := hS_fin.exists_maximal hS_ne
  refine ⟨M, hM_ne, fun B hB ↦ hM_phase ▸ hM₀_max B hB, fun B hB ↦ ?_⟩
  have hB_ne : B ≠ ⊥ := ne_bot_of_gt hB
  have hle := hM₀_max B hB_ne
  rw [hM_phase]
  exact lt_of_le_of_ne hle (fun heq ↦
    absurd (hM_max_in_S ⟨hB_ne, heq⟩ hB.le) (not_le_of_gt hB))


/-- In an abelian category, if `M.arrow` is not an epimorphism, then `cokernel M.arrow`
is nonzero. This applies when `M ≠ ⊤` as a subobject. -/
private lemma cokernel_nonzero_of_ne_top {E : A} {M : Subobject E} (hM : M ≠ ⊤) :
    ¬IsZero (cokernel M.arrow) := by
  intro hZ
  haveI : Epi M.arrow := Preadditive.epi_of_isZero_cokernel M.arrow hZ
  haveI : IsIso M.arrow := isIso_of_mono_of_epi M.arrow
  exact hM (Subobject.eq_top_of_isIso_arrow M)

/-- In an abelian category, `M ≠ ⊤` implies `M.arrow` is not epi. -/
private lemma not_epi_of_ne_top {E : A} {M : Subobject E} (hM : M ≠ ⊤) : ¬Epi M.arrow := by
  intro h; haveI := h
  haveI : IsIso M.arrow := isIso_of_mono_of_epi M.arrow
  exact hM (Subobject.eq_top_of_isIso_arrow M)

/-! ### Short exact sequence from pullback along cokernel projection

For a subobject `M'` of `E` and a subobject `B` of `cokernel M'.arrow`, the pullback
`pb'(B)` of `B` along `cokernel.π M'.arrow` gives a short exact sequence
`M' → pb'(B) → B`. This is used in the HN existence proof to compare phases. -/

/-- The inclusion `M' ≤ pb'(B)` for any subobject `B` of the cokernel. -/
private lemma le_pullback_cokernel {E : A} (M' : Subobject E)
    (B : Subobject (cokernel M'.arrow)) :
    M' ≤ (Subobject.pullback (cokernel.π M'.arrow)).obj B :=
  (pullback_cokernel_bot_eq M').symm.le.trans
    ((Subobject.pullback (cokernel.π M'.arrow)).monotone bot_le)

/-- The composition `ofLE ≫ pullbackπ = 0` for the pullback SES. -/
private lemma ofLE_pullbackπ_eq_zero {E : A} (M' : Subobject E)
    (B : Subobject (cokernel M'.arrow)) :
    Subobject.ofLE M' _ (le_pullback_cokernel M' B) ≫
      Subobject.pullbackπ (cokernel.π M'.arrow) B = 0 := by
  apply (cancel_mono B.arrow).mp
  simp only [zero_comp, Category.assoc]
  have hw := (Subobject.isPullback (cokernel.π M'.arrow) B).w
  calc Subobject.ofLE M' _ (le_pullback_cokernel M' B) ≫
        (Subobject.pullbackπ (cokernel.π M'.arrow) B ≫ B.arrow)
      = Subobject.ofLE M' _ (le_pullback_cokernel M' B) ≫
          (((Subobject.pullback (cokernel.π M'.arrow)).obj B).arrow ≫
            cokernel.π M'.arrow) := by rw [hw]
    _ = (Subobject.ofLE M' _ (le_pullback_cokernel M' B) ≫
          ((Subobject.pullback (cokernel.π M'.arrow)).obj B).arrow) ≫
            cokernel.π M'.arrow := by rw [Category.assoc]
    _ = M'.arrow ≫ cokernel.π M'.arrow := by rw [Subobject.ofLE_arrow]
    _ = 0 := cokernel.condition M'.arrow

/-- The short exact sequence `M' → pb'(B) → B` is short exact. -/
private lemma shortExact_ofLE_pullbackπ_cokernel {E : A} (M' : Subobject E)
    (B : Subobject (cokernel M'.arrow)) :
    (ShortComplex.mk
      (Subobject.ofLE M' _ (le_pullback_cokernel M' B))
      (Subobject.pullbackπ (cokernel.π M'.arrow) B)
      (ofLE_pullbackπ_eq_zero M' B)).ShortExact := by
  set p' := cokernel.π M'.arrow
  set pbB := (Subobject.pullback p').obj B
  set hle := le_pullback_cokernel M' B
  set hcomp := ofLE_pullbackπ_eq_zero M' B
  have hse_orig : (ShortComplex.mk M'.arrow p' (cokernel.condition M'.arrow)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel M'.arrow) inferInstance
      inferInstance
  have hkernel := hse_orig.fIsKernel
  haveI : Epi (Subobject.pullbackπ p' B) := epi_pullbackπ_of_epi p' B
  apply ShortComplex.ShortExact.mk' _ inferInstance inferInstance
  apply ShortComplex.exact_of_f_is_kernel
  have hw := (Subobject.isPullback p' B).w
  -- Helper: given g' ≫ pullbackπ = 0, deduce (g' ≫ pbB.arrow) ≫ p' = 0
  have key : ∀ {W' : A} (g' : W' ⟶ (pbB : A)),
      g' ≫ Subobject.pullbackπ p' B = 0 → (g' ≫ pbB.arrow) ≫ p' = 0 := by
    intro W' g' eq'
    calc (g' ≫ pbB.arrow) ≫ p'
        = g' ≫ (pbB.arrow ≫ p') := by rw [Category.assoc]
      _ = g' ≫ (Subobject.pullbackπ p' B ≫ B.arrow) := by congr 1; exact hw.symm
      _ = (g' ≫ Subobject.pullbackπ p' B) ≫ B.arrow := by rw [← Category.assoc]
      _ = 0 ≫ B.arrow := by rw [eq']
      _ = 0 := zero_comp
  exact KernelFork.IsLimit.ofι' (Subobject.ofLE M' pbB hle) hcomp
    (fun g' eq' ↦ ⟨hkernel.lift (KernelFork.ofι (g' ≫ pbB.arrow) (key g' eq')), by
      apply (cancel_mono pbB.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow]
      exact hkernel.fac (KernelFork.ofι (g' ≫ pbB.arrow) (key g' eq'))
        WalkingParallelPair.zero⟩)

/-- For the maximally destabilizing subobject `M'`, any nonzero subobject `B` of the
quotient `E/M'` has phase strictly less than `phase(M')`. -/
private lemma phase_subobject_cokernel_lt
    (Z : StabilityFunction A) {E : A} {M' : Subobject E}
    (hM'_ne : M' ≠ ⊥)
    (hM'_strict : ∀ B : Subobject E, M' < B → Z.phase (B : A) < Z.phase (M' : A))
    {B : Subobject (cokernel M'.arrow)} (hB : B ≠ ⊥) :
    Z.phase (B : A) < Z.phase (M' : A) := by
  set p' := cokernel.π M'.arrow
  set pbB := (Subobject.pullback p').obj B
  have hle := le_pullback_cokernel M' B
  have hlt : M' < pbB := by
    rcases hle.eq_or_lt with h | h
    · exfalso; apply hB
      exact ((pullback_obj_injective_of_epi p')
        (h ▸ pullback_cokernel_bot_eq M')).symm
    · exact h
  have hpbB_lt := hM'_strict pbB hlt
  have hse := shortExact_ofLE_pullbackπ_cokernel M' B
  have hM'_nz : ¬IsZero (M' : A) := by
    intro hZ; apply hM'_ne
    have : M'.arrow = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rwa [← Subobject.mk_arrow M', Subobject.mk_eq_bot_iff_zero]
  have hB_nz : ¬IsZero (B : A) := by
    intro hZ; apply hB
    have : B.arrow = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rwa [← Subobject.mk_arrow B, Subobject.mk_eq_bot_iff_zero]
  have hmin := Z.min_phase_le_of_shortExact _ hse hM'_nz hB_nz
  by_contra hge
  push_neg at hge
  rw [min_eq_left hge] at hmin
  linarith

/-- Z-additivity for the pullback SES: `Z(pb'(B)) = Z(M') + Z(B)`. -/
private lemma Zobj_pullback_eq_add
    (Z : StabilityFunction A) {E : A} (M' : Subobject E)
    (B : Subobject (cokernel M'.arrow)) :
    Z.Zobj (((Subobject.pullback (cokernel.π M'.arrow)).obj B) : A) =
      Z.Zobj (M' : A) + Z.Zobj (B : A) :=
  Z.additive _ (shortExact_ofLE_pullbackπ_cokernel M' B)

/-- The cokernel of pulled-back subobjects has the same Z-value as the original cokernel.
`Z(cokernel(ofLE pb'(A) pb'(B))) = Z(cokernel(ofLE A B))`. -/
private lemma Zobj_cokernel_pullback_eq
    (Z : StabilityFunction A) {E : A} (M' : Subobject E)
    {A' B' : Subobject (cokernel M'.arrow)} (h : A' ≤ B') :
    Z.Zobj (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M'.arrow)).obj A')
      ((Subobject.pullback (cokernel.π M'.arrow)).obj B')
      ((Subobject.pullback (cokernel.π M'.arrow)).monotone h))) =
      Z.Zobj (cokernel (Subobject.ofLE A' B' h)) := by
  have hse1 : (ShortComplex.mk
      (Subobject.ofLE _ _
        ((Subobject.pullback (cokernel.π M'.arrow)).monotone h))
      (cokernel.π (Subobject.ofLE _ _
        ((Subobject.pullback (cokernel.π M'.arrow)).monotone h)))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have hse2 : (ShortComplex.mk (Subobject.ofLE A' B' h)
      (cokernel.π (Subobject.ofLE A' B' h))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have h1 := Z.additive _ hse1
  have h2 := Z.additive _ hse2
  have hA := Zobj_pullback_eq_add Z M' A'
  have hB := Zobj_pullback_eq_add Z M' B'
  linear_combination -h1 + h2 - hA + hB

/-- The cokernel of consecutive pulled-back subobjects has the same phase as the
original cokernel factor. -/
private lemma phase_cokernel_pullback_eq
    (Z : StabilityFunction A) {E : A} (M' : Subobject E)
    {A' B' : Subobject (cokernel M'.arrow)} (h : A' ≤ B') :
    Z.phase (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M'.arrow)).obj A')
      ((Subobject.pullback (cokernel.π M'.arrow)).obj B')
      ((Subobject.pullback (cokernel.π M'.arrow)).monotone h))) =
      Z.phase (cokernel (Subobject.ofLE A' B' h)) := by
  simp only [StabilityFunction.phase, Zobj_cokernel_pullback_eq Z M' h]

set_option maxHeartbeats 1600000 in
-- The iso involves many compositions; the default heartbeat limit is insufficient.
set_option synthInstance.maxHeartbeats 40000 in
/-- The cokernel of consecutive pulled-back subobjects is isomorphic to the original
cokernel factor. -/
def cokernelPullbackIso (Z : StabilityFunction A) {E : A} (M' : Subobject E)
    {A' B' : Subobject (cokernel M'.arrow)} (h : A' < B') :
    cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M'.arrow)).obj A')
      ((Subobject.pullback (cokernel.π M'.arrow)).obj B')
      ((Subobject.pullback (cokernel.π M'.arrow)).monotone h.le)) ≅
      cokernel (Subobject.ofLE A' B' h.le) := by
  set p' := cokernel.π M'.arrow
  set pbA := (Subobject.pullback p').obj A'
  set pbB := (Subobject.pullback p').obj B'
  set hpb : pbA ≤ pbB := (Subobject.pullback p').monotone h.le
  -- Construct the induced map via cokernel.desc
  have hw_A := (Subobject.isPullback p' A').w
  have hw_B := (Subobject.isPullback p' B').w
  have hcomm : Subobject.ofLE pbA pbB hpb ≫ Subobject.pullbackπ p' B' =
      Subobject.pullbackπ p' A' ≫ Subobject.ofLE A' B' h.le := by
    apply (cancel_mono B'.arrow).mp
    simp only [Category.assoc, Subobject.ofLE_arrow]
    calc Subobject.ofLE pbA pbB hpb ≫ (Subobject.pullbackπ p' B' ≫ B'.arrow)
        = Subobject.ofLE pbA pbB hpb ≫ (pbB.arrow ≫ p') := by rw [hw_B]
      _ = (Subobject.ofLE pbA pbB hpb ≫ pbB.arrow) ≫ p' := by rw [Category.assoc]
      _ = pbA.arrow ≫ p' := by rw [Subobject.ofLE_arrow]
      _ = Subobject.pullbackπ p' A' ≫ A'.arrow := hw_A.symm
    -- Goal after simp: ... = pullbackπ p' A' ≫ A'.arrow
  have hfact : Subobject.ofLE pbA pbB hpb ≫
      (Subobject.pullbackπ p' B' ≫ cokernel.π (Subobject.ofLE A' B' h.le)) = 0 := by
    rw [← Category.assoc, hcomm, Category.assoc, cokernel.condition, comp_zero]
  set φ := cokernel.desc (Subobject.ofLE pbA pbB hpb)
    (Subobject.pullbackπ p' B' ≫ cokernel.π (Subobject.ofLE A' B' h.le)) hfact
  -- φ is epi
  haveI : Epi (Subobject.pullbackπ p' B') := epi_pullbackπ_of_epi p' B'
  haveI : Epi φ :=
    epi_of_epi_fac (cokernel.π_desc _ _ _)
  -- φ is mono: kernel must be zero since Z-values match
  haveI : Mono φ := by
    suffices hk : kernel.ι φ = 0 from Preadditive.mono_of_kernel_zero hk
    have hse_φ : (ShortComplex.mk (kernel.ι φ) φ
        (by simp [kernel.condition])).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel φ) inferInstance inferInstance
    have hZ_add := Z.additive _ hse_φ
    -- hZ_add : Z(cokernel₁) = Z(kernel φ) + Z(cokernel₂)
    have hZ_eq : Z.Zobj (cokernel (Subobject.ofLE pbA pbB hpb)) =
        Z.Zobj (cokernel (Subobject.ofLE A' B' h.le)) :=
      Zobj_cokernel_pullback_eq Z M' h.le
    -- Substitute to get: Z(cokernel₂) = Z(kernel φ) + Z(cokernel₂)
    rw [hZ_eq] at hZ_add
    -- So Z(kernel φ) = 0
    have hZ_ker : Z.Zobj (kernel φ) = 0 := add_eq_right.mp hZ_add.symm
    by_contra hne
    have hker_nz : ¬IsZero (kernel φ) := by
      intro hZ; exact hne (zero_of_source_iso_zero _ hZ.isoZero)
    exact absurd hZ_ker (ne_of_mem_of_not_mem (Z.upper _ hker_nz)
      (show (0 : ℂ) ∉ upperHalfPlaneUnion from fun hc ↦ by
        rcases hc with hc | ⟨_, hc⟩ <;> simp at hc))
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  exact asIso φ

/-- Phase equality when `ofLE` subobject arguments are propositionally equal.
This avoids dependent rewriting issues inside `cokernel (Subobject.ofLE ...)`. -/
private lemma phase_cokernel_ofLE_congr (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂} :
    Z.phase (cokernel (Subobject.ofLE A₁ B₁ h₁)) =
    Z.phase (cokernel (Subobject.ofLE A₂ B₂ h₂)) := by
  subst hA; subst hB; rfl

/-- Semistability transfer when `ofLE` subobject arguments are propositionally equal.
This avoids dependent rewriting issues inside `cokernel (Subobject.ofLE ...)`. -/
private lemma isSemistable_cokernel_ofLE_congr (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂}
    (hs : Z.IsSemistable (cokernel (Subobject.ofLE A₂ B₂ h₂))) :
    Z.IsSemistable (cokernel (Subobject.ofLE A₁ B₁ h₁)) := by
  subst hA; subst hB; exact hs

/-- **Proposition 2.4** (Bridgeland): If every object of `A` has a finite subobject
lattice, then any stability function on `A` has the Harder-Narasimhan property.

The hypothesis `Finite (Subobject E)` follows from Artinian + Noetherian for abelian
categories (via modularity of the subobject lattice). We use it directly to find
the maximally destabilizing subobject (MDS).

The proof proceeds by induction on the cardinality of the subobject lattice.
For a nonzero object `E`: if `E` is semistable, it is its own HN filtration;
otherwise we find the MDS `M` (maximal phase, semistable), and recurse on the
quotient `E/M`, which has strictly fewer subobjects. -/
theorem StabilityFunction.hasHN_of_finiteLength (Z : StabilityFunction A)
    (hFinSub : ∀ (E : A), Finite (Subobject E)) :
    Z.HasHNProperty := by
  -- Prove by induction on Nat.card (Subobject E)
  suffices ∀ (k : ℕ) (E : A), ¬IsZero E →
      Nat.card (Subobject E) ≤ k → Nonempty (AbelianHNFiltration Z E) by
    intro E hE; exact this _ E hE le_rfl
  intro k
  induction k with
  | zero =>
    intro E hE hcard
    haveI := hFinSub E
    haveI : Fintype (Subobject E) := Fintype.ofFinite _
    haveI : Nonempty (Subobject E) := ⟨⊥⟩
    have : 0 < Nat.card (Subobject E) := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos
    omega
  | succ k ih =>
    intro E hE hcard
    haveI := hFinSub E
    by_cases hss : Z.IsSemistable E
    · -- E is semistable: single-factor HN filtration
      exact ⟨{
        n := 1
        hn := Nat.one_pos
        chain := fun i ↦ if i = 0 then ⊥ else ⊤
        chain_strictMono := by
          intro ⟨i, hi⟩ ⟨j, hj⟩ h
          simp only [Fin.lt_def] at h
          have hi0 : i = 0 := by omega
          have hj1 : j = 1 := by omega
          subst hi0; subst hj1
          simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ↓reduceIte,
            Fin.mk_one, one_ne_zero, gt_iff_lt]
          exact lt_of_le_of_ne bot_le
            (Ne.symm (subobject_top_ne_bot_of_not_isZero hE))
        chain_bot := by simp
        chain_top := by simp
        φ := fun _ ↦ Z.phase E
        φ_anti := fun a b h ↦ by exfalso; exact absurd h (by omega)
        factor_phase := by
          intro ⟨j, hj⟩
          have hj0 : j = 0 := by omega
          subst hj0
          change Z.phase (cokernel (Subobject.ofLE ⊥ ⊤ _)) = Z.phase E
          rw [Z.phase_eq_of_iso (Subobject.cokernelBotIso ⊤ bot_le)]
          exact Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow)
        factor_semistable := by
          intro ⟨j, hj⟩
          have hj0 : j = 0 := by omega
          subst hj0
          change Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ _))
          exact Z.isSemistable_of_iso
            ((asIso (⊤ : Subobject E).arrow).symm ≪≫
              (Subobject.cokernelBotIso ⊤ bot_le).symm) hss
      }⟩
    · -- E is not semistable: find MDS and recurse on the quotient
      obtain ⟨M', hM'_ne, hM'_max, hM'_strict⟩ :=
        exists_maxPhase_maximal_subobject Z E hE
      have hM'_ss := Z.maxPhase_isSemistable hM'_ne hM'_max
      have hM'_ne_top : M' ≠ ⊤ :=
        Z.maxPhase_ne_top_of_not_semistable hss M' hM'_ne hM'_max
      set Q' := cokernel M'.arrow
      have hQ'_nz : ¬IsZero Q' := cokernel_nonzero_of_ne_top hM'_ne_top
      have hcard_Q' : Nat.card (Subobject Q') < Nat.card (Subobject E) :=
        card_subobject_cokernel_lt hM'_ne
      haveI := hFinSub Q'
      obtain ⟨hn_Q'⟩ := ih Q' hQ'_nz (by omega)
      have hQ'n_pos := hn_Q'.hn
      -- Build the concatenated HN filtration
      set p' := cokernel.π M'.arrow
      set pb' := (Subobject.pullback p').obj
      have hpb_mono : StrictMono pb' :=
        (Subobject.pullback p').monotone.strictMono_of_injective
          (pullback_obj_injective_of_epi p')
      have hpb_bot : pb' (hn_Q'.chain ⟨0, Nat.zero_lt_succ _⟩) = M' := by
        rw [hn_Q'.chain_bot]; exact pullback_cokernel_bot_eq M'
      have hpb_top :
          pb' (hn_Q'.chain ⟨hn_Q'.n, hn_Q'.n.lt_succ_iff.mpr le_rfl⟩) = ⊤ := by
        rw [hn_Q'.chain_top]; exact Subobject.pullback_top p'
      -- Define the new chain: ⊥ at index 0, then pb'(Q'_j) for j = 0..m
      let newChain : Fin (hn_Q'.n + 2) → Subobject E :=
        fun i ↦ if (i : ℕ) = 0 then ⊥
          else pb' (hn_Q'.chain ⟨(i : ℕ) - 1, by omega⟩)
      have hNewBot : newChain ⟨0, by omega⟩ = ⊥ := by simp [newChain]
      have hNewTop : newChain ⟨hn_Q'.n + 1, by omega⟩ = ⊤ := by
        simp only [newChain, show hn_Q'.n + 1 ≠ 0 from by omega, ite_false]
        convert hpb_top using 2
      have hNewMono : StrictMono newChain := by
        apply Fin.strictMono_iff_lt_succ.mpr
        intro ⟨i, hi⟩
        change newChain ⟨i, by omega⟩ < newChain ⟨i + 1, by omega⟩
        by_cases hi0 : i = 0
        · subst hi0
          simp only [newChain, ite_true, show (0 + 1 : ℕ) ≠ 0 from by omega,
            ite_false]
          rw [hpb_bot]
          exact lt_of_le_of_ne bot_le (Ne.symm (subobject_ne_bot_of_not_isZero
            (subobject_not_isZero_of_ne_bot hM'_ne)))
        · simp only [newChain, hi0, ite_false, show i + 1 ≠ 0 from by omega]
          apply hpb_mono
          exact hn_Q'.chain_strictMono (by simp [Fin.lt_def]; omega)
      -- Key fact: all hn_Q' phases are < phase(M')
      have hQ'_phase_lt : ∀ j : Fin hn_Q'.n,
          hn_Q'.φ j < Z.phase (M' : A) := by
        intro j
        have h_ne : hn_Q'.chain ⟨1, by omega⟩ ≠ ⊥ := by
          intro h
          have := hn_Q'.chain_strictMono (Fin.mk_lt_mk.mpr (by omega) :
            (⟨0, by omega⟩ : Fin _) < ⟨1, by omega⟩)
          rw [hn_Q'.chain_bot, h] at this; exact lt_irrefl _ this
        have hsucc_ne :
            hn_Q'.chain (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).succ ≠ ⊥ := by
          intro h; exact lt_irrefl _
            (hn_Q'.chain_bot ▸ h ▸ hn_Q'.chain_strictMono
              (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).castSucc_lt_succ)
        have hcsc : hn_Q'.chain (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).castSucc =
            ⊥ :=
          (congrArg hn_Q'.chain (Fin.ext rfl)).trans hn_Q'.chain_bot
        have h0_lt : hn_Q'.φ ⟨0, hn_Q'.hn⟩ < Z.phase (M' : A) := by
          rw [← hn_Q'.factor_phase ⟨0, hn_Q'.hn⟩]
          have h_eq : Z.phase (cokernel (Subobject.ofLE
              (hn_Q'.chain (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).castSucc)
              (hn_Q'.chain (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).succ)
              (le_of_lt (hn_Q'.chain_strictMono
                (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).castSucc_lt_succ)))) =
            Z.phase ((hn_Q'.chain
              (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).succ : A)) :=
            (phase_cokernel_ofLE_congr Z hcsc rfl).trans
              (Z.phase_eq_of_iso (Subobject.cokernelBotIso _ bot_le))
          linarith [phase_subobject_cokernel_lt Z hM'_ne hM'_strict
            hsucc_ne]
        calc hn_Q'.φ j
            ≤ hn_Q'.φ ⟨0, hn_Q'.hn⟩ :=
              hn_Q'.φ_anti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ < Z.phase (M' : A) := h0_lt
      -- Helper: for j ≥ 1, newChain(castSucc ⟨j,_⟩) = pb'(chain ⟨j-1,_⟩)
      have hNC_cs : ∀ (j : ℕ) (hj : j < hn_Q'.n + 1), j ≠ 0 →
          newChain (Fin.castSucc ⟨j, hj⟩) =
            pb' (hn_Q'.chain ⟨j - 1, by omega⟩) :=
        fun j _ hj0 ↦ if_neg hj0
      -- Helper: newChain(succ ⟨j,_⟩) = pb'(chain ⟨j,_⟩)
      have hNC_s : ∀ (j : ℕ) (hj : j < hn_Q'.n + 1),
          newChain (Fin.succ ⟨j, hj⟩) =
            pb' (hn_Q'.chain ⟨j, by omega⟩) :=
        fun j _ ↦ if_neg (Nat.succ_ne_zero j)
      -- Helper: chain ⟨j,_⟩ = chain(⟨j-1,_⟩.succ) for j ≥ 1
      have hChain_succ : ∀ (j : ℕ) (hj : j < hn_Q'.n + 1),
          j ≠ 0 → hn_Q'.chain ⟨j, by omega⟩ =
            hn_Q'.chain (⟨j - 1, by omega⟩ : Fin hn_Q'.n).succ :=
        fun j _ hj0 ↦ congrArg hn_Q'.chain
          (Fin.ext (show j = (j - 1) + 1 by omega))
      -- Build the AbelianHNFiltration
      refine ⟨{
        n := hn_Q'.n + 1
        hn := Nat.succ_pos _
        chain := newChain
        chain_strictMono := hNewMono
        chain_bot := hNewBot
        chain_top := hNewTop
        φ := fun ⟨j, hj⟩ ↦ if j = 0 then Z.phase (M' : A)
          else hn_Q'.φ ⟨j - 1, by omega⟩
        φ_anti := by
          intro ⟨i, hi⟩ ⟨j, hj⟩ hij
          simp only [Fin.lt_def] at hij
          simp only
          by_cases hi0 : i = 0
          · subst hi0; simp only [ite_true]
            have hj0 : j ≠ 0 := by omega
            simp only [hj0, ite_false]
            calc hn_Q'.φ ⟨j - 1, by omega⟩
                ≤ hn_Q'.φ ⟨0, hn_Q'.hn⟩ :=
                  hn_Q'.φ_anti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
              _ < Z.phase (M' : A) :=
                  hQ'_phase_lt ⟨0, hn_Q'.hn⟩
          · have hj0 : j ≠ 0 := by omega
            simp only [hi0, ite_false, hj0]
            exact hn_Q'.φ_anti (Fin.mk_lt_mk.mpr (by omega))
        factor_phase := ?_
        factor_semistable := ?_ }⟩
      · -- factor_phase
        intro ⟨j, hj⟩
        simp only
        by_cases hj0 : j = 0
        · -- j = 0: factor ≅ M' via cokernelBotIso + hpb_bot
          subst hj0; simp only [ite_true]
          apply Z.phase_eq_of_iso
          exact Subobject.cokernelBotIso _ bot_le ≪≫
            eqToIso (congrArg (Subobject.underlying.obj ·) hpb_bot)
        · -- j ≥ 1: bridge newChain → pb' → chain → factor_phase
          simp only [hj0, ite_false]
          have h_le : hn_Q'.chain ⟨j - 1, by omega⟩ ≤
              hn_Q'.chain ⟨j, by omega⟩ :=
            le_of_lt (hn_Q'.chain_strictMono (Fin.mk_lt_mk.mpr (by omega)))
          exact (phase_cokernel_ofLE_congr Z
              (hNC_cs j hj hj0) (hNC_s j hj)).trans
            ((phase_cokernel_pullback_eq Z M' h_le).trans
            ((phase_cokernel_ofLE_congr Z rfl
              (hChain_succ j hj hj0)).trans
            (hn_Q'.factor_phase ⟨j - 1, by omega⟩)))
      · -- factor_semistable
        intro ⟨j, hj⟩
        by_cases hj0 : j = 0
        · -- j = 0: factor ≅ M' (semistable by hM'_ss)
          subst hj0
          exact Z.isSemistable_of_iso
            ((Subobject.cokernelBotIso _ bot_le ≪≫
              eqToIso (congrArg (Subobject.underlying.obj ·)
                hpb_bot)).symm) hM'_ss
        · -- j ≥ 1: bridge via congr lemmas
          have h_lt : hn_Q'.chain ⟨j - 1, by omega⟩ <
              hn_Q'.chain ⟨j, by omega⟩ :=
            hn_Q'.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
          exact isSemistable_cokernel_ofLE_congr Z
            (hNC_cs j hj hj0) (hNC_s j hj)
            (Z.isSemistable_of_iso (cokernelPullbackIso Z M' h_lt).symm
              (isSemistable_cokernel_ofLE_congr Z rfl
                (hChain_succ j hj hj0)
                (hn_Q'.factor_semistable ⟨j - 1, by omega⟩)))

/-- For a semistable object `E`, every nonzero epi quotient has phase `≥ phase(E)`.
This uses the phase see-saw and the semistability condition. -/
private lemma phase_le_of_epi (Z : StabilityFunction A)
    {E Q : A} (p : E ⟶ Q) [Epi p] (hss : Z.IsSemistable E) (hQ : ¬IsZero Q) :
    Z.phase E ≤ Z.phase Q := by
  by_cases hker : IsZero (kernel p)
  · haveI : Mono p := Preadditive.mono_of_kernel_zero
      (zero_of_source_iso_zero _ hker.isoZero)
    haveI := isIso_of_mono_of_epi p
    exact le_of_eq (Z.phase_eq_of_iso (asIso p))
  · -- K → E → Q short exact, K = kernel p
    have hK_sub : Z.phase (kernel p) ≤ Z.phase E := by
      calc Z.phase (kernel p)
          = Z.phase (kernelSubobject p : A) :=
            Z.phase_eq_of_iso (kernelSubobjectIso p).symm
        _ ≤ Z.phase E := by
            apply hss.2
            intro hZ
            exact hker (hZ.of_iso (kernelSubobjectIso p).symm)
    by_contra hlt
    push_neg at hlt
    have hadd : Z.Zobj E = Z.Zobj (kernel p) + Z.Zobj Q :=
      Z.additive _
        (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance)
    have hK_mem := Z.upper (kernel p) hker
    have hQ_mem := Z.upper Q hQ
    -- Convert phase inequalities to arg inequalities
    have pi_pos := Real.pi_pos
    have hargK : arg (Z.Zobj (kernel p)) ≤ arg (Z.Zobj E) := by
      unfold StabilityFunction.phase at hK_sub
      exact le_of_mul_le_mul_left (by linarith) (div_pos one_pos pi_pos)
    have hargQ : arg (Z.Zobj Q) < arg (Z.Zobj E) := by
      unfold StabilityFunction.phase at hlt
      exact lt_of_mul_lt_mul_left (by linarith) (div_pos one_pos pi_pos).le
    rw [hadd] at hargK hargQ
    -- hargK : arg(Z(K)) ≤ arg(Z(K)+Z(Q))
    -- hargQ : arg(Z(Q)) < arg(Z(K)+Z(Q))
    have hub := arg_add_le_max hK_mem hQ_mem
    -- hub : arg(Z(K)+Z(Q)) ≤ max(arg(Z(K)), arg(Z(Q)))
    -- From hargQ and hub: arg(Z(Q)) < max(arg(Z(K)), arg(Z(Q)))
    have hQ_lt_max : arg (Z.Zobj Q) < max (arg (Z.Zobj (kernel p))) (arg (Z.Zobj Q)) :=
      lt_of_lt_of_le hargQ hub
    have hK_gt_Q : arg (Z.Zobj Q) < arg (Z.Zobj (kernel p)) := by
      rcases lt_max_iff.mp hQ_lt_max with h | h
      · exact h
      · exact absurd h (lt_irrefl _)
    have hne : arg (Z.Zobj (kernel p)) ≠ arg (Z.Zobj Q) := ne_of_gt hK_gt_Q
    have hstrict := arg_add_lt_max hK_mem hQ_mem hne
    rw [max_eq_left hK_gt_Q.le] at hstrict
    linarith

/-- Hom-vanishing between semistable objects of different phases: if `E` is semistable
with `phase(E) > phase(F)` and `F` is semistable, then every morphism `E → F` is zero. -/
private lemma hom_zero_of_semistable_phase_gt (Z : StabilityFunction A)
    {E F : A} (hE : Z.IsSemistable E) (hF : Z.IsSemistable F)
    (hph : Z.phase F < Z.phase E) (f : E ⟶ F) : f = 0 := by
  by_contra hf
  have hI : ¬IsZero (Limits.image f) := by
    intro hZ
    apply hf
    have : Limits.image.ι f = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rw [← Limits.image.fac f, this, comp_zero]
  have hge := phase_le_of_epi Z (factorThruImage f) hE hI
  have hle : Z.phase (Limits.image f) ≤ Z.phase F := by
    calc Z.phase (Limits.image f)
        = Z.phase (imageSubobject f : A) :=
          Z.phase_eq_of_iso (imageSubobjectIso f).symm
      _ ≤ Z.phase F := by
          apply hF.2
          intro hZ
          exact hI (hZ.of_iso (imageSubobjectIso f).symm)
  linarith

/-- If `E` is semistable and has an HN filtration, the filtration has exactly one factor. -/
private lemma hn_n_eq_one_of_semistable (Z : StabilityFunction A) {E : A}
    (hss : Z.IsSemistable E) (F : AbelianHNFiltration Z E) :
    F.n = 1 := by
  by_contra hn1
  have hhn := F.hn
  have hn_ge : 1 < F.n := by omega
  -- chain(1) is nonzero (since chain is strict mono and chain(0) = ⊥ < chain(1))
  have hchain1_ne_bot : F.chain ⟨1, by omega⟩ ≠ ⊥ := by
    intro heq
    have h01 : F.chain ⟨0, by omega⟩ < F.chain ⟨1, by omega⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
    rw [F.chain_bot, heq] at h01
    exact lt_irrefl _ h01
  -- chain(0) as Fin F.n .castSucc = ⊥
  have h0_eq : F.chain (⟨0, F.hn⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by omega⟩ = ⊥
    exact F.chain_bot
  -- chain(1) = (⟨0, F.hn⟩ : Fin F.n).succ
  have h1_eq : (⟨0, F.hn⟩ : Fin F.n).succ = ⟨1, by omega⟩ := rfl
  -- phase(chain(1)) = φ(0)
  have hchain1_phase : Z.phase (F.chain ⟨1, by omega⟩ : A) = F.φ ⟨0, F.hn⟩ := by
    rw [← F.factor_phase ⟨0, F.hn⟩]
    have hsucc_eq : F.chain (⟨0, F.hn⟩ : Fin F.n).succ = F.chain ⟨1, by omega⟩ := by
      rw [h1_eq]
    exact ((phase_cokernel_ofLE_congr Z h0_eq hsucc_eq).trans
      (Z.phase_eq_of_iso
        (StabilityFunction.Subobject.cokernelBotIso (F.chain ⟨1, by omega⟩) bot_le))).symm
  -- By semistability: φ(0) ≤ phase(E)
  have hφ0_le : F.φ ⟨0, F.hn⟩ ≤ Z.phase E := by
    rw [← hchain1_phase]
    exact hss.2 _ (StabilityFunction.subobject_not_isZero_of_ne_bot hchain1_ne_bot)
  -- chain(n-1) ≠ ⊤ since chain(n-1) < chain(n) = ⊤
  have hchain_ne_top : F.chain ⟨F.n - 1, by omega⟩ ≠ ⊤ := by
    intro heq
    have hlt : F.chain ⟨F.n - 1, by omega⟩ < F.chain ⟨F.n, by omega⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
    rw [heq, F.chain_top] at hlt
    exact lt_irrefl _ hlt
  -- The last Fin n index
  set last : Fin F.n := ⟨F.n - 1, by omega⟩
  -- chain(last.succ) = chain(n) = ⊤
  have hchain_top' : F.chain last.succ = ⊤ := by
    have : last.succ = ⟨F.n, by omega⟩ := Fin.ext (show last.val + 1 = F.n by
      simp only [last]; omega)
    rw [this, F.chain_top]
  -- phase of cokernel of chain(n-1).arrow = φ(last)
  -- phase(E) ≤ φ(last): use phase_le_of_epi on the quotient map, then relate to factor_phase
  have hE_le_last : Z.phase E ≤ F.φ last := by
    have hle := phase_le_of_epi Z (cokernel.π (F.chain ⟨F.n - 1, by omega⟩).arrow) hss
      (cokernel_nonzero_of_ne_top hchain_ne_top)
    suffices Z.phase (cokernel (F.chain ⟨F.n - 1, by omega⟩).arrow) = F.φ last by linarith
    -- factor_phase last : phase(cokernel(ofLE chain(last.castSucc) chain(last.succ) _)) = φ last
    -- We need: phase(cokernel(chain(n-1).arrow)) = phase(cokernel(ofLE ...))
    -- Strategy: use phase_cokernel_ofLE_congr to normalize both sides
    -- then use cokernelBotIso-style argument
    -- Step 1: chain(n-1).arrow = ofLE chain(n-1) ⊤ le_top ≫ ⊤.arrow (by ofLE_arrow)
    -- Step 2: cokernel(chain(n-1).arrow) ≅ cokernel(ofLE chain(n-1) ⊤ le_top)
    --   (by cokernelCompIsIso)
    -- Step 3: cokernel(ofLE chain(n-1) ⊤ _) has same phase as cokernel(ofLE ... chain(last.succ) _)
    --         by phase_cokernel_ofLE_congr Z rfl hchain_top'.symm
    set S := F.chain ⟨F.n - 1, by omega⟩
    haveI : IsIso (⊤ : Subobject E).arrow := inferInstance
    calc Z.phase (cokernel S.arrow)
        = Z.phase (cokernel (Subobject.ofLE S ⊤ le_top)) :=
          Z.phase_eq_of_iso
            (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _)
      _ = Z.phase (cokernel (Subobject.ofLE (F.chain last.castSucc) (F.chain last.succ)
            (le_of_lt (F.chain_strictMono last.castSucc_lt_succ)))) :=
          phase_cokernel_ofLE_congr Z rfl hchain_top'.symm
      _ = F.φ last := F.factor_phase last
  -- But φ(last) < φ(0) since last > 0 and φ is strictly anti
  have hφ_lt : F.φ last < F.φ ⟨0, F.hn⟩ :=
    F.φ_anti (Fin.mk_lt_mk.mpr (by omega))
  linarith

/-- If `B.arrow ≫ cokernel.π M.arrow = 0`, then `B ≤ M` as subobjects of `E`. -/
private lemma le_of_comp_cokernel_zero {E : A} {B M : Subobject E}
    (h : B.arrow ≫ cokernel.π M.arrow = 0) : B ≤ M := by
  have hker : kernelSubobject (cokernel.π M.arrow) = M := by
    have := (ShortComplex.mk M.arrow (cokernel.π M.arrow)
      (cokernel.condition M.arrow)).exact_iff_image_eq_kernel.mp
      (ShortComplex.exact_cokernel M.arrow)
    rw [imageSubobject_mono, Subobject.mk_arrow] at this; exact this.symm
  rw [← hker]
  exact Subobject.le_of_comm
    (factorThruKernelSubobject _ B.arrow h)
    (factorThruKernelSubobject_comp_arrow _ _ _)

/-- If the composition `ofLE B S _ ≫ cokernel.π (ofLE M S _) = 0`, then `B ≤ M`. -/
private lemma le_of_ofLE_comp_cokernel_zero {E : A} {B M S : Subobject E}
    (hBS : B ≤ S) (hMS : M ≤ S)
    (h : Subobject.ofLE B S hBS ≫
      cokernel.π (Subobject.ofLE M S hMS) = 0) : B ≤ M := by
  -- The SES M →(ofLE)→ S →(cokernel.π)→ cokernel gives a kernel fork
  have hse : (ShortComplex.mk (Subobject.ofLE M S hMS)
      (cokernel.π (Subobject.ofLE M S hMS))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  -- Lift ofLE B S through the kernel fork
  set g := hse.fIsKernel.lift (KernelFork.ofι (Subobject.ofLE B S hBS) h)
  have hg : g ≫ Subobject.ofLE M S hMS = Subobject.ofLE B S hBS :=
    hse.fIsKernel.fac (KernelFork.ofι (Subobject.ofLE B S hBS) h) WalkingParallelPair.zero
  -- Compose with S.arrow: g ≫ M.arrow = B.arrow
  have key : g ≫ M.arrow = B.arrow :=
    calc g ≫ M.arrow
        = g ≫ (Subobject.ofLE M S hMS ≫ S.arrow) := by
          congr 1; exact (Subobject.ofLE_arrow hMS).symm
      _ = (g ≫ Subobject.ofLE M S hMS) ≫ S.arrow :=
          (Category.assoc _ _ _).symm
      _ = Subobject.ofLE B S hBS ≫ S.arrow := by congr 1
      _ = B.arrow := Subobject.ofLE_arrow hBS
  exact Subobject.le_of_comm g key

/-- Hom-vanishing from a semistable object to an HN factor: if `B` is semistable
with `phase(B) > φ(j)`, then every morphism from `(B : A)` to the `j`-th factor
of the HN filtration is zero. Direct corollary of `hom_zero_of_semistable_phase_gt`. -/
private lemma hom_zero_to_factor {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : A} (hB : Z.IsSemistable B)
    (j : Fin F.n) (hph : F.φ j < Z.phase B)
    (f : B ⟶ cokernel (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
      (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))) : f = 0 :=
  hom_zero_of_semistable_phase_gt Z hB (F.factor_semistable j)
    (F.factor_phase j ▸ hph) f

/-- **Semistable descent lemma**: A semistable subobject `B` of `E` whose phase
exceeds `φ(j)` for all `j ≥ k` must satisfy `B ≤ chain(k)`. The proof descends
from `chain(n) = ⊤` using hom-vanishing to each factor. -/
private lemma semistable_le_chain_of_phase_gt {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E} (hB : Z.IsSemistable (B : A))
    {k : ℕ} (hk : k ≤ F.n)
    (hph : ∀ j : Fin F.n, k ≤ j.val → F.φ j < Z.phase (B : A)) :
    B ≤ F.chain ⟨k, by omega⟩ := by
  -- Descend from chain(n) = ⊤ to chain(k), one step at a time.
  -- Induct on d = F.n - k.
  suffices h : ∀ d m (hm : m < F.n + 1), F.n - m = d → k ≤ m →
      B ≤ F.chain ⟨m, hm⟩ from
    h (F.n - k) k (by omega) rfl le_rfl
  intro d
  induction d with
  | zero =>
    intro m hm hd hkm
    have hmn : m = F.n := by omega
    subst hmn; rw [F.chain_top]; exact le_top
  | succ d ih =>
    intro m hm hd hkm
    -- B ≤ chain(m+1) by IH
    have hstep : B ≤ F.chain ⟨m + 1, by omega⟩ :=
      ih (m + 1) (by omega) (by omega) (by omega)
    -- Factor at index m: semistable with phase φ(m) < phase(B)
    have hm_lt : m < F.n := by omega
    set j : Fin F.n := ⟨m, hm_lt⟩
    have hj_succ_eq : (j.succ : Fin (F.n + 1)) = ⟨m + 1, by omega⟩ :=
      Fin.ext (by simp [j])
    have hle_jsucc : B ≤ F.chain j.succ := hj_succ_eq ▸ hstep
    have hcomp : Subobject.ofLE B (F.chain j.succ) hle_jsucc ≫
        cokernel.π (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
          (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))) = 0 :=
      hom_zero_of_semistable_phase_gt Z hB (F.factor_semistable j)
        (F.factor_phase j ▸ hph j (by omega)) _
    exact le_of_ofLE_comp_cokernel_zero hle_jsucc
      (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) hcomp

/-- **Semistable descent**: A semistable subobject whose phase exceeds all HN phases
must be zero. Specifically, if `phase(B) > φ(0)`, then `B = ⊥`. -/
private lemma semistable_eq_bot_of_phase_gt_max {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E} (hB : Z.IsSemistable (B : A))
    (hph : F.φ ⟨0, F.hn⟩ < Z.phase (B : A)) : B = ⊥ := by
  have hle : B ≤ F.chain ⟨0, by omega⟩ :=
    semistable_le_chain_of_phase_gt F hB (Nat.zero_le _)
      (fun j _ ↦ lt_of_le_of_lt (F.φ_anti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hph)
  rw [F.chain_bot] at hle
  exact le_bot_iff.mp hle



/-- If `f` is epi, then `imageSubobject f = ⊤`. -/
private lemma imageSubobject_epi_eq_top {X Y : A} (f : X ⟶ Y) [Epi f] :
    imageSubobject f = ⊤ := by
  haveI : Epi (imageSubobject f).arrow :=
    epi_of_epi_fac (imageSubobject_arrow_comp f)
  haveI : IsIso (imageSubobject f).arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

/-- The phase of `chain(1)` in an HN filtration equals `φ(0)`. -/
private lemma chain_one_phase {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn2 : 2 ≤ F.n) :
    Z.phase (F.chain ⟨1, by omega⟩ : A) = F.φ ⟨0, F.hn⟩ := by
  rw [← F.factor_phase ⟨0, F.hn⟩]
  exact ((phase_cokernel_ofLE_congr Z F.chain_bot rfl).trans
    (Z.phase_eq_of_iso
      (StabilityFunction.Subobject.cokernelBotIso (F.chain ⟨1, by omega⟩) bot_le))).symm

/-- In an HN filtration with `n ≥ 2`, `chain(1)` equals the maximally destabilizing
subobject (MDS). -/
private lemma chain_one_eq_MDS {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn2 : 2 ≤ F.n)
    {M : Subobject E} (hM_ne : M ≠ ⊥) (hM_ss : Z.IsSemistable (M : A))
    (hM_max : ∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A))
    (hM_strict : ∀ B : Subobject E, M < B → Z.phase (B : A) < Z.phase (M : A)) :
    F.chain ⟨1, by omega⟩ = M := by
  have hchain1_ne : F.chain ⟨1, by omega⟩ ≠ ⊥ := by
    intro h
    have := F.chain_strictMono (show (⟨0, by omega⟩ : Fin (F.n + 1)) <
      ⟨1, by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
    rw [F.chain_bot, h] at this
    exact lt_irrefl _ this
  have hphM : ∀ j : Fin F.n, 1 ≤ j.val → F.φ j < Z.phase (M : A) := by
    intro j hj
    calc F.φ j
        ≤ F.φ (⟨1, by omega⟩ : Fin F.n) :=
          F.φ_anti.antitone (Fin.mk_le_mk.mpr hj)
      _ < F.φ (⟨0, F.hn⟩ : Fin F.n) :=
          F.φ_anti (Fin.mk_lt_mk.mpr (by omega))
      _ = Z.phase (F.chain ⟨1, by omega⟩ : A) :=
          (chain_one_phase F hn2).symm
      _ ≤ Z.phase (M : A) := hM_max _ hchain1_ne
  -- M ≤ chain(1) via semistable descent
  have hM_le : M ≤ F.chain ⟨1, by omega⟩ :=
    semistable_le_chain_of_phase_gt F hM_ss (by omega) hphM
  -- chain(1) ≤ M: if M < chain(1), then phase(chain(1)) < phase(M), so φ(0) < phase(M),
  -- then semistable_eq_bot_of_phase_gt_max gives M = ⊥, contradiction
  rcases hM_le.eq_or_lt with h | hlt
  · exact h.symm
  · exfalso
    have hlt_phase := hM_strict _ hlt
    rw [chain_one_phase F hn2] at hlt_phase
    exact hM_ne (semistable_eq_bot_of_phase_gt_max F hM_ss hlt_phase)

/-- For `M ≤ S` as subobjects of `E`, the pullback of `imageSubobject(S.arrow ≫ p)` along
`p = cokernel.π M.arrow` equals `S`. Uses the Z-value trick: `Z(pb(I)) = Z(S)` forces
the cokernel of the inclusion `S ↪ pb(I)` to be zero. -/
private lemma pullback_imageSubobject_eq (Z : StabilityFunction A) {E : A}
    {M S : Subobject E} (hMS : M ≤ S) :
    (Subobject.pullback (cokernel.π M.arrow)).obj
      (imageSubobject (S.arrow ≫ cokernel.π M.arrow)) = S := by
  set p := cokernel.π M.arrow
  set I := imageSubobject (S.arrow ≫ p)
  set pbI := (Subobject.pullback p).obj I
  -- S ≤ pb(I) via the pullback universal property
  have hle : S ≤ pbI := Subobject.le_of_comm
    ((Subobject.isPullback p I).isLimit.lift
      (PullbackCone.mk (factorThruImageSubobject (S.arrow ≫ p)) S.arrow
        (imageSubobject_arrow_comp (f := S.arrow ≫ p))))
    ((Subobject.isPullback p I).isLimit.fac _ WalkingCospan.right)
  -- Z(pb(I)) = Z(M) + Z(I) from pullback SES
  have hZ_pb := Zobj_pullback_eq_add Z M I
  -- Z(S) = Z(M) + Z(cokernel(ofLE M S)) from SES M → S → S/M
  have hZ_S := Z.additive _
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (Subobject.ofLE M S hMS))
      inferInstance inferInstance)
  -- Z(I) = Z(S/M): both sides equal Z(S) - Z(M)
  -- First, show Z(I) = Z(cokernel(ofLE M S)) via the canonical iso
  have hZ_I : Z.Zobj (I : A) = Z.Zobj (cokernel (Subobject.ofLE M S hMS)) := by
    -- Use the first isomorphism theorem: image(f) ≅ coimage(f) = cokernel(kernel.ι f)
    -- and kernel(f) ≅ (M : A), where f = S.arrow ≫ p
    -- Step 1: SES kernel(f) → (S : A) → cokernel(kernel.ι f) gives Z-additivity
    have hZ_ses := Z.additive _ (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (kernel.ι (S.arrow ≫ p))) inferInstance inferInstance)
    -- Step 2: Build iso kernel(S.arrow ≫ p) ≅ (M : A)
    have h_cond : Subobject.ofLE M S hMS ≫ (S.arrow ≫ p) = 0 := by
      rw [← Category.assoc, Subobject.ofLE_arrow]; exact cokernel.condition M.arrow
    have h_kerfact : (kernel.ι (S.arrow ≫ p) ≫ S.arrow) ≫ cokernel.π M.arrow = 0 := by
      rw [Category.assoc]; exact kernel.condition (S.arrow ≫ p)
    set k := kernel.lift (S.arrow ≫ p) (Subobject.ofLE M S hMS) h_cond
    set l := Abelian.monoLift M.arrow (kernel.ι (S.arrow ≫ p) ≫ S.arrow) h_kerfact
    have hk : k ≫ kernel.ι (S.arrow ≫ p) = Subobject.ofLE M S hMS := kernel.lift_ι _ _ _
    have hl : l ≫ M.arrow = kernel.ι (S.arrow ≫ p) ≫ S.arrow := Abelian.monoLift_comp _ _ _
    have hkl : k ≫ l = 𝟙 _ := by
      apply (cancel_mono M.arrow).mp
      rw [Category.assoc, hl, ← Category.assoc, hk, Subobject.ofLE_arrow, Category.id_comp]
    have hlk : l ≫ k = 𝟙 _ := by
      apply (cancel_mono (kernel.ι (S.arrow ≫ p))).mp
      rw [Category.assoc, hk, Category.id_comp]
      apply (cancel_mono S.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow, hl]
    have hZ_ker : Z.Zobj (M : A) = Z.Zobj (kernel (S.arrow ≫ p)) :=
      Z.Zobj_eq_of_iso ⟨k, l, hkl, hlk⟩
    -- Step 3: Z(coimage f) = Z(image f), Z(imageSubobject f) = Z(image f)
    have hZ_coim := Z.Zobj_eq_of_iso (Abelian.coimageIsoImage' (S.arrow ≫ p))
    have hZ_im := Z.Zobj_eq_of_iso (imageSubobjectIso (S.arrow ≫ p))
    -- Step 4: Combine: Z(I) = Z(image) = Z(coimage) = Z(S) - Z(kernel) = Z(S) - Z(M)
    rw [← hZ_ker] at hZ_ses
    exact (hZ_im.trans hZ_coim.symm).trans (add_left_cancel (hZ_ses.symm.trans hZ_S))
  -- Conclude Z(pb(I)) = Z(S)
  have hZ_eq : Z.Zobj (pbI : A) = Z.Zobj (S : A) := by
    have h : Z.Zobj (S : A) = Z.Zobj (M : A) +
        Z.Zobj (cokernel (Subobject.ofLE M S hMS)) := hZ_S
    rw [hZ_pb, hZ_I]; exact h.symm
  -- Z-value trick: cokernel of S ↪ pb(I) has Z = 0, hence is zero
  rcases hle.eq_or_lt with h | hlt
  · exact h.symm
  · exfalso
    have hse := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE S pbI hle)) inferInstance inferInstance
    have hZ_add := Z.additive _ hse
    have hZ_cok : Z.Zobj (cokernel (Subobject.ofLE S pbI hle)) = 0 := by
      have h : Z.Zobj (pbI : A) = Z.Zobj (S : A) +
          Z.Zobj (cokernel (Subobject.ofLE S pbI hle)) := hZ_add
      have h2 : Z.Zobj (S : A) + 0 = Z.Zobj (S : A) +
          Z.Zobj (cokernel (Subobject.ofLE S pbI hle)) := by
        rw [add_zero]; exact hZ_eq.symm.trans h
      exact (add_left_cancel h2).symm
    have hcok_nz : ¬IsZero (cokernel (Subobject.ofLE S pbI hle)) := by
      intro hZ
      haveI : Epi (Subobject.ofLE S pbI hle) :=
        Preadditive.epi_of_isZero_cokernel _ hZ
      haveI := isIso_of_mono_of_epi (Subobject.ofLE S pbI hle)
      exact absurd (Subobject.eq_of_comm (asIso (Subobject.ofLE S pbI hle))
        (Subobject.ofLE_arrow hle)) (ne_of_lt hlt)
    exact absurd hZ_cok (ne_of_mem_of_not_mem (Z.upper _ hcok_nz)
      (show (0 : ℂ) ∉ upperHalfPlaneUnion from fun hc ↦ by
        rcases hc with hc | ⟨_, hc⟩ <;> simp at hc))

/-- If `E` is not semistable, any HN filtration of `E` has at least 2 factors. -/
private lemma n_ge_two_of_not_semistable {Z : StabilityFunction A} {E : A}
    (hns : ¬Z.IsSemistable E) (F : AbelianHNFiltration Z E) : 2 ≤ F.n := by
  by_contra hlt
  simp only [not_le] at hlt
  have hn1 : F.n = 1 := by have := F.hn; omega
  suffices Z.IsSemistable E from hns this
  have hss := F.factor_semistable ⟨0, F.hn⟩
  have h_bot : F.chain (⟨0, F.hn⟩ : Fin F.n).castSucc = ⊥ :=
    (congrArg F.chain (Fin.ext rfl)).trans F.chain_bot
  have h_top : F.chain (⟨0, F.hn⟩ : Fin F.n).succ = ⊤ := by
    have : (⟨0, F.hn⟩ : Fin F.n).succ = ⟨F.n, lt_add_one F.n⟩ :=
      Fin.ext (by simp; omega)
    rw [this, F.chain_top]
  -- Transfer semistability: factor ≅ cokernel(ofLE ⊥ ⊤) ≅ (⊤ : A) ≅ E
  have h1 : Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ bot_le)) :=
    isSemistable_cokernel_ofLE_congr Z h_bot.symm h_top.symm hss
  exact Z.isSemistable_of_iso
    (StabilityFunction.Subobject.cokernelBotIso ⊤ bot_le ≪≫
      asIso (⊤ : Subobject E).arrow) h1

set_option maxHeartbeats 1600000 in
-- The proof involves many Fin-indexed compositions; the default heartbeat limit is insufficient.
/-- The tail HN filtration of the quotient `E / chain(1)`, constructed by pushing
the chain forward via `imageSubobject(_.arrow ≫ cokernel.π chain(1).arrow)`. -/
private noncomputable def tailHNFiltration {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn2 : 2 ≤ F.n) :
    AbelianHNFiltration Z (cokernel (F.chain ⟨1, by omega⟩).arrow) where
  n := F.n - 1
  hn := by omega
  chain := fun ⟨j, _⟩ ↦ imageSubobject
    ((F.chain ⟨j + 1, by omega⟩).arrow ≫ cokernel.π (F.chain ⟨1, by omega⟩).arrow)
  chain_strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    change imageSubobject ((F.chain ⟨j + 1, by omega⟩).arrow ≫
        cokernel.π (F.chain ⟨1, by omega⟩).arrow) <
      imageSubobject ((F.chain ⟨j + 2, by omega⟩).arrow ≫
        cokernel.π (F.chain ⟨1, by omega⟩).arrow)
    have hM1 : F.chain ⟨1, by omega⟩ ≤ F.chain ⟨j + 1, by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    have hM2 : F.chain ⟨1, by omega⟩ ≤ F.chain ⟨j + 2, by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    have hS₁S₂ : F.chain ⟨j + 1, by omega⟩ < F.chain ⟨j + 2, by omega⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
    have h_le : imageSubobject ((F.chain ⟨j + 1, by omega⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by omega⟩).arrow) ≤
        imageSubobject ((F.chain ⟨j + 2, by omega⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by omega⟩).arrow) := by
      rw [show (F.chain ⟨j + 1, by omega⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by omega⟩).arrow =
          Subobject.ofLE _ _ hS₁S₂.le ≫ ((F.chain ⟨j + 2, by omega⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by omega⟩).arrow) from
        by rw [← Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_comp_le _ _
    exact lt_of_le_of_ne h_le (fun heq ↦ absurd
      ((pullback_imageSubobject_eq Z hM1).symm.trans
        (heq ▸ pullback_imageSubobject_eq Z hM2))
      (ne_of_lt hS₁S₂))
  chain_bot := by
    change imageSubobject ((F.chain ⟨1, by omega⟩).arrow ≫
      cokernel.π (F.chain ⟨1, by omega⟩).arrow) = ⊥
    rw [cokernel.condition, imageSubobject_zero]
  chain_top := by
    change imageSubobject ((F.chain ⟨F.n - 1 + 1, by omega⟩).arrow ≫
      cokernel.π (F.chain ⟨1, by omega⟩).arrow) = ⊤
    have htop : F.chain ⟨F.n - 1 + 1, by omega⟩ = ⊤ :=
      (congrArg F.chain (Fin.ext (Nat.sub_add_cancel (by omega)))).trans
        F.chain_top
    rw [htop]
    haveI : IsIso (⊤ : Subobject E).arrow := inferInstance
    rw [imageSubobject_iso_comp]
    exact imageSubobject_epi_eq_top _
  φ := fun ⟨j, _⟩ ↦ F.φ ⟨j + 1, by omega⟩
  φ_anti := by
    intro ⟨j₁, _⟩ ⟨j₂, _⟩ h
    simp only [Fin.lt_def] at h
    exact F.φ_anti (Fin.mk_lt_mk.mpr (by omega))
  factor_phase := by
    intro ⟨j, _⟩
    have hM1 : F.chain ⟨1, by omega⟩ ≤ F.chain ⟨j + 1, by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    have hM2 : F.chain ⟨1, by omega⟩ ≤ F.chain ⟨j + 2, by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    exact ((phase_cokernel_pullback_eq Z (F.chain ⟨1, by omega⟩) _).symm.trans
      ((phase_cokernel_ofLE_congr Z
        (pullback_imageSubobject_eq Z hM1)
        (pullback_imageSubobject_eq Z hM2)).trans
      (F.factor_phase ⟨j + 1, by omega⟩)))
  factor_semistable := by
    intro ⟨j, hj⟩
    have hM1 : F.chain ⟨1, by omega⟩ ≤ F.chain ⟨j + 1, by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    have hM2 : F.chain ⟨1, by omega⟩ ≤ F.chain ⟨j + 2, by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    have hlt : imageSubobject ((F.chain ⟨j + 1, by omega⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by omega⟩).arrow) <
        imageSubobject ((F.chain ⟨j + 2, by omega⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by omega⟩).arrow) := by
      have hS₁S₂ : F.chain ⟨j + 1, by omega⟩ < F.chain ⟨j + 2, by omega⟩ :=
        F.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
      have h_le : imageSubobject ((F.chain ⟨j + 1, by omega⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by omega⟩).arrow) ≤
          imageSubobject ((F.chain ⟨j + 2, by omega⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by omega⟩).arrow) := by
        rw [show (F.chain ⟨j + 1, by omega⟩).arrow ≫
              cokernel.π (F.chain ⟨1, by omega⟩).arrow =
            Subobject.ofLE _ _ hS₁S₂.le ≫ ((F.chain ⟨j + 2, by omega⟩).arrow ≫
              cokernel.π (F.chain ⟨1, by omega⟩).arrow) from
          by rw [← Category.assoc, Subobject.ofLE_arrow]]
        exact imageSubobject_comp_le _ _
      exact lt_of_le_of_ne h_le (fun heq ↦ absurd
        ((pullback_imageSubobject_eq Z hM1).symm.trans
          (heq ▸ pullback_imageSubobject_eq Z hM2))
        (ne_of_lt hS₁S₂))
    exact Z.isSemistable_of_iso
      (cokernelPullbackIso Z (F.chain ⟨1, by omega⟩) hlt)
      (isSemistable_cokernel_ofLE_congr Z
        (pullback_imageSubobject_eq Z hM1)
        (pullback_imageSubobject_eq Z hM2)
        (F.factor_semistable ⟨j + 1, by omega⟩))

/-- Transporting an HN filtration along an equality preserves `.n`. -/
private lemma transport_n {Z : StabilityFunction A} {Q₁ Q₂ : A}
    (h : Q₁ = Q₂) (F : AbelianHNFiltration Z Q₁) :
    (h ▸ F).n = F.n := by subst h; rfl

/-- **Proposition 2.3** (Bridgeland): HN filtrations are essentially unique.
When all objects have finite subobject lattices, any two HN filtrations of the
same object have the same number of semistable factors.

The proof shows that `chain(1)` of any HN filtration equals the maximally
destabilizing subobject (MDS), which is intrinsic to the object. The key step
is the semistable descent lemma: any semistable subobject with phase `> φ(0)`
must be zero (by hom-vanishing to each factor). This forces the MDS phase to
equal `φ(0)`, and the MDS to equal `chain(1)`. We then quotient and induct. -/
theorem StabilityFunction.hn_unique (Z : StabilityFunction A) (E : A) (hE : ¬IsZero E)
    (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F₁ F₂ : AbelianHNFiltration Z E) :
    F₁.n = F₂.n := by
  suffices ∀ (k : ℕ) (E : A), ¬IsZero E →
      Nat.card (Subobject E) ≤ k →
      ∀ G₁ G₂ : AbelianHNFiltration Z E, G₁.n = G₂.n by
    exact this _ E hE le_rfl F₁ F₂
  intro k
  induction k with
  | zero =>
    intro E hE hcard
    haveI := hFinSub E
    haveI := Fintype.ofFinite (Subobject E)
    have : 0 < Nat.card (Subobject E) := by
      rw [Nat.card_eq_fintype_card]
      haveI : Nonempty (Subobject E) := ⟨⊥⟩
      exact Fintype.card_pos
    omega
  | succ k ih =>
    intro E hE hcard G₁ G₂
    haveI := hFinSub E
    by_cases hss : Z.IsSemistable E
    · exact (hn_n_eq_one_of_semistable Z hss G₁).trans
        (hn_n_eq_one_of_semistable Z hss G₂).symm
    · -- E not semistable: both filtrations have n ≥ 2
      have hn1 : 2 ≤ G₁.n := n_ge_two_of_not_semistable hss G₁
      have hn2 : 2 ≤ G₂.n := n_ge_two_of_not_semistable hss G₂
      -- Get maximally destabilizing subobject (MDS)
      obtain ⟨M, hM_ne, hM_max, hM_strict⟩ :=
        exists_maxPhase_maximal_subobject Z E hE
      have hM_ss := Z.maxPhase_isSemistable hM_ne hM_max
      have hM_ne_top :=
        Z.maxPhase_ne_top_of_not_semistable hss M hM_ne hM_max
      -- chain(1) = M for both filtrations
      have hc1 : G₁.chain ⟨1, by omega⟩ = M :=
        chain_one_eq_MDS G₁ hn1 hM_ne hM_ss hM_max hM_strict
      have hc2 : G₂.chain ⟨1, by omega⟩ = M :=
        chain_one_eq_MDS G₂ hn2 hM_ne hM_ss hM_max hM_strict
      -- Quotient Q = E/M has strictly fewer subobjects
      have hcard_Q : Nat.card (Subobject (cokernel M.arrow)) <
          Nat.card (Subobject E) :=
        card_subobject_cokernel_lt hM_ne
      -- Transport tail filtrations to cokernel M.arrow
      have hQ₁ : cokernel (G₁.chain ⟨1, by omega⟩).arrow =
          cokernel M.arrow :=
        congrArg (fun S ↦ cokernel (Subobject.arrow S)) hc1
      have hQ₂ : cokernel (G₂.chain ⟨1, by omega⟩).arrow =
          cokernel M.arrow :=
        congrArg (fun S ↦ cokernel (Subobject.arrow S)) hc2
      -- Apply IH: tail filtrations on Q have the same length
      have h_eq : (hQ₁ ▸ tailHNFiltration G₁ hn1).n =
          (hQ₂ ▸ tailHNFiltration G₂ hn2).n :=
        ih (cokernel M.arrow)
          (cokernel_nonzero_of_ne_top hM_ne_top)
          (by omega) _ _
      simp only [transport_n] at h_eq
      change G₁.n - 1 = G₂.n - 1 at h_eq
      omega

/-- The highest phase `φ(0)` of an HN filtration equals the phase of `chain(1)`,
which equals the MDS phase. This is independent of the filtration choice. -/
theorem StabilityFunction.hn_phiPlus_eq (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F₁ F₂ : AbelianHNFiltration Z E) :
    F₁.φ ⟨0, F₁.hn⟩ = F₂.φ ⟨0, F₂.hn⟩ := by
  haveI := hFinSub E
  by_cases hss : Z.IsSemistable E
  · -- Semistable: n = 1, each φ(0) = Z.phase E
    have h1 := hn_n_eq_one_of_semistable Z hss F₁
    have h2 := hn_n_eq_one_of_semistable Z hss F₂
    suffices ∀ (F : AbelianHNFiltration Z E), F.n = 1 →
        F.φ ⟨0, F.hn⟩ = Z.phase E from
      (this F₁ h1).trans (this F₂ h2).symm
    intro F hF
    rw [← F.factor_phase ⟨0, F.hn⟩]
    have h_bot : F.chain (⟨0, F.hn⟩ : Fin F.n).castSucc = ⊥ := by
      change F.chain ⟨0, by have := F.hn; omega⟩ = ⊥; exact F.chain_bot
    have h_top : F.chain (⟨0, F.hn⟩ : Fin F.n).succ = ⊤ := by
      have : (⟨0, F.hn⟩ : Fin F.n).succ = ⟨F.n, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [this]; exact F.chain_top
    exact (phase_cokernel_ofLE_congr Z h_bot h_top).trans
      (Z.phase_eq_of_iso (Subobject.cokernelBotIso ⊤ bot_le ≪≫
        asIso (⊤ : Subobject E).arrow))
  · -- Non-semistable: φ(0) = phase(chain(1)) = phase(MDS) for both
    have hn1 : 2 ≤ F₁.n := n_ge_two_of_not_semistable hss F₁
    have hn2 : 2 ≤ F₂.n := n_ge_two_of_not_semistable hss F₂
    obtain ⟨M, hM_ne, hM_max, hM_strict⟩ :=
      exists_maxPhase_maximal_subobject Z E hE
    have hM_ss := Z.maxPhase_isSemistable hM_ne hM_max
    have hc1 := chain_one_eq_MDS F₁ hn1 hM_ne hM_ss hM_max hM_strict
    have hc2 := chain_one_eq_MDS F₂ hn2 hM_ne hM_ss hM_max hM_strict
    rw [← chain_one_phase F₁ hn1, ← chain_one_phase F₂ hn2, hc1, hc2]

/-- Transporting an HN filtration along an equality preserves the lowest
phase `φ(n-1)`. -/
private lemma transport_phiMinus {Z : StabilityFunction A} {Q₁ Q₂ : A}
    (h : Q₁ = Q₂) (F : AbelianHNFiltration Z Q₁) :
    (h ▸ F).φ ⟨(h ▸ F).n - 1, by have := (h ▸ F).hn; omega⟩ =
      F.φ ⟨F.n - 1, by have := F.hn; omega⟩ := by
  subst h; rfl

/-- The tail filtration's lowest phase equals the original's lowest phase.
Since `tailHNFiltration.φ ⟨j, _⟩ = F.φ ⟨j+1, _⟩` and `tail.n = F.n - 1`,
the tail's last index `tail.n - 1 = F.n - 2` maps to `F.n - 1`. -/
private lemma tailHNFiltration_phiMinus {Z : StabilityFunction A} {E : A}
    (G : AbelianHNFiltration Z E) (hn2 : 2 ≤ G.n) :
    (tailHNFiltration G hn2).φ
      ⟨(tailHNFiltration G hn2).n - 1,
        by have := (tailHNFiltration G hn2).hn; omega⟩ =
    G.φ ⟨G.n - 1, by have := G.hn; omega⟩ :=
  -- After definitional reduction: LHS = G.φ ⟨(G.n-1)-1+1, _⟩
  congrArg G.φ (Fin.ext
    (show ((G.n - 1) - 1 + 1 : ℕ) = G.n - 1 from by omega))

/-- The lowest phase `φ(n-1)` of an HN filtration is independent of the
filtration choice. The proof parallels `hn_unique`: induction on
`Nat.card (Subobject E)`, using the tail filtration on the MDS quotient. -/
theorem StabilityFunction.hn_phiMinus_eq (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F₁ F₂ : AbelianHNFiltration Z E) :
    F₁.φ ⟨F₁.n - 1, by have := F₁.hn; omega⟩ =
      F₂.φ ⟨F₂.n - 1, by have := F₂.hn; omega⟩ := by
  suffices ∀ (k : ℕ) (E : A), ¬IsZero E →
      Nat.card (Subobject E) ≤ k →
      ∀ G₁ G₂ : AbelianHNFiltration Z E,
        G₁.φ ⟨G₁.n - 1, by have := G₁.hn; omega⟩ =
          G₂.φ ⟨G₂.n - 1, by have := G₂.hn; omega⟩ by
    exact this _ E hE le_rfl F₁ F₂
  intro k
  induction k with
  | zero =>
    intro E hE hcard
    haveI := hFinSub E
    haveI := Fintype.ofFinite (Subobject E)
    have : 0 < Nat.card (Subobject E) := by
      rw [Nat.card_eq_fintype_card]
      haveI : Nonempty (Subobject E) := ⟨⊥⟩
      exact Fintype.card_pos
    omega
  | succ k ih =>
    intro E hE hcard G₁ G₂
    haveI := hFinSub E
    by_cases hss : Z.IsSemistable E
    · -- Semistable: n = 1, phiMinus = phiPlus
      have h1 := hn_n_eq_one_of_semistable Z hss G₁
      have h2 := hn_n_eq_one_of_semistable Z hss G₂
      have hG₁_eq : (⟨G₁.n - 1, by have := G₁.hn; omega⟩ : Fin G₁.n) =
          ⟨0, G₁.hn⟩ := Fin.ext (by omega)
      have hG₂_eq : (⟨G₂.n - 1, by have := G₂.hn; omega⟩ : Fin G₂.n) =
          ⟨0, G₂.hn⟩ := Fin.ext (by omega)
      rw [hG₁_eq, hG₂_eq]
      exact Z.hn_phiPlus_eq E hE hFinSub G₁ G₂
    · -- Not semistable: use tail filtrations on MDS quotient
      have hn1 : 2 ≤ G₁.n := n_ge_two_of_not_semistable hss G₁
      have hn2 : 2 ≤ G₂.n := n_ge_two_of_not_semistable hss G₂
      obtain ⟨M, hM_ne, hM_max, hM_strict⟩ :=
        exists_maxPhase_maximal_subobject Z E hE
      have hM_ss := Z.maxPhase_isSemistable hM_ne hM_max
      have hM_ne_top :=
        Z.maxPhase_ne_top_of_not_semistable hss M hM_ne hM_max
      have hc1 := chain_one_eq_MDS G₁ hn1 hM_ne hM_ss hM_max hM_strict
      have hc2 := chain_one_eq_MDS G₂ hn2 hM_ne hM_ss hM_max hM_strict
      have hcard_Q : Nat.card (Subobject (cokernel M.arrow)) <
          Nat.card (Subobject E) := card_subobject_cokernel_lt hM_ne
      have hQ₁ : cokernel (G₁.chain ⟨1, by omega⟩).arrow =
          cokernel M.arrow :=
        congrArg (fun S ↦ cokernel (Subobject.arrow S)) hc1
      have hQ₂ : cokernel (G₂.chain ⟨1, by omega⟩).arrow =
          cokernel M.arrow :=
        congrArg (fun S ↦ cokernel (Subobject.arrow S)) hc2
      -- Tail filtrations on the quotient
      let T₁ := hQ₁ ▸ tailHNFiltration G₁ hn1
      let T₂ := hQ₂ ▸ tailHNFiltration G₂ hn2
      -- IH: tail filtrations have the same lowest phase
      have h_tail : T₁.φ ⟨T₁.n - 1, by have := T₁.hn; omega⟩ =
          T₂.φ ⟨T₂.n - 1, by have := T₂.hn; omega⟩ :=
        ih (cokernel M.arrow) (cokernel_nonzero_of_ne_top hM_ne_top)
          (by omega) T₁ T₂
      -- Connect tail's phiMinus to original's phiMinus
      have hrel₁ : T₁.φ ⟨T₁.n - 1, by have := T₁.hn; omega⟩ =
          G₁.φ ⟨G₁.n - 1, by have := G₁.hn; omega⟩ :=
        (transport_phiMinus hQ₁ (tailHNFiltration G₁ hn1)).trans
          (tailHNFiltration_phiMinus G₁ hn1)
      have hrel₂ : T₂.φ ⟨T₂.n - 1, by have := T₂.hn; omega⟩ =
          G₂.φ ⟨G₂.n - 1, by have := G₂.hn; omega⟩ :=
        (transport_phiMinus hQ₂ (tailHNFiltration G₂ hn2)).trans
          (tailHNFiltration_phiMinus G₂ hn2)
      linarith

/-! ### Intrinsic phase bounds -/

/-- The intrinsic highest phase of a nonzero object `E` with respect to a
stability function `Z`, assuming finite subobject lattices. This is the phase of
the maximally destabilizing subobject. It is well-defined by `hn_phiPlus_eq`. -/
noncomputable def StabilityFunction.phiPlus (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E)) : ℝ :=
  let F := Classical.choice (Z.hasHN_of_finiteLength hFinSub E hE)
  F.φ ⟨0, F.hn⟩

/-- `phiPlus` equals `F.φ ⟨0, F.hn⟩` for any HN filtration `F`. -/
theorem StabilityFunction.phiPlus_eq (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F : AbelianHNFiltration Z E) :
    Z.phiPlus E hE hFinSub = F.φ ⟨0, F.hn⟩ :=
  Z.hn_phiPlus_eq E hE hFinSub _ F

/-- The intrinsic lowest phase of a nonzero object `E` with respect to a
stability function `Z`, assuming finite subobject lattices. This is the phase of
the last HN factor. It is well-defined by `hn_phiMinus_eq`. -/
noncomputable def StabilityFunction.phiMinus (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E)) : ℝ :=
  let F := Classical.choice (Z.hasHN_of_finiteLength hFinSub E hE)
  F.φ ⟨F.n - 1, by have := F.hn; omega⟩

/-- `phiMinus` equals `F.φ ⟨F.n - 1, _⟩` for any HN filtration `F`. -/
theorem StabilityFunction.phiMinus_eq (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F : AbelianHNFiltration Z E) :
    Z.phiMinus E hE hFinSub =
      F.φ ⟨F.n - 1, by have := F.hn; omega⟩ :=
  Z.hn_phiMinus_eq E hE hFinSub _ F

/-- `phiMinus ≤ phiPlus` for nonzero objects. -/
theorem StabilityFunction.phiMinus_le_phiPlus
    (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E)) :
    Z.phiMinus E hE hFinSub ≤ Z.phiPlus E hE hFinSub := by
  let F := Classical.choice (Z.hasHN_of_finiteLength hFinSub E hE)
  rw [Z.phiPlus_eq E hE hFinSub F, Z.phiMinus_eq E hE hFinSub F]
  exact F.φ_anti.antitone (Fin.mk_le_mk.mpr (by have := F.hn; omega))

/-- For semistable objects, `phiPlus = phiMinus = Z.phase E`. -/
theorem StabilityFunction.phiPlus_eq_phiMinus_of_semistable
    (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (hss : Z.IsSemistable E) :
    Z.phiPlus E hE hFinSub = Z.phiMinus E hE hFinSub := by
  let F := Classical.choice (Z.hasHN_of_finiteLength hFinSub E hE)
  have h1 := hn_n_eq_one_of_semistable Z hss F
  have hp := Z.phiPlus_eq E hE hFinSub F
  have hm := Z.phiMinus_eq E hE hFinSub F
  have heq : F.φ ⟨0, F.hn⟩ =
      F.φ ⟨F.n - 1, by have := F.hn; omega⟩ :=
    congrArg F.φ (Fin.ext (by omega))
  linarith

end CategoryTheory

set_option linter.style.longFile 2100
