/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Arg Convexity in the Upper Half Plane

The semi-closed upper half plane `H ∪ ℝ₋` and arg convexity for sums:
if `z₁, z₂` lie in the upper half plane union, then
`min(arg z₁, arg z₂) ≤ arg(z₁ + z₂) ≤ max(arg z₁, arg z₂)`.

The proof uses the "cross product" method: the 2D cross product
`z₁.re * z₂.im - z₁.im * z₂.re = ‖z₁‖ * ‖z₂‖ * sin(arg z₂ - arg z₁)`
determines the ordering of arguments.

## Main definitions

* `CategoryTheory.upperHalfPlaneUnion`: the set `{im > 0} ∪ {im = 0, re < 0}` in `ℂ`

## Main results

* `CategoryTheory.arg_add_le_max`: `arg(z₁ + z₂) ≤ max(arg z₁, arg z₂)`
* `CategoryTheory.min_arg_le_arg_add`: `min(arg z₁, arg z₂) ≤ arg(z₁ + z₂)`
* `CategoryTheory.arg_add_lt_max`: strict version when args differ
* `CategoryTheory.min_arg_lt_arg_add`: strict dual
-/

@[expose] public section

noncomputable section

open Complex Real

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
lemma cross_eq_norm_mul_sin (z₁ z₂ : ℂ) :
    z₁.re * z₂.im - z₁.im * z₂.re =
      ‖z₁‖ * ‖z₂‖ * Real.sin (arg z₂ - arg z₁) := by
  rw [← norm_mul_cos_arg z₁, ← norm_mul_sin_arg z₁,
      ← norm_mul_cos_arg z₂, ← norm_mul_sin_arg z₂, Real.sin_sub]
  ring

/-- If `arg z₁ ≤ arg z₂` (with both in the closed upper half plane), then
the cross product `z₁.re * z₂.im - z₁.im * z₂.re` is nonneg. -/
lemma cross_nonneg_of_arg_le {z₁ z₂ : ℂ}
    (him₁ : 0 ≤ z₁.im) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (h : arg z₁ ≤ arg z₂) :
    0 ≤ z₁.re * z₂.im - z₁.im * z₂.re := by
  have hnn : 0 < ‖z₁‖ * ‖z₂‖ := mul_pos (norm_pos_iff.mpr hz₁) (norm_pos_iff.mpr hz₂)
  rw [cross_eq_norm_mul_sin, mul_nonneg_iff_right_nonneg_of_pos hnn]
  exact sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr h)
    (by linarith [arg_le_pi z₂, arg_nonneg_iff.mpr him₁])

/-- If the cross product is nonneg and both args are positive (in the open upper half plane
or negative real axis), then `arg z₁ ≤ arg z₂`. -/
lemma arg_le_of_cross_nonneg {z₁ z₂ : ℂ}
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
lemma cross_pos_of_arg_lt {z₁ z₂ : ℂ}
    (harg₁ : 0 < arg z₁) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (h : arg z₁ < arg z₂) :
    0 < z₁.re * z₂.im - z₁.im * z₂.re := by
  have hnn : 0 < ‖z₁‖ * ‖z₂‖ := mul_pos (norm_pos_iff.mpr hz₁) (norm_pos_iff.mpr hz₂)
  rw [cross_eq_norm_mul_sin]
  exact mul_pos hnn (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr h)
    (by linarith [arg_le_pi z₂]))

/-- Strict version: if the cross product is positive and both args are positive (in the UHP),
then `arg z₁ < arg z₂`. -/
lemma arg_lt_of_cross_pos {z₁ z₂ : ℂ}
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
lemma arg_add_lt_max {z₁ z₂ : ℂ}
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

/-- The strict lower companion to `arg_add_lt_max`: if the arguments differ, then the
argument of the sum is strictly larger than the smaller argument. -/
lemma min_arg_lt_arg_add {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ upperHalfPlaneUnion) (h₂ : z₂ ∈ upperHalfPlaneUnion)
    (hne : arg z₁ ≠ arg z₂) :
    min (arg z₁) (arg z₂) < arg (z₁ + z₂) := by
  have hz₁ := upperHalfPlaneUnion_ne_zero h₁
  have hz₂ := upperHalfPlaneUnion_ne_zero h₂
  have hs_mem := mem_upperHalfPlaneUnion_of_add h₁ h₂
  have hs_ne := upperHalfPlaneUnion_ne_zero hs_mem
  have harg₁ := arg_pos_of_mem_upperHalfPlaneUnion h₁
  have harg₂ := arg_pos_of_mem_upperHalfPlaneUnion h₂
  have hargs := arg_pos_of_mem_upperHalfPlaneUnion hs_mem
  set cp := z₁.re * z₂.im - z₁.im * z₂.re
  rcases hne.lt_or_gt with h | h
  · rw [min_eq_left h.le]
    apply arg_lt_of_cross_pos hz₁ hs_ne hargs
    show 0 < z₁.re * (z₁ + z₂).im - z₁.im * (z₁ + z₂).re
    have : z₁.re * (z₁ + z₂).im - z₁.im * (z₁ + z₂).re = cp := by
      simp only [Complex.add_re, Complex.add_im, cp]
      ring
    rw [this]
    exact cross_pos_of_arg_lt harg₁ hz₁ hz₂ h
  · rw [min_eq_right h.le]
    apply arg_lt_of_cross_pos hz₂ hs_ne hargs
    show 0 < z₂.re * (z₁ + z₂).im - z₂.im * (z₁ + z₂).re
    have : z₂.re * (z₁ + z₂).im - z₂.im * (z₁ + z₂).re = -cp := by
      simp only [Complex.add_re, Complex.add_im, cp]
      ring
    rw [this]
    have hcp : 0 < z₂.re * z₁.im - z₂.im * z₁.re :=
      cross_pos_of_arg_lt harg₂ hz₂ hz₁ h
    linarith


end CategoryTheory
