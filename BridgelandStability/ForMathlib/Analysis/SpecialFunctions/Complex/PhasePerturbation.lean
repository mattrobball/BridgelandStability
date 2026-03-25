/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Phase Perturbation Estimates

Pure complex-analytic estimates for near-identity perturbation of
complex arguments.

## Main results

* `im_sq_le_norm_sq_mul`: geometric inequality `z.im² ≤ ‖z - 1‖² · ‖z‖²`
* `abs_sin_arg_le_norm_sub_one`: law-of-sines bound `|sin(arg z)| ≤ ‖z - 1‖`
* `sin_abs_eq_abs_sin`: `sin(|x|) = |sin(x)|` for `|x| < π/2`
* `abs_arg_one_add_lt`: near-identity bound `|arg(1+u)| < πε`
-/

@[expose] public section

noncomputable section

/-- **Core geometric inequality**. For any complex number `z`,
`z.im² ≤ ‖z - 1‖² · ‖z‖²`. -/
theorem im_sq_le_norm_sq_mul (z : ℂ) :
    z.im ^ 2 ≤ ‖z - 1‖ ^ 2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm (z - 1), Complex.sq_norm z]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith [sq_nonneg (z.re * z.re + z.im * z.im - z.re)]

/-- For any nonzero `z : ℂ`, `|sin(arg z)| ≤ ‖z - 1‖`. -/
theorem abs_sin_arg_le_norm_sub_one {z : ℂ} (hz : z ≠ 0) :
    |Real.sin (Complex.arg z)| ≤ ‖z - 1‖ := by
  rw [Complex.sin_arg, abs_div, abs_of_pos (norm_pos_iff.mpr hz),
    div_le_iff₀ (norm_pos_iff.mpr hz)]
  exact le_of_sq_le_sq
    (by rw [sq_abs, mul_pow]; exact im_sq_le_norm_sq_mul z)
    (by positivity)

/-- `sin(|x|) = |sin(x)|` for `|x| < π/2`. -/
theorem sin_abs_eq_abs_sin {x : ℝ} (hx : |x| < Real.pi / 2) :
    Real.sin |x| = |Real.sin x| := by
  rcases le_or_gt 0 x with h | h
  · have hx' : x < Real.pi / 2 := by rwa [abs_of_nonneg h] at hx
    rw [abs_of_nonneg h, abs_of_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi h
        (by linarith [Real.pi_pos]))]
  · have : -x < Real.pi / 2 := by rwa [abs_of_neg h] at hx
    have hsin : Real.sin x < 0 := by
      have : 0 < Real.sin (-x) :=
        Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr h)
          (by linarith [Real.pi_pos])
      linarith [Real.sin_neg x]
    rw [abs_of_neg h, Real.sin_neg, abs_of_neg hsin]

/-- **Phase bound for near-identity perturbation**. If
`‖u‖ < sin(πε)` with `0 < ε ≤ 1/2`, then `|arg(1 + u)| < πε`. -/
theorem abs_arg_one_add_lt {u : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hu : ‖u‖ < Real.sin (Real.pi * ε)) :
    |Complex.arg (1 + u)| < Real.pi * ε := by
  have hπ := Real.pi_pos
  have hπε2 : Real.pi * ε ≤ Real.pi / 2 := by nlinarith
  have hu1 : ‖u‖ < 1 := lt_of_lt_of_le hu (Real.sin_le_one _)
  have hz : (1 : ℂ) + u ≠ 0 := by
    intro h
    have h2 : ‖(1 : ℂ)‖ = ‖u‖ := by rw [eq_neg_of_add_eq_zero_left h, norm_neg]
    rw [norm_one] at h2; linarith
  have hre : 0 < ((1 : ℂ) + u).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith [neg_le_of_abs_le (Complex.abs_re_le_norm u)]
  have harg_lt : |Complex.arg ((1 : ℂ) + u)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hsin_le :
      |Real.sin (Complex.arg ((1 : ℂ) + u))| ≤ ‖u‖ := by
    calc |Real.sin (Complex.arg ((1 : ℂ) + u))|
          ≤ ‖(1 : ℂ) + u - 1‖ :=
            abs_sin_arg_le_norm_sub_one hz
      _ = ‖u‖ := by congr 1; ring
  have hsin_abs := sin_abs_eq_abs_sin harg_lt
  by_contra h
  push_neg at h
  have hmono :
      Real.sin (Real.pi * ε) ≤
        Real.sin (|Complex.arg ((1 : ℂ) + u)|) :=
    Real.monotoneOn_sin
      ⟨by linarith [mul_pos hπ hε], hπε2⟩
      ⟨by linarith [abs_nonneg (Complex.arg ((1 : ℂ) + u))],
        harg_lt.le⟩ h
  linarith
