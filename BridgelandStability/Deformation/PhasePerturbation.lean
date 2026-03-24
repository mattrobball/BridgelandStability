/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.WPhase
public import BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.PhasePerturbation

/-!
# W-Phase Perturbation

The generic phase perturbation bound `wPhaseOf_perturbation_generic` for
`m · exp(iπφ) · (1 + u)`, using the pure complex analysis from
`ForMathlib/Analysis/SpecialFunctions/Complex/PhasePerturbation.lean`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### W-phase perturbation -/

section PhasePerturbation

/-- **Generic phase perturbation bound**. If `w = m · exp(iπφ) · (1 + u)` with `m > 0`,
`φ ∈ (α - 1/2, α + 1/2)`, and `‖u‖ < sin(πε)` with `0 < ε ≤ 1/2`, then
`|wPhaseOf(w, α) - φ| < ε`. The proof splits `arg` of the product using `arg_mul`,
computes `arg(m · exp(iπ(φ-α))) = π(φ-α)`, and bounds `|arg(1+u)| < πε`. -/
theorem wPhaseOf_perturbation_generic {m φ α ε : ℝ} {u : ℂ}
    (hm : 0 < m) (hφ : φ ∈ Set.Ioo (α - 1 / 2) (α + 1 / 2))
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hu : ‖u‖ < Real.sin (Real.pi * ε)) :
    |wPhaseOf (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) *
      ((1 : ℂ) + u)) α - φ| < ε := by
  have hπ := Real.pi_pos
  have hu1 : ‖u‖ < 1 := lt_of_lt_of_le hu (Real.sin_le_one _)
  have hz2 : (1 : ℂ) + u ≠ 0 := by
    intro h; have := congr_arg norm (eq_neg_of_add_eq_zero_left h)
    rw [norm_neg, norm_one] at this; linarith
  have harg_u := abs_arg_one_add_lt hε hε2 hu
  -- Reassemble: w · exp(-iπα) = (m · exp(iπ(φ-α))) · (1+u)
  have hreassoc : ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) *
      ((1 : ℂ) + u) * Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
      (↑m * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I)) *
        ((1 : ℂ) + u) := by
    have : Complex.exp (↑(Real.pi * φ) * Complex.I) *
        Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
        Complex.exp (↑(Real.pi * (φ - α)) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc _ = ↑m * (Complex.exp (↑(Real.pi * φ) * Complex.I) *
        Complex.exp (-(↑(Real.pi * α) * Complex.I))) * ((1 : ℂ) + u) := by ring
      _ = _ := by rw [this]
  set z₁ := (↑m : ℂ) * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I)
  set z₂ := (1 : ℂ) + u
  have hz1 : z₁ ≠ 0 := mul_ne_zero (by exact_mod_cast hm.ne') (Complex.exp_ne_zero _)
  have harg1 : Complex.arg z₁ = Real.pi * (φ - α) := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    exact ⟨by grind [mul_pos hπ (show (0 : ℝ) < 1 + (φ - α) from by grind [hφ.1])],
           by grind [mul_pos hπ (show (0 : ℝ) < 1 - (φ - α) from by grind [hφ.2])]⟩
  have hsum_mem : Complex.arg z₁ + Complex.arg z₂ ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [harg1]; obtain ⟨h1, h2⟩ := abs_lt.mp harg_u
    exact ⟨by nlinarith [hφ.1], by nlinarith [hφ.2]⟩
  unfold wPhaseOf
  rw [hreassoc, Complex.arg_mul hz1 hz2 hsum_mem, harg1,
    show α + (Real.pi * (φ - α) + Complex.arg z₂) / Real.pi - φ =
      Complex.arg z₂ / Real.pi from by field_simp; ring,
    abs_div, abs_of_pos hπ, div_lt_iff₀ hπ]
  grind

end PhasePerturbation

end CategoryTheory.Triangulated
