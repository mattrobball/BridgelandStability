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
  have hπε2 : Real.pi * ε ≤ Real.pi / 2 := by nlinarith
  have hu1 : ‖u‖ < 1 := lt_of_lt_of_le hu (Real.sin_le_one _)
  -- 1 + u ≠ 0
  have hz2 : (1 : ℂ) + u ≠ 0 := by
    intro h; have h1 : (1 : ℂ) = -u := eq_neg_of_add_eq_zero_left h
    have h2 : ‖(1 : ℂ)‖ = ‖u‖ := by rw [h1, norm_neg]
    rw [norm_one] at h2; grind
  -- Step 1: |arg(1+u)| < πε
  have harg_u : |Complex.arg ((1 : ℂ) + u)| < Real.pi * ε :=
    abs_arg_one_add_lt hε hε2 hu
  -- Step 2: Reassemble w · exp(-iπα) = (m · exp(iπ(φ-α))) · (1+u)
  have hexp_combine : Complex.exp (↑(Real.pi * φ) * Complex.I) *
      Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
      Complex.exp (↑(Real.pi * (φ - α)) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hreassoc : ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) *
      ((1 : ℂ) + u) * Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
      (↑m * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I)) *
        ((1 : ℂ) + u) := by
    have h := hexp_combine
    calc _ = ↑m * (Complex.exp (↑(Real.pi * φ) * Complex.I) *
        Complex.exp (-(↑(Real.pi * α) * Complex.I))) * ((1 : ℂ) + u) := by ring
      _ = _ := by rw [h]
  -- Step 3: arg of z₁ = m · exp(iπ(φ-α))
  set z₁ := (↑m : ℂ) * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I)
  have hz1 : z₁ ≠ 0 := mul_ne_zero
    (by exact_mod_cast hm.ne') (Complex.exp_ne_zero _)
  have hφα : |φ - α| < 1 / 2 := abs_lt.mpr ⟨by grind [hφ.1], by grind [hφ.2]⟩
  have harg1 : Complex.arg z₁ = Real.pi * (φ - α) := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    exact ⟨by grind [mul_pos hπ (show (0 : ℝ) < 1 + (φ - α) from by grind [hφ.1])],
           by grind [mul_pos hπ (show (0 : ℝ) < 1 - (φ - α) from by grind [hφ.2])]⟩
  -- Step 4: arg(z₁) + arg(z₂) ∈ Ioc(-π, π), apply arg_mul
  set z₂ := (1 : ℂ) + u
  have hsum_mem : Complex.arg z₁ + Complex.arg z₂ ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [harg1]
    have h1 := (abs_lt.mp harg_u).1
    have h2 := (abs_lt.mp harg_u).2
    constructor
    · -- -π < π(φ-α) + arg(z₂)
      have : -(Real.pi / 2) < Real.pi * (φ - α) := by
        grind [mul_pos hπ (show (0 : ℝ) < 1 / 2 + (φ - α) from by grind [hφ.1])]
      linarith
    · -- π(φ-α) + arg(z₂) ≤ π
      have : Real.pi * (φ - α) < Real.pi / 2 := by
        grind [mul_pos hπ (show (0 : ℝ) < 1 / 2 - (φ - α) from by grind [hφ.2])]
      linarith
  have harg_prod : Complex.arg (z₁ * z₂) = Complex.arg z₁ + Complex.arg z₂ :=
    Complex.arg_mul hz1 hz2 hsum_mem
  -- Step 5: Compute wPhaseOf
  unfold wPhaseOf
  rw [hreassoc, harg_prod, harg1]
  -- α + (π(φ-α) + arg(z₂)) / π - φ = arg(z₂) / π
  have hsimpl : α + (Real.pi * (φ - α) + Complex.arg z₂) / Real.pi - φ =
      Complex.arg z₂ / Real.pi := by field_simp; ring
  rw [hsimpl, abs_div, abs_of_pos hπ, div_lt_iff₀ hπ]
  grind

end PhasePerturbation

end CategoryTheory.Triangulated
