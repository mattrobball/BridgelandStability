/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.GrothendieckGroup
import Mathlib.CategoryTheory.Triangulated.Slicing
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.ENNReal.Basic

/-!
# Bridgeland Stability Conditions

We define Bridgeland stability conditions on a pretriangulated category and state
the main theorem from "Stability conditions on triangulated categories" (2007):

* **Theorem 1.2**: For each connected component `Σ` of the space `Stab(D)` of
  locally-finite stability conditions, there exists a linear subspace
  `V(Σ) ⊆ Hom_ℤ(K₀(D), ℂ)` with a linear topology, and a local homeomorphism
  `𝒵 : Σ → V(Σ)` sending `(Z, P)` to `Z`.

## Main definitions

* `CategoryTheory.Triangulated.StabilityCondition`: a locally-finite stability condition
* `CategoryTheory.Triangulated.slicingDist`: the Bridgeland generalized metric on slicings
* `CategoryTheory.Triangulated.stabSeminorm`: the seminorm `‖U‖_σ` on `Hom_ℤ(K₀(D), ℂ)`
* `CategoryTheory.Triangulated.StabilityCondition.topologicalSpace`: the Bridgeland
  topology on `Stab(D)`, constructed from basis neighborhoods
* `CategoryTheory.Triangulated.bridgelandTheorem_1_2`: **Theorem 1.2** as a `Prop`,
  stated componentwise with a linear subspace `V(Σ)`

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ENNReal

universe v u

/-! ### Complex ray rigidity -/

/-- Two positive-real multiples of exponentials on distinct rays in `(-π, π]` cannot be equal.
More precisely, if `m₁ * exp(iπφ) = m₂ * exp(iπψ)` with `m₁, m₂ > 0` and `|φ - ψ| < 2`,
then `φ = ψ`. This is used in **Lemma 6.4** to show that the same central charge pins the phase
of a semistable object uniquely. -/
theorem eq_of_pos_mul_exp_eq {m₁ m₂ φ ψ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (habs : |φ - ψ| < 2)
    (heq : (m₁ : ℂ) * exp (↑(Real.pi * φ) * I) =
      (m₂ : ℂ) * exp (↑(Real.pi * ψ) * I)) : φ = ψ := by
  have hpi := Real.pi_pos
  -- Extract argument equality
  have harg : Complex.arg ((m₁ : ℂ) * exp (↑(Real.pi * φ) * I)) =
    Complex.arg ((m₂ : ℂ) * exp (↑(Real.pi * ψ) * I)) := by rw [heq]
  rw [Complex.arg_real_mul _ hm₁, Complex.arg_real_mul _ hm₂] at harg
  rw [Complex.arg_exp_mul_I, Complex.arg_exp_mul_I] at harg
  rw [toIocMod_eq_toIocMod Real.two_pi_pos] at harg
  obtain ⟨n, hn⟩ := harg
  -- hn : π * ψ - π * φ = n • (2 * π)
  have hsmall : |Real.pi * φ - Real.pi * ψ| < 2 * Real.pi := by
    rw [← mul_sub, abs_mul, abs_of_pos hpi]; nlinarith
  have hn0 : n = 0 := by
    by_contra h
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs h
    have h2 : 2 * Real.pi ≤ |(n : ℝ)| * (2 * Real.pi) := by
      exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast h1)
    have h3 : |Real.pi * φ - Real.pi * ψ| = |(n : ℝ)| * (2 * Real.pi) := by
      have : Real.pi * φ - Real.pi * ψ = -(n • (2 * Real.pi)) := by linarith
      rw [this, abs_neg, zsmul_eq_mul, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith
  rw [hn0, zero_zsmul, sub_eq_zero] at hn
  have := mul_left_cancel₀ hpi.ne' hn
  linarith

/-! ### Sector estimate -/

/-- **Sector projection bound**. If a complex number `z` has argument in the
interval `(α, α + w)` with `w < π`, then projecting `z` onto the bisector direction
`α + w/2` yields at least `cos(w/2) * ‖z‖`. Formally:
`cos(w/2) * ‖z‖ ≤ (z * exp(-i(α + w/2))).re`.

This is the key pointwise ingredient for the sector estimate used in **Lemma 6.2**.
The proof uses the polar decomposition `z = ‖z‖ · exp(i · arg z)` and the monotonicity
of cosine on `[0, π]`. -/
theorem re_mul_exp_neg_ge_cos_mul_norm {z : ℂ} {α w : ℝ}
    (hwπ : w < Real.pi)
    (harg : Complex.arg z ∈ Set.Ioo α (α + w)) :
    Real.cos (w / 2) * ‖z‖ ≤
      (z * exp (-(↑(α + w / 2) * I))).re := by
  rw [Set.mem_Ioo] at harg
  -- Polar form: z = ‖z‖ * exp(i * arg z)
  have polar := Complex.norm_mul_exp_arg_mul_I z
  -- Compute the real part after rotation
  have key : (z * exp (-(↑(α + w / 2) * I))).re =
      ‖z‖ * Real.cos (Complex.arg z - (α + w / 2)) := by
    conv_lhs => rw [← polar]
    rw [mul_assoc, ← Complex.exp_add, Complex.re_ofReal_mul]
    congr 1
    have : Complex.arg z * I + -(↑(α + w / 2) * I) = ↑(Complex.arg z - (α + w / 2)) * I := by
      push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  rw [key]
  -- Need: cos(w/2) * ‖z‖ ≤ ‖z‖ * cos(arg z - (α + w/2))
  -- Since arg z ∈ (α, α+w), the difference arg z - (α + w/2) ∈ (-w/2, w/2)
  -- and |arg z - (α + w/2)| < w/2 ≤ π/2, so cos is ≥ cos(w/2)
  have hd_lo : -(w / 2) < Complex.arg z - (α + w / 2) := by linarith
  have hd_hi : Complex.arg z - (α + w / 2) < w / 2 := by linarith
  have hcos : Real.cos (w / 2) ≤ Real.cos (Complex.arg z - (α + w / 2)) := by
    rw [← Real.cos_abs (Complex.arg z - (α + w / 2))]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
    exact le_of_lt (abs_lt.mpr ⟨by linarith, hd_hi⟩)
  calc Real.cos (w / 2) * ‖z‖ ≤ Real.cos (Complex.arg z - (α + w / 2)) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hcos (norm_nonneg _)
    _ = ‖z‖ * Real.cos (Complex.arg z - (α + w / 2)) := mul_comm _ _

/-- **Sector norm bound**. If complex numbers `z i` for `i ∈ s` all have arguments in
`(α, α + w)` with `w < π`, then `‖∑ i ∈ s, z i‖ ≥ cos(w/2) · ∑ i ∈ s, ‖z i‖`.

This follows from the pointwise bound `re_mul_exp_neg_ge_cos_mul_norm` by summing
and using `‖z‖ ≥ z.re` (applied to the sum rotated by the bisector direction). -/
theorem norm_sum_ge_cos_mul_sum_norm {ι : Type*} {s : Finset ι} {z : ι → ℂ}
    {α w : ℝ} (hwπ : w < Real.pi)
    (harg : ∀ i ∈ s, Complex.arg (z i) ∈ Set.Ioo α (α + w)) :
    Real.cos (w / 2) * ∑ i ∈ s, ‖z i‖ ≤ ‖∑ i ∈ s, z i‖ := by
  calc Real.cos (w / 2) * ∑ i ∈ s, ‖z i‖
      = ∑ i ∈ s, (Real.cos (w / 2) * ‖z i‖) := Finset.mul_sum s _ _
    _ ≤ ∑ i ∈ s, (z i * exp (-(↑(α + w / 2) * I))).re := by
        apply Finset.sum_le_sum
        intro i hi
        exact re_mul_exp_neg_ge_cos_mul_norm hwπ (harg i hi)
    _ ≤ ((∑ i ∈ s, z i) * exp (-(↑(α + w / 2) * I))).re := by
        rw [Finset.sum_mul, Complex.re_sum]
    _ ≤ ‖(∑ i ∈ s, z i) * exp (-(↑(α + w / 2) * I))‖ :=
        Complex.re_le_norm _
    _ = ‖∑ i ∈ s, z i‖ := by
        rw [norm_mul]
        have : -(↑(α + w / 2) * I) = ↑(-(α + w / 2)) * I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Stability conditions -/

/-- A Bridgeland stability condition on a pretriangulated category `C`.
This bundles a slicing with a central charge (an additive group homomorphism
from `K₀ C` to `ℂ`), subject to a compatibility condition relating the phase
of semistable objects to the argument of their central charge.
The slicing is required to be locally finite. -/
structure StabilityCondition where
  /-- The underlying slicing. -/
  slicing : Slicing C
  /-- The central charge, an additive group homomorphism `K₀ C →+ ℂ`. -/
  Z : K₀ C →+ ℂ
  /-- Compatibility: for every nonzero semistable object `E` of phase `φ`, the central charge
  `Z([E])` lies on the ray `ℝ₊ · exp(iπφ)` in `ℂ`. -/
  compat : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (K₀.of C E) = ↑m * exp (↑(Real.pi * φ) * I)
  /-- The slicing is locally finite. -/
  locallyFinite : slicing.IsLocallyFinite C

/-! ### Phase rigidity for same central charge -/

/-- **Lemma 6.4 sublemma**. If two stability conditions `σ` and `τ` have the same central
charge `Z`, and a nonzero object `E` is `σ`-semistable of phase `φ` and `τ`-semistable
of phase `ψ` with `|φ - ψ| < 2`, then `φ = ψ`. -/
theorem StabilityCondition.phase_eq_of_same_Z (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z) {E : C} {φ ψ : ℝ}
    (hσ : σ.slicing.P φ E) (hτ : τ.slicing.P ψ E) (hE : ¬IsZero E)
    (habs : |φ - ψ| < 2) : φ = ψ := by
  obtain ⟨m₁, hm₁, h₁⟩ := σ.compat φ E hσ hE
  obtain ⟨m₂, hm₂, h₂⟩ := τ.compat ψ E hτ hE
  rw [hZ] at h₁
  exact eq_of_pos_mul_exp_eq hm₁ hm₂ habs (h₁.symm.trans h₂)

/-! ### Generalized metric and seminorm -/

/-- The Bridgeland generalized metric on slicings (blueprint A8). For slicings `s₁` and `s₂`,
this is the supremum over all nonzero objects `E` of
`max(|φ₁⁺(E) - φ₂⁺(E)|, |φ₁⁻(E) - φ₂⁻(E)|)`,
where `φᵢ±` are the intrinsic phase bounds (well-defined by HN filtration uniqueness).
Values lie in `[0, ∞]`. -/
def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)

/-- The Bridgeland generalized metric is zero on the diagonal: `d(P, P) = 0`. -/
theorem slicingDist_self (s : Slicing C) : slicingDist C s s = 0 := by
  simp [slicingDist, sub_self, abs_zero, max_self, ENNReal.ofReal_zero]

/-- The Bridgeland generalized metric is symmetric: `d(P, Q) = d(Q, P)`. -/
theorem slicingDist_symm (s₁ s₂ : Slicing C) :
    slicingDist C s₁ s₂ = slicingDist C s₂ s₁ := by
  simp only [slicingDist, abs_sub_comm]

/-- The Bridgeland generalized metric satisfies the triangle inequality. -/
theorem slicingDist_triangle (s₁ s₂ s₃ : Slicing C) :
    slicingDist C s₁ s₃ ≤ slicingDist C s₁ s₂ + slicingDist C s₂ s₃ := by
  apply iSup_le
  intro E
  apply iSup_le
  intro hE
  calc ENNReal.ofReal (max |s₁.phiPlus C E hE - s₃.phiPlus C E hE|
          |s₁.phiMinus C E hE - s₃.phiMinus C E hE|)
      ≤ ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
            |s₁.phiMinus C E hE - s₂.phiMinus C E hE|) +
        ENNReal.ofReal (max |s₂.phiPlus C E hE - s₃.phiPlus C E hE|
            |s₂.phiMinus C E hE - s₃.phiMinus C E hE|) := by
        rw [← ENNReal.ofReal_add (le_max_of_le_left (abs_nonneg _))
          (le_max_of_le_left (abs_nonneg _))]
        apply ENNReal.ofReal_le_ofReal
        have abs_tri : ∀ (a b c : ℝ), |a - c| ≤ |a - b| + |b - c| := fun a b c ↦ by
          calc |a - c| = |(a - b) + (b - c)| := by ring_nf
            _ ≤ |a - b| + |b - c| := abs_add_le _ _
        apply max_le
        · calc |s₁.phiPlus C E hE - s₃.phiPlus C E hE|
              ≤ |s₁.phiPlus C E hE - s₂.phiPlus C E hE| +
                |s₂.phiPlus C E hE - s₃.phiPlus C E hE| := abs_tri _ _ _
            _ ≤ max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                  |s₁.phiMinus C E hE - s₂.phiMinus C E hE| +
                max |s₂.phiPlus C E hE - s₃.phiPlus C E hE|
                  |s₂.phiMinus C E hE - s₃.phiMinus C E hE| :=
              add_le_add (le_max_left _ _) (le_max_left _ _)
        · calc |s₁.phiMinus C E hE - s₃.phiMinus C E hE|
              ≤ |s₁.phiMinus C E hE - s₂.phiMinus C E hE| +
                |s₂.phiMinus C E hE - s₃.phiMinus C E hE| := abs_tri _ _ _
            _ ≤ max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                  |s₁.phiMinus C E hE - s₂.phiMinus C E hE| +
                max |s₂.phiPlus C E hE - s₃.phiPlus C E hE|
                  |s₂.phiMinus C E hE - s₃.phiMinus C E hE| :=
              add_le_add (le_max_right _ _) (le_max_right _ _)
    _ ≤ slicingDist C s₁ s₂ + slicingDist C s₂ s₃ := by
        exact add_le_add (le_iSup_of_le E (le_iSup_of_le hE le_rfl))
          (le_iSup_of_le E (le_iSup_of_le hE le_rfl))

/-- If the slicing distance is less than `ε`, the intrinsic `φ⁺` values are within `ε`.
This is one direction of **Lemma 6.1**. -/
theorem phiPlus_sub_lt_of_slicingDist (s₁ s₂ : Slicing C) {E : C} (hE : ¬IsZero E)
    {ε : ℝ}
    (hd : slicingDist C s₁ s₂ < ENNReal.ofReal ε) :
    |s₁.phiPlus C E hE - s₂.phiPlus C E hE| < ε := by
  by_contra h
  push_neg at h
  have h1 : ENNReal.ofReal ε ≤ ENNReal.ofReal
      (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
           |s₁.phiMinus C E hE - s₂.phiMinus C E hE|) :=
    ENNReal.ofReal_le_ofReal (le_max_of_le_left h)
  have h2 : ENNReal.ofReal
      (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
           |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)
      ≤ slicingDist C s₁ s₂ := le_iSup_of_le E (le_iSup_of_le hE le_rfl)
  exact absurd hd (not_lt.mpr (h1.trans h2))

/-- If the slicing distance is less than `ε`, the intrinsic `φ⁻` values are within `ε`.
This is one direction of **Lemma 6.1**. -/
theorem phiMinus_sub_lt_of_slicingDist (s₁ s₂ : Slicing C) {E : C} (hE : ¬IsZero E)
    {ε : ℝ}
    (hd : slicingDist C s₁ s₂ < ENNReal.ofReal ε) :
    |s₁.phiMinus C E hE - s₂.phiMinus C E hE| < ε := by
  by_contra h
  push_neg at h
  have h1 : ENNReal.ofReal ε ≤ ENNReal.ofReal
      (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
           |s₁.phiMinus C E hE - s₂.phiMinus C E hE|) :=
    ENNReal.ofReal_le_ofReal (le_max_of_le_right h)
  have h2 : ENNReal.ofReal
      (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
           |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)
      ≤ slicingDist C s₁ s₂ := le_iSup_of_le E (le_iSup_of_le hE le_rfl)
  exact absurd hd (not_lt.mpr (h1.trans h2))

/-- **Lemma 6.1** (one direction). If the slicing distance `d(P, Q) < ε`, then every
`Q`-semistable object of phase `φ` has all `P`-HN phases in the interval `(φ - ε, φ + ε)`.
In terms of intrinsic phases: `|φ⁺_P(E) - φ| < ε` and `|φ⁻_P(E) - φ| < ε`. -/
theorem intervalProp_of_semistable_slicingDist (s₁ s₂ : Slicing C) {E : C} {φ : ℝ}
    (hE : ¬IsZero E) (hS : (s₂.P φ) E)
    {ε : ℝ}
    (hd : slicingDist C s₁ s₂ < ENNReal.ofReal ε) :
    s₁.phiPlus C E hE ∈ Set.Ioo (φ - ε) (φ + ε) ∧
    s₁.phiMinus C E hE ∈ Set.Ioo (φ - ε) (φ + ε) := by
  have ⟨hpP, hpM⟩ := s₂.phiPlus_eq_phiMinus_of_semistable C hS hE
  have hP := phiPlus_sub_lt_of_slicingDist C s₁ s₂ hE hd
  have hM := phiMinus_sub_lt_of_slicingDist C s₁ s₂ hE hd
  rw [hpP] at hP; rw [hpM] at hM
  rw [abs_lt] at hP hM
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The generalized metric is at most `ε` if both `φ⁺` and `φ⁻` differences are bounded
by `ε` for all nonzero objects. This is the "converse" direction of the phase-bound lemmas
`phiPlus_sub_lt_of_slicingDist` and `phiMinus_sub_lt_of_slicingDist`. -/
theorem slicingDist_le_of_phase_bounds (s₁ s₂ : Slicing C) {ε : ℝ}
    (hP : ∀ (E : C) (hE : ¬IsZero E),
      |s₁.phiPlus C E hE - s₂.phiPlus C E hE| ≤ ε)
    (hM : ∀ (E : C) (hE : ¬IsZero E),
      |s₁.phiMinus C E hE - s₂.phiMinus C E hE| ≤ ε) :
    slicingDist C s₁ s₂ ≤ ENNReal.ofReal ε := by
  apply iSup_le; intro E
  apply iSup_le; intro hE
  exact ENNReal.ofReal_le_ofReal (max_le (hP E hE) (hM E hE))

/-- The seminorm `‖U‖_σ` on `Hom_ℤ(K₀(D), ℂ)` (blueprint A9). For a stability condition
`σ = (Z, P)` and a group homomorphism `U : K₀(D) → ℂ`, this is
`sup { |U(E)| / |Z(E)| : E is σ-semistable and nonzero }`.
Values lie in `[0, ∞]`. -/
def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)

/-- The seminorm is nonneg: `stabSeminorm σ U ≥ 0`. This is trivially true since
`ℝ≥0∞` values are nonneg, but useful for API. -/
theorem stabSeminorm_nonneg (σ : StabilityCondition C) (U : K₀ C →+ ℂ) :
    0 ≤ stabSeminorm C σ U :=
  zero_le _

/-- The seminorm at zero is zero. -/
theorem stabSeminorm_zero (σ : StabilityCondition C) :
    stabSeminorm C σ 0 = 0 := by
  simp [stabSeminorm, AddMonoidHom.zero_apply, norm_zero, zero_div,
    ENNReal.ofReal_zero]

/-- The subspace `V(σ)` of group homomorphisms with finite seminorm (blueprint Node 6.3a).
This is an `AddSubgroup` of `K₀ C →+ ℂ` consisting of those `U` for which
`‖U‖_σ < ∞`. On a connected component of `Stab(D)`, this subspace is independent
of the chosen `σ` (by Lemma 6.2). -/
def finiteSeminormSubgroup (σ : StabilityCondition C) : AddSubgroup (K₀ C →+ ℂ) where
  carrier := {U | stabSeminorm C σ U < ⊤}
  add_mem' {U V} hU hV := by
    change stabSeminorm C σ (U + V) < ⊤
    have hsub : stabSeminorm C σ (U + V) ≤ stabSeminorm C σ U + stabSeminorm C σ V := by
      apply iSup_le; intro E; apply iSup_le; intro φ
      apply iSup_le; intro hP; apply iSup_le; intro hE
      calc ENNReal.ofReal (‖(U + V) (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)
          ≤ ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖ +
              ‖V (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) := by
            apply ENNReal.ofReal_le_ofReal
            rw [AddMonoidHom.add_apply, ← add_div]
            exact div_le_div_of_nonneg_right
              (norm_add_le _ _) (norm_nonneg _)
        _ = ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) +
            ENNReal.ofReal (‖V (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) :=
          ENNReal.ofReal_add (div_nonneg (norm_nonneg _) (norm_nonneg _))
            (div_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ stabSeminorm C σ U + stabSeminorm C σ V :=
          add_le_add (le_iSup_of_le E (le_iSup_of_le φ (le_iSup_of_le hP
            (le_iSup_of_le hE le_rfl))))
            (le_iSup_of_le E (le_iSup_of_le φ (le_iSup_of_le hP
              (le_iSup_of_le hE le_rfl))))
    exact lt_of_le_of_lt hsub (ENNReal.add_lt_top.mpr ⟨hU, hV⟩)
  zero_mem' := by change stabSeminorm C σ 0 < ⊤; rw [stabSeminorm_zero]; exact ENNReal.zero_lt_top
  neg_mem' {U} hU := by
    change stabSeminorm C σ (-U) < ⊤
    convert hU using 1
    simp [stabSeminorm, AddMonoidHom.neg_apply, norm_neg]

/-! ### Topology on Stab(D) -/

/-- The basis neighborhood `B_ε(σ)` for the Bridgeland topology (blueprint A10).
A stability condition `τ` lies in `B_ε(σ)` if the seminorm distance between
their central charges is less than `sin(πε)` and the slicing distance is less
than `ε`. -/
def basisNhd (σ : StabilityCondition C) (ε : ℝ) : Set (StabilityCondition C) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}

/-- The Bridgeland topology on `Stab(D)`, generated by the basis neighborhoods
`B_ε(σ)` for all stability conditions `σ` and all `ε ∈ (0, 1/8)`. -/
instance StabilityCondition.topologicalSpace :
    TopologicalSpace (StabilityCondition C) :=
  TopologicalSpace.generateFrom
    {U | ∃ (σ : StabilityCondition C) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧
      U = basisNhd C σ ε}

/-! ### Theorem 1.2 -/

/-- **Bridgeland's Theorem 1.2** (corrected statement). For each connected component
`Σ` of the topological space `Stab(D)` (with the Bridgeland topology), there exists
a linear subspace `V(Σ) ⊆ Hom_ℤ(K₀(D), ℂ)` with a topology such that the central
charge map `σ ↦ Z(σ)`, restricted to the component `Σ` and landing in `V(Σ)`, is a
local homeomorphism.

This uses `IsLocalHomeomorph` from `Mathlib.Topology.IsLocalHomeomorph`, avoiding
raw `PartialHomeomorph` with `@`-threaded topologies. The statement implies that each
connected component of `Stab(D)` is a manifold locally modelled on the topological
vector space `V(Σ)`. -/
def bridgelandTheorem_1_2 : Prop :=
  ∀ (cc : ConnectedComponents (StabilityCondition C)),
    ∃ (V : AddSubgroup (K₀ C →+ ℂ))
      (τ_V : TopologicalSpace V)
      (hZ : ∀ σ : StabilityCondition C,
        ConnectedComponents.mk σ = cc → σ.Z ∈ V),
      @IsLocalHomeomorph
        {σ : StabilityCondition C // ConnectedComponents.mk σ = cc}
        V inferInstance τ_V
        (fun ⟨σ, hσ⟩ ↦ ⟨σ.Z, hZ σ hσ⟩)

end CategoryTheory.Triangulated
