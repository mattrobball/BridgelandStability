/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.GrothendieckGroup
import BridgelandStability.IntervalCategory.QuasiAbelian
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option linter.style.longFile 1700

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

/-- **Sector norm bound (explicit exponential form)**. If complex numbers have the form
`m i * exp(i * θ i)` with `m i > 0` and all `θ i` in an interval `(α, α + w)` with `w < π`,
then `cos(w/2) · ∑ m i ≤ ‖∑ m i * exp(i θ i)‖`.

This variant avoids `Complex.arg` and works with explicit phase angles, which is needed when
phases can be any real number (not just in `(-π, π]`). Used in the **Lemma 6.2** sector bound. -/
theorem norm_sum_exp_ge_cos_mul_sum {ι : Type*} {s : Finset ι}
    {m : ι → ℝ} {θ : ι → ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i)
    {α w : ℝ} (hw0 : 0 ≤ w) (hwπ : w < Real.pi)
    (hθ : ∀ i ∈ s, θ i ∈ Set.Icc α (α + w)) :
    Real.cos (w / 2) * ∑ i ∈ s, m i ≤
      ‖∑ i ∈ s, ↑(m i) * exp (↑(θ i) * I)‖ := by
  -- Project onto the bisector direction β = α + w/2
  set β := α + w / 2
  -- Step 1: pointwise bound on real part after rotation
  have point : ∀ i ∈ s, Real.cos (w / 2) * m i ≤
      ((↑(m i) * exp (↑(θ i) * I)) * exp (-(↑β * I))).re := by
    intro i hi
    rw [mul_assoc, ← Complex.exp_add]
    have : ↑(θ i) * I + -(↑β * I) = ↑(θ i - β) * I := by push_cast; ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hd : |θ i - β| ≤ w / 2 := by
      rw [abs_le]; constructor <;> [have := (hθ i hi).1; have := (hθ i hi).2] <;>
        simp only [β] <;> linarith
    calc Real.cos (w / 2) * m i
        ≤ Real.cos (θ i - β) * m i := by
          apply mul_le_mul_of_nonneg_right _ (hm i hi)
          rw [← Real.cos_abs (θ i - β)]
          exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hd
      _ = m i * Real.cos (θ i - β) := mul_comm _ _
  -- Step 2: sum, then bound re by norm
  calc Real.cos (w / 2) * ∑ i ∈ s, m i
      = ∑ i ∈ s, (Real.cos (w / 2) * m i) := Finset.mul_sum s _ _
    _ ≤ ∑ i ∈ s, ((↑(m i) * exp (↑(θ i) * I)) * exp (-(↑β * I))).re :=
        Finset.sum_le_sum point
    _ ≤ ((∑ i ∈ s, ↑(m i) * exp (↑(θ i) * I)) * exp (-(↑β * I))).re := by
        rw [Finset.sum_mul, Complex.re_sum]
    _ ≤ ‖(∑ i ∈ s, ↑(m i) * exp (↑(θ i) * I)) * exp (-(↑β * I))‖ :=
        Complex.re_le_norm _
    _ = ‖∑ i ∈ s, ↑(m i) * exp (↑(θ i) * I)‖ := by
        rw [norm_mul]
        have : -(↑β * I) = ↑(-β) * I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### Stability conditions -/

/-- A Bridgeland stability condition on a triangulated category `C`.
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

/-- A real multiple of `exp(iπψ)` cannot equal a sum of positive real multiples of
`exp(iπθⱼ)` where all `θⱼ` lie strictly below `ψ` and above `ψ - 1`. The proof takes
the imaginary part after dividing by `exp(iπψ)`: since `sin(π(θⱼ - ψ)) < 0` for all `j`,
the imaginary part of the sum is strictly negative, contradicting the real LHS. -/
theorem no_exp_decomp_below {ψ : ℝ} {n : ℕ} (hn : 0 < n)
    {m : ℝ} {b : Fin n → ℝ} (hb : ∀ i, 0 < b i)
    {θ : Fin n → ℝ} (hθ_lt : ∀ i, θ i < ψ) (hθ_gt : ∀ i, ψ - 1 < θ i)
    (heq : (m : ℂ) * exp (↑(Real.pi * ψ) * I) =
      ∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * θ i) * I)) : False := by
  -- Divide both sides by exp(iπψ)
  have hexp_ne : exp (↑(Real.pi * ψ) * I) ≠ 0 := exp_ne_zero _
  have heq' : (m : ℂ) =
      ∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I) := by
    have h1 : ∀ i, (b i : ℂ) * exp (↑(Real.pi * θ i) * I) =
        (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I) *
          exp (↑(Real.pi * ψ) * I) := by
      intro i; rw [mul_assoc, ← exp_add]
      congr 1; push_cast; ring
    rw [show ∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * θ i) * I) =
      (∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)) *
        exp (↑(Real.pi * ψ) * I) from by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ ↦ h1 i)] at heq
    exact mul_right_cancel₀ hexp_ne heq
  -- Take imaginary part
  have him : (0 : ℝ) =
      (∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)).im := by
    rw [← Complex.ofReal_im m, heq']
  -- Each term has strictly negative imaginary part
  have hterm : ∀ i : Fin n,
      ((b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)).im < 0 := by
    intro i
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hb i)
      (Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [hθ_lt i, Real.pi_pos])
        (by nlinarith [hθ_gt i, Real.pi_pos]))
  -- Sum of strictly negative terms is negative
  have hsum : (∑ i : Fin n, ((b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)).im) < 0 :=
    Finset.sum_neg (fun i _ ↦ hterm i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have := map_sum Complex.imAddGroupHom
    (fun i : Fin n ↦ (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)) Finset.univ
  simp only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] at this
  linarith

/-- Symmetric version: a real multiple of `exp(iπψ)` cannot equal a sum of positive
real multiples of `exp(iπθⱼ)` where all `θⱼ` lie strictly above `ψ` and below `ψ + 1`. -/
theorem no_exp_decomp_above {ψ : ℝ} {n : ℕ} (hn : 0 < n)
    {m : ℝ} {b : Fin n → ℝ} (hb : ∀ i, 0 < b i)
    {θ : Fin n → ℝ} (hθ_gt : ∀ i, ψ < θ i) (hθ_lt : ∀ i, θ i < ψ + 1)
    (heq : (m : ℂ) * exp (↑(Real.pi * ψ) * I) =
      ∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * θ i) * I)) : False := by
  have hexp_ne : exp (↑(Real.pi * ψ) * I) ≠ 0 := exp_ne_zero _
  have heq' : (m : ℂ) =
      ∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I) := by
    have h1 : ∀ i, (b i : ℂ) * exp (↑(Real.pi * θ i) * I) =
        (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I) *
          exp (↑(Real.pi * ψ) * I) := by
      intro i; rw [mul_assoc, ← exp_add]
      congr 1; push_cast; ring
    rw [show ∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * θ i) * I) =
      (∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)) *
        exp (↑(Real.pi * ψ) * I) from by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ ↦ h1 i)] at heq
    exact mul_right_cancel₀ hexp_ne heq
  have him : (0 : ℝ) =
      (∑ i : Fin n, (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)).im := by
    rw [← Complex.ofReal_im m, heq']
  have hterm : ∀ i : Fin n,
      0 < ((b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)).im := by
    intro i
    have := Complex.exp_ofReal_mul_I_im (Real.pi * (θ i - ψ))
    rw [Complex.mul_im, this, Complex.ofReal_im, zero_mul, add_zero,
      Complex.ofReal_re]
    exact mul_pos (by exact_mod_cast hb i)
      (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hθ_gt i, Real.pi_pos])
        (by nlinarith [hθ_lt i, Real.pi_pos]))
  have hsum : 0 < (∑ i : Fin n, ((b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)).im) :=
    Finset.sum_pos (fun i _ ↦ hterm i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have := map_sum Complex.imAddGroupHom
    (fun i : Fin n ↦ (b i : ℂ) * exp (↑(Real.pi * (θ i - ψ)) * I)) Finset.univ
  simp only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] at this
  linarith

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

/-! ### Sector bound (Lemma 6.2 core) -/

/-- **Sector bound (Lemma 6.2 core)**. For a stability condition `σ = (Z, P)` and a group
homomorphism `U : K₀ C →+ ℂ`, if every semistable factor satisfies
`‖U([A])‖ ≤ M · ‖Z([A])‖`, then the bound extends to any object `E` with narrow HN width:
`‖U([E])‖ ≤ (M / cos(πη/2)) · ‖Z([E])‖`, where `η` bounds the HN phase width.

The proof decomposes `E` via its HN filtration (a PostnikovTower with phase data),
applies K₀ additivity, the pointwise seminorm bound on factors, and the
sector estimate `norm_sum_exp_ge_cos_mul_sum`. -/
theorem sector_bound (σ : StabilityCondition C) (U : K₀ C →+ ℂ)
    {E : C} (F : HNFiltration C σ.slicing.P E) (hn : 0 < F.n)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1)
    (hwidth : F.φ ⟨0, hn⟩ - F.φ ⟨F.n - 1, by omega⟩ ≤ η)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ (A : C) (φ : ℝ), σ.slicing.P φ A → ¬IsZero A →
      ‖U (K₀.of C A)‖ ≤ M * ‖σ.Z (K₀.of C A)‖) :
    ‖U (K₀.of C E)‖ ≤
      M / Real.cos (Real.pi * η / 2) * ‖σ.Z (K₀.of C E)‖ := by
  set P := F.toPostnikovTower
  -- K₀ decomposition
  have hK₀ : K₀.of C E = ∑ i : Fin F.n, K₀.of C (P.factor i) :=
    K₀.of_postnikovTower_eq_sum C P
  -- U and Z decompose over factors
  have hUE : U (K₀.of C E) = ∑ i : Fin F.n, U (K₀.of C (P.factor i)) := by
    rw [hK₀, map_sum]
  have hZE : σ.Z (K₀.of C E) = ∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i)) := by
    rw [hK₀, map_sum]
  -- Seminorm bound on each factor
  have hMi : ∀ i : Fin F.n,
      ‖U (K₀.of C (P.factor i))‖ ≤ M * ‖σ.Z (K₀.of C (P.factor i))‖ := by
    intro i
    by_cases hi : IsZero (P.factor i)
    · have h0 := K₀.of_isZero C hi; simp [h0]
    · exact hM _ _ (F.semistable i) hi
  -- Z decomposition: Z(factor i) = ‖Z(factor i)‖ * exp(iπφᵢ)
  have hZi : ∀ i : Fin F.n,
      σ.Z (K₀.of C (P.factor i)) =
      ↑(‖σ.Z (K₀.of C (P.factor i))‖) * exp (↑(Real.pi * F.φ i) * I) := by
    intro i
    by_cases hi : IsZero (P.factor i)
    · have h0 := K₀.of_isZero C hi; simp [h0]
    · obtain ⟨m, hm, hmZ⟩ := σ.compat (F.φ i) (P.factor i) (F.semistable i) hi
      rw [hmZ]; congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  -- Phase containment
  set α := Real.pi * F.φ ⟨F.n - 1, by omega⟩
  set w := Real.pi * η
  have hwπ : w < Real.pi := by
    change Real.pi * η < Real.pi; nlinarith [Real.pi_pos]
  have hw0 : 0 ≤ w := by change 0 ≤ Real.pi * η; positivity
  have hθ : ∀ i : Fin F.n, Real.pi * F.φ i ∈ Set.Icc α (α + w) := by
    intro i; simp only [Set.mem_Icc, α, w]; constructor
    · exact mul_le_mul_of_nonneg_left
        (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))) (le_of_lt Real.pi_pos)
    · calc Real.pi * F.φ i
          ≤ Real.pi * F.φ ⟨0, hn⟩ := mul_le_mul_of_nonneg_left
            (F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) (le_of_lt Real.pi_pos)
        _ ≤ Real.pi * F.φ ⟨F.n - 1, by omega⟩ + Real.pi * η := by nlinarith
  -- Sector estimate: cos(πη/2) * ∑ ‖Z(fi)‖ ≤ ‖Z(E)‖
  have hcos_pos : 0 < Real.cos (w / 2) := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> [linarith; linarith]
  have hsector : Real.cos (w / 2) * ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖ ≤
      ‖σ.Z (K₀.of C E)‖ := by
    calc Real.cos (w / 2) * ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖
        ≤ ‖∑ i : Fin F.n,
            ↑(‖σ.Z (K₀.of C (P.factor i))‖) * exp (↑(Real.pi * F.φ i) * I)‖ :=
          norm_sum_exp_ge_cos_mul_sum (fun i _ ↦ norm_nonneg _) hw0 hwπ (fun i _ ↦ hθ i)
      _ = ‖∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i))‖ := by
          congr 1; exact Finset.sum_congr rfl (fun i _ ↦ (hZi i).symm)
      _ = ‖σ.Z (K₀.of C E)‖ := by rw [← hZE]
  -- Combine
  have hsum_bound : ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖ ≤
      ‖σ.Z (K₀.of C E)‖ / Real.cos (w / 2) := by
    rw [le_div_iff₀ hcos_pos, mul_comm]; exact hsector
  calc ‖U (K₀.of C E)‖
      = ‖∑ i : Fin F.n, U (K₀.of C (P.factor i))‖ := by rw [hUE]
    _ ≤ ∑ i : Fin F.n, ‖U (K₀.of C (P.factor i))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin F.n, M * ‖σ.Z (K₀.of C (P.factor i))‖ :=
        Finset.sum_le_sum (fun i _ ↦ hMi i)
    _ = M * ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ M * (‖σ.Z (K₀.of C E)‖ / Real.cos (w / 2)) :=
        mul_le_mul_of_nonneg_left hsum_bound hM0
    _ = M / Real.cos (Real.pi * η / 2) * ‖σ.Z (K₀.of C E)‖ := by
        change M * (‖σ.Z (K₀.of C E)‖ / Real.cos (Real.pi * η / 2)) =
          M / Real.cos (Real.pi * η / 2) * ‖σ.Z (K₀.of C E)‖
        ring

/-- Sector bound using intrinsic phase width `phiPlus - phiMinus`. -/
theorem sector_bound' (σ : StabilityCondition C) (U : K₀ C →+ ℂ)
    {E : C} (hE : ¬IsZero E) {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1)
    (hwidth : σ.slicing.phiPlus C E hE - σ.slicing.phiMinus C E hE ≤ η)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ (A : C) (φ : ℝ), σ.slicing.P φ A → ¬IsZero A →
      ‖U (K₀.of C A)‖ ≤ M * ‖σ.Z (K₀.of C A)‖) :
    ‖U (K₀.of C E)‖ ≤
      M / Real.cos (Real.pi * η / 2) * ‖σ.Z (K₀.of C E)‖ := by
  obtain ⟨F, hn, hP, hM'⟩ := σ.slicing.exists_HN_intrinsic_width C hE
  exact sector_bound C σ U F hn hη hη1 (by rw [hP, hM']; exact hwidth) hM0 hM

/-- **Node 6.2d**: For a `τ`-semistable nonzero object `E` of phase `φ` with
`d(σ, τ) < ε < 1/2`, the `σ`-HN width of `E` is less than `2ε`, so the sector
bound applies. Combined with the seminorm bound on `W - Z`, this controls
`‖Z([E])‖` by `‖W([E])‖` (where `W = τ.Z` and `Z = σ.Z`). -/
theorem norm_Z_le_of_tau_semistable (σ τ : StabilityCondition C)
    {E : C} {φ : ℝ} (hE : ¬IsZero E) (hS : τ.slicing.P φ E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM_bound : ∀ (A : C) (ψ : ℝ), σ.slicing.P ψ A → ¬IsZero A →
      ‖(τ.Z - σ.Z) (K₀.of C A)‖ ≤ M * ‖σ.Z (K₀.of C A)‖) :
    (1 - M / Real.cos (Real.pi * ε)) * ‖σ.Z (K₀.of C E)‖ ≤
      ‖τ.Z (K₀.of C E)‖ := by
  -- The σ-HN width of E is < 2ε (since E is τ-semistable of phase φ and d < ε)
  have hbounds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hS hd
  have hwidth : σ.slicing.phiPlus C E hE - σ.slicing.phiMinus C E hE ≤ 2 * ε := by
    have := hbounds.1; have := hbounds.2
    rw [Set.mem_Ioo] at *; linarith
  -- Apply sector bound with η = 2ε to U = τ.Z - σ.Z
  have h2ε : 2 * ε < 1 := by linarith
  have hcos_eq : Real.pi * (2 * ε) / 2 = Real.pi * ε := by ring
  have hsector := sector_bound' C σ (τ.Z - σ.Z) hE (by linarith) h2ε hwidth hM0 hM_bound
  rw [hcos_eq] at hsector
  -- ‖(τ.Z - σ.Z)([E])‖ ≤ M / cos(πε) * ‖Z([E])‖
  -- By reverse triangle inequality:
  -- ‖τ.Z([E])‖ ≥ ‖Z([E])‖ - ‖(τ.Z - σ.Z)([E])‖
  --            ≥ ‖Z([E])‖ - M/cos(πε) * ‖Z([E])‖
  --            = (1 - M/cos(πε)) * ‖Z([E])‖
  have hkey : ‖(τ.Z - σ.Z) (K₀.of C E)‖ ≤
      M / Real.cos (Real.pi * ε) * ‖σ.Z (K₀.of C E)‖ := hsector
  calc (1 - M / Real.cos (Real.pi * ε)) * ‖σ.Z (K₀.of C E)‖
      = ‖σ.Z (K₀.of C E)‖ - M / Real.cos (Real.pi * ε) * ‖σ.Z (K₀.of C E)‖ := by ring
    _ ≤ ‖σ.Z (K₀.of C E)‖ - ‖(τ.Z - σ.Z) (K₀.of C E)‖ := by linarith
    _ ≤ ‖τ.Z (K₀.of C E)‖ := by
        have : ‖σ.Z (K₀.of C E)‖ ≤ ‖τ.Z (K₀.of C E)‖ +
          ‖(τ.Z - σ.Z) (K₀.of C E)‖ := by
          calc ‖σ.Z (K₀.of C E)‖
              = ‖τ.Z (K₀.of C E) - (τ.Z - σ.Z) (K₀.of C E)‖ := by
                congr 1; simp [AddMonoidHom.sub_apply]
            _ ≤ ‖τ.Z (K₀.of C E)‖ + ‖(τ.Z - σ.Z) (K₀.of C E)‖ :=
                norm_sub_le _ _
        linarith

/-! ### Seminorm comparison (Lemma 6.2 consequence) -/

/-- For σ-semistable nonzero `A`, the ratio `‖U(A)‖/‖Z(A)‖` is bounded by the seminorm. -/
lemma stabSeminorm_bound_real (σ : StabilityCondition C) (U : K₀ C →+ ℂ)
    (hfin : stabSeminorm C σ U ≠ ⊤)
    {A : C} {ψ : ℝ} (hP : σ.slicing.P ψ A) (hA : ¬IsZero A) :
    ‖U (K₀.of C A)‖ ≤ (stabSeminorm C σ U).toReal * ‖σ.Z (K₀.of C A)‖ := by
  obtain ⟨m, hm, hmZ⟩ := σ.compat ψ A hP hA
  have hZ_pos : (0 : ℝ) < ‖σ.Z (K₀.of C A)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  have h1 : ENNReal.ofReal (‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖) ≤
      stabSeminorm C σ U :=
    le_iSup_of_le A (le_iSup_of_le ψ (le_iSup_of_le hP (le_iSup_of_le hA le_rfl)))
  have hratio : ‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖ ≤
      (stabSeminorm C σ U).toReal := by
    calc ‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖
        = (ENNReal.ofReal (‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖)).toReal :=
          (ENNReal.toReal_ofReal (div_nonneg (norm_nonneg _) (norm_nonneg _))).symm
      _ ≤ (stabSeminorm C σ U).toReal := ENNReal.toReal_mono hfin h1
  calc ‖U (K₀.of C A)‖
      = ‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖ * ‖σ.Z (K₀.of C A)‖ := by
        rw [div_mul_cancel₀ _ (ne_of_gt hZ_pos)]
    _ ≤ (stabSeminorm C σ U).toReal * ‖σ.Z (K₀.of C A)‖ :=
        mul_le_mul_of_nonneg_right hratio (le_of_lt hZ_pos)

/-- **Seminorm comparison for same central charge** (**Lemma 6.2** consequence).
If `σ` and `τ` have the same central charge and `d(P, Q) < ε < 1/2`, then
`‖U‖_τ < ⊤` whenever `‖U‖_σ < ⊤`. This shows `V(σ) ⊆ V(τ)`, and by symmetry
`V(σ) = V(τ)` for nearby stability conditions with the same central charge. -/
theorem stabSeminorm_lt_top_of_same_Z (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    (U : K₀ C →+ ℂ) (hU : stabSeminorm C σ U < ⊤) :
    stabSeminorm C τ U < ⊤ := by
  have hU_ne : stabSeminorm C σ U ≠ ⊤ := ne_top_of_lt hU
  set M := (stabSeminorm C σ U).toReal with hM_def
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  -- M bounds ‖U(A)‖ for each σ-semistable nonzero A
  have hM_bound : ∀ (A : C) (ψ : ℝ), σ.slicing.P ψ A → ¬IsZero A →
      ‖U (K₀.of C A)‖ ≤ M * ‖σ.Z (K₀.of C A)‖ :=
    fun A ψ hP hA ↦ stabSeminorm_bound_real C σ U hU_ne hP hA
  -- cos(πε) > 0 since ε < 1/2
  have hcos_pos : 0 < Real.cos (Real.pi * ε) := by
    apply Real.cos_pos_of_mem_Ioo; constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  -- Bound each term in the τ-seminorm iSup by M / cos(πε)
  suffices h : stabSeminorm C τ U ≤
      ENNReal.ofReal (M / Real.cos (Real.pi * ε)) from
    lt_of_le_of_lt h ENNReal.ofReal_lt_top
  apply iSup_le; intro E; apply iSup_le; intro φ
  apply iSup_le; intro hP; apply iSup_le; intro hE
  apply ENNReal.ofReal_le_ofReal
  -- Goal: ‖U(E)‖ / ‖τ.Z(E)‖ ≤ M / cos(πε)
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hP hE
  have hZ_pos : (0 : ℝ) < ‖τ.Z (K₀.of C E)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  -- Sector bound: ‖U(E)‖ ≤ (M / cos(πε)) * ‖τ.Z(E)‖
  have hbounds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hP hd
  have hwidth : σ.slicing.phiPlus C E hE - σ.slicing.phiMinus C E hE ≤ 2 * ε := by
    have := hbounds.1; have := hbounds.2; rw [Set.mem_Ioo] at *; linarith
  have h2ε : 2 * ε < 1 := by linarith
  have hcos_eq : Real.pi * (2 * ε) / 2 = Real.pi * ε := by ring
  have hsector := sector_bound' C σ U hE (by linarith : (0 : ℝ) ≤ 2 * ε) h2ε hwidth hM0
    hM_bound
  rw [hcos_eq, hZ] at hsector
  calc ‖U (K₀.of C E)‖ / ‖τ.Z (K₀.of C E)‖
      ≤ M / Real.cos (Real.pi * ε) * ‖τ.Z (K₀.of C E)‖ / ‖τ.Z (K₀.of C E)‖ :=
        div_le_div_of_nonneg_right hsector (le_of_lt hZ_pos)
    _ = M / Real.cos (Real.pi * ε) :=
        mul_div_cancel_right₀ _ (ne_of_gt hZ_pos)

/-- **Proposition 6.3 (same Z case)**. If `σ` and `τ` have the same central charge
and `d(P, Q) < ε < 1/2`, then the finite seminorm subgroups agree: `V(σ) = V(τ)`.
This is the key ingredient for showing `V(Σ)` is well-defined on connected components. -/
theorem finiteSeminormSubgroup_eq_of_same_Z (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε) :
    finiteSeminormSubgroup C σ = finiteSeminormSubgroup C τ := by
  ext U; simp only [finiteSeminormSubgroup, AddSubgroup.mem_mk]
  constructor
  · exact stabSeminorm_lt_top_of_same_Z C σ τ hZ hε hε1 hd U
  · rw [slicingDist_symm] at hd
    exact stabSeminorm_lt_top_of_same_Z C τ σ hZ.symm hε hε1 hd U

/-- **General Lemma 6.2** (explicit seminorm bound). If `d(P, Q) < ε < 1/2`
and `‖τ.Z - σ.Z‖_σ < cos(πε)`, then for any `U` with finite `σ`-seminorm, the
`τ`-seminorm is bounded: `‖U‖_τ ≤ ‖U‖_σ / (cos(πε) - ‖τ.Z - σ.Z‖_σ)`.

This is the quantitative core of the seminorm comparison, used for both
`stabSeminorm_lt_top_of_near` and the reverse direction of **Proposition 6.3**. -/
theorem stabSeminorm_le_of_near (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    (hZdiff : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)))
    (U : K₀ C →+ ℂ) (hU : stabSeminorm C σ U ≠ ⊤) :
    stabSeminorm C τ U ≤
      ENNReal.ofReal ((stabSeminorm C σ U).toReal /
        (Real.cos (Real.pi * ε) - (stabSeminorm C σ (τ.Z - σ.Z)).toReal)) := by
  have hZdiff_ne : stabSeminorm C σ (τ.Z - σ.Z) ≠ ⊤ :=
    ne_top_of_lt (lt_trans hZdiff ENNReal.ofReal_lt_top)
  set M_U := (stabSeminorm C σ U).toReal
  set M_Z := (stabSeminorm C σ (τ.Z - σ.Z)).toReal
  have hMU0 : 0 ≤ M_U := ENNReal.toReal_nonneg
  have hMZ0 : 0 ≤ M_Z := ENNReal.toReal_nonneg
  have hcos_pos : 0 < Real.cos (Real.pi * ε) := by
    apply Real.cos_pos_of_mem_Ioo; constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hMZ_lt : M_Z < Real.cos (Real.pi * ε) := by
    by_contra hle; push_neg at hle
    have h1 : ENNReal.ofReal (Real.cos (Real.pi * ε)) ≤ ENNReal.ofReal M_Z :=
      ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_toReal hZdiff_ne] at h1
    exact absurd hZdiff (not_lt.mpr h1)
  set c := Real.cos (Real.pi * ε) with hc_def
  have hcMZ : 0 < c - M_Z := by linarith
  have hMU_bound : ∀ (A : C) (ψ : ℝ), σ.slicing.P ψ A → ¬IsZero A →
      ‖U (K₀.of C A)‖ ≤ M_U * ‖σ.Z (K₀.of C A)‖ :=
    fun A ψ hP hA ↦ stabSeminorm_bound_real C σ U hU hP hA
  have hMZ_bound : ∀ (A : C) (ψ : ℝ), σ.slicing.P ψ A → ¬IsZero A →
      ‖(τ.Z - σ.Z) (K₀.of C A)‖ ≤ M_Z * ‖σ.Z (K₀.of C A)‖ :=
    fun A ψ hP hA ↦ stabSeminorm_bound_real C σ (τ.Z - σ.Z) hZdiff_ne hP hA
  apply iSup_le; intro E; apply iSup_le; intro φ
  apply iSup_le; intro hP; apply iSup_le; intro hE
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hP hE
  have hZτ_pos : (0 : ℝ) < ‖τ.Z (K₀.of C E)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  have hbounds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hP hd
  have hwidth : σ.slicing.phiPlus C E hE - σ.slicing.phiMinus C E hE ≤ 2 * ε := by
    have := hbounds.1; have := hbounds.2; rw [Set.mem_Ioo] at *; linarith
  have h2ε : 2 * ε < 1 := by linarith
  have hcos_eq : Real.pi * (2 * ε) / 2 = Real.pi * ε := by ring
  have hsector := sector_bound' C σ U hE (by linarith : (0 : ℝ) ≤ 2 * ε) h2ε hwidth hMU0
    hMU_bound
  rw [hcos_eq] at hsector
  have hreverse := norm_Z_le_of_tau_semistable C σ τ hE hP hε hε1 hd hMZ0 hMZ_bound
  have hσZ_le : ‖σ.Z (K₀.of C E)‖ ≤ c / (c - M_Z) * ‖τ.Z (K₀.of C E)‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcMZ]
    have hmul := mul_le_mul_of_nonneg_left hreverse (le_of_lt hcos_pos)
    have heq : c * ((1 - M_Z / c) * ‖σ.Z (K₀.of C E)‖) =
        (c - M_Z) * ‖σ.Z (K₀.of C E)‖ := by
      field_simp
    linarith
  calc ‖U (K₀.of C E)‖ / ‖τ.Z (K₀.of C E)‖
      ≤ (M_U / c * ‖σ.Z (K₀.of C E)‖) / ‖τ.Z (K₀.of C E)‖ :=
        div_le_div_of_nonneg_right hsector (le_of_lt hZτ_pos)
    _ ≤ (M_U / c * (c / (c - M_Z) * ‖τ.Z (K₀.of C E)‖)) /
          ‖τ.Z (K₀.of C E)‖ := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hZτ_pos)
        exact mul_le_mul_of_nonneg_left hσZ_le (div_nonneg hMU0 (le_of_lt hcos_pos))
    _ = M_U / (c - M_Z) := by
        field_simp [ne_of_gt hcos_pos, ne_of_gt hcMZ, ne_of_gt hZτ_pos]

/-- **General Lemma 6.2** (seminorm finiteness comparison). If `d(P, Q) < ε < 1/2`
and `‖τ.Z - σ.Z‖_σ < cos(πε)`, then `V(σ) ⊆ V(τ)`. -/
theorem stabSeminorm_lt_top_of_near (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    (hZdiff : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)))
    (U : K₀ C →+ ℂ) (hU : stabSeminorm C σ U < ⊤) :
    stabSeminorm C τ U < ⊤ :=
  lt_of_le_of_lt
    (stabSeminorm_le_of_near C σ τ hε hε1 hd hZdiff U (ne_top_of_lt hU))
    ENNReal.ofReal_lt_top

/-- **Proposition 6.3** (V(Σ) equality for nearby stability conditions). If
`τ ∈ B_ε(σ)` with `ε < 1/8`, then `V(σ) = V(τ)`. This shows the subgroup `V`
is locally constant on `Stab(D)`, hence constant on connected components.

The forward direction uses `stabSeminorm_le_of_near`. The reverse direction uses
the explicit bound to show `‖σ.Z - τ.Z‖_τ < cos(πε)`, then applies the
comparison with `σ` and `τ` swapped. The key inequality is
`sin(πε) · (1 + cos(πε)) < cos²(πε)` for `ε < 1/8`, proved via
`sin(x) < x` and `x² + 2x < 1` for `x = πε < π/8 < √2 - 1`. -/
theorem finiteSeminormSubgroup_eq_of_basisNhd (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 8)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    (hZnorm : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    finiteSeminormSubgroup C σ = finiteSeminormSubgroup C τ := by
  have hε2 : ε < 1 / 2 := by linarith
  -- sin(πε) < cos(πε) for ε < 1/4, so the Z-norm hypothesis implies < cos(πε)
  have hsin_lt_cos : Real.sin (Real.pi * ε) < Real.cos (Real.pi * ε) := by
    rw [← Real.cos_pi_div_two_sub]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcos_pos' : 0 < Real.cos (Real.pi * ε) := by
    apply Real.cos_pos_of_mem_Ioo; constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hZdiff : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)) :=
    lt_trans hZnorm ((ENNReal.ofReal_lt_ofReal_iff hcos_pos').mpr hsin_lt_cos)
  -- Forward: V(σ) ⊆ V(τ)
  have hfwd : ∀ U, stabSeminorm C σ U < ⊤ → stabSeminorm C τ U < ⊤ :=
    fun U hU ↦ stabSeminorm_lt_top_of_near C σ τ hε hε2 hd hZdiff U hU
  -- Reverse: V(τ) ⊆ V(σ)
  -- Step 1: Bound ‖τ.Z - σ.Z‖_τ using the explicit bound
  have hZdiff_ne : stabSeminorm C σ (τ.Z - σ.Z) ≠ ⊤ :=
    ne_top_of_lt (lt_trans hZdiff ENNReal.ofReal_lt_top)
  set M_Z := (stabSeminorm C σ (τ.Z - σ.Z)).toReal with hMZ_def
  have hMZ0 : 0 ≤ M_Z := ENNReal.toReal_nonneg
  have hMZ_lt_sin : M_Z < Real.sin (Real.pi * ε) := by
    by_contra hle; push_neg at hle
    have h1 : ENNReal.ofReal (Real.sin (Real.pi * ε)) ≤ ENNReal.ofReal M_Z :=
      ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_toReal hZdiff_ne] at h1
    exact absurd hZnorm (not_lt.mpr h1)
  have hcos_pos := hcos_pos'
  have hMZ_lt_cos : M_Z < Real.cos (Real.pi * ε) := lt_trans hMZ_lt_sin hsin_lt_cos
  set c := Real.cos (Real.pi * ε)
  have hcMZ : 0 < c - M_Z := by linarith
  -- Step 2: Apply explicit bound to U = τ.Z - σ.Z
  have hZbound : stabSeminorm C τ (τ.Z - σ.Z) ≤
      ENNReal.ofReal (M_Z / (c - M_Z)) :=
    stabSeminorm_le_of_near C σ τ hε hε2 hd hZdiff (τ.Z - σ.Z) hZdiff_ne
  -- Step 3: Show M_Z / (c - M_Z) < cos(πε) via the trigonometric inequality
  -- This is equivalent to M_Z · (1 + c) < c², which follows from
  -- M_Z < sin(πε) and sin(πε) · (1 + cos(πε)) < cos²(πε).
  -- Proof: sin(x)(1+cos(x)) ≤ 2x and cos²(x) ≥ 1-x², and 2x + x² < 1 for x < √2-1 > π/8.
  have hsin_pos : 0 < Real.sin (Real.pi * ε) := by
    exact Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  -- Key: sin(πε) · (1 + cos(πε)) < cos²(πε)
  -- Use sin(πε) ≤ πε, 1 + cos(πε) ≤ 2, cos²(πε) ≥ 1 - (πε)²
  have hsin_le : Real.sin (Real.pi * ε) ≤ Real.pi * ε :=
    Real.sin_le (by nlinarith [Real.pi_pos])
  have hx_bound : Real.pi * ε < Real.pi / 8 := by nlinarith [Real.pi_pos]
  -- (πε)² + 2(πε) < 1, which gives sin(πε)(1+cos(πε)) < cos²(πε)
  have hx_ineq : (Real.pi * ε) ^ 2 + 2 * (Real.pi * ε) < 1 := by
    -- Need π²ε² + 2πε < 1 for ε < 1/8.
    -- Equivalent to (π/8)² + π/4 < 1, i.e., π² + 16π < 64.
    -- Use π < 3.15 (from pi_lt_d2): 3.15² + 16·3.15 = 9.9225 + 50.4 = 60.3225 < 64. ✓
    have hpi := Real.pi_lt_d2 -- π < 3.15
    nlinarith [Real.pi_pos, sq_nonneg Real.pi, sq_nonneg ε]
  have hMZ_bound : M_Z * (1 + c) < c ^ 2 := by
    calc M_Z * (1 + c)
        < Real.sin (Real.pi * ε) * (1 + c) :=
          mul_lt_mul_of_pos_right hMZ_lt_sin (by linarith)
      _ ≤ (Real.pi * ε) * 2 := by
          have hcos_le : c ≤ 1 := Real.cos_le_one _
          have : 1 + c ≤ 2 := by linarith
          exact mul_le_mul hsin_le this (by linarith) (by nlinarith [Real.pi_pos])
      _ = 2 * (Real.pi * ε) := by ring
      _ < 1 - (Real.pi * ε) ^ 2 := by linarith
      _ ≤ c ^ 2 := by
          -- cos²(x) = 1 - sin²(x) ≥ 1 - x² since sin(x) ≤ x and 0 ≤ sin(x)
          have hsin_sq : Real.sin (Real.pi * ε) ^ 2 ≤ (Real.pi * ε) ^ 2 := by
            rw [sq, sq]
            exact mul_le_mul hsin_le hsin_le (le_of_lt hsin_pos)
              (by nlinarith [Real.pi_pos])
          have := Real.sin_sq_add_cos_sq (Real.pi * ε)
          nlinarith
  have hbound_lt_cos : M_Z / (c - M_Z) < c := by
    rw [div_lt_iff₀ hcMZ]; linarith
  -- Step 4: Conclude ‖σ.Z - τ.Z‖_τ < cos(πε)
  have hZτ_bound : stabSeminorm C τ (σ.Z - τ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)) := by
    have : stabSeminorm C τ (σ.Z - τ.Z) = stabSeminorm C τ (τ.Z - σ.Z) := by
      simp only [stabSeminorm, AddMonoidHom.sub_apply]
      congr 1; ext E; congr 1; ext φ; congr 1; ext; congr 1; ext
      rw [norm_sub_rev]
    rw [this]
    exact lt_of_le_of_lt hZbound
      ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hbound_lt_cos)
  -- Step 5: Apply stabSeminorm_lt_top_of_near in reverse
  have hrev : ∀ U, stabSeminorm C τ U < ⊤ → stabSeminorm C σ U < ⊤ := by
    intro U hU
    have hd_sym : slicingDist C τ.slicing σ.slicing < ENNReal.ofReal ε := by
      rwa [slicingDist_symm]
    exact stabSeminorm_lt_top_of_near C τ σ hε hε2 hd_sym hZτ_bound U hU
  ext U; simp only [finiteSeminormSubgroup, AddSubgroup.mem_mk]
  exact ⟨hfwd U, hrev U⟩

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

/-! ### Lemma 6.4: Local injectivity -/

/-- **One-sided phase impossibility for Lemma 6.4** (below). If `σ` and `τ` have the same
central charge, `E` is nonzero and `τ`-semistable of phase `φ`, and all nonzero factors
in a `σ`-HN filtration of `E` have phase strictly below `φ` (and above `φ - 1`), then
we reach a contradiction.

The proof decomposes `Z(E) = Σ Z(Fᵢ)` via K₀ additivity, divides by `exp(iπφ)`,
and shows the imaginary part is both zero (since `Z(E) = m · exp(iπφ)` is on a ray)
and strictly negative (since each nonzero factor contributes a negative `sin` term). -/
theorem StabilityCondition.False_of_all_HN_phases_below (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z) {E : C} {φ : ℝ} (hE : ¬IsZero E)
    (hτ : (τ.slicing.P φ) E)
    (F : HNFiltration C σ.slicing.P E)
    (hlt : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) → F.φ i < φ)
    (hgt : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) →
      φ - 1 < F.φ i) : False := by
  -- Get the central charge ray from τ-semistability
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hτ hE
  rw [← hZ] at hmZ
  -- K₀ additivity: Z(E) = Σ Z(factor i)
  have hK₀ : σ.Z (K₀.of C E) =
      ∑ i : Fin F.n, σ.Z (K₀.of C (F.toPostnikovTower.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum, map_sum]
  -- Define the divided term: w i = Z(factor i) * exp(-iπφ)
  set w : Fin F.n → ℂ := fun i ↦
    σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * exp (-(↑(Real.pi * φ) * I))
  -- Sum of divided terms equals m (real)
  have hsum : (m : ℂ) = ∑ i : Fin F.n, w i := by
    have h1 : σ.Z (K₀.of C E) * exp (-(↑(Real.pi * φ) * I)) =
        ∑ i : Fin F.n, w i := by
      rw [hK₀, Finset.sum_mul]
    rw [hmZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * φ) * I + -(↑(Real.pi * φ) * I) = 0 from by ring,
      exp_zero, mul_one] at h1
    exact h1
  -- For nonzero factor i: w i has strictly negative imaginary part
  have hw_neg : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) →
      (w i).im < 0 := by
    intro i hi
    obtain ⟨b, hb, hbZ⟩ := σ.compat (F.φ i) _ (F.semistable i) hi
    change (σ.Z (K₀.of C _) * exp (-(↑(Real.pi * φ) * I))).im < 0
    rw [hbZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * F.φ i) * I + -(↑(Real.pi * φ) * I) =
        ↑(Real.pi * (F.φ i - φ)) * I from by push_cast; ring]
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hb)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [hlt i hi, Real.pi_pos])
        (by nlinarith [hgt i hi, Real.pi_pos]))
  -- For zero factor i: w i = 0
  have hw_zero : ∀ i : Fin F.n, IsZero (F.toPostnikovTower.factor i) →
      w i = 0 := by
    intro i hi
    change σ.Z (K₀.of C _) * _ = 0
    rw [K₀.of_isZero C hi, map_zero, zero_mul]
  -- At least one nonzero factor exists (otherwise Z(E) = 0, contradicting m > 0)
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) := by
    by_contra hall; push_neg at hall
    have : (m : ℂ) = 0 := by
      rw [hsum, Finset.sum_eq_zero (fun i _ ↦ hw_zero i (hall i))]
    exact absurd (Complex.ofReal_eq_zero.mp this) (ne_of_gt hm)
  -- Each imaginary part ≤ 0, with i₀ strictly < 0
  have him_le : ∀ i : Fin F.n, (w i).im ≤ 0 := by
    intro i
    by_cases hi : IsZero (F.toPostnikovTower.factor i)
    · rw [hw_zero i hi]; exact le_rfl
    · exact le_of_lt (hw_neg i hi)
  have him_neg : ∑ i : Fin F.n, (w i).im < 0 := by
    calc ∑ i : Fin F.n, (w i).im
        < ∑ i : Fin F.n, (0 : ℝ) :=
          Finset.sum_lt_sum (fun i _ ↦ him_le i)
            ⟨i₀, Finset.mem_univ _, hw_neg i₀ hi₀⟩
      _ = 0 := Finset.sum_const_zero
  -- But Im(Σ w i) = Im(m) = 0
  have him_eq : (∑ i : Fin F.n, w i).im = ∑ i : Fin F.n, (w i).im := by
    have := map_sum Complex.imAddGroupHom w Finset.univ
    simp only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] at this
    exact this
  have him_zero : (∑ i : Fin F.n, w i).im = 0 := by
    rw [← hsum]; exact Complex.ofReal_im m
  linarith

/-- **One-sided phase impossibility for Lemma 6.4** (above). Symmetric version of
`False_of_all_HN_phases_below`: if all nonzero factors have phase strictly above `φ`
(and below `φ + 1`), we also reach a contradiction. -/
theorem StabilityCondition.False_of_all_HN_phases_above (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z) {E : C} {φ : ℝ} (hE : ¬IsZero E)
    (hτ : (τ.slicing.P φ) E)
    (F : HNFiltration C σ.slicing.P E)
    (hgt : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) → φ < F.φ i)
    (hlt : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) →
      F.φ i < φ + 1) : False := by
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hτ hE
  rw [← hZ] at hmZ
  have hK₀ : σ.Z (K₀.of C E) =
      ∑ i : Fin F.n, σ.Z (K₀.of C (F.toPostnikovTower.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum, map_sum]
  set w : Fin F.n → ℂ := fun i ↦
    σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * exp (-(↑(Real.pi * φ) * I))
  have hsum : (m : ℂ) = ∑ i : Fin F.n, w i := by
    have h1 : σ.Z (K₀.of C E) * exp (-(↑(Real.pi * φ) * I)) =
        ∑ i : Fin F.n, w i := by
      rw [hK₀, Finset.sum_mul]
    rw [hmZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * φ) * I + -(↑(Real.pi * φ) * I) = 0 from by ring,
      exp_zero, mul_one] at h1
    exact h1
  -- For nonzero factor i: w i has strictly positive imaginary part
  have hw_pos : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) →
      0 < (w i).im := by
    intro i hi
    obtain ⟨b, hb, hbZ⟩ := σ.compat (F.φ i) _ (F.semistable i) hi
    change 0 < (σ.Z (K₀.of C _) * exp (-(↑(Real.pi * φ) * I))).im
    rw [hbZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * F.φ i) * I + -(↑(Real.pi * φ) * I) =
        ↑(Real.pi * (F.φ i - φ)) * I from by push_cast; ring]
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hb)
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [hgt i hi, Real.pi_pos])
        (by nlinarith [hlt i hi, Real.pi_pos]))
  have hw_zero : ∀ i : Fin F.n, IsZero (F.toPostnikovTower.factor i) →
      w i = 0 := by
    intro i hi
    change σ.Z (K₀.of C _) * _ = 0
    rw [K₀.of_isZero C hi, map_zero, zero_mul]
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) := by
    by_contra hall; push_neg at hall
    have : (m : ℂ) = 0 := by
      rw [hsum, Finset.sum_eq_zero (fun i _ ↦ hw_zero i (hall i))]
    exact absurd (Complex.ofReal_eq_zero.mp this) (ne_of_gt hm)
  have him_ge : ∀ i : Fin F.n, 0 ≤ (w i).im := by
    intro i
    by_cases hi : IsZero (F.toPostnikovTower.factor i)
    · simp [hw_zero i hi]
    · exact le_of_lt (hw_pos i hi)
  have him_pos : 0 < ∑ i : Fin F.n, (w i).im := by
    calc (0 : ℝ) = ∑ i : Fin F.n, (0 : ℝ) := Finset.sum_const_zero.symm
      _ < ∑ i : Fin F.n, (w i).im :=
          Finset.sum_lt_sum (fun i _ ↦ him_ge i)
            ⟨i₀, Finset.mem_univ _, hw_pos i₀ hi₀⟩
  have him_eq : (∑ i : Fin F.n, w i).im = ∑ i : Fin F.n, (w i).im := by
    have := map_sum Complex.imAddGroupHom w Finset.univ
    simp only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] at this
    exact this
  have him_zero : (∑ i : Fin F.n, w i).im = 0 := by
    rw [← hsum]; exact Complex.ofReal_im m
  linarith

/-- **Lemma 6.4 for P-semistable objects**. If `σ` and `τ` have the same central charge,
`d(P, Q) < 1`, `E` is nonzero and `τ`-semistable of phase `φ`, and `E` is also
`σ`-semistable of some phase `c`, then `c = φ` and `E` is `σ`-semistable of phase `φ`.

This handles the case of Lemma 6.4 where `E` has a trivial `σ`-HN filtration (single
factor), combining the metric phase bound with `phase_eq_of_same_Z`. -/
theorem StabilityCondition.P_of_Q_of_P_semistable (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal 1)
    {E : C} {φ c : ℝ} (hE : ¬IsZero E)
    (hτ : (τ.slicing.P φ) E)
    (hσ : (σ.slicing.P c) E) : (σ.slicing.P φ) E := by
  have hbds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hτ hd
  have ⟨hpP, hpM⟩ := σ.slicing.phiPlus_eq_phiMinus_of_semistable C hσ hE
  rw [hpP] at hbds
  have habs : |c - φ| < 2 := by
    rw [abs_lt]; constructor <;> linarith [hbds.1.1, hbds.1.2]
  have := σ.phase_eq_of_same_Z C τ hZ hσ hτ hE habs
  rwa [this] at hσ

/-- **Phase straddling for Lemma 6.4** (intrinsic). If `σ.Z = τ.Z`, `d(P, Q) < 1`,
`E` is nonzero and `τ`-semistable of phase `φ`, then the intrinsic `σ`-phases satisfy
`phiMinus_σ(E) ≤ φ ≤ phiPlus_σ(E)`.

Combined with `phiPlus_σ(E), phiMinus_σ(E) ∈ (φ-1, φ+1)` from
`intervalProp_of_semistable_slicingDist`, this pins `φ` between the extreme `σ`-phases.
The proof applies `False_of_all_HN_phases_below` / `False_of_all_HN_phases_above` to
the canonical HN filtration from `exists_both_nonzero`. -/
theorem StabilityCondition.phiMinus_le_le_phiPlus (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal 1)
    {E : C} {φ : ℝ} (hE : ¬IsZero E)
    (hτ : (τ.slicing.P φ) E) :
    σ.slicing.phiMinus C E hE ≤ φ ∧ φ ≤ σ.slicing.phiPlus C E hE := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  have hpP := σ.slicing.phiPlus_eq C E hE F hn hfirst
  have hpM := σ.slicing.phiMinus_eq C E hE F hn hlast
  have hbds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hτ hd
  -- Extract bounds on F's extreme phases from hbds + the phiPlus/phiMinus equations
  have hP_lt : F.φ ⟨0, hn⟩ < φ + 1 := by linarith [(Set.mem_Ioo.mp hbds.1).2]
  have hM_gt : φ - 1 < F.φ ⟨F.n - 1, by omega⟩ := by linarith [(Set.mem_Ioo.mp hbds.2).1]
  -- All phases of F lie in [F.φ(n-1), F.φ(0)] by antitonicity
  have hFle : ∀ i : Fin F.n, F.φ ⟨F.n - 1, by omega⟩ ≤ F.φ i :=
    fun i ↦ F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
  have hFge : ∀ i : Fin F.n, F.φ i ≤ F.φ ⟨0, hn⟩ :=
    fun i ↦ F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
  constructor
  · -- phiMinus ≤ φ: if not, all phases > φ, contradicting False_of_all_HN_phases_above
    rw [hpM]
    by_contra h; push_neg at h
    exact σ.False_of_all_HN_phases_above C τ hZ hE hτ F
      (fun i _ ↦ lt_of_lt_of_le h (hFle i))
      (fun i _ ↦ lt_of_le_of_lt (hFge i) hP_lt)
  · -- φ ≤ phiPlus: if not, all phases < φ, contradicting False_of_all_HN_phases_below
    rw [hpP]
    by_contra h; push_neg at h
    exact σ.False_of_all_HN_phases_below C τ hZ hE hτ F
      (fun i _ ↦ lt_of_le_of_lt (hFge i) h)
      (fun i _ ↦ lt_of_lt_of_le hM_gt (hFle i))

/-- **Cross-slicing imaginary part contradiction**. If `σ.Z = τ.Z`, `X` is nonzero,
all `σ`-HN phases of `X` are in `(φ, φ + 1)`, and all `τ`-HN phases are in `(φ - 1, φ]`,
then `False`.

The proof decomposes `Z(X)` via both `σ`- and `τ`-HN filtrations. From the `σ`-decomposition,
`Im(Z(X)/exp(iπφ)) > 0`. From the `τ`-decomposition, `Im(Z(X)/exp(iπφ)) ≤ 0`. -/
theorem StabilityCondition.False_of_gt_and_le_phases (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z) {X : C} {φ : ℝ} (hX : ¬IsZero X)
    (Fσ : HNFiltration C σ.slicing.P X)
    (hσgt : ∀ i : Fin Fσ.n, φ < Fσ.φ i)
    (hσlt : ∀ i : Fin Fσ.n, Fσ.φ i < φ + 1)
    (Fτ : HNFiltration C τ.slicing.P X)
    (hτle : ∀ i : Fin Fτ.n, Fτ.φ i ≤ φ)
    (hτgt : ∀ i : Fin Fτ.n, φ - 1 < Fτ.φ i) : False := by
  -- σ-decomposition: Im(Z(X)/exp(iπφ)) > 0
  have hK₀σ : σ.Z (K₀.of C X) =
      ∑ i : Fin Fσ.n, σ.Z (K₀.of C (Fσ.toPostnikovTower.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum, map_sum]
  set wσ : Fin Fσ.n → ℂ := fun i ↦
    σ.Z (K₀.of C (Fσ.toPostnikovTower.factor i)) * exp (-(↑(Real.pi * φ) * I))
  have hσ_pos : ∀ i : Fin Fσ.n, ¬IsZero (Fσ.toPostnikovTower.factor i) →
      0 < (wσ i).im := by
    intro i hi
    obtain ⟨b, hb, hbZ⟩ := σ.compat (Fσ.φ i) _ (Fσ.semistable i) hi
    change 0 < (σ.Z (K₀.of C _) * exp (-(↑(Real.pi * φ) * I))).im
    rw [hbZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * Fσ.φ i) * I + -(↑(Real.pi * φ) * I) =
        ↑(Real.pi * (Fσ.φ i - φ)) * I from by push_cast; ring]
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hb)
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [hσgt i, Real.pi_pos])
        (by nlinarith [hσlt i, Real.pi_pos]))
  have hσ_zero : ∀ i : Fin Fσ.n, IsZero (Fσ.toPostnikovTower.factor i) →
      wσ i = 0 := by
    intro i hi; change σ.Z (K₀.of C _) * _ = 0
    rw [K₀.of_isZero C hi, map_zero, zero_mul]
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin Fσ.n, ¬IsZero (Fσ.toPostnikovTower.factor i) := by
    by_contra hall; push_neg at hall
    -- All factors are zero → each chain object is zero by induction → E is zero
    apply hX
    have hbase : IsZero (Fσ.toPostnikovTower.chain.left) :=
      Fσ.toPostnikovTower.base_isZero
    have hall_chain : ∀ (k : ℕ) (hk : k ≤ Fσ.n),
        IsZero (Fσ.toPostnikovTower.chain.obj' k (by omega)) := by
      intro k hk
      induction k with
      | zero =>
        change IsZero (Fσ.toPostnikovTower.chain.left)
        exact hbase
      | succ k ih =>
        have hklt : k < Fσ.n := by omega
        have ih' := ih (by omega)
        have h₁ := Fσ.toPostnikovTower.triangle_obj₁ ⟨k, hklt⟩
        have h₂ := Fσ.toPostnikovTower.triangle_obj₂ ⟨k, hklt⟩
        have hdist := Fσ.toPostnikovTower.triangle_dist ⟨k, hklt⟩
        exact (Classical.choice h₂).symm.isZero_iff.mpr
          (Triangle.isZero₂_of_isZero₁₃ _ hdist
            ((Classical.choice h₁).isZero_iff.mpr ih')
            (hall ⟨k, hklt⟩))
    have htop := hall_chain Fσ.n le_rfl
    exact (Classical.choice Fσ.toPostnikovTower.top_iso).symm.isZero_iff.mpr htop
  have him_σ_pos : 0 < (∑ i : Fin Fσ.n, wσ i).im := by
    have him_eq : (∑ i : Fin Fσ.n, wσ i).im = ∑ i : Fin Fσ.n, (wσ i).im := by
      have := map_sum Complex.imAddGroupHom wσ Finset.univ
      simp only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] at this
      exact this
    rw [him_eq]
    have hge : ∀ i : Fin Fσ.n, 0 ≤ (wσ i).im := by
      intro i; by_cases hi : IsZero (Fσ.toPostnikovTower.factor i)
      · simp [hσ_zero i hi]
      · exact le_of_lt (hσ_pos i hi)
    calc (0 : ℝ) = ∑ i : Fin Fσ.n, (0 : ℝ) := Finset.sum_const_zero.symm
      _ < ∑ i : Fin Fσ.n, (wσ i).im :=
          Finset.sum_lt_sum (fun i _ ↦ hge i)
            ⟨i₀, Finset.mem_univ _, hσ_pos i₀ hi₀⟩
  -- τ-decomposition: Im(Z(X)/exp(iπφ)) ≤ 0
  have hK₀τ : τ.Z (K₀.of C X) =
      ∑ i : Fin Fτ.n, τ.Z (K₀.of C (Fτ.toPostnikovTower.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum, map_sum]
  set wτ : Fin Fτ.n → ℂ := fun i ↦
    τ.Z (K₀.of C (Fτ.toPostnikovTower.factor i)) * exp (-(↑(Real.pi * φ) * I))
  have hτ_le : ∀ i : Fin Fτ.n, (wτ i).im ≤ 0 := by
    intro i
    by_cases hi : IsZero (Fτ.toPostnikovTower.factor i)
    · change (τ.Z (K₀.of C _) * _).im ≤ 0
      rw [K₀.of_isZero C hi, map_zero, zero_mul]; exact le_rfl
    · obtain ⟨b, hb, hbZ⟩ := τ.compat (Fτ.φ i) _ (Fτ.semistable i) hi
      change (τ.Z (K₀.of C _) * exp (-(↑(Real.pi * φ) * I))).im ≤ 0
      rw [hbZ, mul_assoc, ← exp_add,
        show ↑(Real.pi * Fτ.φ i) * I + -(↑(Real.pi * φ) * I) =
          ↑(Real.pi * (Fτ.φ i - φ)) * I from by push_cast; ring]
      rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast le_of_lt hb)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (by nlinarith [hτle i, Real.pi_pos])
          (by nlinarith [hτgt i, Real.pi_pos]))
  have him_τ_le : (∑ i : Fin Fτ.n, wτ i).im ≤ 0 := by
    have him_eq : (∑ i : Fin Fτ.n, wτ i).im = ∑ i : Fin Fτ.n, (wτ i).im := by
      have := map_sum Complex.imAddGroupHom wτ Finset.univ
      simp only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] at this
      exact this
    rw [him_eq]
    exact Finset.sum_nonpos (fun i _ ↦ hτ_le i)
  -- Both sums equal Z(X) * exp(-iπφ), so their imaginary parts are equal
  have hσ_sum : σ.Z (K₀.of C X) * exp (-(↑(Real.pi * φ) * I)) =
      ∑ i : Fin Fσ.n, wσ i := by rw [hK₀σ, Finset.sum_mul]
  have hτ_sum : τ.Z (K₀.of C X) * exp (-(↑(Real.pi * φ) * I)) =
      ∑ i : Fin Fτ.n, wτ i := by rw [hK₀τ, Finset.sum_mul]
  have : (∑ i : Fin Fσ.n, wσ i).im = (∑ i : Fin Fτ.n, wτ i).im := by
    rw [← hσ_sum, ← hτ_sum, hZ]
  linarith

/-- **One-sided phase impossibility** (below with equality). If `σ` and `τ` have the same
central charge, `E` is `τ`-semistable at `φ`, and all `σ`-HN phases are `≤ φ` with at
least one strictly below, then `False`. This extends `False_of_all_HN_phases_below`
to allow some phases equal to `φ`. -/
theorem StabilityCondition.False_of_HN_phases_le_with_lt (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z) {E : C} {φ : ℝ} (hE : ¬IsZero E)
    (hτ : (τ.slicing.P φ) E)
    (F : HNFiltration C σ.slicing.P E)
    (hle : ∀ i : Fin F.n, F.φ i ≤ φ)
    (hgt : ∀ i : Fin F.n, φ - 1 < F.φ i)
    (hstrict : ∃ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) ∧ F.φ i < φ) :
    False := by
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hτ hE
  rw [← hZ] at hmZ
  have hK₀ : σ.Z (K₀.of C E) =
      ∑ i : Fin F.n, σ.Z (K₀.of C (F.toPostnikovTower.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum, map_sum]
  set w : Fin F.n → ℂ := fun i ↦
    σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * exp (-(↑(Real.pi * φ) * I))
  have hsum : (m : ℂ) = ∑ i : Fin F.n, w i := by
    have h1 : σ.Z (K₀.of C E) * exp (-(↑(Real.pi * φ) * I)) =
        ∑ i : Fin F.n, w i := by rw [hK₀, Finset.sum_mul]
    rw [hmZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * φ) * I + -(↑(Real.pi * φ) * I) = 0 from by ring,
      exp_zero, mul_one] at h1
    exact h1
  -- Each term has Im ≤ 0
  have hw_le : ∀ i : Fin F.n, (w i).im ≤ 0 := by
    intro i
    by_cases hi : IsZero (F.toPostnikovTower.factor i)
    · change (σ.Z (K₀.of C _) * _).im ≤ 0
      rw [K₀.of_isZero C hi, map_zero, zero_mul]; exact le_rfl
    · obtain ⟨b, hb, hbZ⟩ := σ.compat (F.φ i) _ (F.semistable i) hi
      change (σ.Z (K₀.of C _) * exp (-(↑(Real.pi * φ) * I))).im ≤ 0
      rw [hbZ, mul_assoc, ← exp_add,
        show ↑(Real.pi * F.φ i) * I + -(↑(Real.pi * φ) * I) =
          ↑(Real.pi * (F.φ i - φ)) * I from by push_cast; ring]
      rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast le_of_lt hb)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (by nlinarith [hle i, Real.pi_pos])
          (by nlinarith [hgt i, Real.pi_pos]))
  -- At least one term has Im < 0
  obtain ⟨j₀, hj₀ne, hj₀lt⟩ := hstrict
  have hw_neg : (w j₀).im < 0 := by
    obtain ⟨b, hb, hbZ⟩ := σ.compat (F.φ j₀) _ (F.semistable j₀) hj₀ne
    change (σ.Z (K₀.of C _) * exp (-(↑(Real.pi * φ) * I))).im < 0
    rw [hbZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * F.φ j₀) * I + -(↑(Real.pi * φ) * I) =
        ↑(Real.pi * (F.φ j₀ - φ)) * I from by push_cast; ring]
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hb)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [hj₀lt, Real.pi_pos])
        (by nlinarith [hgt j₀, Real.pi_pos]))
  have him_neg : (∑ i : Fin F.n, w i).im < 0 := by
    have him_eq : (∑ i : Fin F.n, w i).im = ∑ i : Fin F.n, (w i).im := by
      have := map_sum Complex.imAddGroupHom w Finset.univ
      simp only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] at this
      exact this
    rw [him_eq]
    calc ∑ i : Fin F.n, (w i).im
        < ∑ i : Fin F.n, (0 : ℝ) :=
          Finset.sum_lt_sum (fun i _ ↦ hw_le i)
            ⟨j₀, Finset.mem_univ _, hw_neg⟩
      _ = 0 := Finset.sum_const_zero
  have him_zero : (∑ i : Fin F.n, w i).im = 0 := by
    rw [← hsum]; exact Complex.ofReal_im m
  linarith

/-- **Auxiliary**: for a nonzero object with `s.gtProp φ`, the intrinsic minimum phase
is `> φ`. -/
lemma gt_phases_of_gtProp (s : Slicing C) {X : C} {φ : ℝ}
    (hXne : ¬IsZero X) (hXgt : s.gtProp C φ X) :
    φ < s.phiMinus C X hXne := by
  rcases hXgt with hXZ | ⟨GX, hnX, hphiM⟩
  · exact absurd hXZ hXne
  · obtain ⟨FX, hnFX, _, hlast⟩ := HNFiltration.exists_both_nonzero C s hXne
    have h1 : GX.phiMinus C hnX ≤ FX.phiMinus C hnFX :=
      GX.phiMinus_ge_of_nonzero_last_factor C s FX hnX hnFX hlast
    have h2 : FX.phiMinus C hnFX = s.phiMinus C X hXne := by
      rw [HNFiltration.phiMinus, s.phiMinus_eq C X hXne FX hnFX hlast]
    linarith

/-- **Auxiliary**: for a nonzero object with `s.leProp φ`, the intrinsic maximum phase
is `≤ φ`. -/
lemma phiPlus_le_of_leProp (s : Slicing C) {Y : C} {φ : ℝ}
    (hYne : ¬IsZero Y) (hYle : s.leProp C φ Y) :
    s.phiPlus C Y hYne ≤ φ := by
  rcases hYle with hYZ | ⟨GY, hnY, hphiP⟩
  · exact absurd hYZ hYne
  · obtain ⟨FY, hnFY, hfirst, _⟩ := HNFiltration.exists_both_nonzero C s hYne
    have h1 : FY.phiPlus C hnFY ≤ GY.phiPlus C hnY :=
      FY.phiPlus_le_of_nonzero_factor C s GY hnFY hnY hfirst
    have h2 : s.phiPlus C Y hYne = FY.phiPlus C hnFY := by
      rw [HNFiltration.phiPlus, s.phiPlus_eq C Y hYne FY hnFY hfirst]
    linarith

/-- **Auxiliary for Lemma 6.4**: one direction of the biconditional. If `E ∈ Q(φ)` then
`E ∈ P(φ)`, using the cross-slicing imaginary part argument and hom-vanishing. -/
private theorem bridgeland_6_4_one_dir [IsTriangulated C]
    (σ τ : StabilityCondition C) (hZ : σ.Z = τ.Z)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal 1)
    (φ : ℝ) (E : C) (hτ : (τ.slicing.P φ) E) : (σ.slicing.P φ) E := by
  by_cases hE : IsZero E
  · exact σ.slicing.zero_mem' C φ E hE
  -- Step 1: Get σ-HN of E with phases in (φ-1, φ+1)
  have hbds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hτ hd
  obtain ⟨F, hn, hF0, hFn⟩ := σ.slicing.exists_HN_intrinsic_width C hE
  have hPlt : F.φ ⟨0, hn⟩ < φ + 1 := by linarith [(Set.mem_Ioo.mp hbds.1).2]
  have hMgt : φ - 1 < F.φ ⟨F.n - 1, by omega⟩ := by linarith [(Set.mem_Ioo.mp hbds.2).1]
  have hF_interval : ∀ i : Fin F.n, φ - 1 < F.φ i ∧ F.φ i < φ + 1 := by
    intro i; exact ⟨by calc φ - 1 < F.φ ⟨F.n - 1, by omega⟩ := hMgt
      _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ < φ + 1 := hPlt⟩
  -- If all phases = φ, done
  by_cases hall_eq : ∀ i : Fin F.n, F.φ i = φ
  · exact σ.slicing.semistable_of_HN_all_eq C F hall_eq
  push_neg at hall_eq
  -- Step 2: Split E at cutoff φ using tStructureAux on the phase-shifted slicing
  let Fs := F.phaseShift (C := C) φ
  obtain ⟨X, Y, hXgt0, hYle0, f, g, h, hT, hXdata⟩ :=
    Slicing.tStructureAux C (σ.slicing.phaseShift C φ) E Fs
  have hXgt : σ.slicing.gtProp C φ X :=
    (σ.slicing.phaseShift_gtProp_zero C φ X).mp hXgt0
  have hYle : σ.slicing.leProp C φ Y :=
    (σ.slicing.phaseShift_leProp_zero C φ Y).mp hYle0
  have hXub : ∀ (hXne : ¬IsZero X), σ.slicing.phiPlus C X hXne < φ + 1 := by
    intro hXne
    rcases hXdata with hXZ | ⟨GX', hGX', _, hbd, _⟩
    · exact absurd hXZ hXne
    · -- GX' is wrt shifted slicing, phiPlus ≤ Fs.φ(0) = F.φ(0) - φ
      -- Build original-coords HN filtration of X
      let GXorig : HNFiltration C σ.slicing.P X :=
        { n := GX'.n, chain := GX'.chain, triangle := GX'.triangle
          triangle_dist := GX'.triangle_dist, triangle_obj₁ := GX'.triangle_obj₁
          triangle_obj₂ := GX'.triangle_obj₂, base_isZero := GX'.base_isZero
          top_iso := GX'.top_iso, zero_isZero := GX'.zero_isZero
          φ := fun i ↦ GX'.φ i + φ
          hφ := by intro i j hij; linarith [GX'.hφ hij]
          semistable := by intro i; exact GX'.semistable i }
      calc σ.slicing.phiPlus C X hXne
          ≤ GXorig.φ ⟨0, hGX'⟩ :=
            σ.slicing.phiPlus_le_phiPlus_of_hn C hXne GXorig hGX'
        _ = GX'.φ ⟨0, hGX'⟩ + φ := rfl
        _ ≤ Fs.φ ⟨0, hn⟩ + φ := by
          have : GX'.φ ⟨0, hGX'⟩ ≤ Fs.φ ⟨0, hn⟩ := by
            change GX'.phiPlus C hGX' ≤ Fs.φ ⟨0, hn⟩; exact hbd hn
          linarith
        _ = F.φ ⟨0, hn⟩ := by change F.φ ⟨0, hn⟩ - φ + φ = F.φ ⟨0, hn⟩; ring
        _ < φ + 1 := hPlt
  -- Step 3: Show X = 0 via cross-slicing argument
  suffices hXZ : IsZero X by
    -- Step 4: X = 0 ⟹ E ≅ Y
    haveI hiso : IsIso g :=
      ((Triangle.mk f g h).isZero₁_iff_isIso₂ hT).mp hXZ
    -- Transfer: P(φ) Y → P(φ) E
    suffices hY : (σ.slicing.P φ) Y from
      ObjectProperty.prop_of_iso _ (asIso g).symm hY
    -- Y has σ-phases ≤ φ (from leProp)
    by_cases hYZ : IsZero Y
    · exact σ.slicing.zero_mem' C φ Y hYZ
    -- Y ≅ E (since X = 0), so Y is nonzero, τ-semistable at φ
    -- Since IsIso g, E ∈ τ.P(φ) implies Y ∈ τ.P(φ)
    have hτY : (τ.slicing.P φ) Y := ObjectProperty.prop_of_iso _ (asIso g) hτ
    -- Apply the imaginary part argument: σ-phases of Y ≤ φ and some < φ → contradiction
    -- First get σ-HN of Y with all phases ≤ φ and > φ-1
    obtain ⟨FY, hnY, hFY0, hFYn⟩ := σ.slicing.exists_HN_intrinsic_width C hYZ
    have hFY_le : ∀ i : Fin FY.n, FY.φ i ≤ φ := by
      intro i; calc FY.φ i ≤ FY.φ ⟨0, hnY⟩ :=
            FY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C Y hYZ := hFY0
        _ ≤ φ := phiPlus_le_of_leProp C σ.slicing hYZ hYle
    -- Lower bound: Y ≅ E has σ-phiMinus > φ - 1
    have hYσM : φ - 1 < σ.slicing.phiMinus C Y hYZ := by
      -- E ≅ Y via asIso g, so phiMinus transfers
      have hbdsY := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hYZ hτY hd
      exact (Set.mem_Ioo.mp hbdsY.2).1
    have hFY_gt : ∀ i : Fin FY.n, φ - 1 < FY.φ i := by
      intro i; calc φ - 1 < σ.slicing.phiMinus C Y hYZ := hYσM
        _ = FY.φ ⟨FY.n - 1, by omega⟩ := hFYn.symm
        _ ≤ FY.φ i := FY.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
    -- If all phases = φ, done. If some < φ, contradiction
    by_cases hall_eq_Y : ∀ i : Fin FY.n, FY.φ i = φ
    · exact σ.slicing.semistable_of_HN_all_eq C FY hall_eq_Y
    push_neg at hall_eq_Y
    obtain ⟨j, hj_ne⟩ := hall_eq_Y
    have hj_lt : FY.φ j < φ := lt_of_le_of_ne (hFY_le j) hj_ne
    -- Factor j might be zero. Find a nonzero factor with phase < φ
    -- Since phiMinus ≤ φ (as all ≤ φ) and some phase < φ, phiMinus < φ
    -- The canonical filtration has nonzero last factor at phase = phiMinus < φ
    obtain ⟨FY', hnY', hfirst', hlast'⟩ := HNFiltration.exists_both_nonzero C σ.slicing hYZ
    have hm_eq := σ.slicing.phiMinus_eq C Y hYZ FY' hnY' hlast'
    -- FY' has the same phiMinus as FY
    have hFY'_last_lt : FY'.φ ⟨FY'.n - 1, by omega⟩ ≤ φ := by
      have : σ.slicing.phiMinus C Y hYZ ≤ φ := by
        rw [← hFYn]; exact hFY_le ⟨FY.n - 1, by omega⟩
      linarith [hm_eq]
    exfalso
    exact σ.False_of_HN_phases_le_with_lt C τ hZ hYZ hτY FY'
      (fun i ↦ by calc FY'.φ i ≤ FY'.φ ⟨0, hnY'⟩ :=
          FY'.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C Y hYZ :=
          (σ.slicing.phiPlus_eq C Y hYZ FY' hnY' hfirst').symm
        _ ≤ φ := phiPlus_le_of_leProp C σ.slicing hYZ hYle)
      (fun i ↦ by calc φ - 1 < σ.slicing.phiMinus C Y hYZ := hYσM
        _ = FY'.φ ⟨FY'.n - 1, by omega⟩ := hm_eq
        _ ≤ FY'.φ i := FY'.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
      ⟨⟨FY'.n - 1, by omega⟩, hlast', by
        calc FY'.φ ⟨FY'.n - 1, by omega⟩
            = σ.slicing.phiMinus C Y hYZ := hm_eq.symm
          _ = FY.φ ⟨FY.n - 1, by omega⟩ := hFYn.symm
          _ ≤ FY.φ j := FY.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
          _ < φ := hj_lt⟩
  -- Proof that X is zero: cross-slicing argument
  by_contra hXne
  have hXσM : φ < σ.slicing.phiMinus C X hXne := gt_phases_of_gtProp C σ.slicing hXne hXgt
  have hXσP : σ.slicing.phiPlus C X hXne < φ + 1 := hXub hXne
  -- Get canonical τ-HN of X
  obtain ⟨GX, hnGX, hGXfirst, hGXlast⟩ := HNFiltration.exists_both_nonzero C τ.slicing hXne
  -- Show τ.phiPlus(X) ≤ φ
  have hτP_le : τ.slicing.phiPlus C X hXne ≤ φ := by
    by_contra hτP_gt; push_neg at hτP_gt
    set ψ := GX.φ ⟨0, hnGX⟩
    have hψ_gt : φ < ψ := by
      calc φ < τ.slicing.phiPlus C X hXne := hτP_gt
        _ = ψ := τ.slicing.phiPlus_eq C X hXne GX hnGX hGXfirst
    set U := (GX.triangle ⟨0, hnGX⟩).obj₃
    -- Show all maps U → X are zero
    have hU_maps_zero : ∀ α : U ⟶ X, α = 0 := by
      intro α
      have hUE : α ≫ f = 0 :=
        τ.slicing.hom_vanishing ψ φ U E hψ_gt (GX.semistable ⟨0, hnGX⟩) hτ _
      obtain ⟨β, hβ⟩ := Triangle.coyoneda_exact₂ (Triangle.mk f g h).invRotate
        (inv_rot_of_distTriang _ hT) α hUE
      suffices hβ0 : β = 0 by rw [hβ, hβ0]; exact zero_comp
      -- β : U → Y⟦-1⟧. Show this is zero by σ-hom-vanishing
      by_cases hYsZ : IsZero (Y⟦(-1 : ℤ)⟧)
      · exact hYsZ.eq_of_tgt β 0
      · -- Use canonical σ-HN filtrations for both U and Y⟦-1⟧
        obtain ⟨FU, hnFU, hFUfirst, hFUlast⟩ :=
          HNFiltration.exists_both_nonzero C σ.slicing hGXfirst
        obtain ⟨FYs, hnFYs, hFYsfirst, hFYslast⟩ :=
          HNFiltration.exists_both_nonzero C σ.slicing hYsZ
        -- σ-phases of U: min > ψ - 1
        have hU_σ_bds :=
          intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing
            hGXfirst (GX.semistable ⟨0, hnGX⟩) hd
        have hU_σ_M : ψ - 1 < FU.φ ⟨FU.n - 1, by omega⟩ := by
          rw [← σ.slicing.phiMinus_eq C U hGXfirst FU hnFU hFUlast]
          exact (Set.mem_Ioo.mp hU_σ_bds.2).1
        -- σ-phases of Y⟦-1⟧: max ≤ φ - 1
        have hYs_le : σ.slicing.leProp C (φ - 1) (Y⟦(-1 : ℤ)⟧) := by
          have := σ.slicing.leProp_shift C φ Y (-1) hYle
          simp only [Int.cast_neg, Int.cast_one] at this; exact this
        have hYs_P : FYs.φ ⟨0, hnFYs⟩ ≤ φ - 1 := by
          rw [← σ.slicing.phiPlus_eq C _ hYsZ FYs hnFYs hFYsfirst]
          exact phiPlus_le_of_leProp C σ.slicing hYsZ hYs_le
        -- Phase gap: canonical phases of U all > canonical phases of Y⟦-1⟧
        have hgap : ∀ (i : Fin FU.n) (j : Fin FYs.n), FYs.φ j < FU.φ i := by
          intro i j
          calc FYs.φ j ≤ FYs.φ ⟨0, hnFYs⟩ :=
                FYs.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ ≤ φ - 1 := hYs_P
            _ < ψ - 1 := by linarith
            _ < FU.φ ⟨FU.n - 1, by omega⟩ := hU_σ_M
            _ ≤ FU.φ i := FU.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
        exact σ.slicing.hom_eq_zero_of_phase_gap C FU FYs hgap β
    exact hGXfirst (GX.isZero_factor_zero_of_hom_eq_zero C τ.slicing hnGX hU_maps_zero)
  -- τ.phiMinus(X) > φ - 1 by metric bound
  have hτM_gt : φ - 1 < τ.slicing.phiMinus C X hXne := by
    have hM_bd := phiMinus_sub_lt_of_slicingDist C σ.slicing τ.slicing hXne hd
    rw [abs_lt] at hM_bd; linarith
  -- Get canonical σ-HN and τ-HN of X with all phase bounds
  obtain ⟨FX, hnFX, hFXfirst, hFXlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hXne
  exact σ.False_of_gt_and_le_phases C τ hZ hXne FX
    (fun i ↦ by calc φ < σ.slicing.phiMinus C X hXne := hXσM
      _ = FX.φ ⟨FX.n - 1, by omega⟩ :=
          σ.slicing.phiMinus_eq C X hXne FX hnFX hFXlast
      _ ≤ FX.φ i := FX.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
    (fun i ↦ by calc FX.φ i ≤ FX.φ ⟨0, hnFX⟩ :=
          FX.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
      _ = σ.slicing.phiPlus C X hXne :=
          (σ.slicing.phiPlus_eq C X hXne FX hnFX hFXfirst).symm
      _ < φ + 1 := hXσP)
    GX
    (fun i ↦ by calc GX.φ i ≤ GX.φ ⟨0, hnGX⟩ :=
          GX.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
      _ = τ.slicing.phiPlus C X hXne :=
          (τ.slicing.phiPlus_eq C X hXne GX hnGX hGXfirst).symm
      _ ≤ φ := hτP_le)
    (fun i ↦ by calc φ - 1 < τ.slicing.phiMinus C X hXne := hτM_gt
      _ = GX.φ ⟨GX.n - 1, by omega⟩ :=
          τ.slicing.phiMinus_eq C X hXne GX hnGX hGXlast
      _ ≤ GX.φ i := GX.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))

/-- **Bridgeland's Lemma 6.4** (statement and proof). If two stability conditions have the
same central charge and `d(P, Q) < 1`, then their slicings agree on all phases.

The proof proceeds as follows. Given `E ∈ Q(φ)`, we show `E ∈ P(φ)`:
1. Split `E` via `σ`'s t-structure at `φ`: `X → E → Y → X⟦1⟧` with
   `X ∈ P(>φ)` and `Y ∈ P(≤φ)`, all σ-phases in `(φ-1, φ+1)`.
2. Show `τ.phiPlus(X) ≤ φ` by contradiction: if `τ`'s top factor `U` of `X` had
   phase `> φ`, then `Hom(U, E) = 0` (τ-hom-vanishing) forces `U → X` to factor
   through `Y⟦-1⟧`, but `Hom(U, Y⟦-1⟧) = 0` too, giving `U → X = 0`,
   contradicting `U ≠ 0`.
3. Now `X` has σ-phases `> φ` and τ-phases `≤ φ`: the cross-slicing imaginary
   part argument (`False_of_gt_and_le_phases`) gives `X = 0`.
4. So `E ≅ Y` has all σ-phases `≤ φ`. The imaginary part argument then forces
   all phases `= φ`, making `E` σ-semistable at `φ`. -/
theorem bridgeland_lemma_6_4 [IsTriangulated C] (σ τ : StabilityCondition C) (hZ : σ.Z = τ.Z)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal 1)
    (φ : ℝ) (E : C) : (σ.slicing.P φ) E ↔ (τ.slicing.P φ) E := by
  constructor
  · intro hσ
    exact bridgeland_6_4_one_dir C τ σ hZ.symm
      (by rwa [slicingDist_symm]) φ E hσ
  · exact bridgeland_6_4_one_dir C σ τ hZ hd φ E

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
