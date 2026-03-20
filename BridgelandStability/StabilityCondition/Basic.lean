/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.GrothendieckGroup
public import BridgelandStability.IntervalCategory.FiniteLength
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

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


end CategoryTheory.Triangulated
