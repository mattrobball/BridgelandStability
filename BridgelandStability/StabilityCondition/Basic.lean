/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.GrothendieckGroup
public import BridgelandStability.IntervalCategory.FiniteLength
public import BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.SectorBound
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
* `CategoryTheory.Triangulated.StabilityCondition.centralCharge_isLocalHomeomorph_onConnectedComponents`:
  **Theorem 1.2** as a `Prop`, stated componentwise with a linear subspace `V(Σ)`

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ENNReal

universe v u

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
      congr 1; push_cast; ring_nf
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
  grind

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
      congr 1; push_cast; ring_nf
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
  grind


end CategoryTheory.Triangulated
