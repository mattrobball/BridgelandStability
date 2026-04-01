/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.Defs

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

/-!
# Bridgeland Stability Conditions — Ext Theorems and Phase Rigidity

Extensionality theorems for stability conditions, phase rigidity (Lemma 6.4 sublemma),
and the exponential decomposition impossibility lemmas. The core structures, topology,
and seminorm are in `StabilityCondition.Defs`.

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ENNReal

universe v u u'

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}
variable {Λ : Type u'} [AddCommGroup Λ]

/-! ### Ext theorems -/

namespace PreStabilityCondition

omit [IsTriangulated C] in
@[ext] theorem WithClassMap.ext {v : K₀ C →+ Λ}
    {σ τ : WithClassMap C v}
    (hs : σ.slicing = τ.slicing) (hZ : σ.Z = τ.Z) : σ = τ := by
  rcases σ with ⟨sσ, Zσ, cσ⟩
  rcases τ with ⟨sτ, Zτ, cτ⟩
  simp at hs hZ
  cases hs
  cases hZ
  have hcompat : cσ = cτ := Subsingleton.elim _ _
  cases hcompat
  rfl

end PreStabilityCondition

namespace StabilityCondition

@[ext] theorem WithClassMap.ext {v : K₀ C →+ Λ}
    {σ τ : WithClassMap C v}
    (hs : σ.slicing = τ.slicing) (hZ : σ.Z = τ.Z) : σ = τ := by
  have hparent : σ.toWithClassMap = τ.toWithClassMap :=
    PreStabilityCondition.WithClassMap.ext (C := C) hs hZ
  rcases σ with ⟨σpre, hlfσ⟩
  rcases τ with ⟨τpre, hlfτ⟩
  cases hparent
  have hlf : hlfσ = hlfτ := Subsingleton.elim _ _
  cases hlf
  rfl

end StabilityCondition

omit [IsTriangulated C] in
/-- The ordinary compatibility statement for a prestability condition, with the
identity class map simplified away. -/
theorem preStabilityCondition_compat_apply (σ : PreStabilityCondition.WithClassMap C v)
    (φ : ℝ) (E : C) (hE : σ.slicing.P φ E) (hNZ : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      σ.Z (cl C v E) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) := by
  simpa using σ.compat φ E hE hNZ

/-! ### Phase rigidity for same central charge -/

/-- **Lemma 6.4 sublemma**. If two stability conditions `σ` and `τ` have the same central
charge `Z`, and a nonzero object `E` is `σ`-semistable of phase `φ` and `τ`-semistable
of phase `ψ` with `|φ - ψ| < 2`, then `φ = ψ`. -/
theorem StabilityCondition.WithClassMap.phase_eq_of_same_Z (σ τ : StabilityCondition.WithClassMap C v)
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
  linarith

end CategoryTheory.Triangulated
