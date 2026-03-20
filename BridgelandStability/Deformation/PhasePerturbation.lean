/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.WPhase

/-!
# Phase Perturbation Estimates

Pure complex-analytic estimates for phase perturbation and arg convexity.
These are the foundational inequalities underpinning the deformation theorem's
phase arithmetic (Bridgeland §7.3).

## Main results

* `im_sq_le_norm_sq_mul`: geometric inequality `z.im² ≤ ‖z‖² · ‖z - 1‖²`
* `abs_sin_arg_le_norm_sub_one`: law-of-sines bound `|sin(arg z)| ≤ ‖z - 1‖`
* `abs_arg_one_add_lt`: near-identity perturbation bound `|arg(1+u)| < πε`
* `wPhaseOf_perturbation_generic`: generic phase perturbation for `m·exp(iπφ)·(1+u)`
* `arg_sum_le_sup'_of_upperHalfPlane`: arg convexity upper bound for finite sums
* `inf'_le_arg_sum_of_upperHalfPlane`: arg convexity lower bound for finite sums
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

/-! ### Phase perturbation estimates -/

section PhasePerturbation

/-- **Core geometric inequality**. For any complex number `z`, `z.im² ≤ ‖z‖² · ‖z - 1‖²`.
Equivalently, the perpendicular distance from `1` to the line through `0` and `z` is at most
`‖z - 1‖`. The proof uses the algebraic identity
`‖z‖² · ‖z - 1‖² - z.im² = (‖z‖² - z.re)² ≥ 0`. -/
theorem im_sq_le_norm_sq_mul (z : ℂ) :
    z.im ^ 2 ≤ ‖z - 1‖ ^ 2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm (z - 1), Complex.sq_norm z]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith [sq_nonneg (z.re * z.re + z.im * z.im - z.re)]

/-- For any nonzero `z : ℂ`, `|sin(arg z)| ≤ ‖z - 1‖`. This is the law-of-sines bound: the
side `|z - 1|` opposite the angle `arg z` at `0` in the triangle `0-1-z` satisfies
`|z - 1| ≥ sin(arg z)` since the circumradius is at least `1/2`. -/
theorem abs_sin_arg_le_norm_sub_one {z : ℂ} (hz : z ≠ 0) :
    |Real.sin (Complex.arg z)| ≤ ‖z - 1‖ := by
  rw [Complex.sin_arg, abs_div, abs_of_pos (norm_pos_iff.mpr hz),
    div_le_iff₀ (norm_pos_iff.mpr hz)]
  exact le_of_sq_le_sq (by rw [sq_abs, mul_pow]; exact im_sq_le_norm_sq_mul z) (by positivity)

/-- `sin(|x|) = |sin(x)|` for `|x| < π/2`. -/
theorem sin_abs_eq_abs_sin {x : ℝ} (hx : |x| < Real.pi / 2) :
    Real.sin |x| = |Real.sin x| := by
  rcases le_or_gt 0 x with h | h
  · have hx' : x < Real.pi / 2 := by rwa [abs_of_nonneg h] at hx
    rw [abs_of_nonneg h, abs_of_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_pos]))]
  · have hx' : -x < Real.pi / 2 := by rwa [abs_of_neg h] at hx
    have hsin : Real.sin x < 0 := by
      have : 0 < Real.sin (-x) :=
        Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr h) (by linarith [Real.pi_pos])
      linarith [Real.sin_neg x]
    rw [abs_of_neg h, Real.sin_neg, abs_of_neg hsin]

/-- **Phase bound for near-identity perturbation**. If `‖u‖ < sin(πε)` with `0 < ε ≤ 1/2`,
then `|arg(1 + u)| < πε`. The proof combines `abs_sin_arg_le_norm_sub_one` (the law-of-sines
bound) with strict monotonicity of sine on `[0, π/2]`. -/
theorem abs_arg_one_add_lt {u : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hu : ‖u‖ < Real.sin (Real.pi * ε)) :
    |Complex.arg (1 + u)| < Real.pi * ε := by
  have hπ := Real.pi_pos
  have hπε2 : Real.pi * ε ≤ Real.pi / 2 := by nlinarith
  have hu1 : ‖u‖ < 1 := lt_of_lt_of_le hu (Real.sin_le_one _)
  -- 1 + u ≠ 0
  have hz : (1 : ℂ) + u ≠ 0 := by
    intro h
    have h1 : (1 : ℂ) = -u := eq_neg_of_add_eq_zero_left h
    have h2 : ‖(1 : ℂ)‖ = ‖u‖ := by rw [h1, norm_neg]
    rw [norm_one] at h2; linarith
  -- Re(1+u) > 0 ⟹ |arg(1+u)| < π/2
  have hre : 0 < ((1 : ℂ) + u).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith [neg_le_of_abs_le (Complex.abs_re_le_norm u)]
  have harg_lt : |Complex.arg ((1 : ℂ) + u)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  -- sin(|arg(1+u)|) = |sin(arg(1+u))| ≤ ‖u‖ < sin(πε)
  have hsin_le : |Real.sin (Complex.arg ((1 : ℂ) + u))| ≤ ‖u‖ := by
    calc |Real.sin (Complex.arg ((1 : ℂ) + u))| ≤ ‖(1 : ℂ) + u - 1‖ :=
          abs_sin_arg_le_norm_sub_one hz
      _ = ‖u‖ := by congr 1; ring
  have hsin_abs := sin_abs_eq_abs_sin harg_lt
  -- By strict monotonicity of sin: |arg(1+u)| < πε
  by_contra h
  push_neg at h
  have hmono : Real.sin (Real.pi * ε) ≤ Real.sin (|Complex.arg ((1 : ℂ) + u)|) :=
    Real.monotoneOn_sin ⟨by nlinarith [mul_pos hπ hε], hπε2⟩
      ⟨by linarith [abs_nonneg (Complex.arg ((1 : ℂ) + u)), hπ], harg_lt.le⟩ h
  linarith [hsin_abs]

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
    rw [norm_one] at h2; linarith
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
  have hφα : |φ - α| < 1 / 2 := abs_lt.mpr ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have harg1 : Complex.arg z₁ = Real.pi * (φ - α) := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    exact ⟨by nlinarith [mul_pos hπ (show (0 : ℝ) < 1 + (φ - α) from by linarith [hφ.1])],
           by nlinarith [mul_pos hπ (show (0 : ℝ) < 1 - (φ - α) from by linarith [hφ.2])]⟩
  -- Step 4: arg(z₁) + arg(z₂) ∈ Ioc(-π, π), apply arg_mul
  set z₂ := (1 : ℂ) + u
  have hsum_mem : Complex.arg z₁ + Complex.arg z₂ ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [harg1]
    have h1 := (abs_lt.mp harg_u).1
    have h2 := (abs_lt.mp harg_u).2
    constructor
    · -- -π < π(φ-α) + arg(z₂)
      have : -(Real.pi / 2) < Real.pi * (φ - α) := by
        nlinarith [mul_pos hπ (show (0 : ℝ) < 1 / 2 + (φ - α) from by linarith [hφ.1])]
      linarith
    · -- π(φ-α) + arg(z₂) ≤ π
      have : Real.pi * (φ - α) < Real.pi / 2 := by
        nlinarith [mul_pos hπ (show (0 : ℝ) < 1 / 2 - (φ - α) from by linarith [hφ.2])]
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
  linarith [harg_u]

end PhasePerturbation

/-! ### Arg convexity for finite sums -/

section ArgConvexity

open Complex

/-- A Finset sum of upper half-plane vectors is in the upper half-plane union. -/
theorem sum_mem_upperHalfPlane {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℂ} (hf : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion) :
    ∑ i ∈ s, f i ∈ upperHalfPlaneUnion := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simpa using hf j (Finset.mem_singleton_self j)
  | cons j s hjs hs ih =>
    rw [Finset.sum_cons]
    exact mem_upperHalfPlaneUnion_of_add
      (hf j (Finset.mem_cons_self j s))
      (ih (fun i hi ↦ hf i (Finset.mem_cons.mpr (Or.inr hi))))

/-- **Arg upper bound for Finset sums**. If every `f i` is in the upper half-plane union,
then `arg(∑ i ∈ s, f i) ≤ s.sup' hs (arg ∘ f)`. This extends `arg_add_le_max` from two
summands to finitely many by induction. -/
theorem arg_sum_le_sup'_of_upperHalfPlane {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℂ} (hf : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion) :
    arg (∑ i ∈ s, f i) ≤ s.sup' hs (arg ∘ f) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp
  | cons j s hjs hs ih =>
    rw [Finset.sum_cons]
    have hfj : f j ∈ upperHalfPlaneUnion := hf j (Finset.mem_cons_self j s)
    have hfs : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion :=
      fun i hi ↦ hf i (Finset.mem_cons.mpr (Or.inr hi))
    calc arg (f j + ∑ i ∈ s, f i)
        ≤ max (arg (f j)) (arg (∑ i ∈ s, f i)) :=
          arg_add_le_max hfj (sum_mem_upperHalfPlane hs hfs)
      _ ≤ max (arg (f j)) (s.sup' hs (arg ∘ f)) :=
          max_le_max_left _ (ih hfs)
      _ = max ((arg ∘ f) j) (s.sup' hs (arg ∘ f)) := rfl
      _ ≤ (Finset.cons j s hjs).sup' ⟨j, Finset.mem_cons_self j s⟩ (arg ∘ f) := by
          rw [Finset.sup'_cons hs]

/-- **Arg lower bound for Finset sums**. If every `f i` is in the upper half-plane union,
then `s.inf' hs (arg ∘ f) ≤ arg(∑ i ∈ s, f i)`. Dual of `arg_sum_le_sup'_of_upperHalfPlane`. -/
theorem inf'_le_arg_sum_of_upperHalfPlane {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℂ} (hf : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion) :
    s.inf' hs (arg ∘ f) ≤ arg (∑ i ∈ s, f i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp
  | cons j s hjs hs ih =>
    rw [Finset.sum_cons]
    have hfj : f j ∈ upperHalfPlaneUnion := hf j (Finset.mem_cons_self j s)
    have hfs : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion :=
      fun i hi ↦ hf i (Finset.mem_cons.mpr (Or.inr hi))
    calc (Finset.cons j s hjs).inf' ⟨j, Finset.mem_cons_self j s⟩ (arg ∘ f)
        = min ((arg ∘ f) j) (s.inf' hs (arg ∘ f)) := by
          rw [Finset.inf'_cons hs]
      _ = min (arg (f j)) (s.inf' hs (arg ∘ f)) := rfl
      _ ≤ min (arg (f j)) (arg (∑ i ∈ s, f i)) :=
          min_le_min_left _ (ih hfs)
      _ ≤ arg (f j + ∑ i ∈ s, f i) :=
          min_arg_le_arg_add hfj (sum_mem_upperHalfPlane hs hfs)

end ArgConvexity

end CategoryTheory.Triangulated
