/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.Deformation.WPhase

/-!
# Deformation of Stability Conditions — PhaseArithmetic

Phase perturbation, arg convexity, see-saw, Lemma 7.3(b)
-/

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

/-! ### Phase perturbation bound -/

/-- **Coarse phase perturbation bound**. If `E` is σ-semistable of phase `φ ∈ (α-1, α+1]`,
then `wPhaseOf(Z(E), α) = φ`. This is the inverse direction of `wPhaseOf_of_exp`. -/
theorem wPhaseOf_Z_eq (σ : StabilityCondition C) {E : C} {φ : ℝ}
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) {α : ℝ}
    (hφ : φ ∈ Set.Ioc (α - 1) (α + 1)) :
    wPhaseOf (σ.Z (K₀.of C E)) α = φ := by
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E hP hE
  rw [hmZ]; exact wPhaseOf_of_exp hm hφ

/-- **Phase perturbation for σ-semistable objects**. If `E` is σ-semistable of phase `φ`
with `φ ∈ (α - 1/2, α + 1/2)`, and `‖(W-Z)(E)‖ / ‖Z(E)‖ < sin(πε)` with `0 < ε ≤ 1/2`,
then `|wPhaseOf(W(E), α) - φ| < ε`. This is the key quantitative bound for the
deformation theorem. -/
theorem wPhaseOf_perturbation (σ : StabilityCondition C)
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {α ε : ℝ}
    (hφα : φ ∈ Set.Ioo (α - 1 / 2) (α + 1 / 2))
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hbd : ‖(W - σ.Z) (K₀.of C E)‖ <
      Real.sin (Real.pi * ε) * ‖σ.Z (K₀.of C E)‖) :
    |wPhaseOf (W (K₀.of C E)) α - φ| < ε := by
  -- Z(E) = m · exp(iπφ) with m > 0
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E hP hE
  -- Set u = (W-Z)(E) / Z(E)
  set δ := (W - σ.Z) (K₀.of C E)
  have hWZ : δ = W (K₀.of C E) - σ.Z (K₀.of C E) := AddMonoidHom.sub_apply W σ.Z _
  have hZ_norm : ‖σ.Z (K₀.of C E)‖ = m := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hm_pos : (0 : ℝ) < m := hm
  -- W(E) = Z(E) + δ = m · exp(iπφ) · (1 + δ/(m · exp(iπφ)))
  set u := δ / (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I))
  have hZ_ne : (↑m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hm.ne') (Complex.exp_ne_zero _)
  have hW_eq : W (K₀.of C E) =
      ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) * ((1 : ℂ) + u) := by
    rw [show u = δ / (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)) from rfl]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hZ_ne]
    rw [hWZ, ← hmZ]; ring
  -- ‖u‖ < sin(πε)
  have hu : ‖u‖ < Real.sin (Real.pi * ε) := by
    rw [show u = δ / (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)) from rfl,
      norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
      Complex.norm_exp_ofReal_mul_I, mul_one, div_lt_iff₀ hm]
    rwa [hZ_norm] at hbd
  rw [hW_eq]
  exact wPhaseOf_perturbation_generic hm hφα hε hε2 hu

/-- **Phase perturbation from stabSeminorm.** If `‖W - Z‖_σ < sin(πε₀)` and `b - a < 1`,
then for every nonzero `σ`-semistable object `F` with phase `φ ∈ (a, b)`, the W-phase
lies within `ε₀` of `φ`. This bridges the global stabSeminorm bound to the pointwise
hperturb condition needed by phase confinement. -/
theorem hperturb_of_stabSeminorm (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hthin : b - a < 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F → a < φ → φ < b →
      φ - ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
      wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < φ + ε₀ := by
  intro F φ hP hFne haφ hφb
  have hfin : stabSeminorm C σ (W - σ.Z) ≠ ⊤ := ne_top_of_lt hW
  set M := (stabSeminorm C σ (W - σ.Z)).toReal
  -- M < sin(πε₀)
  have hM_sin : M < Real.sin (Real.pi * ε₀) := by
    have hsin_pos : 0 < Real.sin (Real.pi * ε₀) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · exact mul_pos Real.pi_pos hε₀
      · calc Real.pi * ε₀ ≤ Real.pi * (1 / 2) := by nlinarith [Real.pi_pos]
          _ = Real.pi / 2 := by ring
          _ < Real.pi := by linarith [Real.pi_pos]
    rw [show (Real.sin (Real.pi * ε₀) : ℝ) =
      (ENNReal.ofReal (Real.sin (Real.pi * ε₀))).toReal from
      (ENNReal.toReal_ofReal (le_of_lt hsin_pos)).symm]
    exact (ENNReal.toReal_lt_toReal hfin
      (ENNReal.ofReal_ne_top)).mpr hsin
  -- ‖(W-Z)(F)‖ ≤ M * ‖Z(F)‖
  have hbd := stabSeminorm_bound_real C σ (W - σ.Z) hfin hP hFne
  -- Z(F) ≠ 0 (from compatibility)
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ F hP hFne
  have hZ_pos : (0 : ℝ) < ‖σ.Z (K₀.of C F)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
      Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  -- ‖(W-Z)(F)‖ < sin(πε₀) * ‖Z(F)‖
  have hbd_strict : ‖(W - σ.Z) (K₀.of C F)‖ <
      Real.sin (Real.pi * ε₀) * ‖σ.Z (K₀.of C F)‖ :=
    lt_of_le_of_lt hbd (by nlinarith)
  -- φ ∈ ((a+b)/2 - 1/2, (a+b)/2 + 1/2) since b - a < 1
  have hφα : φ ∈ Set.Ioo ((a + b) / 2 - 1 / 2) ((a + b) / 2 + 1 / 2) :=
    ⟨by linarith, by linarith⟩
  -- Apply wPhaseOf_perturbation
  have h := wPhaseOf_perturbation C σ hP hFne W hφα hε₀
    (hε₀2.le.trans (by norm_num)) hbd_strict
  exact ⟨by linarith [abs_lt.mp h], by linarith [abs_lt.mp h]⟩

/-! ### Upper half-plane membership from positive argument -/

/-- A nonzero complex number with positive argument lies in the upper half-plane union. -/
lemma mem_upperHalfPlaneUnion_of_arg_pos {z : ℂ}
    (h : 0 < Complex.arg z) : z ∈ upperHalfPlaneUnion := by
  by_cases him : 0 < z.im
  · exact Or.inl him
  · right
    push_neg at him
    have him' : z.im = 0 := le_antisymm him (Complex.arg_nonneg_iff.mp h.le)
    exact ⟨him', by
      by_contra hre
      push_neg at hre
      have : Complex.arg z = 0 := Complex.arg_eq_zero_iff.mpr ⟨hre, him'⟩
      linarith⟩

/-! ### W-phase bounds for sums (Node 7.3 infrastructure) -/

/-- **wPhaseOf characterizes UHP membership.** `wPhaseOf(w, ψ) > ψ` if and only if
`w · exp(-iπψ)` lies in the upper half-plane union (i.e., has positive argument).
This is the forward direction: UHP membership implies wPhaseOf > ψ. -/
theorem wPhaseOf_gt_of_mem_upperHalfPlaneUnion {w : ℂ} {ψ : ℝ}
    (h : w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) ∈
      CategoryTheory.upperHalfPlaneUnion) :
    ψ < wPhaseOf w ψ := by
  have harg := CategoryTheory.arg_pos_of_mem_upperHalfPlaneUnion h
  unfold wPhaseOf
  linarith [div_pos harg Real.pi_pos]

/-- **UHP membership from wPhaseOf bound.** If `ψ < wPhaseOf(w, ψ)`, then
`w · exp(-iπψ)` lies in the upper half-plane union. -/
theorem mem_upperHalfPlaneUnion_of_wPhaseOf_gt {w : ℂ} {ψ : ℝ}
    (h : ψ < wPhaseOf w ψ) :
    w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) ∈
      CategoryTheory.upperHalfPlaneUnion := by
  apply mem_upperHalfPlaneUnion_of_arg_pos
  unfold wPhaseOf at h
  have hπ := Real.pi_pos
  have : 0 < Complex.arg (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))) /
    Real.pi := by linarith
  exact (div_pos_iff.mp this).elim (fun h ↦ h.1)
    (fun h ↦ absurd h.2 (not_lt.mpr hπ.le))

/-- **W-phase lower bound for sums**. If complex numbers `w₁, ..., wₙ` all have
`wPhaseOf(wⱼ, ψ) > ψ` (i.e., are "above" ψ in phase), then their sum satisfies
`wPhaseOf(Σ wⱼ, ψ) > ψ`. The sum is automatically nonzero since UHP is closed under
addition.

The proof rotates by `exp(-iπψ)`, observes all vectors lie in the upper half-plane (since
wPhaseOf > ψ), uses closure of UHP under sums, and converts back. -/
theorem wPhaseOf_sum_gt {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f : ι → ℂ} {ψ : ℝ}
    (hf_phase : ∀ i ∈ s, ψ < wPhaseOf (f i) ψ) :
    ψ < wPhaseOf (∑ i ∈ s, f i) ψ := by
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  -- Each f(i) * rot is in UHP
  have huhp : ∀ i ∈ s, f i * rot ∈ CategoryTheory.upperHalfPlaneUnion :=
    fun i hi ↦ mem_upperHalfPlaneUnion_of_wPhaseOf_gt (hf_phase i hi)
  -- Sum is in UHP
  have hsum_uhp : (∑ i ∈ s, f i) * rot ∈ CategoryTheory.upperHalfPlaneUnion := by
    rw [Finset.sum_mul]
    exact sum_mem_upperHalfPlane hs huhp
  exact wPhaseOf_gt_of_mem_upperHalfPlaneUnion hsum_uhp

/-- **Imaginary part bound for phases above ψ**. If `w = m · exp(iπφ)` with `m > 0` and
`φ ∈ (ψ, ψ + 1)`, then `Im(w · exp(-iπψ)) > 0`. -/
theorem im_pos_of_phase_above {w : ℂ} {m φ ψ : ℝ} (hm : 0 < m)
    (hw : w = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I))
    (hlo : ψ < φ) (hhi : φ < ψ + 1) :
    0 < (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
  rw [hw, mul_assoc, ← Complex.exp_add]
  have harg : ↑(Real.pi * φ) * Complex.I + -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (φ - ψ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero]
  exact mul_pos hm (Real.sin_pos_of_pos_of_lt_pi
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))

/-- **Imaginary part positivity for sums of phase-above vectors.** If complex numbers
`w₁, ..., wₙ` all satisfy `Im(wⱼ · exp(-iπψ)) > 0`, then so does their sum. This is
immediate from additivity of Im. -/
theorem im_sum_pos_of_all_pos {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f : ι → ℂ} {ψ : ℝ}
    (hf : ∀ i ∈ s, 0 < (f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im) :
    0 < (∑ i ∈ s, f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
  rw [show (∑ i ∈ s, f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im =
      ∑ i ∈ s, (f i *
        Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im from
    map_sum Complex.imAddGroupHom _ _]
  exact Finset.sum_pos hf hs

/-- **wPhaseOf bound from imaginary part.** If `Im(w · exp(-iπψ)) > 0` and
`wPhaseOf(w, α) ∈ (ψ - 1, ψ + 1)` (which rules out the wrapping branch), then
`wPhaseOf(w, α) > ψ`. -/
theorem wPhaseOf_gt_of_im_pos {w : ℂ} {α ψ : ℝ}
    (him : 0 < (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im)
    (hrange : wPhaseOf w α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ < wPhaseOf w α := by
  -- w = ‖w‖ · exp(iπ · wPhaseOf(w, α)), so
  -- w · exp(-iπψ) = ‖w‖ · exp(iπ(wPhaseOf(w, α) - ψ))
  -- Im = ‖w‖ · sin(π(wPhaseOf(w, α) - ψ))
  -- If sin > 0, then π(wPhaseOf(w, α) - ψ) ∈ (0, π) ∪ (-2π, -π), i.e.,
  -- wPhaseOf - ψ ∈ (0, 1) ∪ (-2, -1). The range condition rules out (-2, -1).
  by_contra h
  push_neg at h -- h : wPhaseOf w α ≤ ψ
  -- wPhaseOf(w, α) ∈ (ψ - 1, ψ], so wPhaseOf - ψ ∈ (-1, 0]
  -- sin(π(wPhaseOf - ψ)) ≤ 0 on (-1, 0] (since π · (-1, 0] = (-π, 0])
  have hd : wPhaseOf w α - ψ ∈ Set.Ioc (-1) 0 :=
    ⟨by linarith [hrange.1], by linarith⟩
  have hsin : Real.sin (Real.pi * (wPhaseOf w α - ψ)) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [Real.pi_pos, hd.2])
      (by nlinarith [Real.pi_pos, hd.1])
  -- But Im = ‖w‖ · sin(...) > 0 and ‖w‖ ≥ 0, so sin > 0. Contradiction.
  have hw := wPhaseOf_compat w α
  rw [hw] at him
  rw [mul_assoc, ← Complex.exp_add] at him
  have harg : ↑(Real.pi * wPhaseOf w α) * Complex.I +
      -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (wPhaseOf w α - ψ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero] at him
  linarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w) hsin]

/-! ### Dual im/wPhaseOf infrastructure (for lower bound arguments) -/

/-- **Imaginary part negativity for below-phase vectors.** If `w = m · exp(iπφ)` with `m > 0`
and `φ ∈ (ψ - 1, ψ)`, then `Im(w · exp(-iπψ)) < 0`. Dual of `im_pos_of_phase_above`. -/
theorem im_neg_of_phase_below {w : ℂ} {m φ ψ : ℝ} (hm : 0 < m)
    (hw : w = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I))
    (hlo : ψ - 1 < φ) (hhi : φ < ψ) :
    (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0 := by
  rw [hw, mul_assoc, ← Complex.exp_add]
  have harg : ↑(Real.pi * φ) * Complex.I + -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (φ - ψ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero]
  exact mul_neg_of_pos_of_neg hm (Real.sin_neg_of_neg_of_neg_pi_lt
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))

/-- **Imaginary part negativity for sums of phase-below vectors.** If complex numbers
`w₁, ..., wₙ` all satisfy `Im(wⱼ · exp(-iπψ)) < 0`, then so does their sum.
Dual of `im_sum_pos_of_all_pos`. -/
theorem im_sum_neg_of_all_neg {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f : ι → ℂ} {ψ : ℝ}
    (hf : ∀ i ∈ s, (f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0) :
    (∑ i ∈ s, f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0 := by
  rw [show (∑ i ∈ s, f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im =
      ∑ i ∈ s, (f i *
        Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im from
    map_sum Complex.imAddGroupHom _ _]
  exact Finset.sum_neg hf hs

/-- **wPhaseOf bound from negative imaginary part.** If `Im(w · exp(-iπψ)) < 0` and
`wPhaseOf(w, α) ∈ (ψ - 1, ψ + 1)`, then `wPhaseOf(w, α) < ψ`.
Dual of `wPhaseOf_gt_of_im_pos`. -/
theorem wPhaseOf_lt_of_im_neg {w : ℂ} {α ψ : ℝ}
    (him : (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0)
    (hrange : wPhaseOf w α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    wPhaseOf w α < ψ := by
  by_contra h
  push_neg at h -- h : ψ ≤ wPhaseOf w α
  -- wPhaseOf(w, α) ∈ [ψ, ψ + 1), so wPhaseOf - ψ ∈ [0, 1)
  -- sin(π(wPhaseOf - ψ)) ≥ 0 on [0, 1) (since π · [0, 1) = [0, π))
  have hd : wPhaseOf w α - ψ ∈ Set.Ico 0 1 :=
    ⟨by linarith, by linarith [hrange.2]⟩
  have hsin : 0 ≤ Real.sin (Real.pi * (wPhaseOf w α - ψ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos, hd.1])
      (by nlinarith [Real.pi_pos, hd.2])
  -- But Im = ‖w‖ · sin(...) < 0 and ‖w‖ ≥ 0, so sin < 0. Contradiction.
  have hw := wPhaseOf_compat w α
  rw [hw] at him
  rw [mul_assoc, ← Complex.exp_add] at him
  have harg : ↑(Real.pi * wPhaseOf w α) * Complex.I +
      -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (wPhaseOf w α - ψ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero] at him
  linarith [mul_nonneg (norm_nonneg w) hsin]

/-- **Imaginary part vanishes at exact phase.** If `wPhaseOf(w, α) = ψ`, then
`Im(w · exp(-iπψ)) = 0` (and in fact `w · exp(-iπψ) = ‖w‖`). -/
theorem im_eq_zero_of_wPhaseOf_eq {w : ℂ} {α ψ : ℝ}
    (h : wPhaseOf w α = ψ) :
    (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im = 0 := by
  have hw := wPhaseOf_compat w α
  rw [hw, h, mul_assoc, ← Complex.exp_add]
  have harg : ↑(Real.pi * ψ) * Complex.I +
      -(↑(Real.pi * ψ) * Complex.I) = 0 := by ring
  rw [harg, Complex.exp_zero, mul_one, Complex.ofReal_im]

/-- **Imaginary part sign decomposition.** If `w₁ + w₂ = w` and
`Im(w · exp(-iπψ)) = 0` and `Im(w₂ · exp(-iπψ)) < 0`, then
`Im(w₁ · exp(-iπψ)) > 0`. -/
theorem im_pos_of_sum_zero_and_neg {w₁ w₂ w : ℂ} {ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hw : (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im = 0)
    (h₂ : (w₂ * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0) :
    0 < (w₁ * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
  have : (w₁ + w₂) * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) =
      w₁ * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) +
      w₂ * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) := add_mul _ _ _
  rw [hsum] at this
  have him := congr_arg Complex.im this
  simp only [Complex.add_im] at him
  linarith

/-! ### Phase see-saw lemma -/

/-- **Phase see-saw**: if `w = w₁ + w₂` with `wPhaseOf(w, α) = ψ`,
`wPhaseOf(w₁, α) ∈ (ψ - 1, ψ]` (i.e., w₁ has phase ≤ ψ in the correct range),
and `w₂ ≠ 0` with `wPhaseOf(w₂, α) ∈ (ψ - 1, ψ + 1)`, then `wPhaseOf(w₂, α) ≥ ψ`.

The proof uses the imaginary-part sign argument: `Im(w · rot) = 0` (from phase = ψ),
`Im(w₁ · rot) ≤ 0` (from phase ≤ ψ in (-1, 0] range), and if `Im(w₂ · rot) < 0`
(from phase < ψ), then `Im(w · rot) < 0`, contradiction. -/
theorem wPhaseOf_seesaw {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hψ : wPhaseOf w α = ψ)
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioc (ψ - 1) ψ)
    (hw₂_ne : w₂ ≠ 0)
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ ≤ wPhaseOf w₂ α := by
  by_contra h
  push_neg at h
  -- w₂ has phase < ψ in (ψ-1, ψ), so Im(w₂ · rot) < 0
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im = 0 := im_eq_zero_of_wPhaseOf_eq hψ
  -- Im(w₁ · rot) ≤ 0
  have him_w₁ : (w₁ * rot).im ≤ 0 := by
    have hw₁_compat := wPhaseOf_compat w₁ α
    rw [hw₁_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₁ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₁ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w₁)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw₁_range.2])
        (by nlinarith [Real.pi_pos, hw₁_range.1]))
  -- Im(w₂ · rot) < 0
  have him_w₂ : (w₂ * rot).im < 0 := by
    have hw₂_compat := wPhaseOf_compat w₂ α
    rw [hw₂_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₂ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₂ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, h])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  -- Contradiction: Im(w · rot) = Im(w₁ · rot) + Im(w₂ · rot) < 0
  have hsum_im : (w * rot).im = (w₁ * rot).im + (w₂ * rot).im := by
    rw [← hsum, add_mul, Complex.add_im]
  linarith

/-- **Strict phase see-saw**: if `w = w₁ + w₂` with `wPhaseOf(w, α) = ψ`,
`wPhaseOf(w₂, α) < ψ` with `wPhaseOf(w₂, α) ∈ (ψ - 1, ψ + 1)`, `w₂ ≠ 0`,
and `wPhaseOf(w₁, α) ∈ (ψ - 1, ψ + 1)`, then `wPhaseOf(w₁, α) > ψ`.

This is the dual of `wPhaseOf_seesaw` with roles swapped. -/
theorem wPhaseOf_seesaw_strict {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hψ : wPhaseOf w α = ψ)
    (hw₂_lt : wPhaseOf w₂ α < ψ)
    (hw₂_ne : w₂ ≠ 0)
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ < wPhaseOf w₁ α := by
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im = 0 := im_eq_zero_of_wPhaseOf_eq hψ
  -- Im(w₂ · rot) < 0
  have him_w₂ : (w₂ * rot).im < 0 := by
    have hw₂_compat := wPhaseOf_compat w₂ α
    rw [hw₂_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₂ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₂ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, hw₂_lt])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  -- Im(w₁ · rot) > 0
  have him_w₁ : 0 < (w₁ * rot).im := by
    have hsum_im : (w * rot).im = (w₁ * rot).im + (w₂ * rot).im := by
      rw [← hsum, add_mul, Complex.add_im]
    linarith
  -- Conclude phase(w₁) > ψ
  exact wPhaseOf_gt_of_im_pos him_w₁ hw₁_range

/-- **Dual strict phase see-saw**: if `w = w₁ + w₂` with `wPhaseOf(w, α) = ψ`,
`ψ < wPhaseOf(w₁, α)` and both summands lie in the same branch window
`(ψ - 1, ψ + 1)`, then the other nonzero summand has phase `< ψ`.

This is the quotient-side form used when a strict subobject destabilizes an object:
the complementary strict quotient must have strictly smaller phase. -/
theorem wPhaseOf_seesaw_dual {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hψ : wPhaseOf w α = ψ)
    (hw₁_gt : ψ < wPhaseOf w₁ α)
    (hw₁_ne : w₁ ≠ 0)
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    wPhaseOf w₂ α < ψ := by
  by_contra h
  push_neg at h
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im = 0 := im_eq_zero_of_wPhaseOf_eq hψ
  have him_w₁ : 0 < (w₁ * rot).im := by
    have hw₁_compat := wPhaseOf_compat w₁ α
    rw [hw₁_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₁ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₁ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_pos (norm_pos_iff.mpr hw₁_ne)
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [Real.pi_pos, hw₁_gt])
        (by nlinarith [Real.pi_pos, hw₁_range.2]))
  have him_w₂ : 0 ≤ (w₂ * rot).im := by
    have hw₂_compat := wPhaseOf_compat w₂ α
    rw [hw₂_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₂ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₂ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_nonneg (norm_nonneg w₂)
      (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos, h])
        (by nlinarith [Real.pi_pos, hw₂_range.2]))
  have hsum_im : (w * rot).im = (w₁ * rot).im + (w₂ * rot).im := by
    rw [← hsum, add_mul, Complex.add_im]
  linarith

theorem wPhaseOf_lt_of_add_le_lt {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioc (ψ - 1) ψ)
    (hw₂_lt : wPhaseOf w₂ α < ψ)
    (hw₂_ne : w₂ ≠ 0)
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw_range : wPhaseOf w α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    wPhaseOf w α < ψ := by
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w₁ : (w₁ * rot).im ≤ 0 := by
    have hw₁_compat := wPhaseOf_compat w₁ α
    rw [hw₁_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₁ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₁ α - ψ)) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w₁)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw₁_range.2])
        (by nlinarith [Real.pi_pos, hw₁_range.1]))
  have him_w₂ : (w₂ * rot).im < 0 := by
    have hw₂_compat := wPhaseOf_compat w₂ α
    rw [hw₂_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₂ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₂ α - ψ)) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, hw₂_lt])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  have him_w : (w * rot).im < 0 := by
    rw [← hsum, add_mul, Complex.add_im]
    linarith
  exact wPhaseOf_lt_of_im_neg him_w hw_range

/-- If `w = w₁ + w₂`, the total phase is at most `ψ`, and one summand has phase strictly
above `ψ`, then the other summand has phase strictly below `ψ`. This is the one-sided
source-envelope variant of the phase seesaw used in the faithful Lemma 7.5 argument. -/
theorem wPhaseOf_lt_of_add_le_gt {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hw_le : wPhaseOf w α ≤ ψ)
    (hw_range : wPhaseOf w α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₁_gt : ψ < wPhaseOf w₁ α)
    (hw₁_ne : w₁ ≠ 0)
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    wPhaseOf w₂ α < ψ := by
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im ≤ 0 := by
    have hw_compat := wPhaseOf_compat w α
    rw [hw_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w α - ψ)) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw_le])
        (by nlinarith [Real.pi_pos, hw_range.1]))
  have him_w₁ : 0 < (w₁ * rot).im := by
    have hw₁_compat := wPhaseOf_compat w₁ α
    rw [hw₁_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₁ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₁ α - ψ)) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_pos (norm_pos_iff.mpr hw₁_ne)
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [Real.pi_pos, hw₁_gt])
        (by nlinarith [Real.pi_pos, hw₁_range.2]))
  have him_w₂ : (w₂ * rot).im < 0 := by
    rw [← hsum, add_mul, Complex.add_im] at him_w
    linarith
  exact wPhaseOf_lt_of_im_neg him_w₂ hw₂_range

/-! ### K₀ decomposition of imaginary parts -/

/-- **Im positivity from HN factors.** If `E ∈ P((a, b))` is nonzero and every nonzero
σ-semistable factor of an HN filtration has `Im(W(Fⱼ) · exp(-iπψ)) ≥ 0`, with at least
one factor giving strict positivity, then `Im(W(E) · exp(-iπψ)) > 0`.

The proof decomposes `W([E]) = ∑ W([Fⱼ])` via K₀ additivity and extracts Im through
the sum using the additivity of the imaginary part. -/
theorem im_W_pos_of_intervalProp
    (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {ψ : ℝ}
    {a b : ℝ} (hI : σ.slicing.intervalProp C a b E)
    (him_pos : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        0 < (W (K₀.of C F) *
          Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im) :
    0 < (W (K₀.of C E) *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
  -- Get HN filtration with nonzero first and last factors
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  -- All phases in (a, b) — use uniqueness to relate to intrinsic phases
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b := by
    intro i
    exact ⟨by calc a < σ.slicing.phiMinus C E hE :=
              σ.slicing.phiMinus_gt_of_intervalProp C hE hI
            _ = F.φ ⟨F.n - 1, by omega⟩ :=
              σ.slicing.phiMinus_eq C E hE F hn hlast
            _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by calc F.φ i
            ≤ F.φ ⟨0, hn⟩ :=
              F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C E hE :=
              (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
            _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hE hI⟩
  -- K₀ decomposition: W(E) = Σ W(Fⱼ)
  set P := F.toPostnikovTower
  have hWE : W (K₀.of C E) =
      ∑ i : Fin F.n, W (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  -- Im(W(E) · rot) = Σ Im(W(Fⱼ) · rot)
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  rw [hWE, Finset.sum_mul]
  rw [show (∑ i : Fin F.n, W (K₀.of C (P.factor i)) * rot).im =
      ∑ i : Fin F.n, (W (K₀.of C (P.factor i)) * rot).im from
    map_sum Complex.imAddGroupHom _ _]
  -- Each term ≥ 0, first term > 0
  apply lt_of_lt_of_le _ (Finset.single_le_sum
    (f := fun i ↦ (W (K₀.of C (P.factor i)) * rot).im)
    (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hn⟩))
  · -- First factor contributes Im > 0
    exact him_pos _ _ (F.semistable ⟨0, hn⟩) hfirst
      (hphases ⟨0, hn⟩).1 (hphases ⟨0, hn⟩).2
  · -- Each factor contributes Im ≥ 0
    by_cases hi : IsZero (P.factor i)
    · simp [K₀.of_isZero C hi]
    · exact le_of_lt (him_pos _ _ (F.semistable i) hi
        (hphases i).1 (hphases i).2)

/-- **Dual: Im negativity from HN factors.** If `E ∈ P((a, b))` is nonzero and every
nonzero σ-semistable factor has `Im(W(Fⱼ) · exp(-iπψ)) ≤ 0`, with at least one giving
strict negativity, then `Im(W(E) · exp(-iπψ)) < 0`. -/
theorem im_W_neg_of_intervalProp
    (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {ψ : ℝ}
    {a b : ℝ} (hI : σ.slicing.intervalProp C a b E)
    (him_neg : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        (W (K₀.of C F) *
          Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0) :
    (W (K₀.of C E) *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0 := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b := by
    intro i
    exact ⟨by calc a < σ.slicing.phiMinus C E hE :=
              σ.slicing.phiMinus_gt_of_intervalProp C hE hI
            _ = F.φ ⟨F.n - 1, by omega⟩ :=
              σ.slicing.phiMinus_eq C E hE F hn hlast
            _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by calc F.φ i
            ≤ F.φ ⟨0, hn⟩ :=
              F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C E hE :=
              (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
            _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hE hI⟩
  set P := F.toPostnikovTower
  have hWE : W (K₀.of C E) =
      ∑ i : Fin F.n, W (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  rw [hWE, Finset.sum_mul]
  rw [show (∑ i : Fin F.n, W (K₀.of C (P.factor i)) * rot).im =
      ∑ i : Fin F.n, (W (K₀.of C (P.factor i)) * rot).im from
    map_sum Complex.imAddGroupHom _ _]
  -- Negate: show Σ (-Im) > 0, then Σ Im < 0
  suffices h : 0 < ∑ i : Fin F.n,
      -(W (K₀.of C (P.factor i)) * rot).im by
    linarith [Finset.sum_neg_distrib (G := ℝ) (s := Finset.univ)
      (f := fun i ↦ (W (K₀.of C (P.factor i)) * rot).im)]
  apply lt_of_lt_of_le _ (Finset.single_le_sum
    (f := fun i ↦ -(W (K₀.of C (P.factor i)) * rot).im)
    (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hn⟩))
  · -- First factor: -Im > 0
    exact neg_pos.mpr (him_neg _ _ (F.semistable ⟨0, hn⟩) hfirst
      (hphases ⟨0, hn⟩).1 (hphases ⟨0, hn⟩).2)
  · -- Each factor: -Im ≥ 0
    by_cases hi : IsZero (P.factor i)
    · simp [K₀.of_isZero C hi]
    · exact le_of_lt (neg_pos.mpr (him_neg _ _ (F.semistable i) hi
        (hphases i).1 (hphases i).2))

/-! ### W-phase range for interval objects (Lemma 7.3(b)) -/

/-- **W-phase lower bound for interval objects.** If `E ∈ P((a, b))` is nonzero, and
every nonzero σ-semistable object of phase `φ ∈ (a, b)` has
`W`-phase in `(a - ε, a - ε + 1)` (so `Im(W(F) · exp(-iπ(a-ε))) > 0`), then
`wPhaseOf(W(E), α) > a - ε`.

This is part (b) of **Bridgeland's Lemma 7.3** (lower bound). The proof uses the
K₀ decomposition to show `Im(W(E) · exp(-iπ(a-ε))) > 0`, then converts to a phase
bound via the sin/Im relationship. -/
theorem wPhaseOf_gt_of_intervalProp
    (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {α : ℝ}
    {a b ε : ℝ}
    (hα_ge : a - ε ≤ α)
    (hI : σ.slicing.intervalProp C a b E)
    (hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b → W (K₀.of C F) ≠ 0)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        a - ε < wPhaseOf (W (K₀.of C F)) α ∧
        wPhaseOf (W (K₀.of C F)) α < a - ε + 1) :
    a - ε < wPhaseOf (W (K₀.of C E)) α := by
  -- Each nonzero factor has Im > 0 after rotation by a - ε
  have him : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      0 < (W (K₀.of C F) *
        Complex.exp (-(↑(Real.pi * (a - ε)) * Complex.I))).im := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    have hWne := hW_ne F φ hP hFne haφ hφb
    -- W(F) = ‖W(F)‖ · exp(iπ · wPhaseOf(W(F), α))
    set θ := wPhaseOf (W (K₀.of C F)) α
    have hm : (0 : ℝ) < ‖W (K₀.of C F)‖ := norm_pos_iff.mpr hWne
    exact im_pos_of_phase_above hm (wPhaseOf_compat _ _) hlo hhi
  -- By K₀ decomposition: Im(W(E) · rot) > 0
  have him_pos := im_W_pos_of_intervalProp C σ hE W hI him
  -- Convert Im > 0 to phase bound
  -- W(E) = ‖W(E)‖ · exp(iπψ), so W(E)·rot = ‖W(E)‖ · exp(iπ(ψ - (a-ε)))
  -- Im > 0 means sin(π(ψ - (a-ε))) > 0
  -- If ψ ≤ a - ε, then ψ - (a-ε) ≤ 0, and we need to check sin ≤ 0
  by_contra h
  push_neg at h -- h : wPhaseOf(W(E), α) ≤ a - ε
  set ψ := wPhaseOf (W (K₀.of C E)) α
  have hw := wPhaseOf_compat (W (K₀.of C E)) α
  rw [hw] at him_pos
  rw [mul_assoc, ← Complex.exp_add] at him_pos
  have harg : ↑(Real.pi * ψ) * Complex.I +
      -(↑(Real.pi * (a - ε)) * Complex.I) =
      ↑(Real.pi * (ψ - (a - ε))) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero] at him_pos
  -- ψ - (a - ε) ∈ (-1, 0] (from ψ > α - 1 and ψ ≤ a - ε)
  have hψ_range := wPhaseOf_mem_Ioc (W (K₀.of C E)) α
  have hψ_lo : α - 1 < ψ := hψ_range.1
  -- sin(π(ψ - (a-ε))) ≤ 0 on (-1, 0] (since π(-1, 0] = (-π, 0])
  have hsin : Real.sin (Real.pi * (ψ - (a - ε))) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hψ_lo])
  linarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (W (K₀.of C E))) hsin]

/-- **W-phase upper bound for interval objects.** If `E ∈ P((a, b))` is nonzero, and
every nonzero σ-semistable object of phase `φ ∈ (a, b)` has W-phase in
`(b + ε - 1, b + ε)` (so `Im(W(F) · exp(-iπ(b+ε))) < 0`), then
`wPhaseOf(W(E), α) < b + ε`. -/
theorem wPhaseOf_lt_of_intervalProp
    (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {α : ℝ}
    {a b ε : ℝ}
    (hα_le : α ≤ b + ε)
    (hI : σ.slicing.intervalProp C a b E)
    (hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b → W (K₀.of C F) ≠ 0)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        b + ε - 1 < wPhaseOf (W (K₀.of C F)) α ∧
        wPhaseOf (W (K₀.of C F)) α < b + ε) :
    wPhaseOf (W (K₀.of C E)) α < b + ε := by
  -- Each nonzero factor has Im < 0 after rotation by b + ε
  have him : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      (W (K₀.of C F) *
        Complex.exp (-(↑(Real.pi * (b + ε)) * Complex.I))).im < 0 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    have hWne := hW_ne F φ hP hFne haφ hφb
    set θ := wPhaseOf (W (K₀.of C F)) α
    have hm : (0 : ℝ) < ‖W (K₀.of C F)‖ := norm_pos_iff.mpr hWne
    exact im_neg_of_phase_below hm (wPhaseOf_compat _ _) hlo hhi
  have him_neg := im_W_neg_of_intervalProp C σ hE W hI him
  by_contra h
  push_neg at h -- h : b + ε ≤ wPhaseOf(W(E), α)
  set ψ := wPhaseOf (W (K₀.of C E)) α
  have hw := wPhaseOf_compat (W (K₀.of C E)) α
  rw [hw] at him_neg
  rw [mul_assoc, ← Complex.exp_add] at him_neg
  have harg : ↑(Real.pi * ψ) * Complex.I +
      -(↑(Real.pi * (b + ε)) * Complex.I) =
      ↑(Real.pi * (ψ - (b + ε))) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero] at him_neg
  -- ψ - (b + ε) ∈ [0, 1) (from ψ ≥ b + ε and ψ ≤ α + 1)
  have hψ_range := wPhaseOf_mem_Ioc (W (K₀.of C E)) α
  have hψ_hi : ψ ≤ α + 1 := hψ_range.2
  have hsin : 0 ≤ Real.sin (Real.pi * (ψ - (b + ε))) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hψ_hi])
  linarith [mul_nonneg (norm_nonneg (W (K₀.of C E))) hsin]


end CategoryTheory.Triangulated
