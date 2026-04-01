/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.PhasePerturbation

/-!
# W-Phase Bounds for Deformation

Stability-condition-specific phase bounds: perturbation of σ-semistable phases,
W-phase see-saw lemma, K₀ imaginary-part decomposition, and Lemma 7.3(b)
(W-phase range for interval objects).

Builds on the pure complex analysis in `PhasePerturbation.lean`.
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

/-! ### Phase perturbation bound -/

/-- **Coarse phase perturbation bound**. If `E` is σ-semistable of phase `φ ∈ (α-1, α+1]`,
then `wPhaseOf(Z(E), α) = φ`. This is the inverse direction of `wPhaseOf_of_exp`. -/
theorem wPhaseOf_Z_eq (σ : StabilityCondition C) {E : C} {φ : ℝ}
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) {α : ℝ}
    (hφ : φ ∈ Set.Ioc (α - 1) (α + 1)) :
    wPhaseOf (σ.Z (K₀.of C E)) α = φ := by
  obtain ⟨m, hm, hmZ⟩ := stabilityCondition_compat_apply (C := C) σ φ E hP hE
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
  obtain ⟨m, hm, hmZ⟩ := stabilityCondition_compat_apply (C := C) σ φ E hP hE
  -- Set u = (W-Z)(E) / Z(E)
  set δ := (W - σ.Z) (K₀.of C E)
  have hWZ : δ = W (K₀.of C E) - σ.Z (K₀.of C E) := AddMonoidHom.sub_apply W σ.Z _
  have hZ_norm : ‖σ.Z (K₀.of C E)‖ = m := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm, Complex.norm_exp_ofReal_mul_I, mul_one]
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
  simp only [cl_id] at hbd
  -- Z(F) ≠ 0 (from compatibility)
  obtain ⟨m, hm, hmZ⟩ := stabilityCondition_compat_apply (C := C) σ φ F hP hFne
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
    push Not at him
    have him' : z.im = 0 := le_antisymm him (Complex.arg_nonneg_iff.mp h.le)
    exact ⟨him', by
      by_contra hre
      push Not at hre
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
  rw [hw, im_ofReal_mul_exp_mul_exp_neg]
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
  push Not at h -- h : wPhaseOf w α ≤ ψ
  -- wPhaseOf(w, α) ∈ (ψ - 1, ψ], so wPhaseOf - ψ ∈ (-1, 0]
  -- sin(π(wPhaseOf - ψ)) ≤ 0 on (-1, 0] (since π · (-1, 0] = (-π, 0])
  have hd : wPhaseOf w α - ψ ∈ Set.Ioc (-1) 0 :=
    ⟨by linarith [hrange.1], by linarith⟩
  have hsin : Real.sin (Real.pi * (wPhaseOf w α - ψ)) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [Real.pi_pos, hd.2])
      (by nlinarith [Real.pi_pos, hd.1])
  -- But Im = ‖w‖ · sin(...) > 0 and ‖w‖ ≥ 0, so sin > 0. Contradiction.
  rw [wPhaseOf_compat w α, im_ofReal_mul_exp_mul_exp_neg] at him
  linarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w) hsin]

/-! ### Dual im/wPhaseOf infrastructure (for lower bound arguments) -/

/-- **Imaginary part negativity for below-phase vectors.** If `w = m · exp(iπφ)` with `m > 0`
and `φ ∈ (ψ - 1, ψ)`, then `Im(w · exp(-iπψ)) < 0`. Dual of `im_pos_of_phase_above`. -/
theorem im_neg_of_phase_below {w : ℂ} {m φ ψ : ℝ} (hm : 0 < m)
    (hw : w = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I))
    (hlo : ψ - 1 < φ) (hhi : φ < ψ) :
    (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0 := by
  rw [hw, im_ofReal_mul_exp_mul_exp_neg]
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
  push Not at h -- h : ψ ≤ wPhaseOf w α
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
  rw [hw, im_ofReal_mul_exp_mul_exp_neg] at him
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

/-! ### Rotated imaginary part -/

/-- **Rotated imaginary part identity.** For any `w : ℂ` and `α ψ : ℝ`,
`Im(w · exp(-iπψ)) = ‖w‖ · sin(π · (wPhaseOf w α - ψ))`. This is the
core computation shared by all see-saw and phase-comparison lemmas. -/
theorem im_mul_exp_neg_eq_norm_mul_sin (w : ℂ) (α ψ : ℝ) :
    (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im =
    ‖w‖ * Real.sin (Real.pi * (wPhaseOf w α - ψ)) := by
  conv_lhs => rw [wPhaseOf_compat w α]
  rw [im_ofReal_mul_exp_mul_exp_neg]

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
  push Not at h
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im = 0 := im_eq_zero_of_wPhaseOf_eq hψ
  have him_w₁ : (w₁ * rot).im ≤ 0 := by
    rw [im_mul_exp_neg_eq_norm_mul_sin w₁ α ψ]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w₁)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw₁_range.2])
        (by nlinarith [Real.pi_pos, hw₁_range.1]))
  have him_w₂ : (w₂ * rot).im < 0 := by
    rw [im_mul_exp_neg_eq_norm_mul_sin w₂ α ψ]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, h])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
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
  have him_w₂ : (w₂ * rot).im < 0 := by
    rw [im_mul_exp_neg_eq_norm_mul_sin w₂ α ψ]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, hw₂_lt])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  have him_w₁ : 0 < (w₁ * rot).im := by
    have : (w * rot).im = (w₁ * rot).im + (w₂ * rot).im := by
      rw [← hsum, add_mul, Complex.add_im]
    linarith
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
  push Not at h
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im = 0 := im_eq_zero_of_wPhaseOf_eq hψ
  have him_w₁ : 0 < (w₁ * rot).im := by
    rw [im_mul_exp_neg_eq_norm_mul_sin w₁ α ψ]
    exact mul_pos (norm_pos_iff.mpr hw₁_ne)
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [Real.pi_pos, hw₁_gt])
        (by nlinarith [Real.pi_pos, hw₁_range.2]))
  have him_w₂ : 0 ≤ (w₂ * rot).im := by
    rw [im_mul_exp_neg_eq_norm_mul_sin w₂ α ψ]
    exact mul_nonneg (norm_nonneg w₂)
      (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos, h])
        (by nlinarith [Real.pi_pos, hw₂_range.2]))
  have : (w * rot).im = (w₁ * rot).im + (w₂ * rot).im := by
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
    rw [im_mul_exp_neg_eq_norm_mul_sin w₁ α ψ]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w₁)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw₁_range.2])
        (by nlinarith [Real.pi_pos, hw₁_range.1]))
  have him_w₂ : (w₂ * rot).im < 0 := by
    rw [im_mul_exp_neg_eq_norm_mul_sin w₂ α ψ]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, hw₂_lt])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  have him_w : (w * rot).im < 0 := by
    rw [← hsum, add_mul, Complex.add_im]; linarith
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
    rw [im_mul_exp_neg_eq_norm_mul_sin w α ψ]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw_le])
        (by nlinarith [Real.pi_pos, hw_range.1]))
  have him_w₁ : 0 < (w₁ * rot).im := by
    rw [im_mul_exp_neg_eq_norm_mul_sin w₁ α ψ]
    exact mul_pos (norm_pos_iff.mpr hw₁_ne)
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [Real.pi_pos, hw₁_gt])
        (by nlinarith [Real.pi_pos, hw₁_range.2]))
  have him_w₂ : (w₂ * rot).im < 0 := by
    rw [← hsum, add_mul, Complex.add_im] at him_w; linarith
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
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b := fun i =>
    ⟨by calc a < σ.slicing.phiMinus C E hE :=
              σ.slicing.phiMinus_gt_of_intervalProp C hE hI
            _ = F.φ ⟨F.n - 1, by lia⟩ :=
              σ.slicing.phiMinus_eq C E hE F hn hlast
            _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia)),
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
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b := fun i =>
    ⟨by calc a < σ.slicing.phiMinus C E hE :=
              σ.slicing.phiMinus_gt_of_intervalProp C hE hI
            _ = F.φ ⟨F.n - 1, by lia⟩ :=
              σ.slicing.phiMinus_eq C E hE F hn hlast
            _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia)),
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
  push Not at h -- h : wPhaseOf(W(E), α) ≤ a - ε
  set ψ := wPhaseOf (W (K₀.of C E)) α
  have hw := wPhaseOf_compat (W (K₀.of C E)) α
  rw [hw, im_ofReal_mul_exp_mul_exp_neg] at him_pos
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
  push Not at h -- h : b + ε ≤ wPhaseOf(W(E), α)
  set ψ := wPhaseOf (W (K₀.of C E)) α
  have hw := wPhaseOf_compat (W (K₀.of C E)) α
  rw [hw, im_ofReal_mul_exp_mul_exp_neg] at him_neg
  -- ψ - (b + ε) ∈ [0, 1) (from ψ ≥ b + ε and ψ ≤ α + 1)
  have hψ_range := wPhaseOf_mem_Ioc (W (K₀.of C E)) α
  have hψ_hi : ψ ≤ α + 1 := hψ_range.2
  have hsin : 0 ≤ Real.sin (Real.pi * (ψ - (b + ε))) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hψ_hi])
  linarith [mul_nonneg (norm_nonneg (W (K₀.of C E))) hsin]

end CategoryTheory.Triangulated
