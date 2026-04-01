/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.Setup

/-!
# Deformation of Stability Conditions — WPhase

Skewed stability function, W-phase, W-semistability
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

/-! ### Node 7.2a: W restricts to a skewed stability function -/

/-- **W-nonvanishing**. If the seminorm `‖W - Z‖_σ < 1`, then `W([E]) ≠ 0` for every
nonzero `σ`-semistable object `E`. The proof uses the triangle inequality:
`‖W([E])‖ ≥ ‖Z([E])‖ - ‖(W-Z)([E])‖ ≥ (1 - M) · ‖Z([E])‖ > 0`. -/
theorem StabilityCondition.W_ne_zero_of_seminorm_lt_one (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1) {E : C} {φ : ℝ}
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    W (K₀.of C E) ≠ 0 := by
  have hfin : stabSeminorm C σ (W - σ.Z) ≠ ⊤ := ne_top_of_lt hW
  set M := (stabSeminorm C σ (W - σ.Z)).toReal
  have hM1 : M < 1 := by
    rw [show (1 : ℝ) = (ENNReal.ofReal 1).toReal from
      (ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1)).symm]
    exact (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hW
  -- Z([E]) = m · exp(iπφ) with m > 0, so ‖Z([E])‖ = m > 0
  obtain ⟨m, hm, hmZ⟩ := stabilityCondition_compat_apply (C := C) σ φ E hP hE
  have hZ_pos : (0 : ℝ) < ‖σ.Z (K₀.of C E)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  -- ‖(W - Z)([E])‖ ≤ M · ‖Z([E])‖
  have hbd := stabSeminorm_bound_real C σ (W - σ.Z) hfin hP hE
  simp only [cl_id] at hbd
  -- If W([E]) = 0, then (W - Z)([E]) = -Z([E]), so ‖(W-Z)([E])‖ = ‖Z([E])‖
  -- But ‖(W-Z)([E])‖ ≤ M · ‖Z([E])‖ with M < 1, contradicting ‖Z([E])‖ > 0
  intro hw0
  have hWZ : (W - σ.Z) (K₀.of C E) = W (K₀.of C E) - σ.Z (K₀.of C E) :=
    AddMonoidHom.sub_apply W σ.Z (K₀.of C E)
  rw [hWZ, hw0, zero_sub, norm_neg] at hbd
  nlinarith

/-- **Node 7.2a**. Given a stability condition `σ` and a group homomorphism `W` with
`‖W - Z‖_σ < 1`, `W` restricts to a `SkewedStabilityFunction` on any interval `(a, b)`
with `a < b`. The skewing parameter is `(a + b) / 2`. -/
def StabilityCondition.skewedStabilityFunction_of_near (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b) :
    SkewedStabilityFunction C σ.slicing a b where
  W := W
  α := (a + b) / 2
  hα_mem := ⟨by linarith, by linarith⟩
  nonzero := fun E φ _ _ hP hE ↦
    σ.W_ne_zero_of_seminorm_lt_one C W hW hP hE

/-! ### Z-nonvanishing for interval objects -/

/-- **Z-nonvanishing for interval objects**. For a nonzero object `E` in a thin interval
`P((a, b))` with `b - a < 1`, the central charge satisfies `‖Z([E])‖ > 0`. The proof
decomposes `E` via its HN filtration and applies the sector estimate
`norm_sum_exp_ge_cos_mul_sum` to bound `‖Z(E)‖` from below. -/
theorem StabilityCondition.norm_Z_pos_of_intervalProp (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E) {a b : ℝ} (hab : b - a < 1)
    (hI : σ.slicing.intervalProp C a b E) :
    0 < ‖σ.Z (K₀.of C E)‖ := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  -- All HN phases are in (a, b)
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b := by
    intro i
    constructor
    · calc a < σ.slicing.phiMinus C E hE :=
            σ.slicing.phiMinus_gt_of_intervalProp C hE hI
        _ = F.φ ⟨F.n - 1, by lia⟩ :=
            σ.slicing.phiMinus_eq C E hE F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C E hE :=
            (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
        _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hE hI
  set P := F.toPostnikovTower
  -- K₀ decomposition: Z(E) = Σ Z(Fᵢ) = Σ ‖Z(Fᵢ)‖ * exp(iπφᵢ)
  have hZE : σ.Z (K₀.of C E) =
      ∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  have hZi : ∀ i : Fin F.n,
      σ.Z (K₀.of C (P.factor i)) =
      ↑(‖σ.Z (K₀.of C (P.factor i))‖) *
        Complex.exp (↑(Real.pi * F.φ i) * Complex.I) := by
    intro i
    by_cases hi : IsZero (P.factor i)
    · simp [K₀.of_isZero C hi]
    · obtain ⟨m, hm, hmZ⟩ :=
        stabilityCondition_compat_apply (C := C) σ (F.φ i) (P.factor i) (F.semistable i) hi
      rw [hmZ]; congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  -- Derive a < b from existence of phases
  have hab_pos : 0 < b - a := by
    linarith [(hphases ⟨0, hn⟩).1, (hphases ⟨0, hn⟩).2]
  -- Sector estimate setup
  have hw : Real.pi * (b - a) < Real.pi := by
    nlinarith [Real.pi_pos]
  have hw0 : 0 ≤ Real.pi * (b - a) :=
    mul_nonneg Real.pi_pos.le hab_pos.le
  have hθ : ∀ i : Fin F.n,
      Real.pi * F.φ i ∈ Set.Icc (Real.pi * a)
        (Real.pi * a + Real.pi * (b - a)) := by
    intro i; simp only [Set.mem_Icc]
    exact ⟨mul_le_mul_of_nonneg_left (hphases i).1.le Real.pi_pos.le,
      by nlinarith [(hphases i).2.le, Real.pi_pos]⟩
  -- Apply sector estimate
  have hsector :
      Real.cos (Real.pi * (b - a) / 2) *
        ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖ ≤
      ‖σ.Z (K₀.of C E)‖ := by
    calc Real.cos (Real.pi * (b - a) / 2) *
            ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖
        ≤ ‖∑ i : Fin F.n,
            ↑(‖σ.Z (K₀.of C (P.factor i))‖) *
              Complex.exp (↑(Real.pi * F.φ i) * Complex.I)‖ :=
          norm_sum_exp_ge_cos_mul_sum
            (fun i _ ↦ norm_nonneg _) hw0 hw (fun i _ ↦ hθ i)
      _ = ‖∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i))‖ := by
          congr 1; exact Finset.sum_congr rfl (fun i _ ↦ (hZi i).symm)
      _ = ‖σ.Z (K₀.of C E)‖ := by rw [← hZE]
  -- First factor is nonzero, so ‖Z(F₀)‖ > 0
  have hfactor_pos :
      0 < ‖σ.Z (K₀.of C (P.factor ⟨0, hn⟩))‖ := by
    obtain ⟨m, hm, hmZ⟩ :=
      stabilityCondition_compat_apply (C := C) σ _ _ (F.semistable ⟨0, hn⟩) hfirst
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hm
  have hcos_pos : 0 < Real.cos (Real.pi * (b - a) / 2) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hsum_pos : 0 < ∑ i : Fin F.n,
      ‖σ.Z (K₀.of C (P.factor i))‖ := by
    apply lt_of_lt_of_le hfactor_pos
    exact Finset.single_le_sum
      (f := fun i ↦ ‖σ.Z (K₀.of C (P.factor i))‖)
      (fun i _ ↦ norm_nonneg _)
      (Finset.mem_univ (⟨0, hn⟩ : Fin F.n))
  exact lt_of_lt_of_le (mul_pos hcos_pos hsum_pos) hsector

/-- **W-nonvanishing for interval objects**. If `‖W - Z‖_σ < cos(π(b-a)/2)` and `E` is
a nonzero object in `P((a, b))` with `b - a < 1`, then `W([E]) ≠ 0`. The proof combines
the Z-nonvanishing bound with the sector bound on `W - Z`. -/
theorem StabilityCondition.W_ne_zero_of_intervalProp (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) {a b : ℝ} (hab : b - a < 1)
    (hsmall : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * (b - a) / 2)))
    {E : C} (hE : ¬IsZero E) (hI : σ.slicing.intervalProp C a b E) :
    W (K₀.of C E) ≠ 0 := by
  -- Derive a < b
  have hab_pos : 0 < b - a := by
    rcases hI with hZ | ⟨F, hF⟩
    · exact absurd hZ hE
    · have hn : 0 < F.n := by
        by_contra h; exact hE (F.toPostnikovTower.zero_isZero (by lia))
      linarith [(hF ⟨0, hn⟩).1, (hF ⟨0, hn⟩).2]
  have hcos_pos : 0 < Real.cos (Real.pi * (b - a) / 2) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hfin : stabSeminorm C σ (W - σ.Z) ≠ ⊤ := ne_top_of_lt hsmall
  set M := (stabSeminorm C σ (W - σ.Z)).toReal
  have hM_lt : M < Real.cos (Real.pi * (b - a) / 2) := by
    rw [show Real.cos _ = (ENNReal.ofReal (Real.cos _)).toReal from
      (ENNReal.toReal_ofReal hcos_pos.le).symm]
    exact (ENNReal.toReal_lt_toReal hfin
      ENNReal.ofReal_ne_top).mpr hsmall
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  -- Z(E) ≠ 0
  have hZ_pos := σ.norm_Z_pos_of_intervalProp C hE hab hI
  -- ‖(W-Z)(E)‖ ≤ M / cos(π(b-a)/2) · ‖Z(E)‖ via sector bound
  have hwidth : σ.slicing.phiPlus C E hE -
      σ.slicing.phiMinus C E hE ≤ b - a := by
    have hP := σ.slicing.phiPlus_lt_of_intervalProp C hE hI
    have hM := σ.slicing.phiMinus_gt_of_intervalProp C hE hI
    linarith
  have hWZ_bound : ‖(W - σ.Z) (K₀.of C E)‖ ≤
      M / Real.cos (Real.pi * (b - a) / 2) *
        ‖σ.Z (K₀.of C E)‖ :=
    sector_bound' C σ (W - σ.Z) hE hab_pos.le
      hab hwidth hM0
      (fun A φ hP hA ↦ stabSeminorm_bound_real C σ _ hfin hP hA)
  -- M / cos < 1, so ‖(W-Z)(E)‖ < ‖Z(E)‖
  have hrat : M / Real.cos (Real.pi * (b - a) / 2) < 1 :=
    (div_lt_one hcos_pos).mpr hM_lt
  -- If W(E) = 0, then ‖(W-Z)(E)‖ = ‖Z(E)‖, contradicting the bound
  intro hw0
  have hWZ : (W - σ.Z) (K₀.of C E) =
      W (K₀.of C E) - σ.Z (K₀.of C E) :=
    AddMonoidHom.sub_apply W σ.Z (K₀.of C E)
  rw [hWZ, hw0, zero_sub, norm_neg] at hWZ_bound
  nlinarith

section

omit [IsTriangulated C]

/-! ### W-phase definition -/

/-- The **W-phase** of a complex number `w ≠ 0` relative to a skewing parameter `α`.
Defined as `α + arg(w · exp(-iπα)) / π`, which gives ψ ∈ (α - 1, α + 1] satisfying
`w = ‖w‖ · exp(iπψ)`. -/
noncomputable def wPhaseOf (w : ℂ) (α : ℝ) : ℝ :=
  α + Complex.arg (w * Complex.exp (-(↑(Real.pi * α) * Complex.I))) /
    Real.pi

/-- The W-phase lies in `(α - 1, α + 1]`. -/
theorem wPhaseOf_mem_Ioc (w : ℂ) (α : ℝ) :
    wPhaseOf w α ∈ Set.Ioc (α - 1) (α + 1) := by
  have hπ := Real.pi_pos
  set z := w * Complex.exp (-(↑(Real.pi * α) * Complex.I))
  refine ⟨?_, ?_⟩
  · -- α - 1 < α + arg(z)/π
    suffices -1 < Complex.arg z / Real.pi by
      change α - 1 < α + Complex.arg z / Real.pi; linarith
    rw [lt_div_iff₀ hπ]
    linarith [Complex.neg_pi_lt_arg z]
  · -- α + arg(z)/π ≤ α + 1
    suffices Complex.arg z / Real.pi ≤ 1 by
      change α + Complex.arg z / Real.pi ≤ α + 1; linarith
    rw [div_le_iff₀ hπ, one_mul]
    exact Complex.arg_le_pi z

/-- **Polar compatibility**. A nonzero complex number `w` equals
`‖w‖ * exp(iπ · wPhaseOf w α)`. -/
theorem wPhaseOf_compat (w : ℂ) (α : ℝ) :
    w = ↑‖w‖ * Complex.exp (↑(Real.pi * wPhaseOf w α) * Complex.I) := by
  set z := w * Complex.exp (-(↑(Real.pi * α) * Complex.I)) with hz_def
  -- Step 1: w = z * exp(iπα)
  have hw_eq : w = z * Complex.exp (↑(Real.pi * α) * Complex.I) := by
    rw [hz_def, mul_assoc, ← Complex.exp_add]
    simp [neg_add_cancel]
  -- Step 2: polar decomposition of z
  have polar := Complex.norm_mul_exp_arg_mul_I z
  -- Step 3: ‖z‖ = ‖w‖
  have hnorm : (‖z‖ : ℝ) = ‖w‖ := by
    rw [hz_def, norm_mul]
    have : -(↑(Real.pi * α) * Complex.I) =
        ↑(-(Real.pi * α)) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
  -- Step 4: arg z + πα = π * wPhaseOf w α
  have hphase : ↑(Complex.arg z) * Complex.I +
      ↑(Real.pi * α) * Complex.I =
      ↑(Real.pi * wPhaseOf w α) * Complex.I := by
    have h : Complex.arg z + Real.pi * α = Real.pi * wPhaseOf w α := by
      change z.arg + Real.pi * α = Real.pi * (α + z.arg / Real.pi)
      field_simp; ring
    rw [← h]; push_cast; ring
  calc w = z * Complex.exp (↑(Real.pi * α) * Complex.I) := hw_eq
    _ = ↑‖z‖ * Complex.exp (↑(Complex.arg z) * Complex.I) *
          Complex.exp (↑(Real.pi * α) * Complex.I) := by
        rw [polar]
    _ = ↑‖z‖ * (Complex.exp (↑(Complex.arg z) * Complex.I) *
          Complex.exp (↑(Real.pi * α) * Complex.I)) := by
        rw [mul_assoc]
    _ = ↑‖z‖ * Complex.exp (↑(Real.pi * wPhaseOf w α) *
          Complex.I) := by
        rw [← Complex.exp_add, hphase]
    _ = ↑‖w‖ * Complex.exp (↑(Real.pi * wPhaseOf w α) *
          Complex.I) := by
        rw [hnorm]

/-- The W-phase of `m * exp(iπφ)` with `m > 0` and `φ ∈ (α - 1, α + 1]` equals `φ`. -/
theorem wPhaseOf_of_exp {m φ α : ℝ} (hm : 0 < m)
    (hφ : φ ∈ Set.Ioc (α - 1) (α + 1)) :
    wPhaseOf (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)) α = φ := by
  unfold wPhaseOf
  suffices h : Complex.arg (↑m * Complex.exp (↑(Real.pi * φ) *
      Complex.I) * Complex.exp (-(↑(Real.pi * α) * Complex.I))) =
      Real.pi * (φ - α) by
    rw [h]; field_simp; ring
  -- Simplify: m * exp(iπφ) * exp(-iπα) = m * exp(iπ(φ-α))
  have hexp : ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) *
      Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
      ↑m * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 1; push_cast; ring_nf
  rw [hexp, Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I,
    toIocMod_eq_self]
  exact ⟨by nlinarith [Real.pi_pos, hφ.1], by nlinarith [Real.pi_pos, hφ.2]⟩

/-- **W-phase of zero.** `wPhaseOf(0, α) = α` since `arg(0) = 0`. -/
@[simp]
theorem wPhaseOf_zero (α : ℝ) : wPhaseOf 0 α = α := by
  simp [wPhaseOf, Complex.arg_zero]

/-- **Negation shifts W-phase by 1.** For nonzero `w`, `wPhaseOf(-w, α+1) = wPhaseOf(w, α) + 1`.
Since `exp(iπ) = -1`, negating `w` shifts the argument by π, hence the phase by 1. -/
theorem wPhaseOf_neg {w : ℂ} (hw : w ≠ 0) (α : ℝ) :
    wPhaseOf (-w) (α + 1) = wPhaseOf w α + 1 := by
  set φ := wPhaseOf w α
  have hm : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hpolar := wPhaseOf_compat w α
  -- -w = ‖w‖ · exp(iπ(φ + 1)) since exp(iπ) = -1
  -- Use wPhaseOf_of_exp on -w = ‖w‖ · exp(iπ(φ+1))
  -- φ + 1 ∈ ((α+1) - 1, (α+1) + 1] = (α, α + 2]
  have hmem : φ + 1 ∈ Set.Ioc ((α + 1) - 1) ((α + 1) + 1) := by
    have := wPhaseOf_mem_Ioc w α
    constructor <;> linarith [this.1, this.2]
  -- wPhaseOf(-w, α+1) = wPhaseOf(‖w‖ · exp(iπ(φ+1)), α+1) = φ+1
  -- First establish: -w = ‖w‖ · exp(iπ(φ+1))
  suffices hneg : -w = ↑‖w‖ * Complex.exp (↑(Real.pi * (φ + 1)) * Complex.I) by
    calc wPhaseOf (-w) (α + 1)
        = wPhaseOf (↑‖w‖ * Complex.exp (↑(Real.pi * (φ + 1)) * Complex.I))
            (α + 1) := by rw [← hneg]
      _ = φ + 1 := wPhaseOf_of_exp hm hmem
  -- Prove -w = ‖w‖ · exp(iπ(φ+1))
  calc -w = -(↑‖w‖ * Complex.exp (↑(Real.pi * φ) * Complex.I)) := by
        rw [← hpolar]
    _ = ↑‖w‖ * (-Complex.exp (↑(Real.pi * φ) * Complex.I)) := by ring
    _ = ↑‖w‖ * (Complex.exp (↑Real.pi * Complex.I) *
          Complex.exp (↑(Real.pi * φ) * Complex.I)) := by
        rw [Complex.exp_pi_mul_I]; ring
    _ = ↑‖w‖ * Complex.exp (↑Real.pi * Complex.I +
          ↑(Real.pi * φ) * Complex.I) := by
        rw [Complex.exp_add]
    _ = ↑‖w‖ * Complex.exp (↑(Real.pi * (φ + 1)) * Complex.I) := by
        congr 1; congr 1; push_cast; ring

/-- **Shifting α by 2 shifts wPhaseOf by 2.** For nonzero `w`,
`wPhaseOf w (α + 2) = wPhaseOf w α + 2`. Derived by applying `wPhaseOf_neg` twice. -/
theorem wPhaseOf_add_two {w : ℂ} (hw : w ≠ 0) (α : ℝ) :
    wPhaseOf w (α + 2) = wPhaseOf w α + 2 := by
  have h1 := wPhaseOf_neg hw α
  have h2 := wPhaseOf_neg (neg_ne_zero.mpr hw) (α + 1)
  rw [neg_neg, show (α + 1 : ℝ) + 1 = α + 2 from by ring] at h2
  linarith

/-! ### W-semistability in interval categories -/

/-- **W-semistability**. An object `E` in `P((a, b))` is *W-semistable* of W-phase `ψ` if:
1. `E` is in the interval `P((a, b))` and is nonzero,
2. `W([E]) ≠ 0` (so the W-phase is well-defined),
3. The W-phase of `E` equals `ψ`,
4. For every distinguished triangle `K → E → Q → K[1]` with both `K, Q ∈ P((a, b))`
   and `K` nonzero, the W-phase of `K` is at most `ψ`.

A "strict subobject" of `E` in `P((a,b))` corresponds to a monomorphism in the abelian
heart `P((a, a+1])` whose cokernel also lies in `P((a, b))`, which in turn gives a
distinguished triangle with all vertices in the interval. -/
structure SkewedStabilityFunction.Semistable {s : Slicing C} {a b : ℝ}
    (ssf : SkewedStabilityFunction C s a b) (E : C) (ψ : ℝ) : Prop where
  intervalProp : s.intervalProp C a b E
  nonzero : ¬IsZero E
  wNe : ssf.W (K₀.of C E) ≠ 0
  phase_eq : wPhaseOf (ssf.W (K₀.of C E)) ssf.α = ψ
  le_of_distTriang : ∀ ⦃K Q : C⦄ ⦃f₁ : K ⟶ E⦄ ⦃f₂ : E ⟶ Q⦄ ⦃f₃ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
    Triangle.mk f₁ f₂ f₃ ∈ distTriang C →
    s.intervalProp C a b K → s.intervalProp C a b Q →
    ¬IsZero K →
    wPhaseOf (ssf.W (K₀.of C K)) ssf.α ≤ ψ

/-- **α-independence of wPhaseOf.** For a nonzero complex number `w`, if
`wPhaseOf w α₁ ∈ (α₂ - 1, α₂ + 1]`, then `wPhaseOf w α₁ = wPhaseOf w α₂`.
This shows the W-phase is intrinsic (independent of the skewing parameter),
provided the branch cuts are compatible. -/
theorem wPhaseOf_indep {w : ℂ} (hw : w ≠ 0) (α₁ α₂ : ℝ)
    (h : wPhaseOf w α₁ ∈ Set.Ioc (α₂ - 1) (α₂ + 1)) :
    wPhaseOf w α₁ = wPhaseOf w α₂ := by
  set φ := wPhaseOf w α₁
  have hw_polar := wPhaseOf_compat w α₁
  have hm : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have h1 : wPhaseOf (↑‖w‖ * Complex.exp (↑(Real.pi * φ) * Complex.I)) α₂ = φ :=
    wPhaseOf_of_exp hm h
  rw [← hw_polar] at h1; exact h1.symm

/-- The W-phase of a W-semistable object is in `(α - 1, α + 1]`. -/
lemma SkewedStabilityFunction.Semistable.phase_mem_Ioc
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b} {E : C} {ψ : ℝ}
    (h : ssf.Semistable C E ψ) :
    ψ ∈ Set.Ioc (ssf.α - 1) (ssf.α + 1) :=
  h.phase_eq ▸ wPhaseOf_mem_Ioc _ _

/-- The W-value of a W-semistable object satisfies the polar decomposition. -/
lemma SkewedStabilityFunction.Semistable.polar
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b} {E : C} {ψ : ℝ}
    (h : ssf.Semistable C E ψ) :
    ssf.W (K₀.of C E) = ↑‖ssf.W (K₀.of C E)‖ *
      Complex.exp (↑(Real.pi * ψ) * Complex.I) :=
  h.phase_eq ▸ wPhaseOf_compat _ _

end

end CategoryTheory.Triangulated
