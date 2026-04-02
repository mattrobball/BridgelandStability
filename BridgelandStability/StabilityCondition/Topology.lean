/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.Seminorm
public import BridgelandStability.StabilityCondition.Basic

/-!
# Topology on Stab(D)

Lemma 6.4 (local injectivity) and supporting topology lemmas.
The basis neighborhoods, the topology instance, connected-component types,
and the Theorem 1.2 statement are in `StabilityCondition.Defs`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ZeroObject ENNReal Topology

universe v u u'

namespace CategoryTheory.Triangulated
open PreStabilityCondition.WithClassMap (charge_congr charge_def)

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-! ### Central charge imaginary part helper -/

/-- For a σ-semistable nonzero object of phase `ψ`, the imaginary part of
`Z(F) · exp(-iπφ)` equals `b · sin(π(ψ - φ))` for some `b > 0`. This factors
out the repeated "divide by exp, rewrite to sin" computation in the Lemma 6.4 proofs. -/
theorem im_divided_of_semistable (σ : StabilityCondition.WithClassMap C v) {F : C} {ψ φ : ℝ}
    (hne : ¬IsZero F) (hss : (σ.slicing.P ψ) F) :
    ∃ b : ℝ, 0 < b ∧
      (σ.charge F * exp (-(↑(Real.pi * φ) * I))).im =
        b * Real.sin (Real.pi * (ψ - φ)) := by
  obtain ⟨b, hb, hbZ⟩ := σ.compat ψ F hss hne
  exact ⟨b, hb, by rw [hbZ, im_ofReal_mul_exp_mul_exp_neg]⟩

/-! ### Lemma 6.4: Local injectivity -/

/-- **One-sided phase impossibility for Lemma 6.4** (below). If `σ` and `τ` have the same
central charge, `E` is nonzero and `τ`-semistable of phase `φ`, and all nonzero factors
in a `σ`-HN filtration of `E` have phase strictly below `φ` (and above `φ - 1`), then
we reach a contradiction.

The proof decomposes `Z(E) = Σ Z(Fᵢ)` via K₀ additivity, divides by `exp(iπφ)`,
and shows the imaginary part is both zero (since `Z(E) = m · exp(iπφ)` is on a ray)
and strictly negative (since each nonzero factor contributes a negative `sin` term). -/
theorem StabilityCondition.WithClassMap.false_of_all_hn_phases_below
    (σ τ : StabilityCondition.WithClassMap C v)
    (hZ : σ.Z = τ.Z) {E : C} {φ : ℝ} (hE : ¬IsZero E)
    (hτ : (τ.slicing.P φ) E)
    (F : HNFiltration C σ.slicing.P E)
    (hlt : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) → F.φ i < φ)
    (hgt : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) →
      φ - 1 < F.φ i) : False := by
  -- Get the central charge ray from τ-semistability
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hτ hE
  rw [(charge_congr hZ E).symm] at hmZ
  -- K₀ additivity: Z(E) = Σ Z(factor i)
  have hK₀ := σ.charge_postnikovTower_eq_sum F.toPostnikovTower
  -- Define the divided term: w i = Z(factor i) * exp(-iπφ)
  set w : Fin F.n → ℂ := fun i ↦
    σ.charge (F.toPostnikovTower.factor i) * exp (-(↑(Real.pi * φ) * I))
  -- Sum of divided terms equals m (real)
  have hsum : (m : ℂ) = ∑ i : Fin F.n, w i := by
    have h1 : σ.charge E * exp (-(↑(Real.pi * φ) * I)) =
        ∑ i : Fin F.n, w i := by
      rw [hK₀, Finset.sum_mul]
    rwa [hmZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * φ) * I + -(↑(Real.pi * φ) * I) = 0 from by ring,
      exp_zero, mul_one] at h1
  -- For nonzero factor i: w i has strictly negative imaginary part
  have hw_neg : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) →
      (w i).im < 0 := by
    intro i hi
    obtain ⟨b, hb, hbim⟩ := im_divided_of_semistable C σ hi (F.semistable i)
    change (σ.charge _ * exp (-(↑(Real.pi * φ) * I))).im < 0
    rw [hbim]; exact mul_neg_of_pos_of_neg hb
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [hlt i hi, Real.pi_pos])
        (by nlinarith [hgt i hi, Real.pi_pos]))
  -- For zero factor i: w i = 0
  have hw_zero : ∀ i : Fin F.n, IsZero (F.toPostnikovTower.factor i) →
      w i = 0 := by
    intro i hi; show σ.charge _ * _ = 0
    simp [σ.charge_isZero hi]
  -- At least one nonzero factor exists (otherwise Z(E) = 0, contradicting m > 0)
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) := by
    by_contra hall; push Not at hall
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
    simpa only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] using
      map_sum Complex.imAddGroupHom w Finset.univ
  have him_zero : (∑ i : Fin F.n, w i).im = 0 := by
    rw [← hsum]; exact Complex.ofReal_im m
  linarith

/-- **One-sided phase impossibility for Lemma 6.4** (above). Symmetric version of
`false_of_all_hn_phases_below`: if all nonzero factors have phase strictly above `φ`
(and below `φ + 1`), we also reach a contradiction. -/
theorem StabilityCondition.WithClassMap.false_of_all_hn_phases_above
    (σ τ : StabilityCondition.WithClassMap C v)
    (hZ : σ.Z = τ.Z) {E : C} {φ : ℝ} (hE : ¬IsZero E)
    (hτ : (τ.slicing.P φ) E)
    (F : HNFiltration C σ.slicing.P E)
    (hgt : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) → φ < F.φ i)
    (hlt : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) →
      F.φ i < φ + 1) : False := by
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hτ hE
  rw [(charge_congr hZ E).symm] at hmZ
  have hK₀ := σ.charge_postnikovTower_eq_sum F.toPostnikovTower
  set w : Fin F.n → ℂ := fun i ↦
    σ.charge (F.toPostnikovTower.factor i) * exp (-(↑(Real.pi * φ) * I))
  have hsum : (m : ℂ) = ∑ i : Fin F.n, w i := by
    have h1 : σ.charge E * exp (-(↑(Real.pi * φ) * I)) =
        ∑ i : Fin F.n, w i := by
      rw [hK₀, Finset.sum_mul]
    rwa [hmZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * φ) * I + -(↑(Real.pi * φ) * I) = 0 from by ring,
      exp_zero, mul_one] at h1
  -- For nonzero factor i: w i has strictly positive imaginary part
  have hw_pos : ∀ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) →
      0 < (w i).im := by
    intro i hi
    obtain ⟨b, hb, hbim⟩ := im_divided_of_semistable C σ hi (F.semistable i)
    change 0 < (σ.charge _ * exp (-(↑(Real.pi * φ) * I))).im
    rw [hbim]; exact mul_pos hb
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [hgt i hi, Real.pi_pos])
        (by nlinarith [hlt i hi, Real.pi_pos]))
  have hw_zero : ∀ i : Fin F.n, IsZero (F.toPostnikovTower.factor i) →
      w i = 0 := by
    intro i hi; show σ.charge _ * _ = 0
    simp [σ.charge_isZero hi]
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) := by
    by_contra hall; push Not at hall
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
    simpa only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] using
      map_sum Complex.imAddGroupHom w Finset.univ
  have him_zero : (∑ i : Fin F.n, w i).im = 0 := by
    rw [← hsum]; exact Complex.ofReal_im m
  linarith

/-- **Lemma 6.4 for P-semistable objects**. If `σ` and `τ` have the same central charge,
`d(P, Q) < 1`, `E` is nonzero and `τ`-semistable of phase `φ`, and `E` is also
`σ`-semistable of some phase `c`, then `c = φ` and `E` is `σ`-semistable of phase `φ`.

This handles the case of Lemma 6.4 where `E` has a trivial `σ`-HN filtration (single
factor), combining the metric phase bound with `phase_eq_of_same_Z`. -/
theorem StabilityCondition.WithClassMap.P_of_Q_of_P_semistable
    (σ τ : StabilityCondition.WithClassMap C v) (hZ : σ.Z = τ.Z)
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
The proof applies `false_of_all_hn_phases_below` / `false_of_all_hn_phases_above` to
the canonical HN filtration from `exists_both_nonzero`. -/
theorem StabilityCondition.WithClassMap.phiMinus_le_le_phiPlus
    (σ τ : StabilityCondition.WithClassMap C v) (hZ : σ.Z = τ.Z)
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
  have hM_gt : φ - 1 < F.φ ⟨F.n - 1, by lia⟩ := by linarith [(Set.mem_Ioo.mp hbds.2).1]
  -- All phases of F lie in [F.φ(n-1), F.φ(0)] by antitonicity
  have hFle : ∀ i : Fin F.n, F.φ ⟨F.n - 1, by lia⟩ ≤ F.φ i :=
    fun i ↦ F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
  have hFge : ∀ i : Fin F.n, F.φ i ≤ F.φ ⟨0, hn⟩ :=
    fun i ↦ F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
  constructor
  · -- phiMinus ≤ φ: if not, all phases > φ, contradicting false_of_all_hn_phases_above
    rw [hpM]
    by_contra h; push Not at h
    exact σ.false_of_all_hn_phases_above C τ hZ hE hτ F
      (fun i _ ↦ lt_of_lt_of_le h (hFle i))
      (fun i _ ↦ lt_of_le_of_lt (hFge i) hP_lt)
  · -- φ ≤ phiPlus: if not, all phases < φ, contradicting false_of_all_hn_phases_below
    rw [hpP]
    by_contra h; push Not at h
    exact σ.false_of_all_hn_phases_below C τ hZ hE hτ F
      (fun i _ ↦ lt_of_le_of_lt (hFge i) h)
      (fun i _ ↦ lt_of_lt_of_le hM_gt (hFle i))

/-- **Cross-slicing imaginary part contradiction**. If `σ.Z = τ.Z`, `X` is nonzero,
all `σ`-HN phases of `X` are in `(φ, φ + 1)`, and all `τ`-HN phases are in `(φ - 1, φ]`,
then `False`.

The proof decomposes `Z(X)` via both `σ`- and `τ`-HN filtrations. From the `σ`-decomposition,
`Im(Z(X)/exp(iπφ)) > 0`. From the `τ`-decomposition, `Im(Z(X)/exp(iπφ)) ≤ 0`. -/
theorem StabilityCondition.WithClassMap.false_of_gt_and_le_phases
    (σ τ : StabilityCondition.WithClassMap C v)
    (hZ : σ.Z = τ.Z) {X : C} {φ : ℝ} (hX : ¬IsZero X)
    (Fσ : HNFiltration C σ.slicing.P X)
    (hσgt : ∀ i : Fin Fσ.n, φ < Fσ.φ i)
    (hσlt : ∀ i : Fin Fσ.n, Fσ.φ i < φ + 1)
    (Fτ : HNFiltration C τ.slicing.P X)
    (hτle : ∀ i : Fin Fτ.n, Fτ.φ i ≤ φ)
    (hτgt : ∀ i : Fin Fτ.n, φ - 1 < Fτ.φ i) : False := by
  -- σ-decomposition: Im(Z(X)/exp(iπφ)) > 0
  have hK₀σ := σ.charge_postnikovTower_eq_sum Fσ.toPostnikovTower
  set wσ : Fin Fσ.n → ℂ := fun i ↦
    σ.charge (Fσ.toPostnikovTower.factor i) * exp (-(↑(Real.pi * φ) * I))
  have hσ_pos : ∀ i : Fin Fσ.n, ¬IsZero (Fσ.toPostnikovTower.factor i) →
      0 < (wσ i).im := by
    intro i hi
    obtain ⟨b, hb, hbim⟩ := im_divided_of_semistable C σ hi (Fσ.semistable i)
    change 0 < (σ.charge _ * exp (-(↑(Real.pi * φ) * I))).im
    rw [hbim]; exact mul_pos hb
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [hσgt i, Real.pi_pos])
        (by nlinarith [hσlt i, Real.pi_pos]))
  have hσ_zero : ∀ i : Fin Fσ.n, IsZero (Fσ.toPostnikovTower.factor i) →
      wσ i = 0 := by
    intro i hi; show σ.charge _ * _ = 0
    simp [σ.charge_isZero hi]
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin Fσ.n, ¬IsZero (Fσ.toPostnikovTower.factor i) := by
    by_contra hall; push Not at hall
    -- All factors are zero → each chain object is zero by induction → E is zero
    apply hX
    have hbase : IsZero (Fσ.toPostnikovTower.chain.left) :=
      Fσ.toPostnikovTower.base_isZero
    have hall_chain : ∀ (k : ℕ) (hk : k ≤ Fσ.n),
        IsZero (Fσ.toPostnikovTower.chain.obj' k (by lia)) := by
      intro k hk
      induction k with
      | zero =>
        change IsZero (Fσ.toPostnikovTower.chain.left)
        exact hbase
      | succ k ih =>
        have hklt : k < Fσ.n := by lia
        have ih' := ih (by lia)
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
      simpa only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] using
        map_sum Complex.imAddGroupHom wσ Finset.univ
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
  have hK₀τ := τ.charge_postnikovTower_eq_sum Fτ.toPostnikovTower
  set wτ : Fin Fτ.n → ℂ := fun i ↦
    τ.charge (Fτ.toPostnikovTower.factor i) * exp (-(↑(Real.pi * φ) * I))
  have hτ_le : ∀ i : Fin Fτ.n, (wτ i).im ≤ 0 := by
    intro i
    by_cases hi : IsZero (Fτ.toPostnikovTower.factor i)
    · show (τ.charge _ * _).im ≤ 0
      simp [τ.charge_isZero hi]
    · obtain ⟨b, hb, hbim⟩ := im_divided_of_semistable C τ hi (Fτ.semistable i)
      change (τ.charge _ * exp (-(↑(Real.pi * φ) * I))).im ≤ 0
      rw [hbim]; exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (by nlinarith [hτle i, Real.pi_pos])
          (by nlinarith [hτgt i, Real.pi_pos]))
  have him_τ_le : (∑ i : Fin Fτ.n, wτ i).im ≤ 0 := by
    have him_eq : (∑ i : Fin Fτ.n, wτ i).im = ∑ i : Fin Fτ.n, (wτ i).im := by
      simpa only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] using
        map_sum Complex.imAddGroupHom wτ Finset.univ
    rw [him_eq]
    exact Finset.sum_nonpos (fun i _ ↦ hτ_le i)
  -- Both sums equal Z(X) * exp(-iπφ), so their imaginary parts are equal
  have hσ_sum : σ.charge X * exp (-(↑(Real.pi * φ) * I)) =
      ∑ i : Fin Fσ.n, wσ i := by rw [hK₀σ, Finset.sum_mul]
  have hτ_sum : τ.charge X * exp (-(↑(Real.pi * φ) * I)) =
      ∑ i : Fin Fτ.n, wτ i := by rw [hK₀τ, Finset.sum_mul]
  have : (∑ i : Fin Fσ.n, wσ i).im = (∑ i : Fin Fτ.n, wτ i).im := by
    rw [← hσ_sum, ← hτ_sum, charge_congr hZ]
  linarith

/-- **One-sided phase impossibility** (below with equality). If `σ` and `τ` have the same
central charge, `E` is `τ`-semistable at `φ`, and all `σ`-HN phases are `≤ φ` with at
least one strictly below, then `False`. This extends `false_of_all_hn_phases_below`
to allow some phases equal to `φ`. -/
theorem StabilityCondition.WithClassMap.false_of_hn_phases_le_with_lt
    (σ τ : StabilityCondition.WithClassMap C v)
    (hZ : σ.Z = τ.Z) {E : C} {φ : ℝ} (hE : ¬IsZero E)
    (hτ : (τ.slicing.P φ) E)
    (F : HNFiltration C σ.slicing.P E)
    (hle : ∀ i : Fin F.n, F.φ i ≤ φ)
    (hgt : ∀ i : Fin F.n, φ - 1 < F.φ i)
    (hstrict : ∃ i : Fin F.n, ¬IsZero (F.toPostnikovTower.factor i) ∧ F.φ i < φ) :
    False := by
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hτ hE
  rw [(charge_congr hZ E).symm] at hmZ
  have hK₀ := σ.charge_postnikovTower_eq_sum F.toPostnikovTower
  set w : Fin F.n → ℂ := fun i ↦
    σ.charge (F.toPostnikovTower.factor i) * exp (-(↑(Real.pi * φ) * I))
  have hsum : (m : ℂ) = ∑ i : Fin F.n, w i := by
    have h1 : σ.charge E * exp (-(↑(Real.pi * φ) * I)) =
        ∑ i : Fin F.n, w i := by rw [hK₀, Finset.sum_mul]
    rwa [hmZ, mul_assoc, ← exp_add,
      show ↑(Real.pi * φ) * I + -(↑(Real.pi * φ) * I) = 0 from by ring,
      exp_zero, mul_one] at h1
  -- Each term has Im ≤ 0
  have hw_le : ∀ i : Fin F.n, (w i).im ≤ 0 := by
    intro i
    by_cases hi : IsZero (F.toPostnikovTower.factor i)
    · show (σ.charge _ * _).im ≤ 0
      simp [σ.charge_isZero hi]
    · obtain ⟨b, hb, hbim⟩ := im_divided_of_semistable C σ hi (F.semistable i)
      change (σ.charge _ * exp (-(↑(Real.pi * φ) * I))).im ≤ 0
      rw [hbim]; exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (by nlinarith [hle i, Real.pi_pos])
          (by nlinarith [hgt i, Real.pi_pos]))
  -- At least one term has Im < 0
  obtain ⟨j₀, hj₀ne, hj₀lt⟩ := hstrict
  have hw_neg : (w j₀).im < 0 := by
    obtain ⟨b, hb, hbim⟩ := im_divided_of_semistable C σ hj₀ne (F.semistable j₀)
    change (σ.charge _ * exp (-(↑(Real.pi * φ) * I))).im < 0
    rw [hbim]; exact mul_neg_of_pos_of_neg hb
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [hj₀lt, Real.pi_pos])
        (by nlinarith [hgt j₀, Real.pi_pos]))
  have him_neg : (∑ i : Fin F.n, w i).im < 0 := by
    have him_eq : (∑ i : Fin F.n, w i).im = ∑ i : Fin F.n, (w i).im := by
      simpa only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] using
        map_sum Complex.imAddGroupHom w Finset.univ
    rw [him_eq]
    calc ∑ i : Fin F.n, (w i).im
        < ∑ i : Fin F.n, (0 : ℝ) :=
          Finset.sum_lt_sum (fun i _ ↦ hw_le i)
            ⟨j₀, Finset.mem_univ _, hw_neg⟩
      _ = 0 := Finset.sum_const_zero
  have him_zero : (∑ i : Fin F.n, w i).im = 0 := by
    rw [← hsum]; exact Complex.ofReal_im m
  linarith

section

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

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

end

/-- **Auxiliary for Lemma 6.4**: one direction of the biconditional. If `E ∈ Q(φ)` then
`E ∈ P(φ)`, using the cross-slicing imaginary part argument and hom-vanishing. -/
private theorem bridgeland_6_4_one_dir
    (σ τ : StabilityCondition.WithClassMap C v) (hZ : σ.Z = τ.Z)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal 1)
    (φ : ℝ) (E : C) (hτ : (τ.slicing.P φ) E) : (σ.slicing.P φ) E := by
  by_cases hE : IsZero E
  · exact σ.slicing.zero_mem' C φ E hE
  -- Step 1: Get σ-HN of E with phases in (φ-1, φ+1)
  have hbds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hτ hd
  obtain ⟨F, hn, hF0, hFn⟩ := σ.slicing.exists_HN_intrinsic_width C hE
  have hPlt : F.φ ⟨0, hn⟩ < φ + 1 := by linarith [(Set.mem_Ioo.mp hbds.1).2]
  have hMgt : φ - 1 < F.φ ⟨F.n - 1, by lia⟩ := by linarith [(Set.mem_Ioo.mp hbds.2).1]
  have hF_interval : ∀ i : Fin F.n, φ - 1 < F.φ i ∧ F.φ i < φ + 1 := by
    intro i; exact ⟨by calc φ - 1 < F.φ ⟨F.n - 1, by lia⟩ := hMgt
      _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ < φ + 1 := hPlt⟩
  -- If all phases = φ, done
  by_cases hall_eq : ∀ i : Fin F.n, F.φ i = φ
  · exact σ.slicing.semistable_of_HN_all_eq C F hall_eq
  push Not at hall_eq
  -- Step 2: Split E at cutoff φ using exists_triangle_gtProp_leProp on the
  -- phase-shifted slicing
  let Fs := F.phaseShift (C := C) φ
  obtain ⟨X, Y, hXgt0, hYle0, f, g, h, hT, hXdata⟩ :=
    Slicing.exists_triangle_gtProp_leProp C (σ.slicing.phaseShift C φ) E Fs
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
          semistable := fun i => GX'.semistable i }
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
        _ = FY.φ ⟨FY.n - 1, by lia⟩ := hFYn.symm
        _ ≤ FY.φ i := FY.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    -- If all phases = φ, done. If some < φ, contradiction
    by_cases hall_eq_Y : ∀ i : Fin FY.n, FY.φ i = φ
    · exact σ.slicing.semistable_of_HN_all_eq C FY hall_eq_Y
    push Not at hall_eq_Y
    obtain ⟨j, hj_ne⟩ := hall_eq_Y
    have hj_lt : FY.φ j < φ := lt_of_le_of_ne (hFY_le j) hj_ne
    -- Factor j might be zero. Find a nonzero factor with phase < φ
    -- Since phiMinus ≤ φ (as all ≤ φ) and some phase < φ, phiMinus < φ
    -- The canonical filtration has nonzero last factor at phase = phiMinus < φ
    obtain ⟨FY', hnY', hfirst', hlast'⟩ := HNFiltration.exists_both_nonzero C σ.slicing hYZ
    have hm_eq := σ.slicing.phiMinus_eq C Y hYZ FY' hnY' hlast'
    -- FY' has the same phiMinus as FY
    have hFY'_last_lt : FY'.φ ⟨FY'.n - 1, by lia⟩ ≤ φ := by
      have : σ.slicing.phiMinus C Y hYZ ≤ φ := by
        rw [← hFYn]; exact hFY_le ⟨FY.n - 1, by lia⟩
      linarith [hm_eq]
    exfalso
    exact σ.false_of_hn_phases_le_with_lt C τ hZ hYZ hτY FY'
      (fun i ↦ by calc FY'.φ i ≤ FY'.φ ⟨0, hnY'⟩ :=
          FY'.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C Y hYZ :=
          (σ.slicing.phiPlus_eq C Y hYZ FY' hnY' hfirst').symm
        _ ≤ φ := phiPlus_le_of_leProp C σ.slicing hYZ hYle)
      (fun i ↦ by calc φ - 1 < σ.slicing.phiMinus C Y hYZ := hYσM
        _ = FY'.φ ⟨FY'.n - 1, by lia⟩ := hm_eq
        _ ≤ FY'.φ i := FY'.hφ.antitone (Fin.mk_le_mk.mpr (by lia)))
      ⟨⟨FY'.n - 1, by lia⟩, hlast', by
        calc FY'.φ ⟨FY'.n - 1, by lia⟩
            = σ.slicing.phiMinus C Y hYZ := hm_eq.symm
          _ = FY.φ ⟨FY.n - 1, by lia⟩ := hFYn.symm
          _ ≤ FY.φ j := FY.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
          _ < φ := hj_lt⟩
  -- Proof that X is zero: cross-slicing argument
  by_contra hXne
  have hXσM : φ < σ.slicing.phiMinus C X hXne := gt_phases_of_gtProp C σ.slicing hXne hXgt
  have hXσP : σ.slicing.phiPlus C X hXne < φ + 1 := hXub hXne
  -- Get canonical τ-HN of X
  obtain ⟨GX, hnGX, hGXfirst, hGXlast⟩ := HNFiltration.exists_both_nonzero C τ.slicing hXne
  -- Show τ.phiPlus(X) ≤ φ
  have hτP_le : τ.slicing.phiPlus C X hXne ≤ φ := by
    by_contra hτP_gt; push Not at hτP_gt
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
        have hU_σ_M : ψ - 1 < FU.φ ⟨FU.n - 1, by lia⟩ := by
          rw [← σ.slicing.phiMinus_eq C U hGXfirst FU hnFU hFUlast]
          exact (Set.mem_Ioo.mp hU_σ_bds.2).1
        -- σ-phases of Y⟦-1⟧: max ≤ φ - 1
        have hYs_le : σ.slicing.leProp C (φ - 1) (Y⟦(-1 : ℤ)⟧) := by
          simpa only [Int.cast_neg, Int.cast_one] using
            σ.slicing.leProp_shift C φ Y (-1) hYle
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
            _ < FU.φ ⟨FU.n - 1, by lia⟩ := hU_σ_M
            _ ≤ FU.φ i := FU.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
        exact σ.slicing.hom_eq_zero_of_phase_gap C FU FYs hgap β
    exact hGXfirst (GX.isZero_factor_zero_of_hom_eq_zero C τ.slicing hnGX hU_maps_zero)
  -- τ.phiMinus(X) > φ - 1 by metric bound
  have hτM_gt : φ - 1 < τ.slicing.phiMinus C X hXne := by
    have hM_bd := phiMinus_sub_lt_of_slicingDist C σ.slicing τ.slicing hXne hd
    rw [abs_lt] at hM_bd; linarith
  -- Get canonical σ-HN and τ-HN of X with all phase bounds
  obtain ⟨FX, hnFX, hFXfirst, hFXlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hXne
  exact σ.false_of_gt_and_le_phases C τ hZ hXne FX
    (fun i ↦ by calc φ < σ.slicing.phiMinus C X hXne := hXσM
      _ = FX.φ ⟨FX.n - 1, by lia⟩ :=
          σ.slicing.phiMinus_eq C X hXne FX hnFX hFXlast
      _ ≤ FX.φ i := FX.hφ.antitone (Fin.mk_le_mk.mpr (by lia)))
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
      _ = GX.φ ⟨GX.n - 1, by lia⟩ :=
          τ.slicing.phiMinus_eq C X hXne GX hnGX hGXlast
      _ ≤ GX.φ i := GX.hφ.antitone (Fin.mk_le_mk.mpr (by lia)))

section

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

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
   part argument (`false_of_gt_and_le_phases`) gives `X = 0`.
4. So `E ≅ Y` has all σ-phases `≤ φ`. The imaginary part argument then forces
   all phases `= φ`, making `E` σ-semistable at `φ`. -/
theorem bridgeland_lemma_6_4 (σ τ : StabilityCondition.WithClassMap C v) (hZ : σ.Z = τ.Z)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal 1)
    (φ : ℝ) (E : C) : (σ.slicing.P φ) E ↔ (τ.slicing.P φ) E := by
  constructor
  · intro hσ
    exact bridgeland_6_4_one_dir C τ σ hZ.symm
      (by rwa [slicingDist_symm]) φ E hσ
  · exact bridgeland_6_4_one_dir C σ τ hZ hd φ E

end

/-! ### Theorem 1.2 -/

end CategoryTheory.Triangulated
