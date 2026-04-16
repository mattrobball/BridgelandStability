/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.Basic
public meta import Informal
public import BridgelandStability.StabilityFunction.Uniqueness
public import BridgelandStability.IntervalCategory.FiniteLength
public import BridgelandStability.TStructure.HeartAbelian

/-!
# Deformation of Stability Conditions — PPhiAbelian

P(φ) closure, hom-vanishing, admissibility, P(φ) abelian (Lemma 5.2)
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u u'

namespace CategoryTheory.Triangulated
open PreStabilityCondition.WithClassMap (charge_def)

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-! ### P(φ) closure under K₀ decomposition in the heart

**Bridgeland Lemma 5.2** (each P(φ) is abelian). The key step is that P(φ) is closed
under subobjects and quotients in the heart P((φ-1, φ]). The proof uses the imaginary
part of the central charge: if Z(E) = Z(K) + Z(Q) with E ∈ P(φ), and K, Q have all
σ-phases in (φ-1, φ], then Im(Z(K) · exp(-iπφ)) ≤ 0 (each factor contributes
non-positive imaginary part after rotation), and the sum being zero forces all factors
to have phase exactly φ. -/

/-- **Im non-positivity for heart objects rotated by φ.** If each nonzero σ-semistable
factor of phase `ψ ∈ (a, b)` with `ψ ≤ φ` and `ψ > φ - 1` has non-positive
`Im(Z(F) · exp(-iπφ))`, and E ∈ P((a, b))` with phases ≤ φ and > φ-1, then
`Im(Z(E) · exp(-iπφ)) ≤ 0`. -/
theorem im_Z_nonpos_of_heart_phases
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ}
    {E : C} (hE : ¬IsZero E)
    (hle : σ.slicing.phiPlus C E hE ≤ φ)
    (hgt : φ - 1 < σ.slicing.phiMinus C E hE) :
    (σ.charge E *
      Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im ≤ 0 := by
  -- Get HN filtration with nonzero first and last factors
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  -- Phase bounds for all factors: φ - 1 < F.φ i ≤ φ
  have hphases : ∀ i : Fin F.n, φ - 1 < F.φ i ∧ F.φ i ≤ φ := fun i =>
    ⟨by calc φ - 1 < σ.slicing.phiMinus C E hE := hgt
          _ = F.φ ⟨F.n - 1, by lia⟩ :=
            σ.slicing.phiMinus_eq C E hE F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C E hE :=
            (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
          _ ≤ φ := hle⟩
  -- K₀ decomposition: Z(E) = Σ Z(factors)
  set P := F.toPostnikovTower
  rw [σ.charge_postnikovTower_eq_sum P]
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  rw [Finset.sum_mul, show (∑ i : Fin F.n, σ.charge (P.factor i) * rot).im =
      ∑ i : Fin F.n, (σ.charge (P.factor i) * rot).im from
    map_sum Complex.imAddGroupHom _ _]
  -- Each term ≤ 0
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : IsZero (P.factor i)
  · simp [σ.charge_isZero hi]
  · -- Nonzero factor: Z(factor) = m · exp(iπ · F.φ i) with m > 0
    obtain ⟨m, hm, hval⟩ :=
      σ.compat (F.φ i) (P.factor i) (F.semistable i) hi
    rw [hval, im_ofReal_mul_exp_mul_exp_neg]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, (hphases i).2])
        (by nlinarith [Real.pi_pos, (hphases i).1]))

/-- **From Im = 0 to P(φ).** If `X` is a nonzero object with all σ-phases in
`(φ-1, φ]` (i.e., in the heart) and `Im(Z(X) · exp(-iπφ)) = 0`, then `X ∈ P(φ)`.

The proof uses K₀ decomposition: each HN factor of `X` contributes
`≤ 0` to the sum (by `im_Z_nonpos_of_heart_phases`), and the sum is `0`, so each
contribution is `0`. For nonzero factors, `sin(π(ψ-φ)) = 0` with `ψ ∈ (φ-1, φ]`
forces `ψ = φ`. By strict anti of HN phases, `X` has exactly one factor. -/
theorem P_phi_of_im_zero_heart
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ}
    {X : C} (hXne : ¬IsZero X)
    (hX_le : σ.slicing.phiPlus C X hXne ≤ φ)
    (hX_gt : φ - 1 < σ.slicing.phiMinus C X hXne)
    (him_zero : (σ.charge X *
      Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im = 0) :
    σ.slicing.P φ X := by
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hXne
  -- All factor phases lie in (φ-1, φ]
  have hphases : ∀ i : Fin F.n, φ - 1 < F.φ i ∧ F.φ i ≤ φ := fun i =>
    ⟨by calc φ - 1 < σ.slicing.phiMinus C X hXne := hX_gt
          _ = F.φ ⟨F.n - 1, by lia⟩ :=
            σ.slicing.phiMinus_eq C X hXne F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C X hXne :=
            (σ.slicing.phiPlus_eq C X hXne F hn hfirst).symm
          _ ≤ φ := hX_le⟩
  -- K₀ decomposition: Z(X) = Σ Z(factor_i)
  have hZX := σ.charge_postnikovTower_eq_sum F.toPostnikovTower
  -- Each Im term ≤ 0
  have hterms : ∀ i ∈ Finset.univ,
      (σ.charge (F.toPostnikovTower.factor i) * rot).im ≤ 0 := by
    intro i _
    by_cases hi : IsZero (F.toPostnikovTower.factor i)
    · simp [σ.charge_isZero hi]
    · obtain ⟨mi, hmi, hvali⟩ :=
        σ.compat (F.φ i) _ (F.semistable i) hi
      rw [hvali, im_ofReal_mul_exp_mul_exp_neg]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hmi)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (by nlinarith [Real.pi_pos, (hphases i).2])
          (by nlinarith [Real.pi_pos, (hphases i).1]))
  -- Sum = 0
  have hsum : ∑ i ∈ Finset.univ,
      (σ.charge (F.toPostnikovTower.factor i) * rot).im = 0 := by
    have : (σ.charge X * rot).im =
        ∑ i : Fin F.n,
          (σ.charge (F.toPostnikovTower.factor i) * rot).im := by
      rw [hZX, Finset.sum_mul]
      exact map_sum Complex.imAddGroupHom _ _
    linarith
  -- Each term = 0
  have hterm_zero : ∀ i ∈ Finset.univ,
      (σ.charge (F.toPostnikovTower.factor i) * rot).im = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos hterms).mp hsum
  -- Nonzero factors have phase = φ
  have factor_eq : ∀ i : Fin F.n,
      ¬IsZero (F.toPostnikovTower.factor i) → F.φ i = φ := by
    intro i hi
    have him := hterm_zero i (Finset.mem_univ _)
    obtain ⟨mi, hmi, hvali⟩ :=
      σ.compat (F.φ i) _ (F.semistable i) hi
    rw [hvali, im_ofReal_mul_exp_mul_exp_neg] at him
    have hsin_zero : Real.sin (Real.pi * (F.φ i - φ)) = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · linarith
      · exact h
    by_contra hne
    have hlt : F.φ i - φ < 0 := lt_of_le_of_ne
      (by linarith [(hphases i).2]) (sub_ne_zero.mpr hne)
    exact absurd hsin_zero (ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos, (hphases i).1])))
  -- Top and bottom nonzero factors have phase φ → n = 1
  have htop : F.φ ⟨0, hn⟩ = φ := factor_eq ⟨0, hn⟩ hfirst
  have hbot : F.φ ⟨F.n - 1, by lia⟩ = φ := factor_eq ⟨F.n - 1, by lia⟩ hlast
  have hn1 : F.n = 1 := by
    by_contra h
    have := F.hφ (show (⟨0, hn⟩ : Fin F.n) < ⟨F.n - 1, by lia⟩ from
      Fin.mk_lt_mk.mpr (by lia))
    linarith
  -- X ≅ factor 0 ∈ P(φ)
  have hfact : σ.slicing.P φ (F.toPostnikovTower.factor ⟨0, hn⟩) := by
    rw [← htop]; exact F.semistable ⟨0, hn⟩
  let T := F.triangle ⟨0, hn⟩
  have hZ₁ : IsZero T.obj₁ :=
    IsZero.of_iso F.base_isZero (Classical.choice (F.triangle_obj₁ ⟨0, hn⟩))
  have : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist ⟨0, hn⟩)).mp hZ₁
  have hobj₂_eq : F.chain.obj' (0 + 1) (by lia) =
      F.chain.obj (Fin.last F.n) :=
    congrArg F.chain.obj (Fin.ext (by simp [Fin.last]; lia))
  let e₂ : T.obj₂ ≅ X :=
    (Classical.choice (F.triangle_obj₂ ⟨0, hn⟩)).trans
      ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
  haveI := σ.slicing.closedUnderIso φ
  exact (σ.slicing.P φ).prop_of_iso (e₂.symm.trans (asIso T.mor₂)).symm hfact

/-- **P(φ) closure under subobjects and quotients.** If `E ∈ P(φ)` is nonzero
and `K → E → Q → K⟦1⟧` is a distinguished triangle where both `K` and `Q` have
all σ-phases in `(φ-1, φ]` (both in the heart), then both `K ∈ P(φ)` and
`Q ∈ P(φ)`.

This is the key step in **Bridgeland's Lemma 5.2** (each P(φ) is abelian). -/
theorem P_phi_of_heart_triangle
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ}
    {K E Q : C} {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C)
    (hPφ : σ.slicing.P φ E) (hE : ¬IsZero E)
    (hKne : ¬IsZero K)
    (hK_le : σ.slicing.phiPlus C K hKne ≤ φ)
    (hK_gt : φ - 1 < σ.slicing.phiMinus C K hKne)
    (hQne : ¬IsZero Q)
    (hQ_le : σ.slicing.phiPlus C Q hQne ≤ φ)
    (hQ_gt : φ - 1 < σ.slicing.phiMinus C Q hQne) :
    σ.slicing.P φ K ∧ σ.slicing.P φ Q := by
  -- K₀ additivity: Z(E) = Z(K) + Z(Q)
  have hZsum : σ.charge E = σ.charge K + σ.charge Q := by
    have h := cl_triangle C v (Triangle.mk f₁ f₂ f₃) hT
    simp only [Pretriangulated.Triangle.mk] at h
    simp only [charge_def, h, map_add]
  -- Im(Z(E) · exp(-iπφ)) = 0
  obtain ⟨mE, hmE, hvE⟩ := σ.compat φ E hPφ hE
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  have him_E : (σ.charge E * rot).im = 0 := by
    rw [hvE, mul_assoc, ← Complex.exp_add]
    have : ↑(Real.pi * φ) * Complex.I + -(↑(Real.pi * φ) * Complex.I) = 0 := by ring
    rw [this, Complex.exp_zero, mul_one, Complex.ofReal_im]
  -- Im(Z(K) · rot) ≤ 0 and Im(Z(Q) · rot) ≤ 0
  have him_K := im_Z_nonpos_of_heart_phases C σ hKne hK_le hK_gt
  have him_Q := im_Z_nonpos_of_heart_phases C σ hQne hQ_le hQ_gt
  -- Sum = 0 forces both = 0
  have : (σ.charge K * rot).im + (σ.charge Q * rot).im = 0 := by
    have : (σ.charge E * rot).im =
        (σ.charge K * rot).im + (σ.charge Q * rot).im := by
      rw [hZsum, add_mul, Complex.add_im]
    linarith
  have him_K_zero : (σ.charge K * rot).im = 0 := by linarith
  have him_Q_zero : (σ.charge Q * rot).im = 0 := by linarith
  exact ⟨P_phi_of_im_zero_heart C σ hKne hK_le hK_gt him_K_zero,
    P_phi_of_im_zero_heart C σ hQne hQ_le hQ_gt him_Q_zero⟩

/-- **Im non-negativity for objects with phases above φ.** If `X` has all σ-phases in
`[φ, φ + 1)` (i.e., `φ ≤ phiMinus` and `phiPlus < φ + 1`), then
`Im(Z(X) · exp(-iπφ)) ≥ 0`. Symmetric to `im_Z_nonpos_of_heart_phases`. -/
theorem im_Z_nonneg_of_phases_above
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ}
    {E : C} (hE : ¬IsZero E)
    (hge : φ ≤ σ.slicing.phiMinus C E hE)
    (hlt : σ.slicing.phiPlus C E hE < φ + 1) :
    0 ≤ (σ.charge E *
      Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  have hphases : ∀ i : Fin F.n, φ ≤ F.φ i ∧ F.φ i < φ + 1 := fun i =>
    ⟨by calc φ ≤ σ.slicing.phiMinus C E hE := hge
          _ = F.φ ⟨F.n - 1, by lia⟩ :=
            σ.slicing.phiMinus_eq C E hE F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C E hE :=
            (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
          _ < φ + 1 := hlt⟩
  set P := F.toPostnikovTower
  rw [σ.charge_postnikovTower_eq_sum P]
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  rw [Finset.sum_mul, show (∑ i : Fin F.n, σ.charge (P.factor i) * rot).im =
      ∑ i : Fin F.n, (σ.charge (P.factor i) * rot).im from
    map_sum Complex.imAddGroupHom _ _]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : IsZero (P.factor i)
  · simp [σ.charge_isZero hi]
  · obtain ⟨m, hm, hval⟩ :=
      σ.compat (F.φ i) (P.factor i) (F.semistable i) hi
    rw [hval, im_ofReal_mul_exp_mul_exp_neg]
    exact mul_nonneg (le_of_lt hm)
      (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos, (hphases i).1])
        (by nlinarith [Real.pi_pos, (hphases i).2]))

/-- **From Im = 0 to P(φ) for objects with phases above φ.** If `X` is nonzero with
all σ-phases in `[φ, φ + 1)` and `Im(Z(X) · exp(-iπφ)) = 0`, then `X ∈ P(φ)`.
Symmetric to `P_phi_of_im_zero_heart`. -/
theorem P_phi_of_im_zero_above
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ}
    {X : C} (hXne : ¬IsZero X)
    (hX_ge : φ ≤ σ.slicing.phiMinus C X hXne)
    (hX_lt : σ.slicing.phiPlus C X hXne < φ + 1)
    (him_zero : (σ.charge X *
      Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im = 0) :
    σ.slicing.P φ X := by
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hXne
  have hphases : ∀ i : Fin F.n, φ ≤ F.φ i ∧ F.φ i < φ + 1 := fun i =>
    ⟨by calc φ ≤ σ.slicing.phiMinus C X hXne := hX_ge
          _ = F.φ ⟨F.n - 1, by lia⟩ :=
            σ.slicing.phiMinus_eq C X hXne F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C X hXne :=
            (σ.slicing.phiPlus_eq C X hXne F hn hfirst).symm
          _ < φ + 1 := hX_lt⟩
  have hZX := σ.charge_postnikovTower_eq_sum F.toPostnikovTower
  have hterms : ∀ i ∈ Finset.univ,
      0 ≤ (σ.charge (F.toPostnikovTower.factor i) * rot).im := by
    intro i _
    by_cases hi : IsZero (F.toPostnikovTower.factor i)
    · simp [σ.charge_isZero hi]
    · obtain ⟨mi, hmi, hvali⟩ :=
        σ.compat (F.φ i) _ (F.semistable i) hi
      rw [hvali, im_ofReal_mul_exp_mul_exp_neg]
      exact mul_nonneg (le_of_lt hmi)
        (Real.sin_nonneg_of_nonneg_of_le_pi
          (by nlinarith [Real.pi_pos, (hphases i).1])
          (by nlinarith [Real.pi_pos, (hphases i).2]))
  have hsum : ∑ i ∈ Finset.univ,
      (σ.charge (F.toPostnikovTower.factor i) * rot).im = 0 := by
    have : (σ.charge X * rot).im =
        ∑ i : Fin F.n,
          (σ.charge (F.toPostnikovTower.factor i) * rot).im := by
      rw [hZX, Finset.sum_mul]
      exact map_sum Complex.imAddGroupHom _ _
    linarith
  have hterm_zero : ∀ i ∈ Finset.univ,
      (σ.charge (F.toPostnikovTower.factor i) * rot).im = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum
  have factor_eq : ∀ i : Fin F.n,
      ¬IsZero (F.toPostnikovTower.factor i) → F.φ i = φ := by
    intro i hi
    have him := hterm_zero i (Finset.mem_univ _)
    obtain ⟨mi, hmi, hvali⟩ :=
      σ.compat (F.φ i) _ (F.semistable i) hi
    rw [hvali, im_ofReal_mul_exp_mul_exp_neg] at him
    have hsin_zero : Real.sin (Real.pi * (F.φ i - φ)) = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · linarith
      · exact h
    by_contra hne
    have hlt' : 0 < F.φ i - φ := lt_of_le_of_ne
      (by linarith [(hphases i).1]) (fun h ↦ hne (by linarith))
    exact absurd hsin_zero (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos, (hphases i).2])))
  have htop : F.φ ⟨0, hn⟩ = φ := factor_eq ⟨0, hn⟩ hfirst
  have hbot : F.φ ⟨F.n - 1, by lia⟩ = φ := factor_eq ⟨F.n - 1, by lia⟩ hlast
  have hn1 : F.n = 1 := by
    by_contra h
    have := F.hφ (show (⟨0, hn⟩ : Fin F.n) < ⟨F.n - 1, by lia⟩ from
      Fin.mk_lt_mk.mpr (by lia))
    linarith
  have hfact : σ.slicing.P φ (F.toPostnikovTower.factor ⟨0, hn⟩) := by
    rw [← htop]; exact F.semistable ⟨0, hn⟩
  let T := F.triangle ⟨0, hn⟩
  have hZ₁ : IsZero T.obj₁ :=
    IsZero.of_iso F.base_isZero (Classical.choice (F.triangle_obj₁ ⟨0, hn⟩))
  have : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist ⟨0, hn⟩)).mp hZ₁
  have hobj₂_eq : F.chain.obj' (0 + 1) (by lia) =
      F.chain.obj (Fin.last F.n) :=
    congrArg F.chain.obj (Fin.ext (by simp [Fin.last]; lia))
  let e₂ : T.obj₂ ≅ X :=
    (Classical.choice (F.triangle_obj₂ ⟨0, hn⟩)).trans
      ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
  haveI := σ.slicing.closedUnderIso φ
  exact (σ.slicing.P φ).prop_of_iso (e₂.symm.trans (asIso T.mor₂)).symm hfact

/-! ### P(φ) is abelian (Bridgeland Lemma 5.2)

Each slicing slice `P(φ)` of a stability condition is an abelian category.
The proof uses:
1. Extension closure (`semistable_of_triangle`) for finite products
2. Hom-vanishing from the slicing for negative Hom spaces
3. Admissibility via the t-structure truncation from the shifted slicing,
   with a Z-ray argument promoting heart membership to P(φ) membership -/

/-- P(φ) is closed under biproducts for a stability condition. -/
lemma StabilityCondition.WithClassMap.P_phi_biprod
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ} {X Y : C}
    (hX : σ.slicing.P φ X) (hY : σ.slicing.P φ Y) :
    σ.slicing.P φ (X ⊞ Y) :=
  σ.slicing.semistable_of_triangle C φ hX hY
    (binaryBiproductTriangle_distinguished X Y)

/-- P(φ) is closed under binary products for a stability condition. -/
instance StabilityCondition.WithClassMap.P_phi_closedUnderBinaryProducts
    (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) :
    (σ.slicing.P φ).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    exact (σ.slicing.P φ).prop_of_iso
      ((biprod.isoProd (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) ≪≫
        (HasLimit.isoOfNatIso (Discrete.natIso (fun ⟨j⟩ ↦ match j with
          | WalkingPair.left => Iso.refl _
          | WalkingPair.right => Iso.refl _))).symm)
      (σ.P_phi_biprod C (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))

/-- P(φ) is closed under finite products for a stability condition. -/
instance StabilityCondition.WithClassMap.P_phi_closedUnderFiniteProducts
    (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) :
    (σ.slicing.P φ).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- P(φ) has finite products for a stability condition. -/
noncomputable instance StabilityCondition.P_phi_hasFiniteProducts
    (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) :
    HasFiniteProducts (σ.slicing.P φ).FullSubcategory :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- **No negative Hom spaces in P(φ).** For `X, Y ∈ P(φ)`, every morphism
`ι X ⟶ (ι Y)⟦n⟧` is zero when `n < 0`. Y⟦n⟧ ∈ P(φ+n)` by the shift axiom,
and since `n < 0` we have `φ > φ + n`, so hom-vanishing applies. -/
theorem StabilityCondition.WithClassMap.P_phi_hom_vanishing
    (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) :
    ∀ ⦃X Y : (σ.slicing.P φ).FullSubcategory⦄ ⦃n : ℤ⦄
      (f : (σ.slicing.P φ).ι.obj X ⟶ ((σ.slicing.P φ).ι.obj Y)⟦n⟧),
      n < 0 → f = 0 := fun X Y n f hn =>
  σ.slicing.hom_vanishing φ (φ + ↑n) X.obj (Y.obj⟦n⟧)
    (by linarith [show (↑n : ℝ) < 0 from Int.cast_lt_zero.mpr hn])
    X.property
    ((σ.slicing.shift_int C φ Y.obj n).mp Y.property) f

set_option backward.isDefEq.respectTransparency false in
/-- **P(φ) membership for truncation of a P(φ)-cone** (**Bridgeland's Lemma 5.2**).
Given a distinguished triangle `A → B → X₃ → A⟦1⟧` with `A, B ∈ P(φ)`, the
t-structure truncation pieces of `X₃` (from the shifted slicing) lie in `P(φ)`.

The proof uses K₀ additivity and sign analysis of `Im(Z(·) · exp(-iπφ))`.
From the original triangle, `Im(Z(X₃)·rot) = 0`. From the truncation triangle,
`Im(Z(L)·rot) + Im(Z(Q)·rot) = 0`. Since Q has phases in `(φ-1, φ]`, we get
`Im(Z(Q)·rot) ≤ 0`. Since L has phases in `(φ, φ+1]`, an extra π rotation
gives `Im(Z(L)·rot) ≥ 0`. Both must vanish, and `P_phi_of_im_zero_heart`
promotes to `Q ∈ P(φ)` and `L ∈ P(φ+1)`. -/
theorem P_phi_of_truncation_of_P_phi_cone
    (σ : StabilityCondition.WithClassMap C v) (φ : ℝ)
    {A B X₃ : C} (hA : σ.slicing.P φ A) (hB : σ.slicing.P φ B)
    {f₁ : A ⟶ B} {f₂ : B ⟶ X₃} {f₃ : X₃ ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    let t : TStructure C :=
      @Slicing.toTStructure C _ _ _ _ _ _ ‹IsTriangulated C› (σ.slicing.phaseShift C (φ - 1))
    σ.slicing.P φ ((t.truncGE 0).obj X₃) ∧
      σ.slicing.P φ (((t.truncLT 0).obj X₃)⟦(-1 : ℤ)⟧) := by
  dsimp
  set s := σ.slicing
  set ss := s.phaseShift C (φ - 1)
  set t := ss.toTStructure
  -- P(φ) objects have phase 1 in the shifted slicing
  have hP1A : ss.P 1 A := by
    change s.P (1 + (φ - 1)) A; rw [show (1 : ℝ) + (φ - 1) = φ from by ring]; exact hA
  have hP1B : ss.P 1 B := by
    change s.P (1 + (φ - 1)) B; rw [show (1 : ℝ) + (φ - 1) = φ from by ring]; exact hB
  have cast_le : (-↑(0 : ℤ) : ℝ) = 0 := by simp
  have cast_ge : (1 - ↑(0 : ℤ) : ℝ) = 1 := by simp
  -- A, B are in the heart of t
  haveI hA_le : t.IsLE A 0 := ⟨by
    change ss.gtProp C (-↑(0 : ℤ)) A; rw [cast_le]
    exact ss.gtProp_of_semistable C 1 0 A hP1A (by linarith)⟩
  haveI hB_le : t.IsLE B 0 := ⟨by
    change ss.gtProp C (-↑(0 : ℤ)) B; rw [cast_le]
    exact ss.gtProp_of_semistable C 1 0 B hP1B (by linarith)⟩
  haveI : t.IsGE A 0 := ⟨by
    change ss.leProp C (1 - ↑(0 : ℤ)) A; rw [cast_ge]
    exact ss.leProp_of_semistable C 1 1 A hP1A le_rfl⟩
  haveI : t.IsGE B 0 := ⟨by
    change ss.leProp C (1 - ↑(0 : ℤ)) B; rw [cast_ge]
    exact ss.leProp_of_semistable C 1 1 B hP1B le_rfl⟩
  -- Shift bounds for the rotation
  haveI : t.IsLE (A⟦(1 : ℤ)⟧) 0 := by
    haveI := t.isLE_shift A 0 1 (-1); exact t.isLE_of_le _ (-1) 0
  haveI : t.IsGE B (-1) := t.isGE_of_ge _ (-1) 0
  haveI : t.IsGE (A⟦(1 : ℤ)⟧) (-1) := t.isGE_shift A 0 1 (-1)
  -- X₃ bounds from the rotation triangle
  have hrot := rot_of_distTriang _ hT
  haveI hX₃_le : t.IsLE X₃ 0 := by
    refine t.isLE₂ _ hrot 0 ?_ ?_
    · simp only [Triangle.rotate_obj₁, Triangle.mk_obj₂]; exact hB_le
    · simp only [Triangle.rotate_obj₃, Triangle.mk_obj₁]
      exact ‹t.IsLE (A⟦(1 : ℤ)⟧) 0›
  haveI : t.IsGE X₃ (-1) := by
    refine t.isGE₂ _ hrot (-1) ?_ ?_
    · simp only [Triangle.rotate_obj₁, Triangle.mk_obj₂]; exact ‹t.IsGE B (-1)›
    · simp only [Triangle.rotate_obj₃, Triangle.mk_obj₁]
      exact ‹t.IsGE (A⟦(1 : ℤ)⟧) (-1)›
  -- Truncation of X₃
  have htrunc := t.triangleLTGE_distinguished 0 X₃
  -- Q bounds: IsLE 0, IsGE 0 (heart)
  haveI hQ_le : t.IsLE ((t.truncGE 0).obj X₃) 0 := by
    have hrot_trunc := rot_of_distTriang _ htrunc
    refine t.isLE₂ _ hrot_trunc 0 ?_ ?_
    · dsimp; exact hX₃_le
    · dsimp
      haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
      haveI := t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
      exact t.isLE_of_le _ (-2) 0
  haveI : t.IsGE ((t.truncGE 0).obj X₃) 0 := inferInstance
  -- L bounds: IsLE(-1), IsGE(-1)
  haveI hL_le : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
  haveI : t.IsGE ((t.truncLT 0).obj X₃) (-1) := by
    have hinv := inv_rot_of_distTriang _ htrunc
    refine t.isGE₂ _ hinv (-1) ?_ ?_
    · dsimp
      haveI : t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) 1 :=
        t.isGE_shift _ 0 (-1) 1
      exact t.isGE_of_ge _ (-1) 1
    · dsimp; exact ‹t.IsGE X₃ (-1)›
  -- Convert t-structure bounds to original slicing phase bounds
  -- Q has s-phases in (φ-1, φ]
  have hQ_sgt : s.gtProp C (φ - 1) ((t.truncGE 0).obj X₃) :=
    (s.phaseShift_gtProp_zero C (φ - 1) _).mp (by
      have h := hQ_le.le; change ss.gtProp C (-↑(0 : ℤ)) _ at h; rwa [cast_le] at h)
  have hQ_sle : s.leProp C φ ((t.truncGE 0).obj X₃) := by
    have h : ss.leProp C 1 ((t.truncGE 0).obj X₃) := by
      have h := (inferInstance : t.IsGE ((t.truncGE 0).obj X₃) 0).ge
      change ss.leProp C (1 - ↑(0 : ℤ)) _ at h; rwa [cast_ge] at h
    rcases h with hZ | ⟨F, hF, hle⟩
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      exact Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + (φ - 1),
        fun i j hij ↦ by linarith [F.hφ hij], fun j ↦ F.semistable j⟩, hF, by
        dsimp only [HNFiltration.phiPlus]; linarith⟩
  -- L has s-phases in (φ, φ+1]
  have hL_sgt : s.gtProp C φ ((t.truncLT 0).obj X₃) := by
    have h : ss.gtProp C 1 ((t.truncLT 0).obj X₃) := by
      have h := hL_le.le; change ss.gtProp C (-↑(-1 : ℤ)) _ at h
      simpa only [Int.cast_neg, Int.cast_one, neg_neg] using h
    rcases h with hZ | ⟨F, hF, hgt⟩
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hgt
      exact Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + (φ - 1),
        fun i j hij ↦ by linarith [F.hφ hij], fun j ↦ F.semistable j⟩, hF, by
        dsimp only [HNFiltration.phiMinus]; linarith⟩
  have hL_sle : s.leProp C (φ + 1) ((t.truncLT 0).obj X₃) := by
    have h : ss.leProp C (1 + 1) ((t.truncLT 0).obj X₃) := by
      have h := (inferInstance : t.IsGE ((t.truncLT 0).obj X₃) (-1)).ge
      change ss.leProp C (1 - ↑(-1 : ℤ)) _ at h
      simpa only [Int.cast_neg, Int.cast_one, sub_neg_eq_add] using h
    rcases h with hZ | ⟨F, hF, hle⟩
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      exact Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + (φ - 1),
        fun i j hij ↦ by linarith [F.hφ hij], fun j ↦ F.semistable j⟩, hF, by
        dsimp only [HNFiltration.phiPlus]; linarith⟩
  -- === Epi approach for Q, K₀ for L ===
  have hB_heart : t.heart B := (t.mem_heart_iff _).mpr ⟨hB_le, inferInstance⟩
  have hQ_heart : t.heart ((t.truncGE 0).obj X₃) :=
    (t.mem_heart_iff _).mpr ⟨hQ_le, inferInstance⟩
  letI := t.hasHeartFullSubcategory
  let B_H : t.heart.FullSubcategory := ⟨B, hB_heart⟩
  let Q_H : t.heart.FullSubcategory := ⟨(t.truncGE 0).obj X₃, hQ_heart⟩
  let g_C : B ⟶ (t.truncGE 0).obj X₃ :=
    f₂ ≫ ((t.triangleLTGE 0).obj X₃).mor₂
  let g_H : B_H ⟶ Q_H := ObjectProperty.homMk g_C
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  -- Type conversion for ι.obj
  have hι_simp : ∀ (X : t.heart.FullSubcategory), ι.obj X = X.obj := by
    intro X; rfl
  -- g_H is epi in the heart
  haveI : Epi g_H := by
    rw [Preadditive.epi_iff_cancel_zero]
    intro R k hk
    haveI : t.IsGE R.obj 0 :=
      ((t.mem_heart_iff R.obj).mp R.property).2
    have hk_C : g_C ≫ k.hom = 0 := by
      have := congr_arg InducedCategory.Hom.hom hk
      simpa only [ObjectProperty.FullSubcategory.comp_hom] using this
    have hmk : ((t.triangleLTGE 0).obj X₃).mor₂ ≫ k.hom = 0 := by
      have : f₂ ≫ (((t.triangleLTGE 0).obj X₃).mor₂ ≫ k.hom) = 0 := by
        rwa [← Category.assoc]
      obtain ⟨a, ha⟩ := Triangle.yoneda_exact₃
        (Triangle.mk f₁ f₂ f₃) hT _ this
      dsimp only [Triangle.mk] at a ha
      haveI : t.IsLE (A⟦(1 : ℤ)⟧) (-1) := t.isLE_shift A 0 1 (-1)
      rwa [show a = 0 from t.zero a (-1) 0 (by lia), comp_zero] at ha
    obtain ⟨b, hb⟩ := Triangle.yoneda_exact₃
      ((t.triangleLTGE 0).obj X₃) htrunc k.hom hmk
    dsimp only [TStructure.triangleLTGE, Triangle.functorMk, Triangle.mk] at b hb
    haveI : t.IsLE (((t.truncLT 0).obj X₃)⟦(1 : ℤ)⟧) (-2) :=
      t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
    rw [show b = 0 from t.zero b (-2) 0 (by lia), comp_zero] at hb
    exact ObjectProperty.hom_ext (P := t.heart) hb
  -- Get heart triangle I → B → Q → I⟦1⟧
  obtain ⟨I_H, i_H, δ_heart, hT_heart⟩ :=
    AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) g_H
  -- K₀ conversions via eqToIso
  have hK₀_B : cl C v (ι.obj B_H) = cl C v B :=
    cl_iso C v (eqToIso (hι_simp B_H))
  have hK₀_I : cl C v (ι.obj I_H) = cl C v I_H.obj :=
    cl_iso C v (eqToIso (hι_simp I_H))
  have hK₀_Q : cl C v (ι.obj Q_H) = cl C v ((t.truncGE 0).obj X₃) :=
    cl_iso C v (eqToIso (hι_simp Q_H))
  have hK₀_heart : cl C v B =
      cl C v I_H.obj + cl C v ((t.truncGE 0).obj X₃) := by
    have h := cl_triangle C v _ hT_heart
    dsimp only [Triangle.mk] at h; rwa [hK₀_B, hK₀_I, hK₀_Q] at h
  -- I_H phase bounds
  haveI hI_le : t.IsLE I_H.obj 0 :=
    ((t.mem_heart_iff I_H.obj).mp I_H.property).1
  haveI hI_ge : t.IsGE I_H.obj 0 :=
    ((t.mem_heart_iff I_H.obj).mp I_H.property).2
  have hI_sgt : s.gtProp C (φ - 1) I_H.obj :=
    (s.phaseShift_gtProp_zero C (φ - 1) _).mp (by
      have h := hI_le.le; change ss.gtProp C (-↑(0 : ℤ)) _ at h; rwa [cast_le] at h)
  have hI_sle : s.leProp C φ I_H.obj := by
    have h : ss.leProp C 1 I_H.obj := by
      have h := hI_ge.ge
      change ss.leProp C (1 - ↑(0 : ℤ)) _ at h; rwa [cast_ge] at h
    rcases h with hZ | ⟨F, hF, hle⟩
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      exact Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + (φ - 1),
        fun i j hij ↦ by linarith [F.hφ hij], fun j ↦ F.semistable j⟩, hF, by
        dsimp only [HNFiltration.phiPlus]; linarith⟩
  -- === K₀ + Im(Z·rot) ===
  -- P(φ) objects lie on the real axis after rotation by exp(-iπφ)
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  have him_ray : ∀ {E : C}, s.P φ E → (σ.charge E * rot).im = 0 := by
    intro E hPφ
    by_cases hne : IsZero E
    · simp [σ.charge_isZero hne]
    · obtain ⟨m, _, hv⟩ := σ.compat φ E hPφ hne
      rw [hv, mul_assoc, ← Complex.exp_add,
        show ↑(Real.pi * φ) * Complex.I + -(↑(Real.pi * φ) * Complex.I) = 0 from
          by ring,
        Complex.exp_zero, mul_one, Complex.ofReal_im]
  -- K₀ on truncation triangle: Z(X₃) = Z(L) + Z(Q)
  have hZtrunc : σ.charge X₃ =
      σ.charge ((t.truncLT 0).obj X₃) +
      σ.charge ((t.truncGE 0).obj X₃) := by
    have h := cl_triangle C v _ htrunc
    dsimp [TStructure.triangleLTGE] at h
    simp only [charge_def, h, map_add]
  -- K₀ on original triangle: Im(Z(X₃)·rot) = 0 since A, B ∈ P(φ)
  have hZX₃_im : (σ.charge X₃ * rot).im = 0 := by
    have hZorig : σ.charge B =
        σ.charge A + σ.charge X₃ := by
      have h := cl_triangle C v _ hT
      dsimp [Triangle.mk] at h
      simp only [charge_def, h, map_add]
    have : (σ.charge A * rot).im + (σ.charge X₃ * rot).im =
        (σ.charge B * rot).im := by
      rw [← Complex.add_im, ← add_mul, hZorig]
    linarith [him_ray hA, him_ray hB]
  -- Q ∈ P(φ) via K₀ on heart triangle
  have hQ_Pφ : s.P φ ((t.truncGE 0).obj X₃) := by
    by_cases hQne : IsZero ((t.truncGE 0).obj X₃)
    · exact s.zero_mem' C φ _ hQne
    · by_cases hIne : IsZero I_H.obj
      · -- I = 0 ⟹ g_H is iso ⟹ Q ≅ B ∈ P(φ)
        have hIne' : IsZero (ι.obj I_H) := by rwa [hι_simp]
        haveI : IsIso (ι.map g_H) :=
          (Triangle.isZero₁_iff_isIso₂
            (Triangle.mk (ι.map i_H) (ι.map g_H) δ_heart) hT_heart).mp hIne'
        exact (s.P φ).prop_of_iso
          ((eqToIso (hι_simp B_H)).symm ≪≫
            asIso (ι.map g_H) ≪≫ eqToIso (hι_simp Q_H)) hB
      · -- Both I and Q nonzero: K₀ + Im argument in the heart
        have him_I := im_Z_nonpos_of_heart_phases C σ hIne
          (s.phiPlus_le_of_leProp C hIne hI_sle)
          (s.phiMinus_gt_of_gtProp C hIne hI_sgt)
        have him_Q := im_Z_nonpos_of_heart_phases C σ hQne
          (s.phiPlus_le_of_leProp C hQne hQ_sle)
          (s.phiMinus_gt_of_gtProp C hQne hQ_sgt)
        have him_sum_heart : (σ.charge I_H.obj * rot).im +
            (σ.charge ((t.truncGE 0).obj X₃) * rot).im = 0 := by
          have h : σ.charge I_H.obj * rot +
              σ.charge ((t.truncGE 0).obj X₃) * rot =
              σ.charge B * rot := by
            rw [← add_mul, ← map_add, ← hK₀_heart]
          have him := congr_arg Complex.im h
          simp only [Complex.add_im] at him
          linarith [him_ray hB]
        exact P_phi_of_im_zero_heart C σ hQne
          (s.phiPlus_le_of_leProp C hQne hQ_sle)
          (s.phiMinus_gt_of_gtProp C hQne hQ_sgt) (by linarith)
  -- Im(Z(L)·rot) = 0 from truncation K₀ + hZX₃_im + him_ray hQ_Pφ
  have hL_im0 : (σ.charge ((t.truncLT 0).obj X₃) * rot).im = 0 := by
    have : (σ.charge ((t.truncLT 0).obj X₃) * rot).im +
        (σ.charge ((t.truncGE 0).obj X₃) * rot).im =
        (σ.charge X₃ * rot).im := by
      rw [← Complex.add_im, ← add_mul, ← hZtrunc]
    linarith [him_ray hQ_Pφ]
  -- L ∈ P(φ+1) via P_phi_of_im_zero_heart at phase φ+1
  have hL_Pφ1 : s.P (φ + 1) ((t.truncLT 0).obj X₃) := by
    by_cases hLne : IsZero ((t.truncLT 0).obj X₃)
    · exact s.zero_mem' C (φ + 1) _ hLne
    · exact P_phi_of_im_zero_heart C σ hLne
        (s.phiPlus_le_of_leProp C hLne hL_sle)
        (show φ + 1 - 1 < s.phiMinus C _ hLne from by
          linarith [s.phiMinus_gt_of_gtProp C hLne hL_sgt])
        (by rw [show -(↑(Real.pi * (φ + 1)) * Complex.I) =
              -(↑(Real.pi * φ) * Complex.I) + -(↑Real.pi * Complex.I) from by
                push_cast; ring,
            Complex.exp_add, ← mul_assoc,
            show Complex.exp (-(↑Real.pi * Complex.I)) = -1 from by
              rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one],
            mul_neg_one, Complex.neg_im, hL_im0, neg_zero])
  -- L⟦-1⟧ ∈ P(φ) via shift
  have hK_Pφ : s.P φ (((t.truncLT 0).obj X₃)⟦(-1 : ℤ)⟧) := by
    have h := (s.shift_int C (φ + 1) ((t.truncLT 0).obj X₃) (-1)).mp hL_Pφ1
    convert h using 1; push_cast; ring
  exact ⟨hQ_Pφ, hK_Pφ⟩

/-- **Admissibility of morphisms in P(φ)** (**Bridgeland's Lemma 5.2**). For any morphism
`f₁ : X₁ → X₂` in `P(φ)` and distinguished triangle `ι(X₁) → ι(X₂) → X₃ → ι(X₁)⟦1⟧`,
there exist `K, Q ∈ P(φ)` and a distinguished triangle `(ι K)⟦1⟧ → X₃ → ι Q`.

The proof uses the truncation from the t-structure `(s.phaseShift(φ-1)).toTStructure`
to decompose X₃, then promotes the truncation pieces from heart `P((φ-1, φ])`
to `P(φ)` via `P_phi_of_truncation_of_P_phi_cone` (the epi approach). -/
theorem StabilityCondition.WithClassMap.P_phi_admissible
    (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) :
    let _t : TStructure C :=
      @Slicing.toTStructure C _ _ _ _ _ _ ‹IsTriangulated C› (σ.slicing.phaseShift C (φ - 1))
    AbelianSubcategory.admissibleMorphism (σ.slicing.P φ).ι = ⊤ := by
  dsimp
  set s := σ.slicing
  set ss := s.phaseShift C (φ - 1)
  set t := ss.toTStructure
  ext X₁ X₂ f₁; simp only [MorphismProperty.top_apply, iff_true]
  intro X₃ f₂ f₃ hT
  -- P(φ) objects have phase 1 in the shifted slicing
  have hP1 : ∀ X : (s.P φ).FullSubcategory, ss.P 1 X.obj := by
    intro X; change s.P (1 + (φ - 1)) X.obj
    rw [show (1 : ℝ) + (φ - 1) = φ from by ring]; exact X.property
  -- Cast cleanup helpers
  have cast_le : (-↑(0 : ℤ) : ℝ) = 0 := by simp
  have cast_ge : (1 - ↑(0 : ℤ) : ℝ) = 1 := by simp
  -- Step 1: P(φ) objects are IsLE 0 and IsGE 0 for t
  haveI hX₁_le : t.IsLE X₁.obj 0 := by
    refine ⟨?_⟩; change ss.gtProp C (-↑(0 : ℤ)) X₁.obj
    rw [cast_le]; exact ss.gtProp_of_semistable C 1 0 X₁.obj (hP1 X₁) (by linarith)
  haveI hX₂_le : t.IsLE X₂.obj 0 := by
    refine ⟨?_⟩; change ss.gtProp C (-↑(0 : ℤ)) X₂.obj
    rw [cast_le]; exact ss.gtProp_of_semistable C 1 0 X₂.obj (hP1 X₂) (by linarith)
  haveI hX₁_ge : t.IsGE X₁.obj 0 := by
    refine ⟨?_⟩; change ss.leProp C (1 - ↑(0 : ℤ)) X₁.obj
    rw [cast_ge]; exact ss.leProp_of_semistable C 1 1 X₁.obj (hP1 X₁) le_rfl
  haveI hX₂_ge : t.IsGE X₂.obj 0 := by
    refine ⟨?_⟩; change ss.leProp C (1 - ↑(0 : ℤ)) X₂.obj
    rw [cast_ge]; exact ss.leProp_of_semistable C 1 1 X₂.obj (hP1 X₂) le_rfl
  -- Shifted objects for the rotation
  haveI : t.IsLE (X₁.obj⟦(1 : ℤ)⟧) 0 := by
    haveI := t.isLE_shift X₁.obj 0 1 (-1); exact t.isLE_of_le _ (-1) 0
  haveI : t.IsGE X₂.obj (-1) := t.isGE_of_ge _ (-1) 0
  haveI : t.IsGE (X₁.obj⟦(1 : ℤ)⟧) (-1) := t.isGE_shift X₁.obj 0 1 (-1)
  -- Step 2: X₃ is IsLE 0 and IsGE(-1) from the rotation triangle
  have hrot := rot_of_distTriang _ hT
  haveI hX₃_le : t.IsLE X₃ 0 := by
    refine t.isLE₂ _ hrot 0 ?_ ?_
    · simp only [Triangle.rotate_obj₁, Triangle.mk_obj₂, ObjectProperty.ι_obj]
      exact hX₂_le
    · simp only [Triangle.rotate_obj₃, Triangle.mk_obj₁, ObjectProperty.ι_obj]
      exact ‹t.IsLE (X₁.obj⟦(1 : ℤ)⟧) 0›
  haveI hX₃_ge : t.IsGE X₃ (-1) := by
    refine t.isGE₂ _ hrot (-1) ?_ ?_
    · simp only [Triangle.rotate_obj₁, Triangle.mk_obj₂, ObjectProperty.ι_obj]
      exact ‹t.IsGE X₂.obj (-1)›
    · simp only [Triangle.rotate_obj₃, Triangle.mk_obj₁, ObjectProperty.ι_obj]
      exact ‹t.IsGE (X₁.obj⟦(1 : ℤ)⟧) (-1)›
  -- Step 3: Truncation — decompose X₃ via the t-structure
  have htrunc := t.triangleLTGE_distinguished 0 X₃
  -- Q := (truncGE 0).obj X₃ is IsLE 0 (rotation of truncation + isLE₂)
  haveI hQ_le : t.IsLE ((t.truncGE 0).obj X₃) 0 := by
    have hrot_trunc := rot_of_distTriang _ htrunc
    refine t.isLE₂ _ hrot_trunc 0 ?_ ?_
    · dsimp; exact hX₃_le
    · dsimp
      haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
      haveI := t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
      exact t.isLE_of_le _ (-2) 0
  -- (truncLT 0).obj X₃ is IsGE(-1) (inverse rotation + isGE₂)
  haveI hK_ge : t.IsGE ((t.truncLT 0).obj X₃) (-1) := by
    have hinv := inv_rot_of_distTriang _ htrunc
    refine t.isGE₂ _ hinv (-1) ?_ ?_
    · dsimp
      haveI : t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) 1 :=
        t.isGE_shift _ 0 (-1) 1
      exact t.isGE_of_ge _ (-1) 1
    · dsimp; exact hX₃_ge
  -- Q is in the heart (IsGE 0 by truncation + IsLE 0)
  haveI : t.IsGE ((t.truncGE 0).obj X₃) 0 := inferInstance
  -- K' := ((truncLT 0).obj X₃)⟦-1⟧ is in the heart
  haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
  -- Step 4: Promote from heart to P(φ) via Z-ray argument
  have ⟨hQ_Pφ, hK_Pφ⟩ := P_phi_of_truncation_of_P_phi_cone C σ φ
    X₁.property X₂.property hT
  -- Step 5: Build the admissible triangle from the truncation triangle
  let K : (s.P φ).FullSubcategory := ⟨_, hK_Pφ⟩
  let Q : (s.P φ).FullSubcategory := ⟨_, hQ_Pφ⟩
  let e₁ : ((s.P φ).ι.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLT 0).obj X₃ :=
    (shiftEquiv C (1 : ℤ)).counitIso.app ((t.truncLT 0).obj X₃)
  let α : ((s.P φ).ι.obj K)⟦(1 : ℤ)⟧ ⟶ X₃ := e₁.hom ≫ (t.truncLTι 0).app X₃
  let β : X₃ ⟶ (s.P φ).ι.obj Q := (t.truncGEπ 0).app X₃
  let γ : (s.P φ).ι.obj Q ⟶ ((s.P φ).ι.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    (t.truncGEδLT 0).app X₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv
  exact ⟨K, Q, α, β, γ, isomorphic_distinguished _
    (t.triangleLTGE_distinguished 0 X₃) _
    (Triangle.isoMk _ _ e₁ (Iso.refl _) (Iso.refl _)
      (by dsimp [α, TStructure.triangleLTGE]; simp)
      (by dsimp [β, TStructure.triangleLTGE]; simp)
      (by dsimp [γ]; simp))⟩

variable [IsTriangulated C] in
/-- **P(φ) is abelian** (**Bridgeland's Lemma 5.2**). Each slicing slice `P(φ)` of a
stability condition is an abelian category. -/
@[reducible, informal "Lemma 5.2" complete]
noncomputable def StabilityCondition.WithClassMap.P_phi_abelian
    (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) :
    Abelian (σ.slicing.P φ).FullSubcategory :=
  AbelianSubcategory.abelian (σ.slicing.P φ).ι
    (σ.P_phi_hom_vanishing C φ) (σ.P_phi_admissible C φ)

end CategoryTheory.Triangulated
