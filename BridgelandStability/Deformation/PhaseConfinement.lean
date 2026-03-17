/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Deformation.PhaseArithmetic

/-!
# Deformation of Stability Conditions — PhaseConfinement

Phase confinement of W-semistable objects (Lemma 7.3)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### Node 7.3: Phase confinement of W-semistable objects -/

variable [IsTriangulated C] in
/-- **Bridgeland's Lemma 7.3 (upper bound).** If `E` is W-semistable of W-phase `ψ` in
`P((a, b))`, the interval is thin enough (`b - a + 2ε₀ < 1`), and each nonzero semistable
factor has W-phase within `ε₀` of its σ-phase, then `σ.phiPlus(E) ≤ ψ + ε₀`.

The proof splits `E` at the cutoff `ψ + ε₀` via the t-structure. The resulting subobject
`K` (with σ-phases above `ψ + ε₀`) has W-phase `> ψ` by the Im/sin argument, contradicting
W-semistability. -/
theorem phiPlus_lt_of_wSemistable
    (σ : StabilityCondition C) {E : C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {ψ : ℝ} (hSS : ssf.Semistable C E ψ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀) :
    σ.slicing.phiPlus C E hSS.2.1 < ψ + ε₀ := by
  obtain ⟨hI, hE, _, hψ, hsemistable⟩ := hSS
  -- W nonvanishing and reformulated perturbation bounds
  have hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b → ssf.W (K₀.of C F) ≠ 0 :=
    fun F φ hP hFne haφ hφb ↦ ssf.nonzero F φ haφ hφb hP hFne
  have hperturb_gt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      a - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hperturb_lt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      b + ε₀ - 1 < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  -- ψ bounds from wPhaseOf_gt/lt_of_intervalProp applied to E
  have hψ_lo : a - ε₀ < ψ := by
    rw [← hψ]; exact wPhaseOf_gt_of_intervalProp C σ hE ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hI hW_ne hperturb_gt
  have hψ_hi : ψ < b + ε₀ := by
    rw [← hψ]; exact wPhaseOf_lt_of_intervalProp C σ hE ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hI hW_ne hperturb_lt
  -- Proof by contradiction
  by_contra hgt; push_neg at hgt
  rcases eq_or_lt_of_le hgt with heq | hgt
  · -- Boundary case: phiPlus(E) = ψ + ε₀.
    have hψε_lt_b : ψ + ε₀ < b := heq ▸ σ.slicing.phiPlus_lt_of_intervalProp C hE hI
    have hψε_gt_a : a < ψ + ε₀ := lt_of_lt_of_le
      (σ.slicing.phiMinus_gt_of_intervalProp C hE hI)
      (heq ▸ σ.slicing.phiMinus_le_phiPlus C E hE)
    -- If E is σ-semistable at phase ψ+ε₀, direct perturbation gives contradiction.
    -- If not, split at a gap below ψ+ε₀ to isolate the top factor.
    by_cases hsem : σ.slicing.P (ψ + ε₀) E
    · -- E ∈ P(ψ+ε₀): perturbation gives wPhaseOf(W(E)) > (ψ+ε₀)-ε₀ = ψ
      have ⟨hlo, _⟩ := hperturb E (ψ + ε₀) hsem hE hψε_gt_a hψε_lt_b
      linarith
    · -- E not σ-semistable: phiMinus < phiPlus = ψ+ε₀, so there are multiple factors.
      -- Split at a gap below ψ+ε₀ to isolate the top-phase factors.
      sorry
  have hψε_lt_b : ψ + ε₀ < b :=
    lt_trans hgt (σ.slicing.phiPlus_lt_of_intervalProp C hE hI)
  -- Extract HN filtration from intervalProp
  obtain ⟨F, hF⟩ := hI.resolve_left hE
  have hn : 0 < F.n := F.n_pos C hE
  -- Split E at cutoff ψ + ε₀
  obtain ⟨K, Y, fK, gY, δ, hT, hKgt, hYle, hKphiPlus⟩ :=
    σ.slicing.exists_split_at_cutoff C F hF hn (t := ψ + ε₀)
  -- K is nonzero (otherwise E ∈ leProp(ψ + ε₀), contradicting phiPlus > ψ + ε₀)
  have hKne : ¬IsZero K := by
    intro hKZ
    linarith [σ.slicing.phiPlus_le_of_leProp C hE
      (σ.slicing.leProp_of_triangle C (ψ + ε₀) (Or.inl hKZ) hYle hT)]
  -- K ∈ P((a, b))
  have hKI : σ.slicing.intervalProp C a b K :=
    σ.slicing.intervalProp_of_intrinsic_phases C hKne
      (by linarith [σ.slicing.phiMinus_gt_of_gtProp C hKne hKgt])
      (hKphiPlus hKne)
  -- K ∈ P((ψ + ε₀, b)) (narrower interval for Im argument)
  have hKI' : σ.slicing.intervalProp C (ψ + ε₀) b K :=
    σ.slicing.intervalProp_of_intrinsic_phases C hKne
      (σ.slicing.phiMinus_gt_of_gtProp C hKne hKgt) (hKphiPlus hKne)
  -- Im(W(K) · exp(-iπψ)) > 0 via K₀ decomposition
  have him_pos : 0 < (ssf.W (K₀.of C K) *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
    apply im_W_pos_of_intervalProp C σ hKne ssf.W hKI'
    intro G φ hP hGne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb G φ hP hGne (by linarith) hφb
    exact im_pos_of_phase_above (norm_pos_iff.mpr
      (ssf.nonzero G φ (by linarith) hφb hP hGne))
      (wPhaseOf_compat _ _) (by linarith) (by linarith)
  -- wPhaseOf(W(K), α) ∈ (ψ - 1, ψ + 1) via bounds on the original interval
  have hK_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C K)) ssf.α :=
    wPhaseOf_gt_of_intervalProp C σ hKne ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hKI hW_ne hperturb_gt
  have hK_hi : wPhaseOf (ssf.W (K₀.of C K)) ssf.α < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hKne ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hKI hW_ne hperturb_lt
  -- Y ∈ P((a, b))
  have hYI : σ.slicing.intervalProp C a b Y := by
    by_cases hYZ : IsZero Y
    · exact Or.inl hYZ
    · exact σ.slicing.intervalProp_of_intrinsic_phases C hYZ
        (lt_of_lt_of_le (σ.slicing.phiMinus_gt_of_intervalProp C hE hI)
          (σ.slicing.phiMinus_triangle_le' C hYZ hE (by linarith) hKI
            (lt_of_le_of_lt (σ.slicing.phiPlus_le_of_leProp C hYZ hYle)
              (by linarith)) hT))
        (lt_of_le_of_lt (σ.slicing.phiPlus_le_of_leProp C hYZ hYle)
          (by linarith))
  -- wPhaseOf(W(K), α) > ψ (from Im > 0 + range condition)
  linarith [wPhaseOf_gt_of_im_pos him_pos
    (show wPhaseOf (ssf.W (K₀.of C K)) ssf.α ∈ Set.Ioo (ψ - 1) (ψ + 1) from
      ⟨by linarith, by linarith⟩),
    hsemistable hT hKI hYI hKne]

variable [IsTriangulated C] in
/-- **Bridgeland's Lemma 7.3 (lower bound).** If `E` is W-semistable of W-phase `ψ` in
`P((a, b))`, the interval is thin enough (`b - a + 2ε₀ < 1`), and each nonzero semistable
factor has W-phase within `ε₀` of its σ-phase, then `ψ - ε₀ ≤ σ.phiMinus(E)`.

The proof splits `E` at the cutoff `ψ - ε₀`. The resulting quotient `Y` (with σ-phases
`≤ ψ - ε₀`) has `Im(W(Y) · exp(-iπψ)) < 0` by the sin/Im argument applied to each HN
factor. Combined with `Im(W(E) · exp(-iπψ)) = 0` (from `wPhaseOf(W(E)) = ψ`), this
shows `Im(W(K) · exp(-iπψ)) > 0`, giving `wPhaseOf(W(K)) > ψ` and contradicting
W-semistability. -/
theorem phiMinus_gt_of_wSemistable
    (σ : StabilityCondition C) {E : C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {ψ : ℝ} (hSS : ssf.Semistable C E ψ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀) :
    ψ - ε₀ < σ.slicing.phiMinus C E hSS.2.1 := by
  obtain ⟨hI, hE, _, hψ, hsemistable⟩ := hSS
  -- W nonvanishing and reformulated perturbation bounds
  have hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b → ssf.W (K₀.of C F) ≠ 0 :=
    fun F φ hP hFne haφ hφb ↦ ssf.nonzero F φ haφ hφb hP hFne
  have hperturb_gt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      a - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hperturb_lt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      b + ε₀ - 1 < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  -- ψ bounds from wPhaseOf_gt/lt_of_intervalProp applied to E
  have hψ_lo : a - ε₀ < ψ := by
    rw [← hψ]; exact wPhaseOf_gt_of_intervalProp C σ hE ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hI hW_ne hperturb_gt
  have hψ_hi : ψ < b + ε₀ := by
    rw [← hψ]; exact wPhaseOf_lt_of_intervalProp C σ hE ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hI hW_ne hperturb_lt
  -- Proof by contradiction: assume phiMinus ≤ ψ - ε₀
  by_contra hlt; push_neg at hlt
  rcases eq_or_lt_of_le hlt with heq | hlt
  · -- Boundary case: phiMinus(E) = ψ - ε₀.
    have hψε_gt_a : a < ψ - ε₀ := lt_of_lt_of_le
      (σ.slicing.phiMinus_gt_of_intervalProp C hE hI)
      (heq ▸ le_refl _)
    have hψε_lt_b : ψ - ε₀ < b := lt_of_le_of_lt
      (heq ▸ σ.slicing.phiMinus_le_phiPlus C E hE)
      (σ.slicing.phiPlus_lt_of_intervalProp C hE hI)
    by_cases hsem : σ.slicing.P (ψ - ε₀) E
    · -- E ∈ P(ψ-ε₀): perturbation gives wPhaseOf(W(E)) < (ψ-ε₀)+ε₀ = ψ
      have ⟨_, hhi⟩ := hperturb E (ψ - ε₀) hsem hE hψε_gt_a hψε_lt_b
      linarith
    · -- E not σ-semistable: phiMinus = ψ-ε₀ < phiPlus, multiple factors.
      sorry
  have hψε_gt_a : a < ψ - ε₀ :=
    lt_trans (σ.slicing.phiMinus_gt_of_intervalProp C hE hI) hlt
  -- Extract HN filtration from intervalProp
  obtain ⟨F, hF⟩ := hI.resolve_left hE
  have hn : 0 < F.n := F.n_pos C hE
  -- Split E at cutoff ψ - ε₀
  obtain ⟨K, Y, fK, gY, δ, hT, hKgt, hYle, hKphiPlus⟩ :=
    σ.slicing.exists_split_at_cutoff C F hF hn (t := ψ - ε₀)
  -- Y is nonzero (otherwise E ∈ gtProp(ψ - ε₀), contradicting phiMinus < ψ - ε₀)
  have hYne : ¬IsZero Y := by
    intro hYZ
    linarith [σ.slicing.phiMinus_gt_of_gtProp C hE
      (σ.slicing.gtProp_of_triangle C (ψ - ε₀) hKgt (Or.inl hYZ) hT)]
  -- K ∈ P((a, b))
  have hKI : σ.slicing.intervalProp C a b K := by
    by_cases hKZ : IsZero K
    · exact Or.inl hKZ
    · exact σ.slicing.intervalProp_of_intrinsic_phases C hKZ
        (by linarith [σ.slicing.phiMinus_gt_of_gtProp C hKZ hKgt])
        (hKphiPlus hKZ)
  -- Y ∈ P((a, b)) with phiPlus(Y) ≤ ψ - ε₀
  have hYphiPlus : σ.slicing.phiPlus C Y hYne ≤ ψ - ε₀ :=
    σ.slicing.phiPlus_le_of_leProp C hYne hYle
  have hYminus : a < σ.slicing.phiMinus C Y hYne :=
    lt_of_lt_of_le
      (σ.slicing.phiMinus_gt_of_intervalProp C hE (Or.inr ⟨F, hF⟩))
      (σ.slicing.phiMinus_triangle_le' C hYne hE
        (by linarith) hKI (by linarith [hYphiPlus]) hT)
  have hYI : σ.slicing.intervalProp C a b Y :=
    σ.slicing.intervalProp_of_intrinsic_phases C hYne hYminus
      (lt_of_le_of_lt hYphiPlus (by linarith))
  -- Im(W(Y) · exp(-iπψ)) < 0 via inline K₀ decomposition
  -- (Cannot use im_W_neg_of_intervalProp directly because the callback would need
  -- to handle arbitrary phases in (a, b), but we only know wPhaseOf < ψ for phases ≤ ψ-ε₀)
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_Y_neg : (ssf.W (K₀.of C Y) * rot).im < 0 := by
    obtain ⟨FY, hnY, hfirstY, hlastY⟩ :=
      HNFiltration.exists_both_nonzero C σ.slicing hYne
    -- All Y-phases are in (a, b) with φ ≤ ψ - ε₀
    have hphasesY : ∀ i : Fin FY.n,
        a < FY.φ i ∧ FY.φ i < b ∧ FY.φ i ≤ ψ - ε₀ := by
      intro i
      refine ⟨?_, ?_, ?_⟩
      · calc a < σ.slicing.phiMinus C Y hYne := hYminus
            _ = FY.φ ⟨FY.n - 1, by omega⟩ :=
              σ.slicing.phiMinus_eq C Y hYne FY hnY hlastY
            _ ≤ FY.φ i := FY.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
      · calc FY.φ i ≤ FY.φ ⟨0, hnY⟩ :=
              FY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C Y hYne :=
              (σ.slicing.phiPlus_eq C Y hYne FY hnY hfirstY).symm
            _ ≤ ψ - ε₀ := hYphiPlus
            _ < b := by linarith
      · calc FY.φ i ≤ FY.φ ⟨0, hnY⟩ :=
              FY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C Y hYne :=
              (σ.slicing.phiPlus_eq C Y hYne FY hnY hfirstY).symm
            _ ≤ ψ - ε₀ := hYphiPlus
    -- Each nonzero factor has Im(W · rot) < 0 (wPhaseOf < ψ from φ + ε₀ ≤ ψ)
    have hfactor_neg : ∀ (i : Fin FY.n),
        ¬IsZero (FY.toPostnikovTower.factor i) →
        (ssf.W (K₀.of C (FY.toPostnikovTower.factor i)) * rot).im < 0 := by
      intro i hi
      obtain ⟨hlo_pert, hhi_pert⟩ := hperturb _ _ (FY.semistable i) hi
        (hphasesY i).1 (hphasesY i).2.1
      exact im_neg_of_phase_below
        (norm_pos_iff.mpr (ssf.nonzero _ _ (hphasesY i).1 (hphasesY i).2.1
          (FY.semistable i) hi))
        (wPhaseOf_compat _ _)
        (by linarith [(hphasesY i).1]) (by linarith [(hphasesY i).2.2])
    -- K₀ decomposition: W(Y) = Σ W(Fⱼ)
    set PY := FY.toPostnikovTower
    rw [show ssf.W (K₀.of C Y) = ∑ i : Fin FY.n,
        ssf.W (K₀.of C (PY.factor i)) from by
      rw [K₀.of_postnikovTower_eq_sum C PY, map_sum],
      Finset.sum_mul, show (∑ i : Fin FY.n,
        ssf.W (K₀.of C (PY.factor i)) * rot).im =
        ∑ i : Fin FY.n, (ssf.W (K₀.of C (PY.factor i)) * rot).im from
      map_sum Complex.imAddGroupHom _ _]
    -- Negate: Σ (-Im) > 0 ⟹ Σ Im < 0
    suffices h : 0 < ∑ i : Fin FY.n,
        -(ssf.W (K₀.of C (PY.factor i)) * rot).im by
      linarith [Finset.sum_neg_distrib (G := ℝ) (s := Finset.univ)
        (f := fun i ↦ (ssf.W (K₀.of C (PY.factor i)) * rot).im)]
    apply lt_of_lt_of_le _ (Finset.single_le_sum
      (f := fun i ↦ -(ssf.W (K₀.of C (PY.factor i)) * rot).im)
      (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hnY⟩))
    · exact neg_pos.mpr (hfactor_neg ⟨0, hnY⟩ hfirstY)
    · by_cases hi : IsZero (PY.factor i)
      · simp [K₀.of_isZero C hi]
      · exact le_of_lt (neg_pos.mpr (hfactor_neg i hi))
  -- Im(W(E) · exp(-iπψ)) = 0 (since wPhaseOf(W(E)) = ψ)
  have him_E_zero : (ssf.W (K₀.of C E) * rot).im = 0 :=
    im_eq_zero_of_wPhaseOf_eq hψ
  -- K₀ additivity: W(K) + W(Y) = W(E)
  have hK₀ : ssf.W (K₀.of C K) + ssf.W (K₀.of C Y) = ssf.W (K₀.of C E) := by
    rw [← map_add]; congr 1
    exact (K₀.of_triangle C (Triangle.mk fK gY δ) hT).symm
  -- Case split on K
  by_cases hKZ : IsZero K
  · -- K = 0: W(Y) = W(E), so Im(W(E) · rot) < 0, contradicting Im = 0
    have hWK : ssf.W (K₀.of C K) = 0 := by rw [K₀.of_isZero C hKZ, map_zero]
    have hWY : ssf.W (K₀.of C Y) = ssf.W (K₀.of C E) := by
      have h := hK₀; rw [hWK, zero_add] at h; exact h
    rw [hWY] at him_Y_neg; linarith
  · -- K nonzero: Im(W(K) · rot) > 0 → wPhaseOf(W(K)) > ψ → contradicts semistability
    have him_K_pos := im_pos_of_sum_zero_and_neg hK₀ him_E_zero him_Y_neg
    -- wPhaseOf(W(K)) ∈ (ψ - 1, ψ + 1) via bounds on the original interval
    have hK_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C K)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hKZ ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) hKI hW_ne hperturb_gt
    have hK_hi : wPhaseOf (ssf.W (K₀.of C K)) ssf.α < b + ε₀ :=
      wPhaseOf_lt_of_intervalProp C σ hKZ ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.2])) hKI hW_ne hperturb_lt
    -- wPhaseOf(W(K)) > ψ (from Im > 0 + range condition)
    linarith [wPhaseOf_gt_of_im_pos him_K_pos
      (show wPhaseOf (ssf.W (K₀.of C K)) ssf.α ∈ Set.Ioo (ψ - 1) (ψ + 1) from
        ⟨by linarith, by linarith⟩),
      hsemistable hT hKI hYI hKZ]

variable [IsTriangulated C] in
/-- **Bridgeland's Lemma 7.3 (phase confinement).** If `E` is W-semistable of W-phase `ψ`
in `P((a, b))`, the interval is thin enough, and each nonzero semistable factor has W-phase
within `ε₀` of its σ-phase, then `σ.phiMinus(E) ∈ [ψ - ε₀, ψ + ε₀]` and
`σ.phiPlus(E) ∈ [ψ - ε₀, ψ + ε₀]`. In particular, the σ-phases of `E` are confined to
a window of width `2ε₀` centered at the W-phase `ψ`. -/
theorem phase_confinement_of_wSemistable
    (σ : StabilityCondition C) {E : C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {ψ : ℝ} (hSS : ssf.Semistable C E ψ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀) :
    ψ - ε₀ < σ.slicing.phiMinus C E hSS.2.1 ∧
    σ.slicing.phiPlus C E hSS.2.1 < ψ + ε₀ :=
  ⟨phiMinus_gt_of_wSemistable C σ hSS hε₀ hthin hperturb,
   phiPlus_lt_of_wSemistable C σ hSS hε₀ hthin hperturb⟩

variable [IsTriangulated C] in
/-- **Weak hom-vanishing for W-semistable objects.** If `E` is W-semistable of W-phase `ψ₁`
and `F` is W-semistable of W-phase `ψ₂` with `ψ₁ > ψ₂ + 2ε₀`, then `Hom(E, F) = 0`.

This follows from phase confinement: `E ∈ P((ψ₁-ε₀-δ, ψ₁+ε₀+δ))` and
`F ∈ P((ψ₂-ε₀-δ, ψ₂+ε₀+δ))`, and the intervals are disjoint when
`ψ₁ - ψ₂ > 2ε₀ + 2δ`. -/
theorem hom_eq_zero_of_wSemistable_gap
    (σ : StabilityCondition C) {E F : C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {ψ₁ ψ₂ : ℝ}
    (hE : ssf.Semistable C E ψ₁) (hF : ssf.Semistable C F ψ₂)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hperturb : ∀ (G : C) (φ : ℝ), (σ.slicing.P φ) G → ¬IsZero G →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C G)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C G)) ssf.α < φ + ε₀)
    (hgap : ψ₁ > ψ₂ + 2 * ε₀)
    (f : E ⟶ F) : f = 0 := by
  -- Phase confinement: intrinsic phases are within ε₀ of W-phases
  have ⟨hE_lo, hE_hi⟩ := phase_confinement_of_wSemistable C σ hE hε₀ hthin hperturb
  have ⟨hF_lo, hF_hi⟩ := phase_confinement_of_wSemistable C σ hF hε₀ hthin hperturb
  -- Choose δ > 0 small enough that the widened intervals are still disjoint
  set δ := (ψ₁ - ψ₂ - 2 * ε₀) / 4 with hδ_def
  have hδ_pos : 0 < δ := by linarith
  -- E ∈ P((ψ₁-ε₀-δ, ψ₁+ε₀+δ))
  have hEI : σ.slicing.intervalProp C (ψ₁ - ε₀ - δ) (ψ₁ + ε₀ + δ) E :=
    σ.slicing.intervalProp_of_intrinsic_phases C hE.2.1
      (by linarith) (by linarith)
  -- F ∈ P((ψ₂-ε₀-δ, ψ₂+ε₀+δ))
  have hFI : σ.slicing.intervalProp C (ψ₂ - ε₀ - δ) (ψ₂ + ε₀ + δ) F :=
    σ.slicing.intervalProp_of_intrinsic_phases C hF.2.1
      (by linarith) (by linarith)
  -- The gap: ψ₂+ε₀+δ ≤ ψ₁-ε₀-δ
  have hdisjoint : ψ₂ + ε₀ + δ ≤ ψ₁ - ε₀ - δ := by linarith
  -- Apply interval hom-vanishing
  exact σ.slicing.intervalHom_eq_zero C hEI hFI hdisjoint f

set_option maxHeartbeats 800000 in
variable [IsTriangulated C] in
/-- A nonzero strict quotient of a `W`-semistable interval object has `W`-phase at least
that of the middle term. This is the quotient-side semistability inequality needed for the
thin-interval HN recursion. -/
theorem SkewedStabilityFunction.phase_le_of_strictQuotient
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : σ.slicing.IntervalCat C a b} {ψ ε₀ : ℝ}
    (hX : ssf.Semistable C X.obj ψ)
    (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀)
    (p : X ⟶ Y) (hp : IsStrictEpi p)
    (hY : ¬IsZero Y.obj) :
    ψ ≤ wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α := by
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  let t := (σ.slicing.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := t.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := σ.slicing) a b (Fact.out : b - a ≤ 1)
  have hEpi : Epi ((S.map FL).g) := by
    simpa [S, FL] using
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) p hp
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S] using (kernelIsKernel p)
  have hKer :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExact : (S.map FL).Exact := ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKer
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
  have hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b → ssf.W (K₀.of C F) ≠ 0 :=
    fun F φ hP hFne haφ hφb ↦ ssf.nonzero F φ haφ hφb hP hFne
  have hperturb_gt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      a - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hperturb_lt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      b + ε₀ - 1 < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hψ_lo : a - ε₀ < ψ := by
    rw [← hX.2.2.2.1]
    exact wPhaseOf_gt_of_intervalProp C σ hX.2.1 ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hX.1 hW_ne hperturb_gt
  have hψ_hi : ψ < b + ε₀ := by
    rw [← hX.2.2.2.1]
    exact wPhaseOf_lt_of_intervalProp C σ hX.2.1 ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hX.1 hW_ne hperturb_lt
  by_cases hKz : IsZero (kernel p).obj
  · have hKz' : IsZero (kernel p) :=
      Slicing.IntervalCat.isZero_of_obj_isZero (C := C) (s := σ.slicing) (a := a) (b := b) hKz
    have hkernel_zero : kernel.ι p = 0 := zero_of_source_iso_zero _ hKz'.isoZero
    haveI : Mono p := Preadditive.mono_of_kernel_zero hkernel_zero
    haveI : IsIso p := IsStrictEpi.isIso hp
    let eC : X.obj ≅ Y.obj := ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
      (asIso p))
    rw [← hX.2.2.2.1, ← K₀.of_iso C eC]
  · have hK : ¬IsZero (kernel p).obj := hKz
    obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
      (C := C) (s := σ.slicing) (a := a) (b := b) hL
    have hK_le : wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α ≤ ψ :=
      hX.2.2.2.2 hT (kernel p).property Y.property hK
    have hK_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hK ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) (kernel p).property hW_ne hperturb_gt
    have hY_ne : ssf.W (K₀.of C Y.obj) ≠ 0 := hW_interval Y.property hY
    have hY_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hY ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) Y.property hW_ne hperturb_gt
    have hY_hi : wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α < b + ε₀ :=
      wPhaseOf_lt_of_intervalProp C σ hY ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.2])) Y.property hW_ne hperturb_lt
    have hadd :
        ssf.W (K₀.of C X.obj) =
          ssf.W (K₀.of C (kernel p).obj) + ssf.W (K₀.of C Y.obj) := by
      simpa [S, map_add] using
        congrArg ssf.W (K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT)
    exact wPhaseOf_seesaw
      hadd.symm
      hX.2.2.2.1
      ⟨by
          have : ψ - 1 < a - ε₀ := by
            have hmid : b + ε₀ - 1 < a - ε₀ := by linarith
            linarith
          linarith,
        hK_le⟩
      hY_ne
      ⟨by
          have : ψ - 1 < a - ε₀ := by
            have hmid : b + ε₀ - 1 < a - ε₀ := by linarith
            linarith
          linarith,
        by
          have hψ_up : b + ε₀ < ψ + 1 := by
            have hmid : b + ε₀ < a - ε₀ + 1 := by linarith
            linarith
          linarith⟩

set_option maxHeartbeats 800000 in
variable [IsTriangulated C] in
/-- A nonzero quotient term in a distinguished triangle of a `W`-semistable interval object
has `W`-phase at least that of the middle term, provided both outer terms remain in the same
thin interval. This is the triangle-form quotient inequality used when the quotient is
produced in an ambient heart rather than as an explicit strict quotient in the interval
category itself. -/
theorem SkewedStabilityFunction.phase_le_of_triangle_quotient
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {X K Y : C} {f₁ : K ⟶ X} {f₂ : X ⟶ Y} {f₃ : Y ⟶ K⟦(1 : ℤ)⟧} {ψ ε₀ : ℝ}
    (hX : ssf.Semistable C X ψ)
    (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀)
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C)
    (hKI : σ.slicing.intervalProp C a b K)
    (hYI : σ.slicing.intervalProp C a b Y)
    (hY : ¬IsZero Y) :
    ψ ≤ wPhaseOf (ssf.W (K₀.of C Y)) ssf.α := by
  have hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b → ssf.W (K₀.of C F) ≠ 0 :=
    fun F φ hP hFne haφ hφb ↦ ssf.nonzero F φ haφ hφb hP hFne
  have hperturb_gt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      a - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hperturb_lt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      b + ε₀ - 1 < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hψ_lo : a - ε₀ < ψ := by
    rw [← hX.2.2.2.1]
    exact wPhaseOf_gt_of_intervalProp C σ hX.2.1 ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hX.1 hW_ne hperturb_gt
  have hψ_hi : ψ < b + ε₀ := by
    rw [← hX.2.2.2.1]
    exact wPhaseOf_lt_of_intervalProp C σ hX.2.1 ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hX.1 hW_ne hperturb_lt
  by_cases hKz : IsZero K
  · haveI : IsIso f₂ :=
      (Triangle.isZero₁_iff_isIso₂ (Triangle.mk f₁ f₂ f₃) hT).mp hKz
    let eC : X ≅ Y := asIso f₂
    rw [← hX.2.2.2.1, ← K₀.of_iso C eC]
  · have hK_le : wPhaseOf (ssf.W (K₀.of C K)) ssf.α ≤ ψ :=
      hX.2.2.2.2 hT hKI hYI hKz
    have hK_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C K)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hKz ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) hKI hW_ne hperturb_gt
    have hY_ne : ssf.W (K₀.of C Y) ≠ 0 := hW_interval hYI hY
    have hY_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C Y)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hY ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) hYI hW_ne hperturb_gt
    have hY_hi : wPhaseOf (ssf.W (K₀.of C Y)) ssf.α < b + ε₀ :=
      wPhaseOf_lt_of_intervalProp C σ hY ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.2])) hYI hW_ne hperturb_lt
    have hadd :
        ssf.W (K₀.of C X) =
          ssf.W (K₀.of C K) + ssf.W (K₀.of C Y) := by
      simpa [map_add] using
        congrArg ssf.W (K₀.of_triangle C (Triangle.mk f₁ f₂ f₃) hT)
    exact wPhaseOf_seesaw
      hadd.symm
      hX.2.2.2.1
      ⟨by
          have : ψ - 1 < a - ε₀ := by
            have hmid : b + ε₀ - 1 < a - ε₀ := by linarith
            linarith
          linarith,
        hK_le⟩
      hY_ne
      ⟨by
          have : ψ - 1 < a - ε₀ := by
            have hmid : b + ε₀ - 1 < a - ε₀ := by linarith
            linarith
          linarith,
        by
          have : b + ε₀ < ψ + 1 := by
            have hmid : b + ε₀ < a - ε₀ + 1 := by linarith
            linarith
          linarith⟩

variable [IsTriangulated C] in
/-- **Phase confinement from stabSeminorm.** If `E` is W-semistable with W-phase `ψ` in a
thin interval `(a, b)` with `b - a + 2ε₀ < 1`, and `‖W - Z‖_σ < sin(πε₀)`, then
E's σ-phases are within `ε₀` of `ψ`:
`ψ - ε₀ ≤ phiMinus(E) ≤ phiPlus(E) ≤ ψ + ε₀`. -/
theorem phase_confinement_from_stabSeminorm
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a b : ℝ} (hab : a < b)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {ψ : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ) :
    ψ - ε₀ < σ.slicing.phiMinus C E hSS.2.1 ∧
    σ.slicing.phiPlus C E hSS.2.1 < ψ + ε₀ := by
  have hthin1 : b - a < 1 := by linarith
  exact phase_confinement_of_wSemistable C σ hSS hε₀ hthin
    (hperturb_of_stabSeminorm C σ W hW hthin1 hε₀ hε₀2 hsin)

theorem gtProp_of_wSemistable_phase_gt
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a b : ℝ} (hab : a < b)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {ψ t : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ)
    (hgt : t < ψ - ε₀) :
    σ.slicing.gtProp C t E := by
  have hE : ¬IsZero E := hSS.2.1
  have hconf := phase_confinement_from_stabSeminorm
    (C := C) (σ := σ) (W := W) (hW := hW) hab hε₀ hε₀2 hthin hsin hSS
  exact σ.slicing.gtProp_of_phiMinus_gt C hE (by linarith [hconf.1])

theorem ltProp_of_wSemistable_phase_lt
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a b : ℝ} (hab : a < b)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {ψ t : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ)
    (hlt : ψ + ε₀ < t) :
    σ.slicing.ltProp C t E := by
  have hE : ¬IsZero E := hSS.2.1
  have hconf := phase_confinement_from_stabSeminorm
    (C := C) (σ := σ) (W := W) (hW := hW) hab hε₀ hε₀2 hthin hsin hSS
  exact σ.slicing.ltProp_of_phiPlus_lt C hE (by linarith [hconf.2])

theorem wPhaseOf_eq_of_semistable_of_target_envelope
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a₁ b₁ : ℝ} (hab₁ : a₁ < b₁)
    {ψ : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    {a₂ b₂ ε₀ : ℝ} (hε₀ : 0 < ε₀) (henv₂_lo : a₂ + ε₀ ≤ ψ) (henv₂_hi : ψ ≤ b₂ - ε₀)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1) :
    wPhaseOf (W (K₀.of C E)) ((a₂ + b₂) / 2) = ψ := by
  have hbranch :
      wPhaseOf (W (K₀.of C E)) ((a₁ + b₁) / 2) ∈
        Set.Ioc (((a₂ + b₂) / 2) - 1) (((a₂ + b₂) / 2) + 1) := by
    have hpsi_branch : ψ ∈ Set.Ioc (((a₂ + b₂) / 2) - 1) (((a₂ + b₂) / 2) + 1) := by
      constructor
      · have hlo : ((a₂ + b₂) / 2) - 1 < a₂ + ε₀ := by
          by_contra h
          push_neg at h
          have hwidth : b₂ - a₂ < 1 - 2 * ε₀ := by
            linarith
          nlinarith
        exact lt_of_lt_of_le hlo henv₂_lo
      · have hhi : b₂ - ε₀ ≤ ((a₂ + b₂) / 2) + 1 := by
          by_contra h
          push_neg at h
          have hwidth : b₂ - a₂ < 1 - 2 * ε₀ := by
            linarith
          nlinarith
        exact le_trans henv₂_hi hhi
    have hwphase_eq :
        wPhaseOf (W (K₀.of C E)) ((a₁ + b₁) / 2) = ψ := by
      simpa [StabilityCondition.skewedStabilityFunction_of_near] using hSS.2.2.2.1
    simpa [hwphase_eq] using hpsi_branch
  have hEq :
      wPhaseOf (W (K₀.of C E)) ((a₁ + b₁) / 2) =
        wPhaseOf (W (K₀.of C E)) ((a₂ + b₂) / 2) :=
    wPhaseOf_indep hSS.2.2.1 _ _ hbranch
  calc
    wPhaseOf (W (K₀.of C E)) ((a₂ + b₂) / 2)
        = wPhaseOf (W (K₀.of C E)) ((a₁ + b₁) / 2) := hEq.symm
    _ = ψ := by
      simpa [StabilityCondition.skewedStabilityFunction_of_near] using hSS.2.2.2.1

theorem semistable_of_target_envelope_triangleTest
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a₁ b₁ : ℝ} (hab₁ : a₁ < b₁)
    {ψ : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    {a₂ b₂ : ℝ} (hab₂ : a₂ < b₂) (hI₂ : σ.slicing.intervalProp C a₂ b₂ E)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (henv₂_lo : a₂ + ε₀ ≤ ψ) (henv₂_hi : ψ ≤ b₂ - ε₀)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1)
    (htri : ∀ ⦃K Q : C⦄ ⦃f₁ : K ⟶ E⦄ ⦃f₂ : E ⟶ Q⦄ ⦃f₃ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
      Triangle.mk f₁ f₂ f₃ ∈ distTriang C →
      σ.slicing.intervalProp C a₂ b₂ K → σ.slicing.intervalProp C a₂ b₂ Q →
      ¬IsZero K →
      wPhaseOf (W (K₀.of C K)) ((a₂ + b₂) / 2) ≤ ψ) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  refine ⟨hI₂, hSS.2.1, hSS.2.2.1, ?_, htri⟩
  exact wPhaseOf_eq_of_semistable_of_target_envelope
    (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hSS hε₀ henv₂_lo henv₂_hi hthin₂

theorem stabSeminorm_lt_cos_of_hsin_hthin
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    {a b ε₀ : ℝ} (hab : a < b) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * (b - a) / 2)) := by
  have hsin_lt_cos : Real.sin (Real.pi * ε₀) <
      Real.cos (Real.pi * (b - a) / 2) := by
    rw [← Real.cos_pi_div_two_sub]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    · nlinarith [Real.pi_pos, hab]
    · nlinarith [Real.pi_pos, hthin]
    · nlinarith [Real.pi_pos, hε₀2]
  have hcos_pos : 0 < Real.cos (Real.pi * (b - a) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos, hab]
    · nlinarith [Real.pi_pos, hthin, hε₀]
  exact lt_trans hsin ((ENNReal.ofReal_lt_ofReal_iff hcos_pos).mpr hsin_lt_cos)

theorem wPhaseOf_eq_of_intervalProp_upper_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a b₁ b₂ ε₀ : ℝ} (hab₁ : a < b₁) (hb : b₁ ≤ b₂)
    {E : C} (hI : σ.slicing.intervalProp C a b₁ E) (hEne : ¬IsZero E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin₂ : b₂ - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    wPhaseOf (W (K₀.of C E)) ((a + b₁) / 2) =
      wPhaseOf (W (K₀.of C E)) ((a + b₂) / 2) := by
  have hthin₁ : b₁ - a + 2 * ε₀ < 1 := by
    linarith
  have hthin₁' : b₁ - a < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin₁' hε₀ hε₀2 hsin
  have hW_ne :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₁ → W (K₀.of C F) ≠ 0 := by
    intro F φ hP hFne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  have hpert_lo :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₁ →
        a - ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b₁) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b₁) / 2) < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hpert_hi :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₁ →
        b₁ + ε₀ - 1 < wPhaseOf (W (K₀.of C F)) ((a + b₁) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b₁) / 2) < b₁ + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hlo :
      a - ε₀ < wPhaseOf (W (K₀.of C E)) ((a + b₁) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_lo
  have hhi :
      wPhaseOf (W (K₀.of C E)) ((a + b₁) / 2) < b₁ + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_hi
  have hbranch :
      wPhaseOf (W (K₀.of C E)) ((a + b₁) / 2) ∈
        Set.Ioc (((a + b₂) / 2) - 1) (((a + b₂) / 2) + 1) := by
    constructor
    · linarith [hlo, hb, hthin₂]
    · linarith [hhi, hb, hthin₂]
  have hWneE : W (K₀.of C E) ≠ 0 := by
    exact σ.W_ne_zero_of_intervalProp C W hthin₁'
      (stabSeminorm_lt_cos_of_hsin_hthin
        (C := C) (σ := σ) (W := W) hab₁ hε₀ hε₀2 hthin₁ hsin) hEne hI
  exact wPhaseOf_indep hWneE _ _ hbranch

theorem wPhaseOf_eq_of_intervalProp_lower_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b ε₀ : ℝ} (ha₁ : a₁ < b) (ha₂ : a₂ < b) (ha : a₂ ≤ a₁)
    {E : C} (hI : σ.slicing.intervalProp C a₁ b E) (hEne : ¬IsZero E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin₂ : b - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    wPhaseOf (W (K₀.of C E)) ((a₁ + b) / 2) =
      wPhaseOf (W (K₀.of C E)) ((a₂ + b) / 2) := by
  have hthin₁ : b - a₁ + 2 * ε₀ < 1 := by
    linarith
  have hthin₁' : b - a₁ < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin₁' hε₀ hε₀2 hsin
  have hW_ne :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a₁ < φ → φ < b → W (K₀.of C F) ≠ 0 := by
    intro F φ hP hFne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  have hpert_lo :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a₁ < φ → φ < b →
        a₁ - ε₀ < wPhaseOf (W (K₀.of C F)) ((a₁ + b) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a₁ + b) / 2) < a₁ - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hpert_hi :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a₁ < φ → φ < b →
        b + ε₀ - 1 < wPhaseOf (W (K₀.of C F)) ((a₁ + b) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a₁ + b) / 2) < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hlo :
      a₁ - ε₀ < wPhaseOf (W (K₀.of C E)) ((a₁ + b) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_lo
  have hhi :
      wPhaseOf (W (K₀.of C E)) ((a₁ + b) / 2) < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_hi
  have hbranch :
      wPhaseOf (W (K₀.of C E)) ((a₁ + b) / 2) ∈
        Set.Ioc (((a₂ + b) / 2) - 1) (((a₂ + b) / 2) + 1) := by
    constructor
    · linarith [hlo, ha, hthin₂]
    · linarith [hhi, hthin₂]
  have hWneE : W (K₀.of C E) ≠ 0 := by
    exact σ.W_ne_zero_of_intervalProp C W hthin₁'
      (stabSeminorm_lt_cos_of_hsin_hthin
        (C := C) (σ := σ) (W := W) ha₁ hε₀ hε₀2 hthin₁ hsin) hEne hI
  exact wPhaseOf_indep hWneE _ _ hbranch

theorem wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a b ψ ε₀ : ℝ} {E : C}
    (hI : σ.slicing.intervalProp C a b E) (hEne : ¬IsZero E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    wPhaseOf (W (K₀.of C E)) ((a + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) := by
  have hab : a < b := by
    rcases hI with hEZ | ⟨F, hF⟩
    · exact absurd hEZ hEne
    · have hn : 0 < F.n := by
        by_contra hn
        exact hEne (F.toPostnikovTower.zero_isZero (by omega))
      linarith [(hF ⟨0, hn⟩).1, (hF ⟨0, hn⟩).2]
  have hthin' : b - a < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin' hε₀ hε₀2 hsin
  have hW_ne :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b → W (K₀.of C F) ≠ 0 := by
    intro F φ hP hFne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  have hpert_lo :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        a - ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hpert_hi :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        b + ε₀ - 1 < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hlo :
      a - ε₀ < wPhaseOf (W (K₀.of C E)) ((a + b) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_lo
  have hhi :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_hi
  constructor <;> linarith


end CategoryTheory.Triangulated
