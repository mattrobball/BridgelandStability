/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.PhaseArithmetic

/-!
# Deformation of Stability Conditions — PhaseConfinement

Phase confinement of W-semistable objects (Lemma 7.3)
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

/-! ### Node 7.3: Phase confinement of W-semistable objects -/

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
  -- Proof by contradiction (Bridgeland p.21: use top σ-factor)
  by_contra hgt; push_neg at hgt
  -- Set φ = phiPlus(E) ≥ ψ + ε₀
  set φ := σ.slicing.phiPlus C E hE with hφ_def
  have hφ_ge : ψ + ε₀ ≤ φ := hgt
  have hφ_lt_b : φ < b := σ.slicing.phiPlus_lt_of_intervalProp C hE hI
  have hφ_gt_a : a < φ := lt_of_lt_of_le
    (σ.slicing.phiMinus_gt_of_intervalProp C hE hI)
    (σ.slicing.phiMinus_le_phiPlus C E hE)
  -- Extract HN filtration
  obtain ⟨F, hF⟩ := hI.resolve_left hE
  have hn : 0 < F.n := F.n_pos C hE
  -- If E is σ-semistable of phase φ: perturbation gives wPhaseOf(W(E)) > φ-ε₀ ≥ ψ,
  -- contradicting hψ : wPhaseOf = ψ. (Handles both boundary and interior cases.)
  by_cases hsem : σ.slicing.P φ E
  · have ⟨hlo, _⟩ := hperturb E φ hsem hE hφ_gt_a hφ_lt_b
    linarith
  · -- E not σ-semistable at phase φ. Find the gap below φ in the HN phases.
    -- The top HN phase = φ (by phiPlus_eq). Since not semistable, there exists a
    -- strictly lower phase. Split at the gap to isolate the top-phase factors
    -- (all at phase φ), forming a σ-semistable K ∈ P(φ) with wPhaseOf(W(K)) > ψ.
    obtain ⟨F₀, hn₀, hne₀, hneL₀⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
    have hF₀_top : F₀.φ ⟨0, hn₀⟩ = φ := (σ.slicing.phiPlus_eq C E hE F₀ hn₀ hne₀).symm
    -- Not all HN phases equal φ (otherwise σ-semistable, contradicting hsem)
    have hexists_lower : ∃ j : Fin F₀.n, F₀.φ j < φ := by
      by_contra hall; push_neg at hall
      -- All phases ≥ φ (from hall) and ≤ φ (antitone from F₀.φ(0) = φ), so all = φ.
      -- phiPlus = phiMinus = φ, so E is σ-semistable via semistable_of_phiPlus_eq_phiMinus.
      have hall_eq : ∀ j : Fin F₀.n, F₀.φ j = φ := fun j ↦
        le_antisymm
          (hF₀_top ▸ F₀.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val)))
          (hall j)
      have hphiMin_le : σ.slicing.phiMinus C E hE ≤ φ :=
        σ.slicing.phiMinus_le_phiPlus C E hE
      have hphiMin_ge : φ ≤ σ.slicing.phiMinus C E hE := by
        have hge := σ.slicing.phiMinus_ge_phiMinus_of_hn C hE F₀ hn₀
        simp only [HNFiltration.phiMinus] at hge
        linarith [hall_eq ⟨F₀.n - 1, by omega⟩]
      have hphiMin : σ.slicing.phiMinus C E hE = φ := le_antisymm hphiMin_le hphiMin_ge
      have heq_plus_minus : σ.slicing.phiPlus C E hE = σ.slicing.phiMinus C E hE := by
        rw [hphiMin]
      have hsem' := σ.slicing.semistable_of_phiPlus_eq_phiMinus C hE heq_plus_minus
      -- hsem' : P(phiPlus) E = P(φ) E
      exact hsem hsem'
    -- Find maximum HN phase strictly below φ, then split at the midpoint of the gap.
    -- K contains only factors at phase φ → K is σ-semistable of phase φ.
    -- Perturbation gives wPhaseOf(W(K)) > φ-ε₀ ≥ ψ, contradicting W-semistability.
    classical
    let Slower := ((Finset.univ : Finset (Fin F₀.n)).image F₀.φ).filter (· < φ)
    have hSlower_ne : Slower.Nonempty := by
      obtain ⟨j_low, hj_low⟩ := hexists_lower
      exact ⟨F₀.φ j_low, Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨j_low, Finset.mem_univ _, rfl⟩, hj_low⟩⟩
    set m := Slower.max' hSlower_ne
    have hm_lt_φ : m < φ := (Finset.mem_filter.mp (Finset.max'_mem Slower hSlower_ne)).2
    -- No HN phase in (m, φ): m is the max of phases < φ
    have hgap : ∀ j : Fin F₀.n, F₀.φ j ≤ m ∨ F₀.φ j = φ := by
      intro j
      by_cases hj : F₀.φ j < φ
      · left; exact Finset.le_max' Slower (F₀.φ j)
          (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hj⟩)
      · right; push_neg at hj
        exact le_antisymm (hF₀_top ▸ F₀.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hj
    set t₀ := (m + φ) / 2
    have ht₀_lt : t₀ < φ := by simp only [t₀]; linarith
    have ht₀_gt : m < t₀ := by simp only [t₀]; linarith
    -- HN filtration F₀ has all phases in (a,b) (from hF transported via phiPlus/phiMinus)
    have hF₀_phases : ∀ i : Fin F₀.n, a < F₀.φ i ∧ F₀.φ i < b := by
      intro i
      constructor
      · -- F₀.φ(i) ≥ F₀.φ(n-1) (antitone) ≥ phiMinus(E) (phiMinus_ge) ≥ ... > a (intervalProp)
        -- Actually: a < phiMinus(E) ≤ phiPlus(E) ≤ F₀.φ(0) = φ, and F₀.φ(i) ≤ F₀.φ(0)
        -- For the LOWER bound: use hF (the OTHER HN filtration from intervalProp)
        -- hF gives ∀ j, a < F.φ j. And phiMinus(E) > a. And F₀.φ(i) ≥ F₀.phiMinus ≥ ?
        -- Simplest: use phiMinus_gt_of_intervalProp and phiMinus_le_phiPlus
        -- F₀.φ(i) ≥ F₀.φ(n-1) = F₀.phiMinus (by def)
        -- F₀.phiMinus ≥ F.phiMinus (by phiMinus_ge_of_nonzero_last_factor) ≥ hF(n-1).1 > a
        -- But this requires F to have nonzero last factor, etc. Just use intervalProp directly:
        have hge := σ.slicing.phiMinus_ge_phiMinus_of_hn C hE F₀ hn₀
        -- hge : F₀.phiMinus ≤ Slicing.phiMinus
        -- F₀.φ(i) ≥ F₀.phiMinus (antitone, i ≤ n-1)
        -- a < Slicing.phiMinus (intervalProp)
        -- So a < Slicing.phiMinus ≥ F₀.phiMinus = F₀.φ(n-1) ≤ F₀.φ(i)
        -- Wait, hge gives F₀.phiMinus ≤ Slicing.phiMinus, so F₀.φ(n-1) ≤ Slicing.phiMinus > a
        -- And F₀.φ(i) ≥ F₀.φ(n-1). So we need a < F₀.φ(n-1), which isn't directly available.
        -- Use: a < Slicing.phiMinus AND F₀.phiMinus ≤ Slicing.phiMinus doesn't give
        -- a < F₀.phiMinus. BUT: from hF (the intervalProp HN), a < F.φ j for all j.
        -- F.phiMinus > a (from hF). Slicing.phiMinus = F.phiMinus (by phiMinus_eq).
        -- F₀.phiMinus ≤ Slicing.phiMinus. Doesn't give F₀.phiMinus > a.
        -- INSTEAD: just use phiMinus_gt_of_intervalProp + phiMinus_le_phiPlus + antitone
        -- F₀.φ(i) ≤ F₀.φ(0) = φ < b (OK for upper bound)
        -- F₀.φ(i) ≥ F₀.φ(n-1) ≥ ? > a (need to show F₀.φ(n-1) > a)
        -- F₀.φ(n-1) = F₀.phiMinus. We know F₀.phiMinus ≤ Slicing.phiMinus.
        -- And Slicing.phiMinus > a. But F₀.phiMinus could be < a (e.g., a "bad" HN filtration
        -- with a zero last factor at an arbitrary phase).
        -- Actually NO: F₀ is a σ-HN filtration of E. Its factors are σ-semistable.
        -- Each factor F₀.factor(i) ∈ P(F₀.φ(i)). If F₀.φ(i) ≤ a, then F₀.factor(i) ∈ P(≤a)
        -- while E ∈ P((a,b)). By hom-vanishing, all maps from E to P(≤a) are zero...
        -- Actually, the HN filtration factors ARE in the intervalProp since the HN is derived
        -- from the intervalProp filtration. Each factor is σ-semistable with phase in (a,b).
        -- Use: σ.slicing.phiMinus_gt_of_intervalProp + monotonicity
        have hanti : F₀.φ ⟨F₀.n - 1, by omega⟩ ≤ F₀.φ i :=
          F₀.hφ.antitone (Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt i.isLt))
        have hphiMin_eq := σ.slicing.phiMinus_eq C E hE F₀ hn₀ hneL₀
        linarith [σ.slicing.phiMinus_gt_of_intervalProp C hE hI]
      · exact lt_of_le_of_lt
          (hF₀_top ▸ F₀.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val)))
          hφ_lt_b
    -- Split E at cutoff t₀ using tStructureAux directly (keeping phase containment)
    let Fs := F₀.phaseShift (C := C) t₀
    obtain ⟨K, Y, hKgt₀, hYle₀, fK, gY, δ, hT, hKdata⟩ :=
      Slicing.tStructureAux C (σ.slicing.phaseShift C t₀) E Fs
    have hKgt : σ.slicing.gtProp C t₀ K :=
      (σ.slicing.phaseShift_gtProp_zero C t₀ K).mp hKgt₀
    have hYle : σ.slicing.leProp C t₀ Y :=
      (σ.slicing.phaseShift_leProp_zero C t₀ Y).mp hYle₀
    have hKne : ¬IsZero K := by
      intro hKZ
      linarith [σ.slicing.phiPlus_le_of_leProp C hE
        (σ.slicing.leProp_of_triangle C t₀ (Or.inl hKZ) hYle hT)]
    rcases hKdata with hKZ | ⟨GX, hGXn, _, _, hGX_contain⟩
    · exact absurd hKZ hKne
    · -- GX phases (shifted back) are among F₀'s phases > t₀, which are all = φ by hgap.
      let GXorig : HNFiltration C σ.slicing.P K :=
        { n := GX.n, chain := GX.chain, triangle := GX.triangle
          triangle_dist := GX.triangle_dist, triangle_obj₁ := GX.triangle_obj₁
          triangle_obj₂ := GX.triangle_obj₂, base_isZero := GX.base_isZero
          top_iso := GX.top_iso, zero_isZero := GX.zero_isZero
          φ := fun j ↦ GX.φ j + t₀
          hφ := by intro i j hij; linarith [GX.hφ hij]
          semistable := fun j ↦ GX.semistable j }
      have hGXorig_phases_eq : ∀ j : Fin GXorig.n, GXorig.φ j = φ := by
        intro j
        obtain ⟨i_s, hi_eq⟩ := hGX_contain j
        have hGXj_eq : GXorig.φ j = F₀.φ ⟨i_s.val, i_s.isLt⟩ := by
          show GX.φ j + t₀ = F₀.φ ⟨i_s.val, i_s.isLt⟩
          have : Fs.φ i_s = F₀.φ ⟨i_s.val, i_s.isLt⟩ - t₀ := rfl
          linarith [hi_eq]
        rw [hGXj_eq]
        rcases hgap ⟨i_s.val, i_s.isLt⟩ with hle_m | heq_phase
        · -- F₀.φ i ≤ m, but GXorig.φ j > t₀ > m, contradiction
          have hj_gt_t₀ : GXorig.φ j > t₀ := by
            show GX.φ j + t₀ > t₀
            have hanti : GX.φ ⟨GX.n - 1, by omega⟩ ≤ GX.φ j :=
              GX.hφ.antitone (Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt j.isLt))
            simp only [HNFiltration.phiMinus] at *; linarith
          linarith
        · exact heq_phase
      -- K ∈ P(φ): phiPlus ≤ φ and phiMinus ≥ φ from GXorig having all phases = φ
      have hK_sem : σ.slicing.P φ K := by
        have hphiPlus_le : σ.slicing.phiPlus C K hKne ≤ φ := by
          have := σ.slicing.phiPlus_le_phiPlus_of_hn C hKne GXorig hGXn
          simp only [HNFiltration.phiPlus, hGXorig_phases_eq] at this; exact this
        have hphiMinus_ge : φ ≤ σ.slicing.phiMinus C K hKne := by
          have := σ.slicing.phiMinus_ge_phiMinus_of_hn C hKne GXorig hGXn
          simp only [HNFiltration.phiMinus, hGXorig_phases_eq] at this; exact this
        have heq := le_antisymm (le_trans hphiPlus_le hphiMinus_ge)
          (σ.slicing.phiMinus_le_phiPlus C K hKne)
        have hpe : σ.slicing.phiPlus C K hKne = φ :=
          le_antisymm hphiPlus_le (le_trans hphiMinus_ge (heq ▸ le_refl _))
        have hsem := σ.slicing.semistable_of_phiPlus_eq_phiMinus C hKne heq
        rwa [hpe] at hsem
      have hm_gt_a : a < m := by
        obtain ⟨j_m, _, hj_m_eq⟩ := Finset.mem_image.mp
          (Finset.mem_filter.mp (Finset.max'_mem Slower hSlower_ne)).1
        linarith [(hF₀_phases j_m).1]
      have hKI : σ.slicing.intervalProp C a b K :=
        σ.slicing.intervalProp_of_intrinsic_phases C hKne
          (by linarith [σ.slicing.phiMinus_gt_of_gtProp C hKne hKgt])
          (by linarith [(σ.slicing.phiPlus_eq_phiMinus_of_semistable C hK_sem hKne).1])
      have ⟨hlo, _⟩ := hperturb K φ hK_sem hKne (by linarith) hφ_lt_b
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
      -- W-semistability: wPhaseOf(W(K)) ≤ ψ. But wPhaseOf > φ-ε₀ ≥ ψ. Contradiction.
      linarith [hsemistable hT hKI hYI hKne]

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
    · -- Dual of upper bound: gap-split isolates bottom factors at ψ-ε₀.
      -- Y ∈ P(ψ-ε₀) via tStructureAux phase containment → perturbation → Im → contradiction.
      -- Part 1: gap-split isolates bottom factors at ψ-ε₀
      obtain ⟨F₀, hn₀, hne₀, hneL₀⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
      have hF₀_bot : F₀.φ ⟨F₀.n - 1, by omega⟩ = ψ - ε₀ := by
        linarith [σ.slicing.phiMinus_eq C E hE F₀ hn₀ hneL₀]
      -- Not all HN phases = ψ-ε₀ (otherwise E σ-semistable → contradiction)
      have hexists_upper : ∃ j : Fin F₀.n, ψ - ε₀ < F₀.φ j := by
        by_contra hall; push_neg at hall
        have hall_eq : ∀ j : Fin F₀.n, F₀.φ j = ψ - ε₀ := fun j ↦
          le_antisymm (hall j)
            (hF₀_bot ▸ F₀.hφ.antitone (Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt j.isLt)))
        have hphiPlus_le : σ.slicing.phiPlus C E hE ≤ ψ - ε₀ := by
          have := σ.slicing.phiPlus_le_phiPlus_of_hn C hE F₀ hn₀
          simp only [HNFiltration.phiPlus, hall_eq] at this; exact this
        have heq_pm : σ.slicing.phiPlus C E hE = σ.slicing.phiMinus C E hE := by
          linarith [σ.slicing.phiMinus_le_phiPlus C E hE]
        have hpe : σ.slicing.phiPlus C E hE = ψ - ε₀ :=
          le_antisymm hphiPlus_le (by linarith [σ.slicing.phiMinus_le_phiPlus C E hE])
        have hsem' := σ.slicing.semistable_of_phiPlus_eq_phiMinus C hE heq_pm
        rw [hpe] at hsem'; exact hsem hsem'
      -- Find gap: min phase above ψ-ε₀
      classical
      let Supper := ((Finset.univ : Finset (Fin F₀.n)).image F₀.φ).filter (ψ - ε₀ < ·)
      have hSupper_ne : Supper.Nonempty := by
        obtain ⟨j_up, hj_up⟩ := hexists_upper
        exact ⟨F₀.φ j_up, Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨j_up, Finset.mem_univ _, rfl⟩, hj_up⟩⟩
      set m_lo := Supper.min' hSupper_ne
      have hm_gt : ψ - ε₀ < m_lo :=
        (Finset.mem_filter.mp (Supper.min'_mem hSupper_ne)).2
      -- Gap: every HN phase is = ψ-ε₀ or ≥ m_lo
      have hgap : ∀ j : Fin F₀.n, F₀.φ j = ψ - ε₀ ∨ m_lo ≤ F₀.φ j := by
        intro j
        by_cases hj : ψ - ε₀ < F₀.φ j
        · right; exact Supper.min'_le (F₀.φ j)
            (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hj⟩)
        · left; push_neg at hj; exact le_antisymm hj
            (hF₀_bot ▸ F₀.hφ.antitone (Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt j.isLt)))
      set t_lo := ((ψ - ε₀) + m_lo) / 2
      have ht_lo_gt : ψ - ε₀ < t_lo := by simp only [t_lo]; linarith
      have ht_lo_lt : t_lo < m_lo := by simp only [t_lo]; linarith
      -- F₀ phases are in (a, b)
      have hF₀_phases : ∀ i : Fin F₀.n, a < F₀.φ i ∧ F₀.φ i < b := by
        intro i
        constructor
        · have hanti : F₀.φ ⟨F₀.n - 1, by omega⟩ ≤ F₀.φ i :=
            F₀.hφ.antitone (Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt i.isLt))
          have hphiMin_eq := σ.slicing.phiMinus_eq C E hE F₀ hn₀ hneL₀
          linarith [σ.slicing.phiMinus_gt_of_intervalProp C hE hI]
        · exact lt_of_le_of_lt
            (F₀.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val)))
            (by linarith [σ.slicing.phiPlus_eq C E hE F₀ hn₀ hne₀,
              σ.slicing.phiPlus_lt_of_intervalProp C hE hI])
      -- Split E at cutoff t_lo via tStructureAux
      let Fs := F₀.phaseShift (C := C) t_lo
      obtain ⟨K, Y, hKgt₀, hYle₀, fK, gY, δ, hT, hXdata, hYdata⟩ :=
        Slicing.tStructureAux C (σ.slicing.phaseShift C t_lo) E Fs
      have hKgt : σ.slicing.gtProp C t_lo K :=
        (σ.slicing.phaseShift_gtProp_zero C t_lo K).mp hKgt₀
      have hYle : σ.slicing.leProp C t_lo Y :=
        (σ.slicing.phaseShift_leProp_zero C t_lo Y).mp hYle₀
      -- K nonzero: F₀.φ(0) ≥ m_lo > t_lo, so phiPlus(E) > t_lo
      have hKne : ¬IsZero K := by
        intro hKZ
        have hE_le := σ.slicing.phiPlus_le_of_leProp C hE
          (σ.slicing.leProp_of_triangle C t_lo (Or.inl hKZ) hYle hT)
        obtain ⟨j_up, hj_up⟩ := hexists_upper
        have h0_gt : ψ - ε₀ < F₀.φ ⟨0, hn₀⟩ :=
          lt_of_lt_of_le hj_up (F₀.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _)))
        have h0_ge_m : m_lo ≤ F₀.φ ⟨0, hn₀⟩ := Supper.min'_le (F₀.φ ⟨0, hn₀⟩)
          (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
            ⟨⟨0, hn₀⟩, Finset.mem_univ _, rfl⟩, h0_gt⟩)
        linarith [σ.slicing.phiPlus_eq C E hE F₀ hn₀ hne₀]
      -- Y nonzero: phiMinus(E) = ψ-ε₀ < t_lo, contradicts gtProp
      have hYne : ¬IsZero Y := by
        intro hYZ
        linarith [σ.slicing.phiMinus_gt_of_gtProp C hE
          (σ.slicing.gtProp_of_triangle C t_lo hKgt (Or.inl hYZ) hT)]
      -- Extract X data (for K's phiPlus bound)
      obtain hKZ | ⟨GX, hGXn', hGX_pos, hGX_upper, hGX_contain'⟩ := hXdata
      · exact absurd hKZ hKne
      -- Extract Y data (for Y ∈ P(ψ-ε₀))
      obtain hYZ | ⟨GY, hGYn, hGY_le, hGY_contain⟩ := hYdata
      · exact absurd hYZ hYne
      -- GYorig: shift GY phases back to σ.slicing
      let GYorig : HNFiltration C σ.slicing.P Y :=
        { n := GY.n, chain := GY.chain, triangle := GY.triangle
          triangle_dist := GY.triangle_dist, triangle_obj₁ := GY.triangle_obj₁
          triangle_obj₂ := GY.triangle_obj₂, base_isZero := GY.base_isZero
          top_iso := GY.top_iso, zero_isZero := GY.zero_isZero
          φ := fun j ↦ GY.φ j + t_lo
          hφ := by intro i j hij; linarith [GY.hφ hij]
          semistable := fun j ↦ GY.semistable j }
      -- All GYorig phases = ψ-ε₀ (gap + containment)
      have hGYorig_phases_eq : ∀ j : Fin GYorig.n, GYorig.φ j = ψ - ε₀ := by
        intro j
        obtain ⟨i_s, hi_eq⟩ := hGY_contain j
        have hGYj_eq : GYorig.φ j = F₀.φ ⟨i_s.val, i_s.isLt⟩ := by
          show GY.φ j + t_lo = F₀.φ ⟨i_s.val, i_s.isLt⟩
          have : Fs.φ i_s = F₀.φ ⟨i_s.val, i_s.isLt⟩ - t_lo := rfl
          linarith [hi_eq]
        rw [hGYj_eq]
        rcases hgap ⟨i_s.val, i_s.isLt⟩ with heq_phase | hge_m
        · exact heq_phase
        · exfalso
          have hGY_unfold : GYorig.φ j = GY.φ j + t_lo := rfl
          have hle_top : GY.φ j ≤ GY.φ ⟨0, hGYn⟩ :=
            GY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val))
          simp only [HNFiltration.phiPlus] at hGY_le
          linarith
      -- Y ∈ P(ψ-ε₀): all HN phases equal → semistable
      have hY_sem : σ.slicing.P (ψ - ε₀) Y := by
        have hphiPlus_le : σ.slicing.phiPlus C Y hYne ≤ ψ - ε₀ := by
          have := σ.slicing.phiPlus_le_phiPlus_of_hn C hYne GYorig hGYn
          simp only [HNFiltration.phiPlus, hGYorig_phases_eq] at this; exact this
        have hphiMinus_ge : ψ - ε₀ ≤ σ.slicing.phiMinus C Y hYne := by
          have := σ.slicing.phiMinus_ge_phiMinus_of_hn C hYne GYorig hGYn
          simp only [HNFiltration.phiMinus, hGYorig_phases_eq] at this; exact this
        have heq_pm := le_antisymm (le_trans hphiPlus_le hphiMinus_ge)
          (σ.slicing.phiMinus_le_phiPlus C Y hYne)
        have hpe : σ.slicing.phiPlus C Y hYne = ψ - ε₀ :=
          le_antisymm hphiPlus_le (le_trans hphiMinus_ge (heq_pm ▸ le_refl _))
        have hsem_Y := σ.slicing.semistable_of_phiPlus_eq_phiMinus C hYne heq_pm
        rwa [hpe] at hsem_Y
      -- GXorig: shift GX phases back for K's phiPlus bound
      let GXorig : HNFiltration C σ.slicing.P K :=
        { n := GX.n, chain := GX.chain, triangle := GX.triangle
          triangle_dist := GX.triangle_dist, triangle_obj₁ := GX.triangle_obj₁
          triangle_obj₂ := GX.triangle_obj₂, base_isZero := GX.base_isZero
          top_iso := GX.top_iso, zero_isZero := GX.zero_isZero
          φ := fun j ↦ GX.φ j + t_lo
          hφ := by intro i j hij; linarith [GX.hφ hij]
          semistable := fun j ↦ GX.semistable j }
      have hKphiPlus_lt_b : σ.slicing.phiPlus C K hKne < b := by
        have hle := σ.slicing.phiPlus_le_phiPlus_of_hn C hKne GXorig hGXn'
        have h_upper := hGX_upper hn₀
        simp only [HNFiltration.phiPlus] at hle h_upper
        have : (GXorig.φ ⟨0, hGXn'⟩ : ℝ) = GX.φ ⟨0, hGXn'⟩ + t_lo := rfl
        have : (Fs.φ ⟨0, hn₀⟩ : ℝ) = F₀.φ ⟨0, hn₀⟩ - t_lo := rfl
        linarith [(hF₀_phases ⟨0, hn₀⟩).2]
      -- K ∈ P((a, b))
      have hKI : σ.slicing.intervalProp C a b K :=
        σ.slicing.intervalProp_of_intrinsic_phases C hKne
          (by linarith [σ.slicing.phiMinus_gt_of_gtProp C hKne hKgt])
          hKphiPlus_lt_b
      -- Y ∈ P((a, b))
      have hYI : σ.slicing.intervalProp C a b Y :=
        σ.slicing.intervalProp_of_intrinsic_phases C hYne
          (by linarith [(σ.slicing.phiPlus_eq_phiMinus_of_semistable C hY_sem hYne).2])
          (by linarith [(σ.slicing.phiPlus_eq_phiMinus_of_semistable C hY_sem hYne).1])
      -- Part 2: Im argument → contradiction
      set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
      -- Im(W(Y)·rot) < 0: Y ∈ P(ψ-ε₀) with wPhaseOf(W(Y)) < ψ
      have ⟨hlo_Y, hhi_Y⟩ := hperturb Y (ψ - ε₀) hY_sem hYne hψε_gt_a hψε_lt_b
      have him_Y_neg : (ssf.W (K₀.of C Y) * rot).im < 0 :=
        im_neg_of_phase_below
          (norm_pos_iff.mpr (ssf.nonzero Y (ψ - ε₀) hψε_gt_a hψε_lt_b hY_sem hYne))
          (wPhaseOf_compat _ _)
          (by linarith) (by linarith)
      -- Im(W(E)·rot) = 0 (wPhaseOf(W(E)) = ψ)
      have him_E_zero : (ssf.W (K₀.of C E) * rot).im = 0 :=
        im_eq_zero_of_wPhaseOf_eq hψ
      -- K₀ additivity: W(K) + W(Y) = W(E)
      have hK₀ : ssf.W (K₀.of C K) + ssf.W (K₀.of C Y) = ssf.W (K₀.of C E) := by
        rw [← map_add]; congr 1
        exact (K₀.of_triangle C (Triangle.mk fK gY δ) hT).symm
      -- Im(W(K)·rot) > 0 → wPhaseOf(W(K)) > ψ → contradicts W-semistability
      have him_K_pos := im_pos_of_sum_zero_and_neg hK₀ him_E_zero him_Y_neg
      have hK_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C K)) ssf.α :=
        wPhaseOf_gt_of_intervalProp C σ hKne ssf.W
          (le_of_lt (by linarith [ssf.hα_mem.1])) hKI hW_ne hperturb_gt
      have hK_hi : wPhaseOf (ssf.W (K₀.of C K)) ssf.α < b + ε₀ :=
        wPhaseOf_lt_of_intervalProp C σ hKne ssf.W
          (le_of_lt (by linarith [ssf.hα_mem.2])) hKI hW_ne hperturb_lt
      linarith [wPhaseOf_gt_of_im_pos him_K_pos
        (show wPhaseOf (ssf.W (K₀.of C K)) ssf.α ∈ Set.Ioo (ψ - 1) (ψ + 1) from
          ⟨by linarith, by linarith⟩),
        hsemistable hT hKI hYI hKne]
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
          linarith, by
          have hψ_up : b + ε₀ < ψ + 1 := by
            have hmid : b + ε₀ < a - ε₀ + 1 := by linarith
            linarith
          linarith⟩

set_option maxHeartbeats 800000 in
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
          linarith, by
          have : b + ε₀ < ψ + 1 := by
            have hmid : b + ε₀ < a - ε₀ + 1 := by linarith
            linarith
          linarith⟩


end CategoryTheory.Triangulated
