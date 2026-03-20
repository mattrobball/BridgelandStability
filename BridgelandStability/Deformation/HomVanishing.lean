/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.Deformation.StrictSES
import BridgelandStability.Deformation.BoundaryTriangles

/-!
# Deformation of Stability Conditions — HomVanishing

Deformed predicate and sharp hom-vanishing for Q (Lemma 7.6)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### Deformed slicing predicate -/

/-- **Deformed slicing predicate** (Node 7.Q). Given a stability condition `σ`, a
perturbation `W` with `‖W - Z‖_σ < sin(πε₀)`, the deformed slicing `Q(ψ)` consists of
zero objects and objects that are W-semistable of W-phase `ψ` in some thin interval
`P((a, b))` with `b - a + 2ε₀ < 1` and the **enveloping condition** `a + ε₀ ≤ ψ ≤ b - ε₀`.
The thinness constraint ensures phase confinement (Node 7.3) is always available.
The enveloping condition (matching Bridgeland §7) ensures the object's W-phase is well
inside the interval, which is needed for heart factorization arguments in hom-vanishing
(Lemma 7.6) and interval independence (Lemma 7.5). -/
def StabilityCondition.deformedPred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (_hε₀ : 0 < ε₀) (_hε₀2 : ε₀ < 1 / 4)
    (_hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (ψ : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (a b : ℝ) (hab : a < b) (_ : b - a + 2 * ε₀ < 1)
    (_ : a + ε₀ ≤ ψ) (_ : ψ ≤ b - ε₀),
    (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ

/-- Zero objects are in every `Q(ψ)`. -/
lemma StabilityCondition.deformedPred_zero (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (ψ : ℝ) {E : C} (hE : IsZero E) :
    σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ E :=
  Or.inl hE

lemma StabilityCondition.deformedPred_closedUnderIso (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (ψ : ℝ) :
    (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ).IsClosedUnderIsomorphisms := by
  constructor
  intro E E' e h
  rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
  · exact Or.inl ((Iso.isZero_iff e).mp hZ)
  · refine Or.inr ⟨a, b, hab, hthin, henv_lo, henv_hi, ?_, ?_, ?_, ?_,
      fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
    · rcases hSS.1 with hZ' | ⟨F, hF⟩
      · exact absurd hZ' hSS.2.1
      · exact Or.inr ⟨F.ofIso C e, hF⟩
    · exact fun hE' ↦ hSS.2.1 ((Iso.isZero_iff e.symm).mp hE')
    · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
      exact hSS.2.2.1
    · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
      exact hSS.2.2.2.1
    · have hT' : Triangle.mk (f₁ ≫ e.inv) (e.hom ≫ f₂) f₃ ∈ distTriang C :=
        isomorphic_distinguished _ hT _
          (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
            (by simp) (by simp) (by simp))
      exact hSS.2.2.2.2 hT' hK hQ hKne

variable [IsTriangulated C] in
theorem gtProp_of_lt_phiMinus_smallGap
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : t < s.phiMinus C E hE) :
    s.gtProp C t E := by
  obtain ⟨F, hn, hlast⟩ := HNFiltration.exists_nonzero_last C s hE
  refine s.gtProp_of_hn C F t (fun j ↦ ?_) hn
  calc
    t < s.phiMinus C E hE := h
    _ = F.φ ⟨F.n - 1, by omega⟩ := s.phiMinus_eq C E hE F hn hlast
    _ ≤ F.φ j := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))

variable [IsTriangulated C] in
theorem leProp_of_phiPlus_le_smallGap
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : s.phiPlus C E hE ≤ t) :
    s.leProp C t E := by
  obtain ⟨F, hn, hfirst⟩ := HNFiltration.exists_nonzero_first C s hE
  refine s.leProp_of_hn C F t (fun j ↦ ?_) hn
  calc
    F.φ j ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val))
    _ = s.phiPlus C E hE := (s.phiPlus_eq C E hE F hn hfirst).symm
    _ ≤ t := h

variable [IsTriangulated C] in
theorem geProp_of_phiMinus_ge_smallGap
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : t ≤ s.phiMinus C E hE) :
    s.geProp C t E := by
  obtain ⟨F, hn, hlast⟩ := HNFiltration.exists_nonzero_last C s hE
  refine s.geProp_of_hn C F t (fun j ↦ ?_) hn
  calc
    t ≤ s.phiMinus C E hE := h
    _ = F.φ ⟨F.n - 1, by omega⟩ := s.phiMinus_eq C E hE F hn hlast
    _ ≤ F.φ j := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))

variable [IsTriangulated C] in
theorem mem_phaseShiftHeart_of_phaseBounds_smallGap
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (hgt : t < s.phiMinus C E hE)
    (hle : s.phiPlus C E hE ≤ t + 1) :
    ((s.phaseShift C t).toTStructure).heart E := by
  let ss := s.phaseShift C t
  let u := ss.toTStructure
  have cast_le : (-↑(0 : ℤ) : ℝ) = 0 := by simp
  have cast_ge : (1 - ↑(0 : ℤ) : ℝ) = 1 := by simp
  have hE_gt : s.gtProp C t E :=
    gtProp_of_lt_phiMinus_smallGap (C := C) (s := s) hE hgt
  have hE_le : s.leProp C (t + 1) E :=
    leProp_of_phiPlus_le_smallGap (C := C) (s := s) hE hle
  have hE_le' : s.leProp C (1 + t) E := by
    simpa [add_comm] using hE_le
  haveI : u.IsLE E 0 := ⟨by
    change ss.gtProp C (-↑(0 : ℤ)) E
    rw [cast_le]
    simpa [ss] using (s.phaseShift_gtProp_zero C t E).mpr hE_gt⟩
  haveI : u.IsGE E 0 := ⟨by
    change ss.leProp C (1 - ↑(0 : ℤ)) E
    rw [cast_ge]
    simpa [ss] using (s.phaseShift_leProp C t 1 E).mpr hE_le'⟩
  exact (u.mem_heart_iff E).mpr ⟨inferInstance, inferInstance⟩

variable [IsTriangulated C] in
theorem gtProp_leProp_of_phaseShiftHeart
    (s : Slicing C) {E : C} {a u : ℝ}
    (hHeart : ((s.phaseShift C a).toTStructure).heart E)
    (hE : ¬IsZero E)
    (hu : s.phiPlus C E hE ≤ u) :
    s.gtProp C a E ∧ s.leProp C u E := by
  have hHeart' := hHeart
  rw [(s.phaseShift C a).toTStructure_heart_iff] at hHeart'
  constructor
  · exact (s.phaseShift_gtProp_zero C a E).mp hHeart'.1
  · exact leProp_of_phiPlus_le_smallGap (C := C) (s := s) hE hu

variable [IsTriangulated C] in
theorem geProp_leProp_of_phaseShiftHeart
    (s : Slicing C) {E : C} {a l : ℝ}
    (hHeart : ((s.phaseShift C a).toTStructure).heart E)
    (hE : ¬IsZero E)
    (hl : l ≤ s.phiMinus C E hE) :
    s.geProp C l E ∧ s.leProp C (a + 1) E := by
  have hHeart' := hHeart
  rw [(s.phaseShift C a).toTStructure_heart_iff] at hHeart'
  constructor
  · exact geProp_of_phiMinus_ge_smallGap (C := C) (s := s) hE hl
  · have hle : s.leProp C (1 + a) E := by
      simpa [add_comm] using
        (s.phaseShift_leProp C a 1 E).mp hHeart'.2
    simpa [add_comm] using hle

theorem midpoint_left_target_thin
    {ψ₁ ψ₂ ε₀ : ℝ} (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀) (hε₀8 : ε₀ < 1 / 8) :
    (ψ₁ + ε₀) - ((ψ₁ + ψ₂) / 2 - 1 / 2) + 2 * ε₀ < 1 := by
  linarith

theorem midpoint_right_target_thin
    {ψ₁ ψ₂ ε₀ : ℝ} (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀) (hε₀8 : ε₀ < 1 / 8) :
    (((ψ₁ + ψ₂) / 2 - 1 / 2) + 1) - (ψ₂ - ε₀) + 2 * ε₀ < 1 := by
  linarith

theorem midpoint_image_window_thin
    {ψ₁ ψ₂ ε₀ : ℝ} (hgap : ψ₂ < ψ₁) (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀)
    (hε₀8 : ε₀ < 1 / 8) :
    (ψ₂ + ε₀) - (ψ₁ - ε₀) + 2 * ε₀ < 1 := by
  linarith

variable [IsTriangulated C] in
theorem mem_phaseShiftHeart_of_midpoint_left
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {ψ₁ ψ₂ ε₀ : ℝ}
    (hlo : ψ₁ - ε₀ ≤ s.phiMinus C E hE)
    (hhi : s.phiPlus C E hE ≤ ψ₁ + ε₀)
    (hgap : ψ₂ < ψ₁) (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀) (hε₀4 : ε₀ < 1 / 4) :
    (((s.phaseShift C ((ψ₁ + ψ₂) / 2 - 1 / 2)).toTStructure).heart E) := by
  refine mem_phaseShiftHeart_of_phaseBounds_smallGap (C := C) (s := s) hE ?_ ?_
  · have hmid : (ψ₁ + ψ₂) / 2 - 1 / 2 < s.phiMinus C E hE := by
      have h' : (ψ₁ + ψ₂) / 2 - 1 / 2 < ψ₁ - ε₀ := by
        linarith [hgap, hε₀4]
      exact lt_of_lt_of_le h' hlo
    exact hmid
  · have hmid : s.phiPlus C E hE ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
      have h' : ψ₁ + ε₀ ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
        linarith [hsmall, hε₀4]
      exact le_trans hhi h'
    exact hmid

variable [IsTriangulated C] in
theorem mem_phaseShiftHeart_of_midpoint_right
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {ψ₁ ψ₂ ε₀ : ℝ}
    (hlo : ψ₂ - ε₀ ≤ s.phiMinus C E hE)
    (hhi : s.phiPlus C E hE ≤ ψ₂ + ε₀)
    (hgap : ψ₂ < ψ₁) (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀) (hε₀4 : ε₀ < 1 / 4) :
    (((s.phaseShift C ((ψ₁ + ψ₂) / 2 - 1 / 2)).toTStructure).heart E) := by
  refine mem_phaseShiftHeart_of_phaseBounds_smallGap (C := C) (s := s) hE ?_ ?_
  · have hmid : (ψ₁ + ψ₂) / 2 - 1 / 2 < s.phiMinus C E hE := by
      have h' : (ψ₁ + ψ₂) / 2 - 1 / 2 < ψ₂ - ε₀ := by
        linarith [hsmall, hε₀4]
      exact lt_of_lt_of_le h' hlo
    exact hmid
  · have hmid : s.phiPlus C E hE ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
      have h' : ψ₂ + ε₀ ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
        linarith [hgap, hε₀4]
      exact le_trans hhi h'
    exact hmid

/-! ### Sharp hom-vanishing for Q (Node 7.6) -/

variable [IsTriangulated C] in
/-- **Sharp hom-vanishing for Q** (**Bridgeland's Lemma 7.6**). If `E ∈ Q(ψ₁)` and
`F ∈ Q(ψ₂)` with `ψ₁ > ψ₂`, then every morphism `E → F` is zero.

**Proof outline.** Two cases:
- **Large gap** (`ψ₁ > ψ₂ + 2ε₀`): Phase confinement
  (`phase_confinement_from_stabSeminorm`) puts `E` and `F` in disjoint σ-intervals,
  so `intervalHom_eq_zero` applies (cf. `hom_eq_zero_of_wSemistable_gap`).
- **Small gap** (`ψ₁ - ψ₂ ≤ 2ε₀`): Embed both `E, F` in the abelian heart
  `P((c, c+1])` of a σ-t-structure. Factor `f` as `E ↠ im(f) ↪ F`.
  F's W-semistability (weakened to only require `K ∈ P((a,b))`, not `Q`) gives
  `wPhaseOf(W(im(f))) ≤ ψ₂`. The K₀ identity `W(E) = W(ker(f)) + W(im(f))`
  with `phase(W(E)) = ψ₁ > ψ₂` forces `phase(W(ker(f))) > ψ₁`, contradicting
  E's W-semistability.

**Remaining blockers**: Both cases require **Lemma 7.5** (interval independence)
to place E and F in a common thin interval. Additionally, the small-gap case
requires abelian heart factorization and K₀ arithmetic in the heart. -/
theorem StabilityCondition.hom_eq_zero_of_deformedPred
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E F : C} {ψ₁ ψ₂ : ℝ}
    (hE : σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ₁ E)
    (hF : σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ₂ F)
    (hgap : ψ₁ > ψ₂)
    (f : E ⟶ F) : f = 0 := by
  -- Dispatch IsZero cases
  rcases hE with hEZ | ⟨a₁, b₁, hab₁, hthin₁, henv₁_lo, henv₁_hi, hSS₁⟩
  · exact hEZ.eq_of_src f 0
  rcases hF with hFZ | ⟨a₂, b₂, hab₂, hthin₂, henv₂_lo, henv₂_hi, hSS₂⟩
  · exact hFZ.eq_of_tgt f 0
  -- Both nonzero: E is W-semistable on (a₁, b₁) with phase ψ₁,
  -- F is W-semistable on (a₂, b₂) with phase ψ₂.
  -- Phase confinement: E's σ-phases ∈ [ψ₁ - ε₀, ψ₁ + ε₀],
  -- F's σ-phases ∈ [ψ₂ - ε₀, ψ₂ + ε₀]
  have ⟨hE_lo, hE_hi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab₁
    hε₀ hε₀2 hthin₁ hsin hSS₁
  have ⟨hF_lo, hF_hi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab₂
    hε₀ hε₀2 hthin₂ hsin hSS₂
  -- Large gap: E and F lie in disjoint σ-intervals
  set δ := (ψ₁ - ψ₂ - 2 * ε₀) / 4 with hδ_def
  -- Note: if ψ₁ - ψ₂ ≤ 2ε₀, then δ ≤ 0. We still proceed since
  -- intervalProp_of_intrinsic_phases and intervalHom_eq_zero work
  -- with any parameters.
  -- E ∈ P((ψ₁ - ε₀ - (ψ₁-ψ₂)/2, ψ₁ + ε₀ + (ψ₁-ψ₂)/2))
  -- But we use a tighter interval: E ∈ P((ψ₂ + ε₀, ...)) is wrong.
  -- Instead, use direct computation:
  -- ψ₂ + ε₀ < ψ₁ - ε₀ is equivalent to ψ₁ - ψ₂ > 2ε₀.
  -- When this holds, the σ-intervals [ψ₂-ε₀, ψ₂+ε₀] and [ψ₁-ε₀, ψ₁+ε₀] are disjoint.
  by_cases hlargeGap : ψ₁ > ψ₂ + 2 * ε₀
  · -- Large gap: disjoint σ-intervals
    set δ' := (ψ₁ - ψ₂ - 2 * ε₀) / 4 with hδ'_def
    have hδ'_pos : 0 < δ' := by linarith
    have hEI : σ.slicing.intervalProp C (ψ₁ - ε₀ - δ') (ψ₁ + ε₀ + δ') E :=
      σ.slicing.intervalProp_of_intrinsic_phases C hSS₁.2.1
        (by linarith) (by linarith)
    have hFI : σ.slicing.intervalProp C (ψ₂ - ε₀ - δ') (ψ₂ + ε₀ + δ') F :=
      σ.slicing.intervalProp_of_intrinsic_phases C hSS₂.2.1
        (by linarith) (by linarith)
    have hdisjoint : ψ₂ + ε₀ + δ' ≤ ψ₁ - ε₀ - δ' := by
      simp only [hδ'_def]; linarith
    exact σ.slicing.intervalHom_eq_zero C hEI hFI hdisjoint f
  · -- Small gap: 0 < ψ₁ - ψ₂ ≤ 2ε₀.
    -- Faithful Lemma 7.6 route:
    -- choose the midpoint heart A = P((a,a+1]) with a = (ψ₁ + ψ₂)/2 - 1/2,
    -- factor f in A, then compare the image in the paper's two thin target windows
    -- P((a, ψ₁ + ε₀)) and P((ψ₂ - ε₀, a + 1)).
    push_neg at hlargeGap
    by_cases hf : f = 0
    · exact hf
    · set a : ℝ := (ψ₁ + ψ₂) / 2 - 1 / 2
      have hsmallGap : ψ₁ ≤ ψ₂ + 2 * ε₀ := hlargeGap
      have hleftThin : (ψ₁ + ε₀) - a + 2 * ε₀ < 1 := by
        simpa [a] using midpoint_left_target_thin (ψ₁ := ψ₁) (ψ₂ := ψ₂) hsmallGap hε₀8
      have hrightThin : (a + 1) - (ψ₂ - ε₀) + 2 * ε₀ < 1 := by
        simpa [a] using midpoint_right_target_thin (ψ₁ := ψ₁) (ψ₂ := ψ₂) hsmallGap hε₀8
      have himageThin : (ψ₂ + ε₀) - (ψ₁ - ε₀) + 2 * ε₀ < 1 := by
        exact midpoint_image_window_thin (ψ₁ := ψ₁) (ψ₂ := ψ₂) hgap hsmallGap hε₀8
      set ss := σ.slicing.phaseShift C a
      let t := ss.toTStructure
      have hE_heart : t.heart E := by
        simpa [t, ss, a] using
          mem_phaseShiftHeart_of_midpoint_left (C := C) (s := σ.slicing) hSS₁.2.1
            (le_of_lt hE_lo) (le_of_lt hE_hi) hgap hsmallGap hε₀2
      have hF_heart : t.heart F := by
        simpa [t, ss, a] using
          mem_phaseShiftHeart_of_midpoint_right (C := C) (s := σ.slicing) hSS₂.2.1
            (le_of_lt hF_lo) (le_of_lt hF_hi) hgap hsmallGap hε₀2
      have hE_window :
          σ.slicing.gtProp C a E ∧ σ.slicing.leProp C (ψ₁ + ε₀) E := by
        exact gtProp_leProp_of_phaseShiftHeart (C := C) (s := σ.slicing)
          (a := a) hE_heart hSS₁.2.1 (le_of_lt hE_hi)
      have hF_window :
          σ.slicing.geProp C (ψ₂ - ε₀) F ∧ σ.slicing.leProp C (a + 1) F := by
        exact geProp_leProp_of_phaseShiftHeart (C := C) (s := σ.slicing)
          (a := a) hF_heart hSS₂.2.1 (le_of_lt hF_lo)
      have habE_left_src : a₁ < ψ₁ + ε₀ := by
        linarith [henv₁_lo]
      have hE_upper : σ.slicing.intervalProp C a₁ (ψ₁ + ε₀) E := by
        exact intervalProp_of_wSemistable_upper_target
          (C := C) (σ := σ) (W := W) (hW := hW) habE_left_src hab₁
          (by linarith [henv₁_hi]) hSS₁ hε₀ hε₀2 henv₁_lo (by linarith) hthin₁ hsin
      have habE_left : a < ψ₁ + ε₀ := by
        linarith
      have hE_left : σ.slicing.intervalProp C a (ψ₁ + ε₀) E := by
        exact σ.slicing.intervalProp_of_intrinsic_phases C hSS₁.2.1
          (σ.slicing.phiMinus_gt_of_gtProp C hSS₁.2.1 hE_window.1)
          (σ.slicing.phiPlus_lt_of_intervalProp C hSS₁.2.1 hE_upper)
      have henvE_left_lo : a + ε₀ ≤ ψ₁ := by
        dsimp [a]
        linarith
      have hSS₁_left :
          (σ.skewedStabilityFunction_of_near C W hW habE_left).Semistable C E ψ₁ := by
        exact semistable_of_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hab₁ habE_left hSS₁ hE_left
          hε₀ hε₀2 henv₁_lo henv₁_hi henvE_left_lo (by linarith) hthin₁ hleftThin hsin
      have habF_right_tgt : ψ₂ - ε₀ < b₂ := by
        linarith [henv₂_hi]
      have hF_lower : σ.slicing.intervalProp C (ψ₂ - ε₀) b₂ F := by
        exact intervalProp_of_wSemistable_lower_target
          (C := C) (σ := σ) (W := W) (hW := hW) hab₂ habF_right_tgt
          (by linarith [henv₂_lo]) hSS₂ hε₀ hε₀2 (by linarith) henv₂_hi hthin₂ hsin
      have habF_right : ψ₂ - ε₀ < a + 1 := by
        linarith
      have hF_right : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1) F := by
        exact σ.slicing.intervalProp_of_intrinsic_phases C hSS₂.2.1
          (σ.slicing.phiMinus_gt_of_intervalProp C hSS₂.2.1 hF_lower)
          (lt_trans hF_hi (by
            dsimp [a]
            linarith [hgap, hε₀2]))
      have henvF_right_hi : ψ₂ ≤ (a + 1) - ε₀ := by
        dsimp [a]
        linarith [hsmallGap]
      have hSS₂_right :
          (σ.skewedStabilityFunction_of_near C W hW habF_right).Semistable C F ψ₂ := by
        exact semistable_of_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hab₂ habF_right hSS₂ hF_right
          hε₀ hε₀2 henv₂_lo henv₂_hi (by linarith) henvF_right_hi hthin₂ hrightThin hsin
      letI := t.hasHeartFullSubcategory
      letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
      let EH : t.heart.FullSubcategory := ⟨E, hE_heart⟩
      let FH : t.heart.FullSubcategory := ⟨F, hF_heart⟩
      let fH : EH ⟶ FH := ObjectProperty.homMk f
      let ι := t.ιHeart (H := t.heart.FullSubcategory)
      have hι_simp : ∀ (X : t.heart.FullSubcategory), ι.obj X = X.obj := by
        intro X
        rfl
      obtain ⟨X₃, f₂, f₃, hT_hom⟩ := distinguished_cocone_triangle (ι.map fH)
      have hadm : AbelianSubcategory.admissibleMorphism
          (t.ιHeart (H := t.heart.FullSubcategory)) fH := by
        rw [TStructure.heart_admissible t]
        trivial
      obtain ⟨K, Q, α, β, γ, hT_adm⟩ := hadm f₂ f₃ hT_hom
      obtain ⟨I_H, i_I, δ_I, pH, m₃, hT_I, hT_pH, hpH⟩ :=
        Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_image_factorisation
          (ι := t.ιHeart (H := t.heart.FullSubcategory))
          (hι := TStructure.heart_hι t) (hA := TStructure.heart_admissible t)
          (X₁ := EH) (X₂ := FH) (f₁ := fH) (X₃ := X₃)
          (K := K) (Q := Q) f₂ f₃ hT_hom α β hT_adm
      let πQH : FH ⟶ Q := Triangulated.AbelianSubcategory.πQ f₂ β
      let hKerI := Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
        (TStructure.heart_hι t) i_I πQH δ_I hT_I
      haveI : Mono i_I := mono_of_isLimit_fork hKerI
      let hCoker_p :=
        Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
          (ι := t.ιHeart (H := t.heart.FullSubcategory))
          (hι := TStructure.heart_hι t)
          (Triangulated.AbelianSubcategory.ιK f₃ α) pH (-m₃) hT_pH
      haveI : Epi pH := Cofork.IsColimit.epi hCoker_p
      have hfH : fH ≠ 0 := by
        intro h
        apply hf
        simpa [fH] using congrArg (fun g => g.hom) h
      have hK_heart : t.heart K.obj := K.property
      have hQ_heart : t.heart Q.obj := Q.property
      have hI_heart : t.heart I_H.obj := I_H.property
      have hK_heart' := hK_heart
      have hQ_heart' := hQ_heart
      have hI_heart' := hI_heart
      rw [(σ.slicing.phaseShift C a).toTStructure_heart_iff] at hK_heart' hQ_heart' hI_heart'
      have hK_gt : σ.slicing.gtProp C a K.obj := by
        exact (σ.slicing.phaseShift_gtProp_zero C a K.obj).mp hK_heart'.1
      have hQ_le : σ.slicing.leProp C (a + 1) Q.obj := by
        simpa [add_comm] using
          (σ.slicing.phaseShift_leProp C a 1 Q.obj).mp hQ_heart'.2
      have hI_gt : σ.slicing.gtProp C a I_H.obj := by
        exact (σ.slicing.phaseShift_gtProp_zero C a I_H.obj).mp hI_heart'.1
      have hI_le : σ.slicing.leProp C (a + 1) I_H.obj := by
        simpa [add_comm] using
          (σ.slicing.phaseShift_leProp C a 1 I_H.obj).mp hI_heart'.2
      have hT_I' : Triangle.mk i_I.hom (f₂ ≫ β) δ_I ∈ distTriang C := by
        simpa using hT_I
      have hT_pH' :
          Triangle.mk (Triangulated.AbelianSubcategory.ιK f₃ α).hom pH.hom (-m₃) ∈
            distTriang C := by
        simpa [ι] using hT_pH
      have hIne : ¬IsZero I_H.obj := by
        intro hIZ
        have hIZH : IsZero I_H := by
          exact IsZero.of_full_of_faithful_of_isZero ι I_H (by simpa [hι_simp] using hIZ)
        have hiI_zero : i_I = 0 := zero_of_source_iso_zero _ hIZH.isoZero
        have hfH_zero : fH = 0 := by
          rw [← hpH, hiI_zero]
          simp
        exact hfH hfH_zero
      have hI_phiPlus_left : σ.slicing.phiPlus C I_H.obj hIne < ψ₁ + ε₀ := by
        exact σ.slicing.phiPlus_lt_of_triangle_with_leProp C hIne
          (fun hF' ↦ lt_trans hF_hi (by linarith [hgap])) hQ_le (by linarith) hT_I'
      have hI_left : σ.slicing.intervalProp C a (ψ₁ + ε₀) I_H.obj := by
        exact σ.slicing.intervalProp_of_intrinsic_phases C hIne
          (σ.slicing.phiMinus_gt_of_gtProp C hIne hI_gt)
          hI_phiPlus_left
      have hI_phiMinus_right : ψ₂ - ε₀ < σ.slicing.phiMinus C I_H.obj hIne := by
        exact σ.slicing.phiMinus_gt_of_triangle_with_gtProp C hIne
          (fun hE' ↦ lt_trans (by linarith [hgap]) hE_lo) hK_gt (by linarith) hT_pH'
      have hI_right : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1) I_H.obj := by
        exact σ.slicing.intervalProp_of_intrinsic_phases C hIne
          hI_phiMinus_right
          (lt_of_lt_of_le hI_phiPlus_left (by linarith [hsmallGap, hε₀2]))
      let αL : ℝ := (a + (ψ₁ + ε₀)) / 2
      let αR : ℝ := ((ψ₂ - ε₀) + (a + 1)) / 2
      have hleftThin' : (ψ₁ + ε₀) - a < 1 := by
        linarith
      have hab_left : a < ψ₁ + ε₀ := by
        linarith
      have hW_ne_left :
          ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
            a < θ → θ < ψ₁ + ε₀ → W (K₀.of C G) ≠ 0 := by
        intro G θ hG hGne _ _
        exact σ.W_ne_zero_of_seminorm_lt_one C W hW hG hGne
      have hpert_left := hperturb_of_stabSeminorm C σ W hW hleftThin' hε₀ hε₀2 hsin
      have hpert_left_lo :
          ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
            a < θ → θ < ψ₁ + ε₀ →
            a - ε₀ < wPhaseOf (W (K₀.of C G)) αL ∧
              wPhaseOf (W (K₀.of C G)) αL < a - ε₀ + 1 := by
        intro G θ hG hGne haθ hθ
        obtain ⟨hlo, hhi⟩ := hpert_left G θ hG hGne haθ hθ
        simpa [αL] using ⟨by linarith, by linarith⟩
      have hpert_left_hi :
          ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
            a < θ → θ < ψ₁ + ε₀ →
            ψ₁ + ε₀ + ε₀ - 1 < wPhaseOf (W (K₀.of C G)) αL ∧
              wPhaseOf (W (K₀.of C G)) αL < ψ₁ + ε₀ + ε₀ := by
        intro G θ hG hGne haθ hθ
        obtain ⟨hlo, hhi⟩ := hpert_left G θ hG hGne haθ hθ
        simpa [αL] using ⟨by linarith, by linarith⟩
      have hI_phase_left_lo : a - ε₀ < wPhaseOf (W (K₀.of C I_H.obj)) αL := by
        have hαL_ge : a - ε₀ ≤ αL := by
          simp [αL]
          linarith
        exact wPhaseOf_gt_of_intervalProp C σ hIne W hαL_ge
          hI_left hW_ne_left hpert_left_lo
      have hI_phase_left_hi' : wPhaseOf (W (K₀.of C I_H.obj)) αL < ψ₁ + ε₀ + ε₀ := by
        have hαL_le : αL ≤ ψ₁ + ε₀ + ε₀ := by
          simp [αL]
          linarith
        exact wPhaseOf_lt_of_intervalProp (C := C) (σ := σ) (E := I_H.obj) hIne W
          (α := αL) (a := a) (b := ψ₁ + ε₀) (ε := ε₀) hαL_le
          hI_left hW_ne_left hpert_left_hi
      have hI_phase_left_hi : wPhaseOf (W (K₀.of C I_H.obj)) αL < ψ₁ + 2 * ε₀ := by
        linarith
      have hWneI : W (K₀.of C I_H.obj) ≠ 0 := by
        exact σ.W_ne_zero_of_intervalProp C W hleftThin'
          (stabSeminorm_lt_cos_of_hsin_hthin
            (C := C) (σ := σ) (W := W) hab_left hε₀ hε₀2 hleftThin hsin) hIne hI_left
      have hI_phase_eq_left_right :
          wPhaseOf (W (K₀.of C I_H.obj)) αL =
            wPhaseOf (W (K₀.of C I_H.obj)) αR := by
        have hbranch :
            wPhaseOf (W (K₀.of C I_H.obj)) αL ∈ Set.Ioc (αR - 1) (αR + 1) := by
          constructor
          · simp [αL, αR] at *
            linarith
          · simp [αL, αR] at *
            linarith [hsmallGap, hε₀2]
        exact wPhaseOf_indep hWneI _ _ hbranch
      letI : Fact (a < ψ₁ + ε₀) := ⟨habE_left⟩
      letI : Fact (ψ₁ + ε₀ - a ≤ 1) := ⟨by linarith⟩
      let EL : σ.slicing.IntervalCat C a (ψ₁ + ε₀) := ⟨E, hE_left⟩
      let IL : σ.slicing.IntervalCat C a (ψ₁ + ε₀) := ⟨I_H.obj, hI_left⟩
      let pL : EL ⟶ IL := ObjectProperty.homMk pH.hom
      let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := σ.slicing) a (ψ₁ + ε₀)
        (Fact.out : ψ₁ + ε₀ - a ≤ 1)
      have hpL_epi : Epi (FL.map pL) := by
        simpa [FL, pL, EL, IL] using (inferInstance : Epi pH)
      have hpL_strict : IsStrictEpi pL := by
        letI : Epi (FL.map pL) := hpL_epi
        exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
          (C := C) (s := σ.slicing) (a := a) (b := ψ₁ + ε₀) pL
      have hW_interval_left :
          ∀ {G : C}, σ.slicing.intervalProp C a (ψ₁ + ε₀) G → ¬IsZero G →
            W (K₀.of C G) ≠ 0 := by
        intro G hG hGne
        exact σ.W_ne_zero_of_intervalProp C W hleftThin'
          (stabSeminorm_lt_cos_of_hsin_hthin
            (C := C) (σ := σ) (W := W) hab_left hε₀ hε₀2 hleftThin hsin) hGne hG
      have hI_phase_ge_left :
          ψ₁ ≤ wPhaseOf (W (K₀.of C I_H.obj)) αL := by
        let ssfL := σ.skewedStabilityFunction_of_near C W hW habE_left
        simpa [StabilityCondition.skewedStabilityFunction_of_near, EL, IL, pL] using
          (SkewedStabilityFunction.phase_le_of_strictQuotient
            (C := C) (σ := σ) (a := a) (b := ψ₁ + ε₀) (ssf := ssfL)
            (X := EL) (Y := IL) hSS₁_left hε₀ hleftThin hW_interval_left hpert_left pL
            hpL_strict hIne)
      have hK_left : σ.slicing.intervalProp C a (ψ₁ + ε₀) K.obj := by
        exact σ.slicing.first_intervalProp_of_triangle C habE_left hE_left hI_le hK_gt hT_pH'
      have hQ_phiMinus_right :
          ∀ (hQne : ¬IsZero Q.obj), ψ₂ - ε₀ < σ.slicing.phiMinus C Q.obj hQne := by
        intro hQne
        exact σ.slicing.phiMinus_gt_of_triangle_with_gtProp C hQne
          (fun hF' ↦ σ.slicing.phiMinus_gt_of_intervalProp C hF' hF_right)
          hI_gt (by
            dsimp [a]
            linarith [hε₀2]) hT_I'
      set δ := (1 - (((a + 1) - (ψ₂ - ε₀)) + 2 * ε₀)) / 2 with hδ_def
      have hδ_pos : 0 < δ := by
        have : ((a + 1) - (ψ₂ - ε₀)) + 2 * ε₀ < 1 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrightThin
        linarith
      have habF_big : ψ₂ - ε₀ < a + 1 + δ := by
        linarith
      have hthin_big : (a + 1 + δ) - (ψ₂ - ε₀) + 2 * ε₀ < 1 := by
        rw [hδ_def]
        linarith
      have hF_big : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1 + δ) F := by
        exact σ.slicing.intervalProp_mono C (show ψ₂ - ε₀ ≤ ψ₂ - ε₀ by linarith)
          (show a + 1 ≤ a + 1 + δ by linarith) hF_right
      have hSS₂_big :
          (σ.skewedStabilityFunction_of_near C W hW habF_big).Semistable C F ψ₂ := by
        exact semistable_of_upper_inclusion
          (C := C) (σ := σ) (W := W) (hW := hW)
          (hab₁ := habF_right) (hab₂ := habF_big)
          (hb := by linarith) hSS₂_right hε₀ hε₀2
          (by linarith) henvF_right_hi hthin_big hsin
      have hI_big : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1 + δ) I_H.obj := by
        exact σ.slicing.intervalProp_mono C (show ψ₂ - ε₀ ≤ ψ₂ - ε₀ by linarith)
          (show a + 1 ≤ a + 1 + δ by linarith) hI_right
      have hQ_big : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1 + δ) Q.obj := by
        by_cases hQZ : IsZero Q.obj
        · exact Or.inl hQZ
        · exact σ.slicing.intervalProp_of_intrinsic_phases C hQZ
            (hQ_phiMinus_right hQZ)
            (lt_of_le_of_lt (σ.slicing.phiPlus_le_of_leProp C hQZ hQ_le) (by linarith))
      have hI_phase_le_big :
          wPhaseOf (W (K₀.of C I_H.obj)) ((ψ₂ - ε₀ + (a + 1 + δ)) / 2) ≤ ψ₂ := by
        simpa [StabilityCondition.skewedStabilityFunction_of_near] using
          hSS₂_big.2.2.2.2 hT_I' hI_big hQ_big hIne
      have hI_phase_eq_right_big :
          wPhaseOf (W (K₀.of C I_H.obj)) αR =
            wPhaseOf (W (K₀.of C I_H.obj)) ((ψ₂ - ε₀ + (a + 1 + δ)) / 2) := by
        simpa [αR] using
          (wPhaseOf_eq_of_intervalProp_upper_inclusion
            (C := C) (σ := σ) (W := W) (hW := hW) habF_right (by linarith)
            hI_right hIne hε₀ hε₀2 hthin_big hsin)
      have hI_phase_le_right :
          wPhaseOf (W (K₀.of C I_H.obj)) αR ≤ ψ₂ := by
        rw [hI_phase_eq_right_big]
        exact hI_phase_le_big
      rw [← hI_phase_eq_left_right] at hI_phase_le_right
      linarith


end CategoryTheory.Triangulated
