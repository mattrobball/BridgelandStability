/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.TargetEnvelope

/-!
# Deformation of Stability Conditions — BoundaryTriangles

Upper/lower boundary triangles, strict SES, target semistability
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

theorem exists_upper_boundary_triangle
    (s : Slicing C) {a b₁ b₂ : ℝ}
    (hab₁ : a < b₁)
    {Q : C} (hQ : s.intervalProp C a b₂ Q) :
    ∃ (X Y : C) (f : X ⟶ Q) (g : Q ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      s.geProp C b₁ X ∧
      s.intervalProp C a b₁ Y := by
  let ss := s.phaseShift C b₁
  let t := ss.toTStructureGE
  obtain ⟨X, Y, hX : t.le 0 X, hY : t.ge 1 Y, f, g, h, hT⟩ := t.exists_triangle_zero_one Q
  have hX_ge : s.geProp C b₁ X := by
    have hX' : ss.geProp C 0 X := by
      change ss.geProp C (-↑(0 : ℤ)) X at hX
      simpa using hX
    exact (s.phaseShift_geProp_zero C b₁ X).mp hX'
  have hY_lt : s.ltProp C b₁ Y := by
    have hY' : ss.ltProp C 0 Y := by
      change ss.ltProp C (1 - ↑(1 : ℤ)) Y at hY
      simpa using hY
    exact (s.phaseShift_ltProp_zero C b₁ Y).mp hY'
  refine ⟨X, Y, f, g, h, hT, hX_ge,
    ?_⟩
  by_cases hYZ : IsZero Y
  · exact Or.inl hYZ
  · have hY_minus : a < s.phiMinus C Y hYZ :=
      s.phiMinus_gt_of_triangle_with_geProp C hYZ
        (fun hQZ ↦ s.phiMinus_gt_of_intervalProp C hQZ hQ)
        hX_ge (by grind) hT
    have hY_plus : s.phiPlus C Y hYZ < b₁ := s.phiPlus_lt_of_ltProp C hYZ hY_lt
    obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C s hYZ
    exact Or.inr ⟨F, fun i ↦ ⟨by
      calc
        a < s.phiMinus C Y hYZ := hY_minus
        _ = F.φ ⟨F.n - 1, by grind⟩ := s.phiMinus_eq C Y hYZ F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by grind)), by
        calc
          F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
          _ = s.phiPlus C Y hYZ := (s.phiPlus_eq C Y hYZ F hn hfirst).symm
          _ < b₁ := hY_plus⟩⟩

omit [IsTriangulated C] in
theorem gtProp_of_geProp_of_lt
    (s : Slicing C) {a b : ℝ} (hab : a < b) {E : C}
    (hE : s.geProp C b E) :
    s.gtProp C a E := by
  rcases hE with hZ | ⟨F, hF, hge⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨F, hF, lt_of_lt_of_le hab hge⟩

theorem wPhaseOf_gt_of_geProp_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ψ ε₀ : ℝ} {E : C}
    (hI : σ.slicing.intervalProp C a b E) (hEne : ¬IsZero E)
    (hGe : σ.slicing.geProp C (ψ + ε₀) E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    ψ < wPhaseOf (W (K₀.of C E)) ((a + b) / 2) := by
  have hthin1 : b - a < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin1 hε₀ hε₀2 hsin
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEne
  have hphi_lower : ψ + ε₀ ≤ σ.slicing.phiMinus C E hEne :=
    σ.slicing.phiMinus_ge_of_geProp C hEne hGe
  have hphases : ∀ i : Fin F.n, ψ + ε₀ ≤ F.φ i ∧ F.φ i < b := by
    intro i
    constructor
    · calc
        ψ + ε₀ ≤ σ.slicing.phiMinus C E hEne := hphi_lower
        _ = F.φ ⟨F.n - 1, by grind⟩ := σ.slicing.phiMinus_eq C E hEne F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by grind))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        _ = σ.slicing.phiPlus C E hEne := (σ.slicing.phiPlus_eq C E hEne F hn hfirst).symm
        _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hEne hI
  set P := F.toPostnikovTower
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have hWE : W (K₀.of C E) =
      ∑ i : Fin F.n, W (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  have him_pos :
      0 < (W (K₀.of C E) * rot).im := by
    rw [hWE, Finset.sum_mul]
    rw [show (∑ i : Fin F.n, W (K₀.of C (P.factor i)) * rot).im =
        ∑ i : Fin F.n, (W (K₀.of C (P.factor i)) * rot).im from
      map_sum Complex.imAddGroupHom _ _]
    apply lt_of_lt_of_le _ (Finset.single_le_sum
      (f := fun i ↦ (W (K₀.of C (P.factor i)) * rot).im)
      (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hn⟩))
    · obtain ⟨hlo_pert, hhi_pert⟩ := hpert _ _ (F.semistable ⟨0, hn⟩) hfirst
        (by linarith [(hphases ⟨0, hn⟩).1]) (hphases ⟨0, hn⟩).2
      have hlo_pert' :
          F.φ ⟨0, hn⟩ - ε₀ <
            wPhaseOf (W (K₀.of C (P.factor ⟨0, hn⟩))) ((a + b) / 2) := by
        simpa [P] using hlo_pert
      have hhi_pert' :
          wPhaseOf (W (K₀.of C (P.factor ⟨0, hn⟩))) ((a + b) / 2) < F.φ ⟨0, hn⟩ + ε₀ := by
        simpa [P] using hhi_pert
      exact im_pos_of_phase_above
        (norm_pos_iff.mpr (σ.W_ne_zero_of_seminorm_lt_one C W hW
          (F.semistable ⟨0, hn⟩) hfirst))
        (wPhaseOf_compat _ _)
        (by linarith [hlo_pert', (hphases ⟨0, hn⟩).1])
        (by
          have hbψ : b + ε₀ < ψ + 1 := by
            linarith
          have hupper : F.φ ⟨0, hn⟩ + ε₀ < ψ + 1 := by
            linarith [(hphases ⟨0, hn⟩).2, hbψ]
          linarith [hhi_pert', hupper])
    · by_cases hi : IsZero (P.factor i)
      · simp [K₀.of_isZero C hi]
      · obtain ⟨hlo_pert, hhi_pert⟩ := hpert _ _ (F.semistable i) hi
          (by linarith [(hphases i).1]) (hphases i).2
        have hlo_pert' :
            F.φ i - ε₀ < wPhaseOf (W (K₀.of C (P.factor i))) ((a + b) / 2) := by
          simpa [P] using hlo_pert
        have hhi_pert' :
            wPhaseOf (W (K₀.of C (P.factor i))) ((a + b) / 2) < F.φ i + ε₀ := by
          simpa [P] using hhi_pert
        exact le_of_lt <| im_pos_of_phase_above
          (norm_pos_iff.mpr (σ.W_ne_zero_of_seminorm_lt_one C W hW (F.semistable i) hi))
          (wPhaseOf_compat _ _)
          (by linarith [hlo_pert', (hphases i).1])
          (by
            have hbψ : b + ε₀ < ψ + 1 := by
              linarith
            have hupper : F.φ i + ε₀ < ψ + 1 := by
              linarith [(hphases i).2, hbψ]
            linarith [hhi_pert', hupper])
  have hW_ne_ab : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b → W (K₀.of C G) ≠ 0 := by
    intro G θ hG hGne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hG hGne
  have hpert_gt : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b →
      a - ε₀ < wPhaseOf (W (K₀.of C G)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C G)) ((a + b) / 2) < a - ε₀ + 1 := by
    intro G θ hG hGne haθ hθb
    obtain ⟨hlo, hhi⟩ := hpert G θ hG hGne haθ hθb
    exact ⟨by linarith, by grind⟩
  have hpert_lt : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b →
      b + ε₀ - 1 < wPhaseOf (W (K₀.of C G)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C G)) ((a + b) / 2) < b + ε₀ := by
    intro G θ hG hGne haθ hθb
    obtain ⟨hlo, hhi⟩ := hpert G θ hG hGne haθ hθb
    exact ⟨by linarith, by grind⟩
  have hphase_lo :
      a - ε₀ < wPhaseOf (W (K₀.of C E)) ((a + b) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W (by grind) hI hW_ne_ab hpert_gt
  have hphase_hi :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W (by grind) hI hW_ne_ab hpert_lt
  have hrange :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) := by
    constructor
    · have : ψ - 1 < a - ε₀ := by
        linarith
      linarith
    · have : b + ε₀ < ψ + 1 := by
        linarith
      linarith
  exact wPhaseOf_gt_of_im_pos him_pos hrange

section

omit [IsTriangulated C]

theorem intervalProp_of_upper_boundary_triangle
    (s : Slicing C) {a b₁ b₂ : ℝ}
    (hab₁ : a < b₁) (hab₂ : a < b₂) (hb₁ : b₁ ≤ a + 1)
    {Q X Y : C}
    (hQ : s.intervalProp C a b₂ Q)
    (hX_ge : s.geProp C b₁ X)
    (hY : s.intervalProp C a b₁ Y)
    {f : X ⟶ Q} {g : Q ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a b₂ X := by
  have hY_le : s.leProp C (a + 1) Y := by
    exact ((s.leProp_mono (C := C) (t₁ := b₁) (t₂ := a + 1) hb₁) Y)
      (s.leProp_of_intervalProp C hY)
  have hX_gt : s.gtProp C a X :=
    gtProp_of_geProp_of_lt (C := C) (s := s) hab₁ hX_ge
  exact s.first_intervalProp_of_triangle C hab₂ hQ hY_le hX_gt hT

end

theorem wPhaseOf_gt_of_upper_boundary_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b₁ b₂ ψ ε₀ : ℝ}
    (hab₁ : a < b₁) (hab₂ : a < b₂) (hb : b₁ ≤ b₂)
    {Q X Y : C}
    (hQ : σ.slicing.intervalProp C a b₂ Q)
    (hX_ge : σ.slicing.geProp C b₁ X)
    (hY : σ.slicing.intervalProp C a b₁ Y)
    (hXne : ¬IsZero X)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b₁ - ε₀)
    (hthin : b₂ - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ Q} {g : Q ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    ψ < wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) := by
  have hb₁ : b₁ ≤ a + 1 := by
    have : b₂ - a < 1 := by
      linarith
    linarith
  have hXI : σ.slicing.intervalProp C a b₂ X :=
    intervalProp_of_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb₁ hQ hX_ge hY hT
  have hX_ge' : σ.slicing.geProp C (ψ + ε₀) X := by
    exact ((σ.slicing.geProp_anti (C := C) (t₁ := ψ + ε₀) (t₂ := b₁)
      (by grind)) X) hX_ge
  have henv_hi₂ : ψ ≤ b₂ - ε₀ := by
    linarith
  exact wPhaseOf_gt_of_geProp_target (C := C) σ W hW
    hXI hXne hX_ge' hε₀ hε₀2 henv_lo henv_hi₂ hthin hsin

theorem wPhaseOf_gt_of_upper_source_boundary_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {φ ψ ε₀ : ℝ} {Q X Y : C}
    (hQ : σ.slicing.intervalProp C (ψ - ε₀) (φ + ε₀) Q)
    (hX_ge : σ.slicing.geProp C (ψ + ε₀) X)
    (hY : σ.slicing.intervalProp C (ψ - ε₀) (ψ + ε₀) Y)
    (hXne : ¬IsZero X)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hψ_lo : φ - ε₀ < ψ) (hψ_le : ψ ≤ φ)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ Q} {g : Q ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    ψ < wPhaseOf (W (K₀.of C X)) (((ψ - ε₀) + (φ + ε₀)) / 2) := by
  have hthin : (φ + ε₀) - (ψ - ε₀) + 2 * ε₀ < 1 := by
    linarith [hε₀8]
  exact wPhaseOf_gt_of_upper_boundary_triangle
    (C := C) (σ := σ) (W := W) (hW := hW)
    (a := ψ - ε₀) (b₁ := ψ + ε₀) (b₂ := φ + ε₀) (ψ := ψ) (ε₀ := ε₀)
    (by grind) (by grind) (by linarith [hψ_le]) hQ hX_ge hY hXne
    hε₀ hε₀2 (by grind) (by grind) hthin hsin hT

theorem wPhaseOf_gt_of_upper_source_boundary_P_phi
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {φ ψ ε₀ : ℝ} {Q X Y : C}
    (hQ : σ.slicing.intervalProp C (ψ - ε₀) (φ + ε₀) Q)
    (hX_ge : σ.slicing.geProp C (ψ + ε₀) X)
    (hY_Pφ : σ.slicing.P φ Y)
    (hXne : ¬IsZero X)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hψ_lo : φ - ε₀ < ψ) (hψ_hi : ψ < φ + ε₀) (hψ_le : ψ ≤ φ)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ Q} {g : Q ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    ψ < wPhaseOf (W (K₀.of C X)) (((ψ - ε₀) + (φ + ε₀)) / 2) := by
  have hY :
      σ.slicing.intervalProp C (ψ - ε₀) (ψ + ε₀) Y := by
    exact σ.slicing.intervalProp_of_semistable C hY_Pφ (by grind) (by grind)
  exact wPhaseOf_gt_of_upper_source_boundary_target
    (C := C) (σ := σ) (W := W) (hW := hW)
    hQ hX_ge hY hXne hε₀ hε₀2 hε₀8 hψ_lo hψ_le hsin hT

theorem wPhaseOf_lt_of_leProp_source
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ψ ε₀ : ℝ} {E : C}
    (hI : σ.slicing.intervalProp C a b E) (hEne : ¬IsZero E)
    (hLe : σ.slicing.leProp C (ψ - ε₀) E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    wPhaseOf (W (K₀.of C E)) ((a + b) / 2) < ψ := by
  have hthin1 : b - a < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin1 hε₀ hε₀2 hsin
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEne
  have hphi_upper : σ.slicing.phiPlus C E hEne ≤ ψ - ε₀ :=
    σ.slicing.phiPlus_le_of_leProp C hEne hLe
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i ≤ ψ - ε₀ := by
    intro i
    constructor
    · calc
        a < σ.slicing.phiMinus C E hEne := σ.slicing.phiMinus_gt_of_intervalProp C hEne hI
        _ = F.φ ⟨F.n - 1, by grind⟩ := σ.slicing.phiMinus_eq C E hEne F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by grind))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        _ = σ.slicing.phiPlus C E hEne := (σ.slicing.phiPlus_eq C E hEne F hn hfirst).symm
        _ ≤ ψ - ε₀ := hphi_upper
  set P := F.toPostnikovTower
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have hWE : W (K₀.of C E) =
      ∑ i : Fin F.n, W (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  have him_neg :
      (W (K₀.of C E) * rot).im < 0 := by
    rw [hWE, Finset.sum_mul]
    rw [show (∑ i : Fin F.n, W (K₀.of C (P.factor i)) * rot).im =
        ∑ i : Fin F.n, (W (K₀.of C (P.factor i)) * rot).im from
      map_sum Complex.imAddGroupHom _ _]
    suffices h : 0 < ∑ i : Fin F.n, -(W (K₀.of C (P.factor i)) * rot).im by
      linarith [Finset.sum_neg_distrib (G := ℝ) (s := Finset.univ)
        (f := fun i ↦ (W (K₀.of C (P.factor i)) * rot).im)]
    apply lt_of_lt_of_le _ (Finset.single_le_sum
      (f := fun i ↦ -(W (K₀.of C (P.factor i)) * rot).im)
      (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hn⟩))
    · obtain ⟨hlo_pert, hhi_pert⟩ := hpert _ _ (F.semistable ⟨0, hn⟩) hfirst
          (hphases ⟨0, hn⟩).1 (lt_of_le_of_lt (hphases ⟨0, hn⟩).2 <| by grind)
      have hlo_pert' :
          F.φ ⟨0, hn⟩ - ε₀ <
            wPhaseOf (W (K₀.of C (P.factor ⟨0, hn⟩))) ((a + b) / 2) := by
        simpa [P] using hlo_pert
      have hhi_pert' :
          wPhaseOf (W (K₀.of C (P.factor ⟨0, hn⟩))) ((a + b) / 2) <
            F.φ ⟨0, hn⟩ + ε₀ := by
        simpa [P] using hhi_pert
      exact neg_pos.mpr <| im_neg_of_phase_below
        (norm_pos_iff.mpr (σ.W_ne_zero_of_seminorm_lt_one C W hW
          (F.semistable ⟨0, hn⟩) hfirst))
        (wPhaseOf_compat _ _)
        (by
          have hlower : ψ - 1 < a - ε₀ := by
            linarith
          linarith [hlo_pert', hlower, (hphases ⟨0, hn⟩).1])
        (by linarith [hhi_pert', (hphases ⟨0, hn⟩).2])
    · by_cases hi : IsZero (P.factor i)
      · simp [P, K₀.of_isZero C hi]
      · obtain ⟨hlo_pert, hhi_pert⟩ := hpert _ _ (F.semistable i) hi (hphases i).1
            (lt_of_le_of_lt (hphases i).2 <| by grind)
        have hlo_pert' :
            F.φ i - ε₀ <
              wPhaseOf (W (K₀.of C (P.factor i))) ((a + b) / 2) := by
          simpa [P] using hlo_pert
        have hhi_pert' :
            wPhaseOf (W (K₀.of C (P.factor i))) ((a + b) / 2) < F.φ i + ε₀ := by
          simpa [P] using hhi_pert
        exact le_of_lt <| neg_pos.mpr <| im_neg_of_phase_below
          (norm_pos_iff.mpr (σ.W_ne_zero_of_seminorm_lt_one C W hW (F.semistable i) hi))
          (wPhaseOf_compat _ _)
          (by
            have hlower : ψ - 1 < a - ε₀ := by
              linarith
            linarith [hlo_pert', hlower, (hphases i).1])
          (by linarith [hhi_pert', (hphases i).2])
  have hW_ne_ab : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b → W (K₀.of C G) ≠ 0 := by
    intro G θ hG hGne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hG hGne
  have hpert_gt : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b →
      a - ε₀ < wPhaseOf (W (K₀.of C G)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C G)) ((a + b) / 2) < a - ε₀ + 1 := by
    intro G θ hG hGne haθ hθb
    obtain ⟨hlo, hhi⟩ := hpert G θ hG hGne haθ hθb
    exact ⟨by linarith, by grind⟩
  have hpert_lt : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b →
      b + ε₀ - 1 < wPhaseOf (W (K₀.of C G)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C G)) ((a + b) / 2) < b + ε₀ := by
    intro G θ hG hGne haθ hθb
    obtain ⟨hlo, hhi⟩ := hpert G θ hG hGne haθ hθb
    exact ⟨by linarith, by grind⟩
  have hphase_lo :
      a - ε₀ < wPhaseOf (W (K₀.of C E)) ((a + b) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W
      (by grind) hI hW_ne_ab hpert_gt
  have hphase_hi :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W
      (by grind) hI hW_ne_ab hpert_lt
  have hrange :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) := by
    constructor
    · have : ψ - 1 < a - ε₀ := by
        linarith
      linarith
    · have : b + ε₀ < ψ + 1 := by
        linarith
      linarith
  exact wPhaseOf_lt_of_im_neg him_neg hrange

theorem exists_lower_boundary_triangle
    (s : Slicing C) {a₁ a₂ b : ℝ}
    (ha₁ : a₁ < b)
    {K : C} (hK : s.intervalProp C a₂ b K) :
    ∃ (X Y : C) (f : X ⟶ K) (g : K ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      s.intervalProp C a₁ b X ∧
      s.leProp C a₁ Y := by
  let ss := s.phaseShift C a₁
  let t := ss.toTStructure
  obtain ⟨X, Y, hX : t.le 0 X, hY : t.ge 1 Y, f, g, h, hT⟩ := t.exists_triangle_zero_one K
  have hX_gt : s.gtProp C a₁ X := by
    have hX' : ss.gtProp C 0 X := by
      change ss.gtProp C (-↑(0 : ℤ)) X at hX
      simpa using hX
    exact (s.phaseShift_gtProp_zero C a₁ X).mp hX'
  have hY_le : s.leProp C a₁ Y := by
    have hY' : ss.leProp C 0 Y := by
      change ss.leProp C (1 - ↑(1 : ℤ)) Y at hY
      simpa using hY
    exact (s.phaseShift_leProp_zero C a₁ Y).mp hY'
  have hX_I : s.intervalProp C a₁ b X := by
    by_cases hXZ : IsZero X
    · exact Or.inl hXZ
    · have hX_plus : s.phiPlus C X hXZ < b :=
        s.phiPlus_lt_of_triangle_with_leProp C hXZ
          (fun hKZ ↦ s.phiPlus_lt_of_intervalProp C hKZ hK) hY_le (by grind) hT
      have hX_minus : a₁ < s.phiMinus C X hXZ :=
        s.phiMinus_gt_of_gtProp C hXZ hX_gt
      exact s.intervalProp_of_intrinsic_phases C hXZ hX_minus hX_plus
  exact ⟨X, Y, f, g, h, hT, hX_I, hY_le⟩

section

omit [IsTriangulated C]

theorem intervalProp_of_lower_boundary_triangle
    (s : Slicing C) {a₁ a₂ b : ℝ}
    (ha₁ : a₁ < b) (ha : a₂ ≤ a₁)
    {K X Y : C}
    (hK : s.intervalProp C a₂ b K)
    (hX : s.intervalProp C a₁ b X)
    (hY_le : s.leProp C a₁ Y)
    {f : X ⟶ K} {g : K ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a₂ b Y := by
  by_cases hY0 : IsZero Y
  · exact Or.inl hY0
  · have hY_plus : s.phiPlus C Y hY0 < b := by
      have hY_plus_le : s.phiPlus C Y hY0 ≤ a₁ := s.phiPlus_le_of_leProp C hY0 hY_le
      linarith
    have hX_ge : s.geProp C a₁ X := by
      rcases s.gtProp_of_intervalProp C hX with hXZ | ⟨F, hF, hgt⟩
      · exact Or.inl hXZ
      · exact Or.inr ⟨F, hF, le_of_lt hgt⟩
    have hY_minus : a₂ < s.phiMinus C Y hY0 :=
      s.phiMinus_gt_of_triangle_with_geProp C hY0
        (fun hK0 ↦ s.phiMinus_gt_of_intervalProp C hK0 hK)
        hX_ge (by grind) hT
    exact s.intervalProp_of_intrinsic_phases C hY0 hY_minus hY_plus

end

theorem wPhaseOf_lt_of_lower_boundary_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a₁ a₂ b ψ ε₀ : ℝ}
    (ha₁ : a₁ < b) (ha : a₂ ≤ a₁)
    {K X Y : C}
    (hK : σ.slicing.intervalProp C a₂ b K)
    (hX : σ.slicing.intervalProp C a₁ b X)
    (hY_le : σ.slicing.leProp C a₁ Y)
    (hYne : ¬IsZero Y)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a₁ + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin : b - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ K} {g : K ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    wPhaseOf (W (K₀.of C Y)) ((a₂ + b) / 2) < ψ := by
  have hY_I : σ.slicing.intervalProp C a₂ b Y :=
    intervalProp_of_lower_boundary_triangle (C := C) (s := σ.slicing)
      ha₁ ha hK hX hY_le hT
  have hY_le' : σ.slicing.leProp C (ψ - ε₀) Y := by
    exact ((σ.slicing.leProp_mono (C := C) (t₁ := a₁) (t₂ := ψ - ε₀) (by grind)) Y) hY_le
  exact wPhaseOf_lt_of_leProp_source (C := C) σ W hW
    hY_I hYne hY_le' hε₀ hε₀2 (by grind) henv_hi hthin hsin

theorem wPhaseOf_lt_of_lower_source_boundary_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {φ ψ ε₀ : ℝ} {K X Y : C}
    (hK : σ.slicing.intervalProp C (φ - ε₀) (ψ + ε₀) K)
    (hX : σ.slicing.intervalProp C (ψ - ε₀) (ψ + ε₀) X)
    (hY_le : σ.slicing.leProp C (ψ - ε₀) Y)
    (hYne : ¬IsZero Y)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hψ_hi : ψ < φ + ε₀) (hφ_le : φ ≤ ψ)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ K} {g : K ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    wPhaseOf (W (K₀.of C Y)) (((φ - ε₀) + (ψ + ε₀)) / 2) < ψ := by
  have hthin : (ψ + ε₀) - (φ - ε₀) + 2 * ε₀ < 1 := by
    linarith [hε₀8]
  exact wPhaseOf_lt_of_lower_boundary_triangle
    (C := C) (σ := σ) (W := W) (hW := hW)
    (a₁ := ψ - ε₀) (a₂ := φ - ε₀) (b := ψ + ε₀) (ψ := ψ) (ε₀ := ε₀)
    (by grind) (by linarith [hφ_le]) hK hX hY_le hYne
    hε₀ hε₀2 (by grind) (by grind) hthin hsin hT

theorem wPhaseOf_lt_of_lower_source_boundary_P_phi
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {φ ψ ε₀ : ℝ} {K X Y : C}
    (hK : σ.slicing.intervalProp C (φ - ε₀) (ψ + ε₀) K)
    (hX_Pφ : σ.slicing.P φ X)
    (hY_le : σ.slicing.leProp C (ψ - ε₀) Y)
    (hYne : ¬IsZero Y)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hψ_hi : ψ < φ + ε₀) (hφ_le : φ ≤ ψ)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ K} {g : K ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    wPhaseOf (W (K₀.of C Y)) (((φ - ε₀) + (ψ + ε₀)) / 2) < ψ := by
  have hX :
      σ.slicing.intervalProp C (ψ - ε₀) (ψ + ε₀) X := by
    exact σ.slicing.intervalProp_of_semistable C hX_Pφ (by grind) (by grind)
  exact wPhaseOf_lt_of_lower_source_boundary_target
    (C := C) (σ := σ) (W := W) (hW := hW)
    hK hX hY_le hYne hε₀ hε₀2 hε₀8 hψ_hi hφ_le hsin hT

/-- Package the upper-boundary truncation as a strict short exact sequence in the larger thin
interval category. This is the Section 7 reduction step `0 → A → E → E' → 0`, with the
subobject supported on the upper boundary strip and the quotient still lying in the larger thin
category. -/
theorem exists_upper_boundary_strictShortExact
    (s : Slicing C) {a b₁ b₂ : ℝ}
    [Fact (a < b₂)] [Fact (b₂ - a ≤ 1)]
    (hab₁ : a < b₁) (hb : b₁ ≤ b₂)
    {Q : C} (hQ : s.intervalProp C a b₂ Q) :
    ∃ S : ShortComplex (s.IntervalCat C a b₂),
      StrictShortExact S ∧
      S.X₂ = ⟨Q, hQ⟩ ∧
      s.geProp C b₁ S.X₁.obj ∧
      s.intervalProp C a b₁ S.X₃.obj := by
  have hab₂ : a < b₂ := Fact.out
  have hthin₂ : b₂ - a ≤ 1 := Fact.out
  obtain ⟨X, Y, f, g, h, hT, hX_ge, hY_small⟩ :=
    exists_upper_boundary_triangle (C := C) (s := s)
      (a := a) (b₁ := b₁) (b₂ := b₂) hab₁ hQ
  have hb₁_le : b₁ ≤ a + 1 := by
    linarith
  let XI : s.IntervalCat C a b₂ := ⟨X,
    intervalProp_of_upper_boundary_triangle (C := C) (s := s)
      (a := a) (b₁ := b₁) (b₂ := b₂) hab₁ hab₂ hb₁_le hQ hX_ge hY_small hT⟩
  let YI : s.IntervalCat C a b₂ := ⟨Y,
    s.intervalProp_mono C (show a ≤ a by grind) hb hY_small⟩
  let QI : s.IntervalCat C a b₂ := ⟨Q, hQ⟩
  let fi : XI ⟶ QI := ObjectProperty.homMk f
  let gi : QI ⟶ YI := ObjectProperty.homMk g
  let S : ShortComplex (s.IntervalCat C a b₂) := ShortComplex.mk fi gi (by
      ext
      simpa [fi, gi] using comp_distTriang_mor_zero₁₂ _ hT)
  have hTS : Triangle.mk S.f.hom S.g.hom h ∈ distTriang C := by
    simpa [S, fi, gi] using hT
  refine ⟨S, ?_, ?_, hX_ge, hY_small⟩
  · exact Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := s) (a := a) (b := b₂) hTS
  · simp [S, QI]

/-- Package the lower-boundary truncation as a strict short exact sequence in the larger thin
interval category. This is the dual Section 7 reduction step, with the kernel already lying in
the smaller target interval and the quotient supported on the lower boundary strip. -/
theorem exists_lower_boundary_strictShortExact
    (s : Slicing C) {a₁ a₂ b : ℝ}
    [Fact (a₂ < b)] [Fact (b - a₂ ≤ 1)]
    (ha₁ : a₁ < b) (ha : a₂ ≤ a₁)
    {K : C} (hK : s.intervalProp C a₂ b K) :
    ∃ S : ShortComplex (s.IntervalCat C a₂ b),
      StrictShortExact S ∧
      S.X₂ = ⟨K, hK⟩ ∧
      s.intervalProp C a₁ b S.X₁.obj ∧
      s.leProp C a₁ S.X₃.obj := by
  have ha₂b : a₂ < b := Fact.out
  have hthin : b - a₂ ≤ 1 := Fact.out
  obtain ⟨X, Y, f, g, h, hT, hX_small, hY_le⟩ :=
    exists_lower_boundary_triangle (C := C) (s := s)
      (a₁ := a₁) (a₂ := a₂) (b := b) ha₁ hK
  let XI : s.IntervalCat C a₂ b := ⟨X,
    s.intervalProp_mono C ha (show b ≤ b by grind) hX_small⟩
  let YI : s.IntervalCat C a₂ b := ⟨Y,
    intervalProp_of_lower_boundary_triangle (C := C) (s := s)
      (a₁ := a₁) (a₂ := a₂) (b := b) ha₁ ha
      hK hX_small hY_le hT⟩
  let KI : s.IntervalCat C a₂ b := ⟨K, hK⟩
  let fi : XI ⟶ KI := ObjectProperty.homMk f
  let gi : KI ⟶ YI := ObjectProperty.homMk g
  let S : ShortComplex (s.IntervalCat C a₂ b) := ShortComplex.mk fi gi (by
      ext
      simpa [fi, gi] using comp_distTriang_mor_zero₁₂ _ hT)
  have hTS : Triangle.mk S.f.hom S.g.hom h ∈ distTriang C := by
    simpa [S, fi, gi] using hT
  refine ⟨S, ?_, ?_, hX_small, hY_le⟩
  · exact Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := s) (a := a₂) (b := b) hTS
  · simp [S, KI]

theorem intervalProp_of_wSemistable_upper_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b₁ b₂ ψ ε₀ : ℝ} (hab₁ : a < b₁) (hab₂ : a < b₂) (hb : b₁ ≤ b₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b₁ - ε₀)
    (hthin₂ : b₂ - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    σ.slicing.intervalProp C a b₁ E := by
  have hthin₂' : b₂ - a < 1 := by
    linarith
  obtain ⟨X, Y, fX, gY, δY, hTQ, hX_ge, hY₁⟩ :=
    exists_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hSS.1
  have hb₁_le : b₁ ≤ a + 1 := by
    linarith
  have hX₂ : σ.slicing.intervalProp C a b₂ X :=
    intervalProp_of_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb₁_le hSS.1 hX_ge hY₁ hTQ
  have hY₂ : σ.slicing.intervalProp C a b₂ Y :=
    σ.slicing.intervalProp_mono C (show a ≤ a by grind) hb hY₁
  by_cases hX_zero : IsZero X
  · exact σ.slicing.intervalProp_of_triangle C (Or.inl hX_zero) hY₁ hTQ
  · have hX_phase_gt :
        ψ < wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) :=
      wPhaseOf_gt_of_upper_boundary_triangle
        (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hab₂ hb hSS.1 hX_ge hY₁ hX_zero
        hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin hTQ
    by_cases hY_zero : IsZero Y
    · haveI : IsIso fX :=
        (Triangle.isZero₃_iff_isIso₁ (Triangle.mk fX gY δY) hTQ).mp hY_zero
      have hX_phase_eq :
          wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) = ψ := by
        rw [K₀.of_iso C (asIso fX)]
        simpa [StabilityCondition.skewedStabilityFunction_of_near] using hSS.2.2.2.1
      linarith
    · letI : Fact (a < b₂) := ⟨hab₂⟩
      letI : Fact (b₂ - a ≤ 1) := ⟨by grind⟩
      let EI₂ : σ.slicing.IntervalCat C a b₂ := ⟨E, hSS.1⟩
      let XI₂ : σ.slicing.IntervalCat C a b₂ := ⟨X, hX₂⟩
      let YI₂ : σ.slicing.IntervalCat C a b₂ := ⟨Y, hY₂⟩
      let xE : XI₂ ⟶ EI₂ := ObjectProperty.homMk fX
      let qY : EI₂ ⟶ YI₂ := ObjectProperty.homMk gY
      let hcomp : xE ≫ qY = 0 := by
        ext
        simpa [xE, qY] using comp_distTriang_mor_zero₁₂ _ hTQ
      let S : ShortComplex (σ.slicing.IntervalCat C a b₂) := ShortComplex.mk xE qY hcomp
      have hT₂ : Triangle.mk S.f.hom S.g.hom δY ∈ distTriang C := by
        simpa [S, xE, qY] using hTQ
      have hS : StrictShortExact S :=
        Slicing.IntervalCat.strictShortExact_of_distTriang
          (C := C) (s := σ.slicing) (a := a) (b := b₂) hT₂
      have hqY_strict : IsStrictEpi qY := ⟨hS.shortExact.epi_g, hS.strict_g⟩
      let hpert₂ := hperturb_of_stabSeminorm C σ W hW hthin₂' hε₀ hε₀2 hsin
      have hW_interval :
          ∀ {F : C}, σ.slicing.intervalProp C a b₂ F → ¬IsZero F → W (K₀.of C F) ≠ 0 := by
        intro F hF hFne
        exact σ.W_ne_zero_of_intervalProp C W hthin₂'
          (stabSeminorm_lt_cos_of_hsin_hthin
            (C := C) (σ := σ) (W := W) hab₂ hε₀ hthin₂ hsin) hFne hF
      have hY_phase_ge :
          ψ ≤ wPhaseOf (W (K₀.of C Y)) ((a + b₂) / 2) := by
        let ssf₂ := σ.skewedStabilityFunction_of_near C W hW hab₂
        simpa [StabilityCondition.skewedStabilityFunction_of_near, EI₂, YI₂, qY] using
          (SkewedStabilityFunction.phase_le_of_strictQuotient
            (C := C) (σ := σ) (a := a) (b := b₂) (ssf := ssf₂)
            (X := EI₂) (Y := YI₂) hSS hε₀ hthin₂ hW_interval hpert₂ qY hqY_strict hY_zero)
      have henv_hi₂ : ψ ≤ b₂ - ε₀ := by
        linarith
      have hX_range :
          wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hX₂ hX_zero hε₀ hε₀2 henv_lo henv_hi₂
          hthin₂ hsin
      have hY_range :
          wPhaseOf (W (K₀.of C Y)) ((a + b₂) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hY₂ hY_zero hε₀ hε₀2 henv_lo henv_hi₂
          hthin₂ hsin
      have hsum :
          W (K₀.of C E) = W (K₀.of C X) + W (K₀.of C Y) := by
        simpa [map_add] using congrArg W
          (K₀.of_triangle C (Triangle.mk fX gY δY) hTQ)
      have hY_phase_lt :
          wPhaseOf (W (K₀.of C Y)) ((a + b₂) / 2) < ψ := by
        exact wPhaseOf_seesaw_dual hsum.symm
          (by simpa [StabilityCondition.skewedStabilityFunction_of_near] using hSS.2.2.2.1)
          hX_phase_gt (hW_interval hX₂ hX_zero) hX_range hY_range
      linarith

theorem intervalProp_of_wSemistable_lower_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b ψ ε₀ : ℝ} (ha₁ : a₁ < b) (ha₂ : a₂ < b) (ha : a₁ ≤ a₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW ha₁).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a₂ + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin₁ : b - a₁ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    σ.slicing.intervalProp C a₂ b E := by
  obtain ⟨X, Y, fX, gY, δY, hTQ, hX₂, hY_le⟩ :=
    exists_lower_boundary_triangle (C := C) (s := σ.slicing)
      (a₁ := a₂) (a₂ := a₁) (b := b) ha₂ hSS.1
  have hY₁ : σ.slicing.intervalProp C a₁ b Y :=
    intervalProp_of_lower_boundary_triangle (C := C) (s := σ.slicing)
      (a₁ := a₂) (a₂ := a₁) (b := b) ha₂ ha hSS.1 hX₂ hY_le hTQ
  by_cases hY_zero : IsZero Y
  · exact σ.slicing.intervalProp_of_triangle C hX₂ (Or.inl hY_zero) hTQ
  · have hY_phase_lt :
      wPhaseOf (W (K₀.of C Y)) ((a₁ + b) / 2) < ψ :=
      wPhaseOf_lt_of_lower_boundary_triangle
        (C := C) (σ := σ) (W := W) (hW := hW) ha₂ ha hSS.1 hX₂ hY_le hY_zero
        hε₀ hε₀2 henv_lo henv_hi hthin₁ hsin hTQ
    letI : Fact (a₁ < b) := ⟨ha₁⟩
    letI : Fact (b - a₁ ≤ 1) := ⟨by grind⟩
    have hX₁ : σ.slicing.intervalProp C a₁ b X :=
      σ.slicing.intervalProp_mono C ha (show b ≤ b by grind) hX₂
    let EI₁ : σ.slicing.IntervalCat C a₁ b := ⟨E, hSS.1⟩
    let XI₁ : σ.slicing.IntervalCat C a₁ b := ⟨X, hX₁⟩
    let YI₁ : σ.slicing.IntervalCat C a₁ b := ⟨Y, hY₁⟩
    let xE : XI₁ ⟶ EI₁ := ObjectProperty.homMk fX
    let qY : EI₁ ⟶ YI₁ := ObjectProperty.homMk gY
    let hcomp : xE ≫ qY = 0 := by
      ext
      simpa [xE, qY] using comp_distTriang_mor_zero₁₂ _ hTQ
    let S : ShortComplex (σ.slicing.IntervalCat C a₁ b) := ShortComplex.mk xE qY hcomp
    have hT₁ : Triangle.mk S.f.hom S.g.hom δY ∈ distTriang C := by
      simpa [S, xE, qY] using hTQ
    have hS : StrictShortExact S :=
      Slicing.IntervalCat.strictShortExact_of_distTriang
        (C := C) (s := σ.slicing) (a := a₁) (b := b) hT₁
    have hqY_strict : IsStrictEpi qY := ⟨hS.shortExact.epi_g, hS.strict_g⟩
    have hthin₁' : b - a₁ < 1 := by
      linarith
    let hpert₁ := hperturb_of_stabSeminorm C σ W hW hthin₁' hε₀ hε₀2 hsin
    have hW_interval :
        ∀ {F : C}, σ.slicing.intervalProp C a₁ b F → ¬IsZero F → W (K₀.of C F) ≠ 0 := by
      intro F hF hFne
      exact σ.W_ne_zero_of_intervalProp C W hthin₁'
        (stabSeminorm_lt_cos_of_hsin_hthin
          (C := C) (σ := σ) (W := W) ha₁ hε₀ hthin₁ hsin) hFne hF
    have hY_phase_ge :
        ψ ≤ wPhaseOf (W (K₀.of C Y)) ((a₁ + b) / 2) := by
      let ssf₁ := σ.skewedStabilityFunction_of_near C W hW ha₁
      simpa [StabilityCondition.skewedStabilityFunction_of_near, EI₁, YI₁, qY] using
        (SkewedStabilityFunction.phase_le_of_strictQuotient
          (C := C) (σ := σ) (a := a₁) (b := b) (ssf := ssf₁)
          (X := EI₁) (Y := YI₁) hSS hε₀ hthin₁ hW_interval hpert₁ qY hqY_strict hY_zero)
    linarith


end CategoryTheory.Triangulated
