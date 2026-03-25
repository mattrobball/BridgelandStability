/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.PhaseConfinement

/-!
# Target Envelope and Seminorm Corollaries

Phase confinement corollaries: stabSeminorm-based bounds, gtProp/ltProp from
W-semistability, target envelope tests, interval inclusion phase estimates.
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
    {a b ε₀ : ℝ} (hab : a < b) (hε₀ : 0 < ε₀)
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
    · nlinarith [Real.pi_pos, hthin, hε₀]
  have hcos_pos : 0 < Real.cos (Real.pi * (b - a) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos, hab]
    · nlinarith [Real.pi_pos, hthin, hε₀]
  exact lt_trans hsin ((ENNReal.ofReal_lt_ofReal_iff hcos_pos).mpr hsin_lt_cos)

theorem wPhaseOf_eq_of_intervalProp_upper_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
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
  have hWneE : W (K₀.of C E) ≠ 0 :=
    σ.W_ne_zero_of_intervalProp C W hthin₁'
      (stabSeminorm_lt_cos_of_hsin_hthin
        (C := C) (σ := σ) (W := W) hab₁ hε₀ hthin₁ hsin) hEne hI
  exact wPhaseOf_indep hWneE _ _ hbranch

theorem wPhaseOf_eq_of_intervalProp_lower_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a₁ a₂ b ε₀ : ℝ} (ha₁ : a₁ < b) (ha : a₂ ≤ a₁)
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
  have hWneE : W (K₀.of C E) ≠ 0 :=
    σ.W_ne_zero_of_intervalProp C W hthin₁'
      (stabSeminorm_lt_cos_of_hsin_hthin
        (C := C) (σ := σ) (W := W) ha₁ hε₀ hthin₁ hsin) hEne hI
  exact wPhaseOf_indep hWneE _ _ hbranch

theorem wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
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
        exact hEne (F.toPostnikovTower.zero_isZero (by lia))
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
