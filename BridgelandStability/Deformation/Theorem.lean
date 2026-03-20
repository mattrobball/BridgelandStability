/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.DeformedSlicing

/-!
# Deformation Theorem (Theorem 7.1)

The main deformation theorem: given a stability condition σ and a nearby central charge W,
there exists a stability condition τ = (W, Q) with d(P, Q) ≤ ε.
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

/-! ### Deformation theorem (Theorem 7.1) -/

variable [IsTriangulated C] in
/-- A quantitative helper for **Bridgeland's Theorem 7.1**. Given a
stability condition `σ = (Z, P)` on a triangulated category `D` and a group
homomorphism `W : K₀(D) → ℂ` with `‖W - Z‖_σ < sin(πε)` for some `0 < ε < ε₀`
(where `ε₀` comes from the local finiteness of `σ`), there exists a locally-finite
stability condition `τ = (W, Q)` with `d(P, Q) ≤ ε`.

The proof constructs the deformed slicing `Q` via `deformedSlicing`, then verifies:
1. **Hom-vanishing** (Lemma 7.6): `hom_eq_zero_of_deformedPred`
2. **HN filtrations** (Lemma 7.7 + Nodes 7.8–7.9): well-founded recursion in thin
   quasi-abelian categories, assembled via t-structures `Q(> t)`
3. **Compatibility**: `deformedSlicing_compat`
4. **Local finiteness**: inherited from `σ` via the interval inclusion
   `Q((t-ε₀,t+ε₀)) ⊆ P((t-2ε₀,t+2ε₀))`
5. **Distance bound**: `d(P, Q) ≤ ε` by phase confinement (Node 7.3)
-/
theorem bridgeland_7_1_le (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    ∃ (τ : StabilityCondition C), τ.Z = W ∧
      slicingDist C σ.slicing τ.slicing ≤ ENNReal.ofReal ε := by
  have hε₀8 : ε₀ < 1 / 8 := by linarith
  have hε₀2 : ε₀ < 1 / 4 := by linarith
  let hSector : SectorFiniteLength (C := C) σ ε₀ hε₀ hε₀2 :=
    SectorFiniteLength.of_wide (C := C) σ hε₀ hε₀2 hε₀8 hWide
  refine ⟨⟨σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin, W,
    σ.deformedSlicing_compat C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin, ?_⟩, rfl, ?_⟩
  · -- Local finiteness: inherited from σ via Q((t-ε₀,t+ε₀)) ⊆ P((t-2ε₀,t+2ε₀))
    constructor
    refine ⟨ε₀, hε₀, by linarith, fun t E ↦ ?_⟩
    letI : Fact (t - ε₀ < t + ε₀) := ⟨by linarith [hε₀]⟩
    letI : Fact ((t + ε₀) - (t - ε₀) ≤ 1) := ⟨by linarith [hε₀10]⟩
    letI : Fact (t - 2 * ε₀ < t + 2 * ε₀) := ⟨by linarith [hε₀]⟩
    letI : Fact ((t + 2 * ε₀) - (t - 2 * ε₀) ≤ 1) := ⟨by linarith [hε₀10]⟩
    have hIncl :
        (σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin).intervalProp C
            (t - ε₀) (t + ε₀) ≤
          σ.slicing.intervalProp C (t - 2 * ε₀) (t + 2 * ε₀) :=
      deformed_intervalProp_subset_sigma_intervalProp C σ W hW hε₀ hε₀10 hWide hε hεε₀
        hsin t
    have hbig :
        IsStrictArtinianObject ((ObjectProperty.ιOfLE hIncl).obj E) ∧
          IsStrictNoetherianObject ((ObjectProperty.ιOfLE hIncl).obj E) := by
      simpa [hSector] using hSector t ((ObjectProperty.ιOfLE hIncl).obj E)
    haveI : IsStrictArtinianObject ((ObjectProperty.ιOfLE hIncl).obj E) := hbig.1
    haveI : IsStrictNoetherianObject ((ObjectProperty.ιOfLE hIncl).obj E) := hbig.2
    have hstrictE :
        IsStrictArtinianObject E ∧ IsStrictNoetherianObject E :=
      interval_strictFiniteLength_of_inclusion_strict (C := C)
        (s₁ := σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin)
        (s₂ := σ.slicing)
        (a₁ := t - ε₀) (b₁ := t + ε₀) (a₂ := t - 2 * ε₀) (b₂ := t + 2 * ε₀)
        hIncl (X := E)
    haveI : IsStrictArtinianObject E := hstrictE.1
    haveI : IsStrictNoetherianObject E := hstrictE.2
    exact ⟨inferInstance, inferInstance⟩
  · -- Distance bound: d(P, Q) ≤ ε by phase confinement
    set Q := σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin
    have deformedGtPred_subset_gtProp :
        ∀ {t : ℝ} {E : C},
          σ.deformedGtPred C W hW ε hε (by linarith) hsin t E →
            Q.gtProp C t E := by
      intro t E hE
      induction hE with
      | zero hZ =>
          exact Or.inl hZ
      | mem hE =>
          rename_i E'
          rcases hE with ⟨ψ, hψ, hQ⟩
          have hQ' : Q.P ψ E' := by
            simpa [Q, StabilityCondition.deformedSlicing] using hQ
          exact Q.gtProp_of_semistable C ψ t E' hQ' hψ
      | ext hT _ _ ihX ihY =>
          exact Q.gtProp_of_triangle C t ihX ihY hT
    have deformedLtPred_subset_ltProp :
        ∀ {t : ℝ} {E : C},
          σ.deformedLtPred C W hW ε hε (by linarith) hsin t E →
            Q.ltProp C t E := by
      intro t E hE
      induction hE with
      | zero hZ =>
          exact Or.inl hZ
      | mem hE =>
          rename_i E'
          rcases hE with ⟨ψ, hψ, hQ⟩
          have hQ' : Q.P ψ E' := by
            simpa [Q, StabilityCondition.deformedSlicing] using hQ
          exact Or.inr ⟨HNFiltration.single C E' ψ hQ',
            show 0 < 1 from by omega, hψ⟩
      | ext hT _ _ ihX ihY =>
          exact Q.ltProp_of_triangle C t ihX ihY hT
    -- Forward: Q-HN factors → phase confinement → σ-intervalProp
    have forward : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
        σ.slicing.intervalProp C
          (Q.phiMinus C E hE - ε - δ) (Q.phiPlus C E hE + ε + δ) E := by
      intro E hE δ hδ
      obtain ⟨G, hnG, hfirstG, hlastG⟩ := HNFiltration.exists_both_nonzero C Q hE
      apply intervalProp_of_postnikovTower C σ.slicing G.toPostnikovTower
      intro i
      by_cases hGi : IsZero (G.toPostnikovTower.factor i)
      · exact Or.inl hGi
      · have hsem := G.semistable i
        change σ.deformedPred C W hW ε hε (by linarith) hsin (G.φ i) _ at hsem
        rcases hsem with hZ_i | ⟨a_i, b_i, hab_i, hthin_i, _, _, hSS_i⟩
        · exact absurd hZ_i hGi
        · have ⟨hlo, hhi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab_i
            hε (by linarith) hthin_i hsin hSS_i
          have hGi_le : G.φ i ≤ Q.phiPlus C E hE := by
            rw [Q.phiPlus_eq C E hE G hnG hfirstG]
            exact G.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
          have hGi_ge : Q.phiMinus C E hE ≤ G.φ i := by
            rw [Q.phiMinus_eq C E hE G hnG hlastG]
            exact G.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
          exact σ.slicing.intervalProp_of_intrinsic_phases C hSS_i.2.1
            (by linarith) (by linarith)
    -- Reverse: σ-HN factors → reverse phase confinement → Q-intervalProp
    have reverse : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
        Q.intervalProp C
          (σ.slicing.phiMinus C E hE - ε - δ)
          (σ.slicing.phiPlus C E hE + ε + δ) E := by
      intro E hE δ hδ
      obtain ⟨F, hnF, hfirstF, hlastF⟩ :=
        HNFiltration.exists_both_nonzero C σ.slicing hE
      have hgt : Q.gtProp C (σ.slicing.phiMinus C E hE - ε - δ) E := by
        apply gtProp_of_postnikovTower (C := C) Q F.toPostnikovTower
        intro i
        by_cases hFi : IsZero (F.toPostnikovTower.factor i)
        · exact Or.inl hFi
        · have hFi_ge : σ.slicing.phiMinus C E hE ≤ F.φ i := by
            rw [σ.slicing.phiMinus_eq C E hE F hnF hlastF]
            exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
          exact deformedGtPred_subset_gtProp <|
            P_in_deformedGtPred C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin
              (by linarith [hFi_ge, hδ]) (F.semistable i) hFi
      have hlt : Q.ltProp C (σ.slicing.phiPlus C E hE + ε + δ) E := by
        apply ltProp_of_postnikovTower (C := C) Q F.toPostnikovTower
        intro i
        by_cases hFi : IsZero (F.toPostnikovTower.factor i)
        · exact Or.inl hFi
        · have hFi_le : F.φ i ≤ σ.slicing.phiPlus C E hE := by
            rw [σ.slicing.phiPlus_eq C E hE F hnF hfirstF]
            exact F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
          exact deformedLtPred_subset_ltProp <|
            P_in_deformedLtPred C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin
              (by linarith [hFi_le, hδ]) (F.semistable i) hFi
      exact Q.intervalProp_of_intrinsic_phases C hE
        (Q.phiMinus_gt_of_gtProp C hE hgt)
        (Q.phiPlus_lt_of_ltProp C hE hlt)
    -- Combine: |σ.phiPlus - Q.phiPlus| ≤ ε and |σ.phiMinus - Q.phiMinus| ≤ ε
    apply slicingDist_le_of_phase_bounds
    · -- |σ.phiPlus(E) - Q.phiPlus(E)| ≤ ε
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiPlus(E) ≤ σ.phiPlus(E) + ε
        by_contra h; push_neg at h
        have := Q.phiPlus_lt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < Q.phiPlus C E hE -
            σ.slicing.phiPlus C E hE - ε))
        linarith
      · -- σ.phiPlus(E) ≤ Q.phiPlus(E) + ε
        by_contra h; push_neg at h
        have := σ.slicing.phiPlus_lt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiPlus C E hE -
            Q.phiPlus C E hE - ε))
        linarith
    · -- |σ.phiMinus(E) - Q.phiMinus(E)| ≤ ε
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiMinus(E) - ε ≤ σ.phiMinus(E)
        by_contra h; push_neg at h
        have := σ.slicing.phiMinus_gt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < Q.phiMinus C E hE -
            σ.slicing.phiMinus C E hE - ε))
        linarith
      · -- σ.phiMinus(E) ≤ Q.phiMinus(E) + ε
        by_contra h; push_neg at h
        have := Q.phiMinus_gt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiMinus C E hE -
            Q.phiMinus C E hE - ε))
        linarith

variable [IsTriangulated C] in
/-- **Bridgeland's Theorem 7.1** (deformation of stability conditions). Under the
usual small-deformation hypothesis on `W`, there exists a locally-finite stability
condition `τ = (W, Q)` with `d(P, Q) < ε`.

This is obtained from `bridgeland_7_1_le` by shrinking `ε` slightly using the strict
hypothesis `‖W - Z‖_σ < sin(πε)`. -/
theorem bridgeland_7_1 (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    ∃ (τ : StabilityCondition C), τ.Z = W ∧
      slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε := by
  set x := (stabSeminorm C σ (W - σ.Z)).toReal
  have hx_lt : x < Real.sin (Real.pi * ε) := by
    dsimp [x]
    exact ENNReal.toReal_lt_of_lt_ofReal hsin
  have hε_half : ε < 1 / 2 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi * ε) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos, hε]
    · nlinarith [Real.pi_pos, hε_half]
  set y := (x + Real.sin (Real.pi * ε)) / 2
  have hy_between : x < y ∧ y < Real.sin (Real.pi * ε) := by
    dsimp [y]
    constructor <;> linarith
  have hy_pos : 0 < y := by
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      exact ENNReal.toReal_nonneg
    linarith
  have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · linarith
    · have hy_le : y ≤ Real.sin (Real.pi * ε) := le_of_lt hy_between.2
      exact le_trans hy_le (Real.sin_le_one _)
  set ε' : ℝ := Real.arcsin y / Real.pi
  have hε'_pos : 0 < ε' := by
    dsimp [ε']
    exact div_pos (Real.arcsin_pos.2 hy_pos) Real.pi_pos
  have hpiε_mem : Real.pi * ε ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos, hε_half]
  have hε'_lt : ε' < ε := by
    have harcsin_lt : Real.arcsin y < Real.pi * ε := by
      exact (Real.arcsin_lt_iff_lt_sin hy_mem hpiε_mem).2 hy_between.2
    have hdiv : Real.arcsin y / Real.pi < ε := by
      refine (div_lt_iff₀ Real.pi_pos).2 ?_
      nlinarith
    simpa [ε'] using hdiv
  have hε'ε₀ : ε' < ε₀ := by
    exact lt_trans hε'_lt hεε₀
  have hsin'_eq : Real.sin (Real.pi * ε') = y := by
    have hpiε' : Real.pi * ε' = Real.arcsin y := by
      dsimp [ε']
      field_simp [ne_of_gt Real.pi_pos]
    rw [hpiε']
    exact Real.sin_arcsin hy_mem.1 hy_mem.2
  have hsin'_pos : 0 < Real.sin (Real.pi * ε') := by
    rw [hsin'_eq]
    exact hy_pos
  have hsin' : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε')) := by
    have hx_ne_top : stabSeminorm C σ (W - σ.Z) ≠ ⊤ := ne_top_of_lt hsin
    have hx_lt' : (stabSeminorm C σ (W - σ.Z)).toReal <
        (ENNReal.ofReal (Real.sin (Real.pi * ε'))).toReal := by
      rw [ENNReal.toReal_ofReal (le_of_lt hsin'_pos)]
      simpa [x, hsin'_eq] using hy_between.1
    exact (ENNReal.toReal_lt_toReal hx_ne_top ENNReal.ofReal_ne_top).1 hx_lt'
  obtain ⟨τ, hτZ, hτdist⟩ :=
    bridgeland_7_1_le C σ W hW ε₀ hε₀ hε₀10 hWide ε' hε'_pos hε'ε₀ hsin'
  refine ⟨τ, hτZ, lt_of_le_of_lt hτdist ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hε'_lt

end CategoryTheory.Triangulated
