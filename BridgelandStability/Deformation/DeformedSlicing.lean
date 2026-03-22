/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.DeformedSlicingHN

/-!
# Deformed Slicing Construction

Construction of the deformed slicing Q from a stability condition σ and a nearby
central charge W. The slicing Q has Q(ψ) = deformedPred σ W ψ.
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

/-! ### Deformed slicing construction -/

variable [IsTriangulated C] in
/-- **Deformed slicing** (Node 7.Q + 7.6 + 7.7). The slicing `Q` with `Q(ψ) =
deformedPred σ W hW ε ψ`, where `ε` is the perturbation parameter (`ε < ε₀`) and
`ε₀` is the local finiteness parameter (< 1/10).

The `closedUnderIso` and `shift_iff` fields are complete. The `hom_vanishing` field
is Lemma 7.6 via `hom_eq_zero_of_deformedPred`. The `hn_exists` field delegates to
`deformedSlicing_hn_exists`, which combines `deformedGtLe_triangle` (sorry: iterated
octahedral assembly over σ-HN factors) with
`exists_hn_of_deformedGt_deformedLe_triangle`. -/
def StabilityCondition.deformedSlicing (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    Slicing C where
  P := σ.deformedPred C W hW ε
  closedUnderIso := fun φ ↦ ⟨fun {E E'} e h ↦ by
    rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
    · exact Or.inl ((Iso.isZero_iff e).mp hZ)
    · refine Or.inr ⟨a, b, hab, hthin, henv_lo, henv_hi, ?_, fun h ↦ hSS.2.1
        ((Iso.isZero_iff e).mpr h), ?_, ?_, fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
      · -- intervalProp: transport via HNFiltration.ofIso
        rcases hSS.1 with hZ' | ⟨F, hF⟩
        · exact absurd hZ' hSS.2.1
        · exact Or.inr ⟨F.ofIso C e, hF⟩
      · -- W(K₀.of C E') ≠ 0
        rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]; exact hSS.2.2.1
      · -- wPhaseOf = φ
        rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]; exact hSS.2.2.2.1
      · -- semistability: compose triangle with iso
        have hT' : Triangle.mk (f₁ ≫ e.inv) (e.hom ≫ f₂) f₃ ∈ distTriang C :=
          isomorphic_distinguished _ hT _
            (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
              (by simp) (by simp) (by simp))
        exact hSS.2.2.2.2 hT' hK hQ hKne⟩
  zero_mem ψ := σ.deformedPred_zero C W hW ε ψ (isZero_zero C)
  shift_iff := fun φ X ↦ by
    constructor
    · -- Forward: deformedPred φ X → deformedPred (φ+1) (X⟦1⟧)
      intro h
      rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
      · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
      · -- Use interval (a+1, b+1) with α' = (a+b)/2 + 1
        refine Or.inr ⟨a + 1, b + 1, by linarith, by linarith, by linarith, by linarith,
          ?_, fun h ↦ hSS.2.1
          (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) X h), ?_,
          ?_, fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
        · -- intervalProp C (a+1) (b+1) (X⟦1⟧)
          rcases hSS.1 with hZ' | ⟨F, hF⟩
          · exact absurd hZ' hSS.2.1
          · exact Or.inr ⟨F.shiftHN C σ.slicing 1, fun i ↦ by
              simp only [HNFiltration.shiftHN, Int.cast_one]
              constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
        · -- W(K₀.of C (X⟦1⟧)) ≠ 0
          rw [K₀.of_shift_one, map_neg]
          exact neg_ne_zero.mpr hSS.2.2.1
        · -- wPhaseOf(W(K₀.of C (X⟦1⟧))) ((a+b)/2 + 1) = φ + 1
          change wPhaseOf (W (K₀.of C (X⟦(1 : ℤ)⟧))) ((a + 1 + (b + 1)) / 2) = φ + 1
          rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by grind]
          rw [K₀.of_shift_one, map_neg]
          have hphase : wPhaseOf (W (K₀.of C X)) ((a + b) / 2) = φ := hSS.2.2.2.1
          have hWne : W (K₀.of C X) ≠ 0 := hSS.2.2.1
          exact (wPhaseOf_neg hWne _).trans (by grind)
        · -- Semistability transport: shift K → X⟦1⟧ → Q by -1, compose with iso
          -- to get K⟦-1⟧ → X → Q⟦-1⟧ (dist), apply X's semistability
          have hT_sh := Triangle.shift_distinguished _ hT (-1 : ℤ)
          -- Build triangle with obj₂ = X via iso (X⟦1⟧)⟦-1⟧ ≅ X
          have h10 : (1 : ℤ) + (-1 : ℤ) = 0 := by grind
          let eX := (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) h10).app X
          let shT := (Triangle.shiftFunctor C (-1)).obj (Triangle.mk f₁ f₂ f₃)
          set T' := Triangle.mk (shT.mor₁ ≫ eX.hom) (eX.inv ≫ shT.mor₂) shT.mor₃
          have hT' : T' ∈ distTriang C :=
            isomorphic_distinguished _ hT_sh _
              (Triangle.isoMk T' shT
                (Iso.refl _) eX.symm (Iso.refl _)
                (by simp [T'])
                (by change (eX.inv ≫ shT.mor₂) ≫ 𝟙 _ = eX.symm.hom ≫ shT.mor₂
                    simp [Iso.symm])
                (by simp [T']))
          -- K⟦-1⟧ ∈ P((a,b)), Q⟦-1⟧ ∈ P((a,b))
          have hK1 : σ.slicing.intervalProp C a b (K⟦(-1 : ℤ)⟧) := by
            rcases hK with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing (-1), fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hQ1 : σ.slicing.intervalProp C a b (Q⟦(-1 : ℤ)⟧) := by
            rcases hQ with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing (-1), fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hKne1 : ¬IsZero (K⟦(-1 : ℤ)⟧) := fun h ↦
            hKne (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (-1 : ℤ)) K h)
          -- Apply X's semistability
          have hsem : wPhaseOf (W (K₀.of C (K⟦(-1 : ℤ)⟧))) ((a + b) / 2) ≤ φ :=
            hSS.2.2.2.2 hT' hK1 hQ1 hKne1
          rw [K₀.of_shift_neg_one, map_neg] at hsem
          -- hsem : wPhaseOf (-W (K₀.of C K)) ((a + b) / 2) ≤ φ
          change wPhaseOf (W (K₀.of C K)) ((a + 1 + (b + 1)) / 2) ≤ φ + 1
          rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by grind]
          by_cases hWK : W (K₀.of C K) = 0
          · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; grind
          · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by grind] at key
            have key2 := wPhaseOf_add_two hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 2 = (a + b) / 2 + 1 from by grind] at key2
            linarith
    · -- Backward: deformedPred (φ+1) (X⟦1⟧) → deformedPred φ X
      intro h
      rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
      · exact Or.inl (IsZero.of_full_of_faithful_of_isZero
          (shiftFunctor C (1 : ℤ)) X hZ)
      · -- Use interval (a-1, b-1) with α' = (a+b)/2 - 1
        refine Or.inr ⟨a - 1, b - 1, by linarith, by linarith, by linarith, by linarith, ?_,
          fun h ↦ hSS.2.1 ((shiftFunctor C (1 : ℤ)).map_isZero h), ?_, ?_,
          fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
        · -- intervalProp C (a-1) (b-1) X from intervalProp C a b (X⟦1⟧)
          rcases hSS.1 with hZ' | ⟨F, hF⟩
          · exact absurd hZ' hSS.2.1
          · exact Or.inr ⟨(F.shiftHN C σ.slicing (-1)).ofIso C
              ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by grind)).app X),
              fun i ↦ by
                change a - 1 < (F.shiftHN C σ.slicing (-1)).φ i ∧
                  (F.shiftHN C σ.slicing (-1)).φ i < b - 1
                simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
        · -- W(K₀.of C X) ≠ 0
          change W (K₀.of C X) ≠ 0
          intro h; exact hSS.2.2.1 (show W (K₀.of C (X⟦(1 : ℤ)⟧)) = 0 from by
            rw [K₀.of_shift_one, map_neg, h, neg_zero])
        · -- wPhaseOf(W(K₀.of C X)) ((a-1+b-1)/2) = φ
          change wPhaseOf (W (K₀.of C X)) ((a - 1 + (b - 1)) / 2) = φ
          rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by grind]
          -- hSS.2.2.2.1 : wPhaseOf (W (K₀.of C (X⟦1⟧))) ((a+b)/2) = φ + 1
          have hphase : wPhaseOf (-W (K₀.of C X)) ((a + b) / 2) = φ + 1 := by
            have := hSS.2.2.2.1
            rwa [K₀.of_shift_one, map_neg] at this
          have hWne : W (K₀.of C X) ≠ 0 := by
            intro h; apply hSS.2.2.1
            change W (K₀.of C (X⟦(1 : ℤ)⟧)) = 0
            rw [K₀.of_shift_one, map_neg, neg_eq_zero]
            exact h
          have key := wPhaseOf_neg hWne ((a + b) / 2 - 1)
          rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by grind] at key
          linarith
        · -- Semistability: transport via ⟦1⟧
          -- Shift triangle K → X → Q by 1 to get K⟦1⟧ → X⟦1⟧ → Q⟦1⟧
          have hT' := Triangle.shift_distinguished _ hT (1 : ℤ)
          -- K⟦1⟧ ∈ P((a,b)), Q⟦1⟧ ∈ P((a,b))
          have hK1 : σ.slicing.intervalProp C a b (K⟦(1 : ℤ)⟧) := by
            rcases hK with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing 1, fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hQ1 : σ.slicing.intervalProp C a b (Q⟦(1 : ℤ)⟧) := by
            rcases hQ with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing 1, fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hKne1 : ¬IsZero (K⟦(1 : ℤ)⟧) := fun h ↦
            hKne (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) K h)
          -- Apply X⟦1⟧'s semistability
          have hsem : wPhaseOf (W (K₀.of C (K⟦(1 : ℤ)⟧))) ((a + b) / 2) ≤ φ + 1 :=
            hSS.2.2.2.2 hT' hK1 hQ1 hKne1
          rw [K₀.of_shift_one, map_neg] at hsem
          -- hsem : wPhaseOf (-W (K₀.of C K)) ((a + b) / 2) ≤ φ + 1
          change wPhaseOf (W (K₀.of C K)) ((a - 1 + (b - 1)) / 2) ≤ φ
          rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by grind]
          by_cases hWK : W (K₀.of C K) = 0
          · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; grind
          · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by grind] at key
            linarith
  hom_vanishing ψ₁ ψ₂ A B hlt hA hB f :=
    σ.hom_eq_zero_of_deformedPred C W hW hε (by grind) (by grind) hsin hA hB hlt f
  hn_exists := fun E ↦
    deformedSlicing_hn_exists C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin E

/-- **W-compatibility of the deformed slicing.** For every nonzero Q-semistable object `E`
of Q-phase `ψ`, the central charge `W([E])` lies on the ray `ℝ₊ · exp(iπψ)`. This
follows directly from the `Semistable` definition, which stores
`wPhaseOf(W([E]), α) = ψ`. -/
theorem StabilityCondition.deformedSlicing_compat
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (ψ : ℝ) (E : C)
    (hQ : (σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin).P ψ E)
    (hE : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      W (K₀.of C E) = ↑m * Complex.exp (↑(Real.pi * ψ) * Complex.I) := by
  -- hQ : deformedPred, so either IsZero or ∃ a b hab hthin, Semistable
  rcases hQ with hEZ | ⟨a, b, hab, _, _, _, hSS⟩
  · exact absurd hEZ hE
  · exact ⟨‖W (K₀.of C E)‖, norm_pos_iff.mpr hSS.2.2.1, hSS.polar⟩

/-! #### Step A4: Main theorem -/

/-- **Reverse phase confinement**. If `E` is σ-semistable of phase `φ` and
`‖W - Z‖_σ < sin(πε)`, then `E` lies in the Q-interval `(φ - 2ε - δ, φ + 4ε + δ)`
for any `δ > 0`.

This replaces the incorrect statement `sigma_semistable_is_deformedPred` which claimed
σ-semistable implies Q-semistable. That is **false**: a σ-semistable object `E` can
decompose into W-semistable factors with different W-phases (e.g., `E = S₁ ⊕ S₂` with
`S₁, S₂` σ-stable of the same phase but different W-phases), so `E` need not be
Q-semistable. The correct statement is that `E` lies in the larger Q-interval
`(φ - 2ε - δ, φ + 4ε + δ)`.

The proof applies `sigmaSemistable_hasDeformedHN` to obtain a Q-HN filtration for `E`
whose factors have phases in `(φ - 2ε, φ + 4ε)`, then enlarges this by `δ`.
-/
theorem sigma_semistable_intervalProp
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    {δ : ℝ} (hδ : 0 < δ) :
    (σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin).intervalProp C
      (φ - 2 * ε - δ) (φ + 4 * ε + δ) E := by
  -- Apply sigmaSemistable_hasDeformedHN to get Q-HN with phases in (φ-2ε, φ+4ε).
  -- Then enlarge by δ to get the desired Q-interval bound.
  obtain ⟨G, hGφ⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin hP hE
  exact Or.inr ⟨G, fun j ↦ ⟨by linarith [(hGφ j).1], by linarith [(hGφ j).2]⟩⟩

theorem deformed_intervalProp_subset_sigma_intervalProp
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (t : ℝ) :
    (σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin).intervalProp C
        (t - ε₀) (t + ε₀) ≤
      σ.slicing.intervalProp C (t - 2 * ε₀) (t + 2 * ε₀) := by
  intro X hX
  rcases hX with hZ | ⟨F, hF⟩
  · exact Or.inl hZ
  · apply intervalProp_of_postnikovTower C σ.slicing F.toPostnikovTower
    intro i
    have hsem := F.semistable i
    change σ.deformedPred C W hW ε (F.φ i) _ at hsem
    rcases hsem with hZ_i | ⟨a_i, b_i, hab_i, hthin_i, _, _, hSS_i⟩
    · exact Or.inl hZ_i
    · have ⟨hlo, hhi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab_i
        hε (by grind) hthin_i hsin hSS_i
      exact σ.slicing.intervalProp_of_intrinsic_phases C hSS_i.2.1
        (by
          have hleft := (hF i).1
          linarith)
        (by
          have hright := (hF i).2
          linarith)

end CategoryTheory.Triangulated
