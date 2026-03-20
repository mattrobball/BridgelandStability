/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.DeformedGtLe

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


/-!
# Deformed Slicing HN Existence

Shift lemmas for deformedPred, closure lemmas for Q(>t)/Q(≤t),
truncation-zero lemmas, and the main `deformedSlicing_hn_exists` theorem.
-/

/-! ### Shift lemmas for Q-HN existence -/

variable [IsTriangulated C] in
/-- Forward shift for `deformedPred`: if `E` is Q-semistable of phase `φ`, then `E⟦1⟧`
is Q-semistable of phase `φ + 1`. Extracted from `deformedSlicing.shift_iff`. -/
theorem deformedPred_shift_one
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {φ : ℝ} {X : C}
    (h : σ.deformedPred C W hW ε hε hε2 hsin φ X) :
    σ.deformedPred C W hW ε hε hε2 hsin (φ + 1) (X⟦(1 : ℤ)⟧) := by
  rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
  · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
  · refine Or.inr ⟨a + 1, b + 1, by linarith, by linarith, by linarith, by linarith,
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
    · -- wPhaseOf = φ + 1
      change wPhaseOf (W (K₀.of C (X⟦(1 : ℤ)⟧))) ((a + 1 + (b + 1)) / 2) = φ + 1
      rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by ring]
      rw [K₀.of_shift_one, map_neg]
      have hphase : wPhaseOf (W (K₀.of C X)) ((a + b) / 2) = φ := hSS.2.2.2.1
      have hWne : W (K₀.of C X) ≠ 0 := hSS.2.2.1
      exact (wPhaseOf_neg hWne _).trans (by linarith)
    · -- Semistability transport: shift by -1
      have hT_sh := Triangle.shift_distinguished _ hT (-1 : ℤ)
      have h10 : (1 : ℤ) + (-1 : ℤ) = 0 := by omega
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
      have hsem : wPhaseOf (W (K₀.of C (K⟦(-1 : ℤ)⟧))) ((a + b) / 2) ≤ φ :=
        hSS.2.2.2.2 hT' hK1 hQ1 hKne1
      rw [K₀.of_shift_neg_one, map_neg] at hsem
      change wPhaseOf (W (K₀.of C K)) ((a + 1 + (b + 1)) / 2) ≤ φ + 1
      rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by ring]
      by_cases hWK : W (K₀.of C K) = 0
      · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; linarith
      · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
        rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
        have key2 := wPhaseOf_add_two hWK ((a + b) / 2 - 1)
        rw [show (a + b) / 2 - 1 + 2 = (a + b) / 2 + 1 from by ring] at key2
        linarith

variable [IsTriangulated C] in
/-- Backward shift for `deformedPred`: if `E⟦1⟧` is Q-semistable of phase `φ + 1`,
then `E` is Q-semistable of phase `φ`. -/
theorem deformedPred_of_shift_one
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {φ : ℝ} {X : C}
    (h : σ.deformedPred C W hW ε hε hε2 hsin (φ + 1) (X⟦(1 : ℤ)⟧)) :
    σ.deformedPred C W hW ε hε hε2 hsin φ X := by
  rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
  · exact Or.inl (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) X hZ)
  · refine Or.inr ⟨a - 1, b - 1, by linarith, by linarith, by linarith, by linarith, ?_,
      fun h ↦ hSS.2.1 ((shiftFunctor C (1 : ℤ)).map_isZero h), ?_, ?_,
      fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
    · -- intervalProp C (a-1) (b-1) X
      rcases hSS.1 with hZ' | ⟨F, hF⟩
      · exact absurd hZ' hSS.2.1
      · exact Or.inr ⟨(F.shiftHN C σ.slicing (-1)).ofIso C
          ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).app X),
          fun i ↦ by
            change a - 1 < (F.shiftHN C σ.slicing (-1)).φ i ∧
              (F.shiftHN C σ.slicing (-1)).φ i < b - 1
            simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
            constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
    · -- W(K₀.of C X) ≠ 0
      intro hw
      apply hSS.2.2.1
      change W (K₀.of C (X⟦(1 : ℤ)⟧)) = 0
      rw [K₀.of_shift_one, map_neg]
      change W (K₀.of C X) = 0 at hw
      rw [hw, neg_zero]
    · -- wPhaseOf = φ
      change wPhaseOf (W (K₀.of C X)) ((a - 1 + (b - 1)) / 2) = φ
      rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by ring]
      have hphase : wPhaseOf (-W (K₀.of C X)) ((a + b) / 2) = φ + 1 := by
        have := hSS.2.2.2.1; rwa [K₀.of_shift_one, map_neg] at this
      have hWne : W (K₀.of C X) ≠ 0 := by
        intro hw; apply hSS.2.2.1; rw [K₀.of_shift_one, map_neg, neg_eq_zero]; exact hw
      have key := wPhaseOf_neg hWne ((a + b) / 2 - 1)
      rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
      linarith
    · -- Semistability: shift by +1
      have hT' := Triangle.shift_distinguished _ hT (1 : ℤ)
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
      have hsem : wPhaseOf (W (K₀.of C (K⟦(1 : ℤ)⟧))) ((a + b) / 2) ≤ φ + 1 :=
        hSS.2.2.2.2 hT' hK1 hQ1 hKne1
      rw [K₀.of_shift_one, map_neg] at hsem
      change wPhaseOf (W (K₀.of C K)) ((a - 1 + (b - 1)) / 2) ≤ φ
      rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by ring]
      by_cases hWK : W (K₀.of C K) = 0
      · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; linarith
      · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
        rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
        linarith

variable [IsTriangulated C] in
/-- `Q(>t)⟦1⟧ ⊆ Q(>t+1)`: the forward shift sends `Q(>t)`-objects to `Q(>t+1)`. -/
theorem StabilityCondition.deformedGtPred_shift_one
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {X : C}
    (hX : σ.deformedGtPred C W hW ε hε hε2 hsin t X) :
    σ.deformedGtPred C W hW ε hε hε2 hsin (t + 1) (X⟦(1 : ℤ)⟧) := by
  induction hX with
  | zero hZ => exact .zero ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
  | mem hP =>
    obtain ⟨ψ, hψ, hPred⟩ := hP
    exact .mem ⟨ψ + 1, by linarith,
      deformedPred_shift_one C σ W hW hε hε2 hsin hPred⟩
  | ext hT _ _ ihX ihY =>
    exact .ext (Triangle.shift_distinguished _ hT (1 : ℤ)) ihX ihY

variable [IsTriangulated C] in
/-- `Q(≤t)⟦1⟧ ⊆ Q(≤t+1)`: the forward shift sends `Q(≤t)`-objects to `Q(≤t+1)`. -/
theorem StabilityCondition.deformedLePred_shift_one
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {X : C}
    (hX : σ.deformedLePred C W hW ε hε hε2 hsin t X) :
    σ.deformedLePred C W hW ε hε hε2 hsin (t + 1) (X⟦(1 : ℤ)⟧) := by
  induction hX with
  | zero hZ => exact .zero ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
  | mem hP =>
    obtain ⟨ψ, hψ, hPred⟩ := hP
    exact .mem ⟨ψ + 1, by linarith,
      deformedPred_shift_one C σ W hW hε hε2 hsin hPred⟩
  | ext hT _ _ ihX ihY =>
    exact .ext (Triangle.shift_distinguished _ hT (1 : ℤ)) ihX ihY

variable [IsTriangulated C] in
/-- `Q(≤t)⟦-1⟧ ⊆ Q(≤t-1)`: the backward shift sends `Q(≤t)`-objects to `Q(≤t-1)`. -/
theorem StabilityCondition.deformedLePred_shift_neg_one
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {X : C}
    (hX : σ.deformedLePred C W hW ε hε hε2 hsin t X) :
    σ.deformedLePred C W hW ε hε hε2 hsin (t - 1) (X⟦(-1 : ℤ)⟧) := by
  induction hX with
  | zero hZ => exact .zero ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
  | @mem E hP =>
    obtain ⟨ψ, hψ, hPred⟩ := hP
    -- Need deformedPred (ψ-1) (E⟦-1⟧) from deformedPred ψ E.
    -- Use backward shift: deformedPred ψ (Y⟦1⟧) → deformedPred (ψ-1) Y with Y = E⟦-1⟧.
    set Y := E⟦(-1 : ℤ)⟧ with hY_def
    have eYE : Y⟦(1 : ℤ)⟧ ≅ E :=
      (shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by omega)).app E
    letI := σ.deformedPred_closedUnderIso C W hW ε hε hε2 hsin ψ
    have hPredY : σ.deformedPred C W hW ε hε hε2 hsin ψ (Y⟦(1 : ℤ)⟧) :=
      (σ.deformedPred C W hW ε hε hε2 hsin ψ).prop_of_iso eYE.symm hPred
    have hback := deformedPred_of_shift_one C σ W hW hε hε2 hsin
      (show σ.deformedPred C W hW ε hε hε2 hsin ((ψ - 1) + 1) (Y⟦(1 : ℤ)⟧) from
        by rw [show (ψ - 1) + 1 = ψ from by ring]; exact hPredY)
    exact .mem ⟨ψ - 1, by linarith, hback⟩
  | ext hT _ _ ihX ihY =>
    exact .ext (Triangle.shift_distinguished _ hT (-1 : ℤ)) ihX ihY

variable [IsTriangulated C] in
/-- If `X ∈ Q(>t) ∩ Q(≤t)`, then `X = 0`. -/
theorem isZero_of_deformedGtPred_deformedLePred
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4) (hε8 : ε < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {X : C}
    (hGt : σ.deformedGtPred C W hW ε hε hε2 hsin t X)
    (hLe : σ.deformedLePred C W hW ε hε hε2 hsin t X) :
    IsZero X :=
  (IsZero.iff_id_eq_zero X).mpr
    (σ.hom_eq_zero_of_deformedGt_deformedLe C W hW hε hε2 hε8 hsin hGt hLe (𝟙 X))

variable [IsTriangulated C] in
/-- **Third-vertex closure for Q(>t)**: if distinguished triangle X → S → Y
with X, S ∈ Q(>t), then Y ∈ Q(>t). Uses rotation + forward shift + ExtensionClosure. -/
theorem deformedGtPred_of_triangle_obj₃
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {X S Y : C} {f : X ⟶ S} {g : S ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hX : σ.deformedGtPred C W hW ε hε hε2 hsin t X)
    (hS : σ.deformedGtPred C W hW ε hε hε2 hsin t S) :
    σ.deformedGtPred C W hW ε hε hε2 hsin t Y := by
  -- Rotate: S → Y → X[1] is distinguished. Y is the middle.
  have hrot := rot_of_distTriang _ hT
  -- X[1] ∈ Q(>t+1) ⊆ Q(>t)
  have hX1 : σ.deformedGtPred C W hW ε hε hε2 hsin t (X⟦(1 : ℤ)⟧) :=
    σ.deformedGtPred_anti C W hW hε hε2 hsin (show t ≤ t + 1 by linarith) _
      (σ.deformedGtPred_shift_one C W hW hε hε2 hsin hX)
  exact .ext hrot hS hX1

variable [IsTriangulated C] in
/-- **First-vertex closure for Q(≤t)**: if distinguished triangle X → R₀ → R₁
with R₀, R₁ ∈ Q(≤t), then X ∈ Q(≤t). Uses invRotate + backward shift + ExtensionClosure. -/
theorem deformedLePred_of_triangle_obj₁
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {X R₀ R₁ : C} {f : X ⟶ R₀} {g : R₀ ⟶ R₁} {h : R₁ ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hR₀ : σ.deformedLePred C W hW ε hε hε2 hsin t R₀)
    (hR₁ : σ.deformedLePred C W hW ε hε hε2 hsin t R₁) :
    σ.deformedLePred C W hW ε hε hε2 hsin t X := by
  -- invRotate: R₁[-1] → X → R₀ is distinguished. X is the middle.
  have hinv := inv_rot_of_distTriang _ hT
  -- R₁[-1] ∈ Q(≤t-1) ⊆ Q(≤t)
  have hR₁' : σ.deformedLePred C W hW ε hε hε2 hsin t (R₁⟦(-1 : ℤ)⟧) :=
    σ.deformedLePred_mono C W hW hε hε2 hsin (show t - 1 ≤ t by linarith) _
      (σ.deformedLePred_shift_neg_one C W hW hε hε2 hsin hR₁)
  exact .ext hinv hR₁' hR₀

variable [IsTriangulated C] in
/-- If `S ∈ Q(>t)` and dist triangle `X → S → Y` with `X ∈ Q(>t)`, `Y ∈ Q(≤t)`,
then `Y = 0`. (The Q(≤t) part of a Q(>t) object is zero.) -/
theorem isZero_deformedLe_of_deformedGt_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4) (hε8 : ε < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {X S Y : C} {f : X ⟶ S} {g : S ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hX : σ.deformedGtPred C W hW ε hε hε2 hsin t X)
    (hS : σ.deformedGtPred C W hW ε hε hε2 hsin t S)
    (hY : σ.deformedLePred C W hW ε hε hε2 hsin t Y) :
    IsZero Y :=
  isZero_of_deformedGtPred_deformedLePred C σ W hW hε hε2 hε8 hsin
    (deformedGtPred_of_triangle_obj₃ C σ W hW hε hε2 hsin hT hX hS) hY

variable [IsTriangulated C] in
/-- Dual: if `S ∈ Q(≤t)` and dist triangle `X → S → Y` with `X ∈ Q(>t)`, `Y ∈ Q(≤t)`,
then `X = 0`. -/
theorem isZero_deformedGt_of_deformedLe_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4) (hε8 : ε < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {X S Y : C} {f : X ⟶ S} {g : S ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hX : σ.deformedGtPred C W hW ε hε hε2 hsin t X)
    (hS : σ.deformedLePred C W hW ε hε hε2 hsin t S)
    (hY : σ.deformedLePred C W hW ε hε hε2 hsin t Y) :
    IsZero X :=
  isZero_of_deformedGtPred_deformedLePred C σ W hW hε hε2 hε8 hsin hX
    (deformedLePred_of_triangle_obj₁ C σ W hW hε hε2 hsin hT hS hY)

variable [IsTriangulated C] in
/-- **Q-HN existence** (Bridgeland p.24, Steps 1+2). Every object admits a Q-HN filtration.
Combines `deformedGtLe_triangle` (Step 2) with
`exists_hn_of_deformedGt_deformedLe_triangle`. -/
theorem deformedSlicing_hn_exists
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (E : C) :
    Nonempty (HNFiltration C (σ.deformedPred C W hW ε hε (by linarith) hsin) E) := by
  have hε2 : ε < 1 / 4 := by linarith
  have hε8 : ε < 1 / 8 := by linarith
  -- Zero case
  by_cases hEz : IsZero E
  · exact ⟨HNFiltration.zero C E hEz⟩
  -- Get σ-HN of E
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  have hFn : 0 < F.n := by
    by_contra h; push_neg at h
    exact hEz (F.toPostnikovTower.zero_isZero (show F.n = 0 by omega))
  -- Each σ-factor has Q-HN via sigmaSemistable_hasDeformedHN
  have hfactor_hn : ∀ j : Fin F.n, ¬IsZero (F.toPostnikovTower.factor j) →
      ∃ G : HNFiltration C (σ.deformedPred C W hW ε hε (by linarith) hsin)
        (F.toPostnikovTower.factor j),
        ∀ i, F.φ j - 2 * ε < G.φ i ∧ G.φ i < F.φ j + 4 * ε :=
    fun j hj ↦ sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin
      (F.semistable j) hj
  -- ExtensionClosure idempotency helpers
  have ec_idem_le : ∀ {t' : ℝ} {X : C},
      (σ.deformedLePred C W hW ε hε hε2 hsin t').ExtensionClosure X →
      σ.deformedLePred C W hW ε hε hε2 hsin t' X := by
    intro t' X hX; induction hX with
    | zero hZ => exact .zero hZ
    | mem h => exact h
    | ext hT _ _ ihX ihY => exact .ext hT ihX ihY
  have ec_idem_gt : ∀ {s' : ℝ} {X : C},
      (σ.deformedGtPred C W hW ε hε hε2 hsin s').ExtensionClosure X →
      σ.deformedGtPred C W hW ε hε hε2 hsin s' X := by
    intro s' X hX; induction hX with
    | zero hZ => exact .zero hZ
    | mem h => exact h
    | ext hT _ _ ihX ihY => exact .ext hT ihX ihY
  -- Step A: E ∈ Q(≤t) for t ≥ max phase + 4ε
  have hE_le : ∀ t : ℝ, (∀ j : Fin F.n, F.φ j + 4 * ε ≤ t) →
      σ.deformedLePred C W hW ε hε hε2 hsin t E := by
    intro t ht
    apply ec_idem_le
    exact ObjectProperty.ExtensionClosure.of_postnikovTower F.toPostnikovTower (fun j ↦ by
      by_cases hjz : IsZero (F.toPostnikovTower.factor j)
      · exact ObjectProperty.ExtensionClosure.zero hjz
      · obtain ⟨G, hG⟩ := hfactor_hn j hjz
        -- factor j ∈ Q(≤t): each Q-HN factor has phase < sⱼ+4ε ≤ t
        apply σ.deformedLePred_of_deformedLtPred C W hW hε (by linarith) hsin
        exact ObjectProperty.ExtensionClosure.of_postnikovTower G.toPostnikovTower (fun i ↦
          ⟨G.φ i, by linarith [(hG i).2, ht j], G.semistable i⟩))
  -- Step B: E ∈ Q(>s) for s ≤ min phase - ε
  have hE_gt : ∀ s : ℝ, (∀ j : Fin F.n, s + ε ≤ F.φ j) →
      σ.deformedGtPred C W hW ε hε hε2 hsin s E := by
    intro s hs
    apply ec_idem_gt
    exact ObjectProperty.ExtensionClosure.of_postnikovTower F.toPostnikovTower (fun j ↦ by
      by_cases hjz : IsZero (F.toPostnikovTower.factor j)
      · exact ObjectProperty.ExtensionClosure.mem ⟨s + 1, by linarith, Or.inl hjz⟩
      · exact P_in_deformedGtPred C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin
            (show F.φ j ≥ s + ε from hs j) (F.semistable j) hjz)
  -- Step C: Iterative truncation
  -- Main claim: for R ∈ Q(≤t) ∩ Q(>t-nδ), R has Q-HN
  set δ := 4 * (ε₀ - ε) with hδ_def
  have hδ : 0 < δ := by simp [δ]; linarith
  -- hStep1 for deformedGtLe_triangle
  have hStep1 : ∀ {E' : C} {φ' : ℝ}, σ.slicing.P φ' E' → ¬IsZero E' → ∀ t' : ℝ,
      ∃ (X Y : C) (f : X ⟶ E') (g : E' ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧
        σ.deformedGtPred C W hW ε hε (by linarith) hsin t' X ∧
        σ.deformedLePred C W hW ε hε (by linarith) hsin t' Y :=
    fun hP hE' t' ↦ sigmaSemistable_deformedGtLe_triangle C σ W hW hε₀ hε₀10 hWide
      hε hεε₀ hsin hP hE' t'
  suffices hmain : ∀ (n : ℕ) (t : ℝ) (R : C),
      σ.deformedLePred C W hW ε hε hε2 hsin t R →
      σ.deformedGtPred C W hW ε hε hε2 hsin (t - ↑n * δ) R →
      ∃ G : HNFiltration C (σ.deformedPred C W hW ε hε hε2 hsin) R,
        (∀ j, t - ↑n * δ < G.φ j) ∧ (∀ j, G.φ j ≤ t) by
    -- Apply with E, choosing t and n
    set t := F.φ ⟨0, hFn⟩ + 4 * ε
    set s := F.φ ⟨F.n - 1, by omega⟩ - 2 * ε - δ
    set N := Nat.ceil ((t - s) / δ) + 1
    have hE_le_t : σ.deformedLePred C W hW ε hε hε2 hsin t E :=
      hE_le t (fun j ↦ by
        have : F.φ j ≤ F.φ ⟨0, hFn⟩ :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val))
        simp only [t]; linarith)
    have hE_gt_s : σ.deformedGtPred C W hW ε hε hε2 hsin s E :=
      hE_gt s (fun j ↦ by
        have : F.φ ⟨F.n - 1, by omega⟩ ≤ F.φ j :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (by omega : j.val ≤ F.n - 1))
        simp only [s, δ]; linarith)
    have hNδ : t - ↑N * δ ≤ s := by
      have h1 : (t - s) / δ ≤ ↑(Nat.ceil ((t - s) / δ)) := Nat.le_ceil _
      have h2 : ↑N = (↑(Nat.ceil ((t - s) / δ)) : ℝ) + 1 := by
        simp only [N, Nat.cast_add, Nat.cast_one]
      have h3 : (t - s) / δ * δ = t - s := div_mul_cancel₀ _ (ne_of_gt hδ)
      nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hδ)]
    obtain ⟨G, _, _⟩ := hmain N t E hE_le_t
      (σ.deformedGtPred_anti C W hW hε hε2 hsin hNδ _ hE_gt_s)
    exact ⟨G⟩
  -- Prove hmain by induction on n
  intro n; induction n with
  | zero =>
    intro t R hLe hGt
    simp only [Nat.zero_eq, Nat.cast_zero, zero_mul, sub_zero] at hGt
    have hRz := isZero_of_deformedGtPred_deformedLePred C σ W hW hε hε2 hε8 hsin hGt hLe
    exact ⟨HNFiltration.zero C R hRz, fun j ↦ Fin.elim0 j, fun j ↦ Fin.elim0 j⟩
  | succ n ih =>
    intro t R hLe hGt
    -- Apply deformedGtLe_triangle at threshold t - δ
    set t' := t - δ
    obtain ⟨X, Y, fXR, gRY, hYX, hT, hX_gt, hY_le⟩ :=
      deformedGtLe_triangle C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin hStep1 R t'
    -- Y ∈ Q(≤t') ⊆ Q(≤t) (monotonicity since t' ≤ t)
    have hY_le_t : σ.deformedLePred C W hW ε hε hε2 hsin t Y :=
      σ.deformedLePred_mono C W hW hε hε2 hsin (show t' ≤ t by simp [t']; linarith) _ hY_le
    -- Strip membership: X ∈ Q(≤t) (first-vertex closure)
    have hX_le : σ.deformedLePred C W hW ε hε hε2 hsin t X :=
      deformedLePred_of_triangle_obj₁ C σ W hW hε hε2 hsin hT hLe hY_le_t
    -- Y ∈ Q(>t-(n+1)δ) (third-vertex closure)
    have hle_t' : t - ↑(n + 1) * δ ≤ t' := by
      simp only [t']; push_cast; nlinarith
    have hX_gt' : σ.deformedGtPred C W hW ε hε hε2 hsin (t - ↑(n + 1) * δ) X :=
      σ.deformedGtPred_anti C W hW hε hε2 hsin hle_t' _ hX_gt
    have hY_gt : σ.deformedGtPred C W hW ε hε hε2 hsin (t - ↑(n + 1) * δ) Y :=
      deformedGtPred_of_triangle_obj₃ C σ W hW hε hε2 hsin hT hX_gt' hGt
    -- Convert Y's bound: t-(n+1)δ = t' - nδ
    have hY_gt' : σ.deformedGtPred C W hW ε hε hε2 hsin (t' - ↑n * δ) Y := by
      have : t' - ↑n * δ = t - ↑(n + 1) * δ := by push_cast; simp only [t']; ring
      rw [this]; exact hY_gt
    -- IH gives Q-HN of Y
    obtain ⟨GY, hGY_lo, hGY_hi⟩ := ih t' Y hY_le hY_gt'
    -- X ∈ Q(>t') ∩ Q(≤t) — get Q-HN of X
    -- X is nonzero OR zero
    by_cases hXz : IsZero X
    · -- X = 0, so R ≅ Y via the triangle, transfer Q-HN
      haveI : IsIso gRY :=
        (Triangle.isZero₁_iff_isIso₂ _ hT).mp hXz
      refine ⟨GY.ofIso C (asIso gRY).symm, fun j ↦ ?_, fun j ↦ ?_⟩
      · show t - ↑(n + 1) * δ < GY.φ j
        have : t' - ↑n * δ = t - ↑(n + 1) * δ := by push_cast; simp [t']; ring
        linarith [hGY_lo j]
      · show GY.φ j ≤ t
        exact le_trans (hGY_hi j) (by simp [t']; linarith)
    · -- X nonzero: get Q-HN of X with phases in (t', t], combine with GY
      -- Step 1: Q(>t') ⊆ σ.gtProp(t'-ε) and Q(≤t) ⊆ σ.leProp(t+ε) for X
      have hX_sigmaGt : σ.slicing.gtProp C (t' - ε) X := by
        have h : ∀ {X' : C}, σ.deformedGtPred C W hW ε hε hε2 hsin t' X' →
            σ.slicing.gtProp C (t' - ε) X' := by
          intro X' hX'; induction hX' with
          | zero hZ => exact Or.inl hZ
          | mem hP =>
            obtain ⟨ψ, hψ, hPred⟩ := hP
            rcases hPred with hZ | ⟨a', b', hab', hthin', _, _, hSS'⟩
            · exact Or.inl hZ
            · exact gtProp_of_wSemistable_phase_gt C σ W hW hab' hε hε2 hthin' hsin hSS'
                (by linarith)
          | ext hT' _ _ ih1 ih3 =>
            exact σ.slicing.gtProp_of_triangle C _ ih1 ih3 hT'
        exact h hX_gt
      have hX_sigmaLe : σ.slicing.leProp C (t + ε) X := by
        have h : ∀ {X' : C}, σ.deformedLePred C W hW ε hε hε2 hsin t X' →
            σ.slicing.leProp C (t + ε) X' := by
          intro X' hX'; induction hX' with
          | zero hZ => exact Or.inl hZ
          | mem hP =>
            obtain ⟨ψ, hψ, hPred⟩ := hP
            rcases hPred with hZ | ⟨a', b', hab', hthin', _, _, hSS'⟩
            · exact Or.inl hZ
            · exact σ.slicing.leProp_of_phiPlus_le C hSS'.2.1
                (by linarith [(phase_confinement_from_stabSeminorm C σ W hW hab' hε hε2
                  hthin' hsin hSS').2])
          | ext hT' _ _ ih1 ih3 =>
            exact σ.slicing.leProp_of_triangle C _ ih1 ih3 hT'
        exact h hX_le
      -- Step 2: Embed X in thin interval, apply interior_has_enveloped_HN
      -- X ∈ σ.intervalProp(t'-ε, t+ε+η) for small η. Use η = ε₀ - ε.
      set η := ε₀ - ε with hη_def
      have hη : 0 < η := by linarith
      have hX_int : σ.slicing.intervalProp C (t' - ε) (t + ε + η) X :=
        σ.slicing.intervalProp_of_intrinsic_phases C hXz
          (σ.slicing.phiMinus_gt_of_gtProp C hXz hX_sigmaGt)
          (by linarith [σ.slicing.phiPlus_le_of_leProp C hXz hX_sigmaLe])
      set a_int := t' - 3 * ε
      set b_int := t + 5 * ε + η
      have hab_int : a_int < b_int := by simp only [a_int, b_int, t']; nlinarith
      haveI : Fact (a_int < b_int) := ⟨hab_int⟩
      haveI : Fact (b_int - a_int ≤ 1) := ⟨by simp only [a_int, b_int, t', δ]; nlinarith⟩
      have hthin_int : b_int - a_int + 2 * ε < 1 := by
        simp only [a_int, b_int, t', δ]; nlinarith
      have hFL_int : ThinFiniteLengthInInterval (C := C) σ a_int b_int :=
        ThinFiniteLengthInInterval.of_wide (C := C) σ hε₀ (by linarith)
          (show (t + ε) - 4 * ε₀ ≤ a_int by simp only [a_int, t', δ]; linarith)
          (show b_int ≤ (t + ε) + 4 * ε₀ by simp only [b_int, η]; linarith) hWide
      have hX_interior : σ.slicing.intervalProp C (a_int + 2 * ε) (b_int - 4 * ε) X := by
        have ha : a_int + 2 * ε = t' - ε := by simp only [a_int]; ring
        have hb : b_int - 4 * ε = t + ε + η := by simp only [b_int]; ring
        rw [ha, hb]; exact hX_int
      obtain ⟨GX_coarse, hGX_coarse⟩ :=
        interior_has_enveloped_HN C σ W hW hab_int hε (by linarith : ε < 1 / 10) hthin_int
          hsin hFL_int hXz hX_interior
      -- Step 3: Split at t' to get phases > t'. X ∈ Q(>t') kills the ≤t' part.
      obtain ⟨X_hi, X_lo, GX_hi, GX_lo, f_hi, g_lo, h_lo, hT_split, hprops⟩ :=
        split_hn_filtration_at_cutoff (C := C) GX_coarse t'
      have hGXhi_gt := hprops.1
      have hGXlo_le := hprops.2.1
      have hGXlo_bound := hprops.2.2.1
      have hGXhi_contain := hprops.2.2.2
      have hX_lo_le : σ.deformedLePred C W hW ε hε hε2 hsin t' X_lo :=
        ec_idem_le <| ObjectProperty.ExtensionClosure.of_postnikovTower
          GX_lo.toPostnikovTower (fun j ↦ ObjectProperty.ExtensionClosure.mem
            ⟨GX_lo.φ j, hGXlo_le j, GX_lo.semistable j⟩)
      have hX_hi_gt : σ.deformedGtPred C W hW ε hε hε2 hsin t' X_hi :=
        ec_idem_gt <| ObjectProperty.ExtensionClosure.of_postnikovTower
          GX_hi.toPostnikovTower (fun j ↦ ObjectProperty.ExtensionClosure.mem
            ⟨GX_hi.φ j, hGXhi_gt j, GX_hi.semistable j⟩)
      have hX_lo_z : IsZero X_lo :=
        isZero_deformedLe_of_deformedGt_triangle C σ W hW hε hε2 hε8 hsin
          hT_split hX_hi_gt hX_gt hX_lo_le
      haveI : IsIso f_hi :=
        (Triangle.isZero₃_iff_isIso₁ _ hT_split).mp hX_lo_z
      -- Step 4: Split at t to get phases ≤ t. X ∈ Q(≤t) kills the >t part.
      obtain ⟨X_vhi, X_mid, GX_vhi, GX_mid, f_vhi, g_mid, h_mid,
        hT_split2, hprops2⟩ :=
        split_hn_filtration_at_cutoff (C := C) GX_hi t
      have hGXvhi_gt := hprops2.1
      have hGXmid_le := hprops2.2.1
      have hGXmid_bound := hprops2.2.2.1
      have hX_vhi_gt' : σ.deformedGtPred C W hW ε hε hε2 hsin t X_vhi :=
        ec_idem_gt <| ObjectProperty.ExtensionClosure.of_postnikovTower
          GX_vhi.toPostnikovTower (fun j ↦ ObjectProperty.ExtensionClosure.mem
            ⟨GX_vhi.φ j, hGXvhi_gt j, GX_vhi.semistable j⟩)
      letI : (σ.deformedLePred C W hW ε hε hε2 hsin t).IsClosedUnderIsomorphisms :=
        ⟨fun e h ↦ ec_idem_le (.of_iso e (.mem h))⟩
      have hX_hi_le' : σ.deformedLePred C W hW ε hε hε2 hsin t X_hi :=
        (σ.deformedLePred C W hW ε hε hε2 hsin t).prop_of_iso (asIso f_hi).symm hX_le
      have hX_mid_le' : σ.deformedLePred C W hW ε hε hε2 hsin t X_mid :=
        ec_idem_le <| ObjectProperty.ExtensionClosure.of_postnikovTower
          GX_mid.toPostnikovTower (fun j ↦ ObjectProperty.ExtensionClosure.mem
            ⟨GX_mid.φ j, hGXmid_le j, GX_mid.semistable j⟩)
      have hX_vhi_z : IsZero X_vhi :=
        isZero_deformedGt_of_deformedLe_triangle C σ W hW hε hε2 hε8 hsin
          hT_split2 hX_vhi_gt' hX_hi_le' hX_mid_le'
      haveI : IsIso g_mid :=
        (Triangle.isZero₁_iff_isIso₂ _ hT_split2).mp hX_vhi_z
      -- GX_mid is a Q-HN of X (via iso X_mid ≅ X_hi ≅ X) with phases ∈ (t', t]
      let eX : X_mid ≅ X := (asIso g_mid).symm.trans (asIso f_hi)
      let GX := GX_mid.ofIso C eX
      -- Phase lower bound: GX_mid phases > t' (from GX_hi's phases via the bound)
      have hGXn_pos : 0 < GX_hi.n := by
        by_contra h; push_neg at h
        have hXhiz := GX_hi.toPostnikovTower.zero_isZero (show GX_hi.n = 0 by omega)
        exact hXz ((Iso.isZero_iff (asIso f_hi)).mp hXhiz)
      have hGX_lo_bound : ∀ j : Fin GX.n, t' < GX.φ j := by
        intro j
        have hbd := hGXmid_bound hGXn_pos j
        exact lt_of_lt_of_le (hGXhi_gt ⟨GX_hi.n - 1, by omega⟩) hbd
      have hGX_hi_bound : ∀ j : Fin GX.n, GX.φ j ≤ t := hGXmid_le
      -- Step 5: Combine GX and GY
      have hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j :=
        fun i j ↦ lt_of_le_of_lt (hGY_hi i) (hGX_lo_bound j)
      have hPiso : ∀ φ' : ℝ,
          (σ.deformedPred C W hW ε hε hε2 hsin φ').IsClosedUnderIsomorphisms :=
        fun φ' ↦ σ.deformedPred_closedUnderIso C W hW ε hε hε2 hsin φ'
      obtain ⟨G, hG_lo, hG_hi⟩ :=
        Triangulated.append_hn_filtration_of_triangle_le (C := C) hPiso GX GY
        fXR gRY hYX hT
        (t - ↑(n + 1) * δ) t
        (fun j ↦ by linarith [hGX_lo_bound j, hle_t'])
        (fun i ↦ by
          have : t' - ↑n * δ = t - ↑(n + 1) * δ := by push_cast; simp [t']; ring
          linarith [hGY_lo i]) hsep
        hGX_hi_bound
        (fun i ↦ le_trans (hGY_hi i) (by simp [t']; linarith))
      exact ⟨G, hG_lo, hG_hi⟩


end CategoryTheory.Triangulated
