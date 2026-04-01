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

universe v u u'

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

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
def StabilityCondition.WithClassMap.deformedSlicing (σ : StabilityCondition.WithClassMap C v)
    (W : Λ →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    Slicing C where
  P := σ.deformedPred C W hW ε
  closedUnderIso := fun φ ↦ ⟨fun {E E'} e h ↦ by
    rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
    · exact Or.inl ((Iso.isZero_iff e).mp hZ)
    · refine Or.inr ⟨a, b, hab, hthin, henv_lo, henv_hi, ?_, fun h ↦ hSS.nonzero
        ((Iso.isZero_iff e).mpr h), ?_, ?_, fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
      · -- intervalProp: transport via HNFiltration.ofIso
        rcases hSS.intervalProp with hZ' | ⟨F, hF⟩
        · exact absurd hZ' hSS.nonzero
        · exact Or.inr ⟨F.ofIso C e, hF⟩
      · -- W(cl C v E') ≠ 0
        rw [show cl C v E' = cl C v E from (cl_iso C v e).symm]; exact hSS.wNe
      · -- wPhaseOf = φ
        rw [show cl C v E' = cl C v E from (cl_iso C v e).symm]; exact hSS.phase_eq
      · -- semistability: compose triangle with iso
        have hT' : Triangle.mk (f₁ ≫ e.inv) (e.hom ≫ f₂) f₃ ∈ distTriang C :=
          isomorphic_distinguished _ hT _
            (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
              (by simp) (by simp) (by simp))
        exact hSS.le_of_distTriang hT' hK hQ hKne⟩
  zero_mem ψ := σ.deformedPred_zero C W hW ε ψ (isZero_zero C)
  shift_iff := fun φ X ↦ by
    constructor
    · -- Forward: deformedPred φ X → deformedPred (φ+1) (X⟦1⟧)
      exact fun a => deformedPred_shift_one C σ W hW hε a
    · -- Backward: deformedPred (φ+1) (X⟦1⟧) → deformedPred φ X
      exact fun a => deformedPred_of_shift_one C σ W hW hε a
  hom_vanishing ψ₁ ψ₂ A B hlt hA hB f :=
    σ.hom_eq_zero_of_deformedPred C W hW hε (by linarith) (by linarith) hsin hA hB hlt f
  hn_exists := fun E ↦
    deformedSlicing_hn_exists C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin E

/-- **W-compatibility of the deformed slicing.** For every nonzero Q-semistable object `E`
of Q-phase `ψ`, the central charge `W([E])` lies on the ray `ℝ₊ · exp(iπψ)`. This
follows directly from the `Semistable` definition, which stores
`wPhaseOf(W([E]), α) = ψ`. -/
theorem StabilityCondition.WithClassMap.deformedSlicing_compat
    (σ : StabilityCondition.WithClassMap C v)
    (W : Λ →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (ψ : ℝ) (E : C)
    (hQ : (σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin).P ψ E)
    (hE : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      W (cl C v E) = ↑m * Complex.exp (↑(Real.pi * ψ) * Complex.I) := by
  -- hQ : deformedPred, so either IsZero or ∃ a b hab hthin, Semistable
  rcases hQ with hEZ | ⟨a, b, hab, _, _, _, hSS⟩
  · exact absurd hEZ hE
  · exact ⟨‖W (cl C v E)‖, norm_pos_iff.mpr hSS.wNe, hSS.polar⟩

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
    (σ : StabilityCondition.WithClassMap C v) (W : Λ →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith))
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
    (σ : StabilityCondition.WithClassMap C v) (W : Λ →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith))
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
        hε (by linarith) hthin_i hsin hSS_i
      exact σ.slicing.intervalProp_of_intrinsic_phases C hSS_i.nonzero
        (by
          have hleft := (hF i).1
          linarith)
        (by
          have hright := (hF i).2
          linarith)

end CategoryTheory.Triangulated
