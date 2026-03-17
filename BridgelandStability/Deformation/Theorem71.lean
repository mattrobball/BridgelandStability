/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Deformation.TStructure
import Mathlib.CategoryTheory.Triangulated.Deformation.PPhiAbelian

/-!
# Deformation of Stability Conditions — Theorem71

Deformed slicing construction, main theorem, Theorem 1.2
-/

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
deformedPred σ W hW ε₀ ψ`. The hom-vanishing axiom is Node 7.6, the HN existence
axiom is Node 7.7, and the shift axiom requires K₀.of interaction with shift.

**Remaining sorrys:**
- `hn_exists`: HN filtrations for Q (Node 7.7, requires abelian HN theory in the heart)
- Small-gap case of `hom_vanishing` (ψ₁ - ψ₂ ≤ 2ε₀, requires heart factorization)

The `closedUnderIso` and `shift_iff` fields are complete. The `hom_vanishing` field
handles the large-gap case via phase confinement and interval disjointness. -/
def StabilityCondition.deformedSlicing (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    Slicing C where
  P := σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin
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
  zero_mem ψ := σ.deformedPred_zero C W hW ε₀ hε₀ hε₀2 hsin ψ (isZero_zero C)
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
          rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by ring]
          rw [K₀.of_shift_one, map_neg]
          have hphase : wPhaseOf (W (K₀.of C X)) ((a + b) / 2) = φ := hSS.2.2.2.1
          have hWne : W (K₀.of C X) ≠ 0 := hSS.2.2.1
          exact (wPhaseOf_neg hWne _).trans (by linarith)
        · -- Semistability transport: shift K → X⟦1⟧ → Q by -1, compose with iso
          -- to get K⟦-1⟧ → X → Q⟦-1⟧ (dist), apply X's semistability
          have hT_sh := Triangle.shift_distinguished _ hT (-1 : ℤ)
          -- Build triangle with obj₂ = X via iso (X⟦1⟧)⟦-1⟧ ≅ X
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
          rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by ring]
          by_cases hWK : W (K₀.of C K) = 0
          · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; linarith
          · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
            have key2 := wPhaseOf_add_two hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 2 = (a + b) / 2 + 1 from by ring] at key2
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
              ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).app X),
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
          rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by ring]
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
          rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
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
          rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by ring]
          by_cases hWK : W (K₀.of C K) = 0
          · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; linarith
          · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
            linarith
  hom_vanishing ψ₁ ψ₂ A B hlt hA hB f :=
    σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hε₀8 hsin hA hB hlt f
  hn_exists := by
    -- Faithful p.24 route:
    -- 1. use the exact strip-local Lemma 7.7 wrappers, not the old `P(φ)` detour;
    -- 2. build the paper's `Q(> t) / Q(≤ t)` and `Q(> t) / Q(< t + δ)` triangles
    --    from those strip windows;
    -- 3. assemble the global `Q`-HN filtration through
    --    `exists_hn_of_deformedGt_deformedLe_triangle`.
    sorry

variable [IsTriangulated C] in
/-- **W-compatibility of the deformed slicing.** For every nonzero Q-semistable object `E`
of Q-phase `ψ`, the central charge `W([E])` lies on the ray `ℝ₊ · exp(iπψ)`. This
follows directly from the `Semistable` definition, which stores
`wPhaseOf(W([E]), α) = ψ`. -/
theorem StabilityCondition.deformedSlicing_compat
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (ψ : ℝ) (E : C)
    (hQ : (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin).P ψ E)
    (hE : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      W (K₀.of C E) = ↑m * Complex.exp (↑(Real.pi * ψ) * Complex.I) := by
  -- hQ : deformedPred, so either IsZero or ∃ a b hab hthin, Semistable
  rcases hQ with hEZ | ⟨a, b, hab, _, _, _, hSS⟩
  · exact absurd hEZ hE
  · exact ⟨‖W (K₀.of C E)‖, norm_pos_iff.mpr hSS.2.2.1, hSS.polar⟩



variable [IsTriangulated C] in
/-- **σ-semistable objects have Q-HN filtrations** (Bridgeland p.24).
For E ∈ P(φ), embed E in the wide interval P((φ-3ε₀, φ+5ε₀)) and apply Lemma 7.7
(`exists_deformedHN_of_enveloped_interval`). The enveloping condition is automatic
since phase confinement (Lemma 7.3) gives W-phases in (φ-ε₀, φ+ε₀) ⊂ (a+ε₀, b-ε₀). -/
theorem sigmaSemistable_hasDeformedHN
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    Nonempty (HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E) := by
  -- Bridgeland p.24: embed E in P((φ-3ε₀, φ+5ε₀)), apply Lemma 7.7.
  sorry

/-! #### Step A4: Main theorem -/

variable [IsTriangulated C] in
/-- **Reverse phase confinement**. If `E` is σ-semistable of phase `φ` and
`‖W - Z‖_σ < sin(πε₀)`, then `E` lies in the Q-interval `(φ - ε₀ - δ, φ + ε₀ + δ)`
for any `δ > 0`.

This replaces the incorrect statement `sigma_semistable_is_deformedPred` which claimed
σ-semistable implies Q-semistable. That is **false**: a σ-semistable object `E` can
decompose into W-semistable factors with different W-phases (e.g., `E = S₁ ⊕ S₂` with
`S₁, S₂` σ-stable of the same phase but different W-phases), so `E` need not be
Q-semistable. The correct statement is that `E` lies in a Q-interval of half-width
`ε₀ + δ` centered at `φ`.

The proof constructs a Q-HN filtration for `E` by decomposing it in the abelian
category `P(φ)` using the W-stability function restricted to `P(φ)`. Each W-HN
factor in `P(φ)` has W-phase within `ε₀` of `φ`, giving the desired interval bound.
-/
theorem sigma_semistable_intervalProp
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (_hE : ¬IsZero E)
    {δ : ℝ} (hδ : 0 < δ) :
    (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin).intervalProp C
      (φ - ε₀ - δ) (φ + ε₀ + δ) E := by
  -- Bridgeland p.24: embed E ∈ P(φ) in wide interval P((φ-3ε₀, φ+5ε₀)),
  -- apply Lemma 7.7 (exists_deformedHN_of_enveloped_interval), then read off
  -- the Q-interval bounds from the HN factor phases.
  sorry

/-! ### Deformation theorem (Theorem 7.1) -/

variable [IsTriangulated C] in
/-- **Bridgeland's Theorem 7.1** (deformation of stability conditions). Given a
stability condition `σ = (Z, P)` on a triangulated category `D` and a group
homomorphism `W : K₀(D) → ℂ` with `‖W - Z‖_σ < sin(πε₀)` (where `ε₀` comes from
the local finiteness of `σ`), there exists a locally-finite stability condition
`τ = (W, Q)` with `d(P, Q) ≤ ε₀`.

The proof constructs the deformed slicing `Q` via `deformedSlicing`, then verifies:
1. **Hom-vanishing** (Lemma 7.6): `hom_eq_zero_of_deformedPred`
2. **HN filtrations** (Lemma 7.7 + Nodes 7.8–7.9): well-founded recursion in thin
   quasi-abelian categories, assembled via t-structures `Q(> t)`
3. **Compatibility**: `deformedSlicing_compat`
4. **Local finiteness**: inherited from `σ` via phase confinement (Node 7.3)
5. **Distance bound**: `d(P, Q) ≤ ε₀` by phase confinement (Node 7.3)

The hypothesis `hε₀_lf` ensures `ε₀` is small enough relative to `σ`'s local finiteness
parameter, following Bridgeland's condition that intervals of half-width `ε₀ + δ` have
finite length. -/
theorem bridgeland_7_1 (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (hε₀_lf : ∃ δ : ℝ, 0 < δ ∧ ε₀ + δ < 1 / 2 ∧ ∀ t : ℝ,
      ∀ (E :
        (σ.slicing.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ))).FullSubcategory),
        IsArtinianObject E ∧ IsNoetherianObject E) :
    ∃ (τ : StabilityCondition C), τ.Z = W ∧
      slicingDist C σ.slicing τ.slicing ≤ ENNReal.ofReal ε₀ := by
  let hSector : SectorFiniteLength (C := C) σ ε₀ hε₀ hε₀2 :=
    SectorFiniteLength.of_wide (C := C) σ hε₀ hε₀2 hε₀8 hWide
  refine ⟨⟨σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin, W,
    σ.deformedSlicing_compat C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin, ?_⟩, rfl, ?_⟩
  · -- Local finiteness: inherited from σ via phase confinement
    obtain ⟨δ, hδ, hδ_half, hlf_σ⟩ := hε₀_lf
    let δ' : ℝ := min (δ / 2) (1 / 4)
    constructor
    refine ⟨δ', by
      dsimp [δ']
      positivity, by
      dsimp [δ']
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun t E ↦ ?_⟩
    letI : Fact (t - δ' < t + δ') := ⟨by
      dsimp [δ']
      have : 0 < δ' := by
        dsimp [δ']
        positivity
      linarith⟩
    letI : Fact ((t + δ') - (t - δ') ≤ 1) := ⟨by
      dsimp [δ']
      have hδ' : δ' ≤ 1 / 4 := by
        dsimp [δ']
        exact min_le_right _ _
      linarith⟩
    have hIncl :
        (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin).intervalProp C
            (t - δ') (t + δ') ≤
          σ.slicing.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ)) := by
      intro X hX
      rcases hX with hZ | ⟨F, hF⟩
      · exact Or.inl hZ
      · apply intervalProp_of_postnikovTower C σ.slicing F.toPostnikovTower
        intro i
        have hsem := F.semistable i
        change σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin (F.φ i) _ at hsem
        rcases hsem with hZ_i | ⟨a_i, b_i, hab_i, hthin_i, _, _, hSS_i⟩
        · exact Or.inl hZ_i
        · have ⟨hlo, hhi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab_i
            hε₀ hε₀2 hthin_i hsin hSS_i
          exact σ.slicing.intervalProp_of_intrinsic_phases C hSS_i.2.1
            (by
              have hleft := (hF i).1
              dsimp [δ'] at hleft
              linarith [hlo, min_le_left (δ / 2) (1 / 4 : ℝ)])
            (by
              have hright := (hF i).2
              dsimp [δ'] at hright
              linarith [hhi, min_le_left (δ / 2) (1 / 4 : ℝ)])
    let I :
        (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin).IntervalCat C
            (t - δ') (t + δ') ⥤
          σ.slicing.IntervalCat C (t - (ε₀ + δ)) (t + (ε₀ + δ)) :=
      ObjectProperty.ιOfLE hIncl
    letI : Fact (t - (ε₀ + δ) < t + (ε₀ + δ)) := ⟨by linarith [hε₀, hδ]⟩
    letI : Fact ((t + (ε₀ + δ)) - (t - (ε₀ + δ)) ≤ 1) := ⟨by linarith [hδ_half]⟩
    have hI : IsArtinianObject (I.obj E) ∧ IsNoetherianObject (I.obj E) :=
      hlf_σ t (I.obj E)
    haveI : IsArtinianObject (I.obj E) := hI.1
    haveI : IsNoetherianObject (I.obj E) := hI.2
    have hstrictE :
        IsStrictArtinianObject E ∧ IsStrictNoetherianObject E :=
      interval_strictFiniteLength_of_inclusion (C := C)
        (s₁ := σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin) (s₂ := σ.slicing)
        (a₁ := t - δ') (b₁ := t + δ') (a₂ := t - (ε₀ + δ)) (b₂ := t + (ε₀ + δ))
        hIncl (X := E)
    haveI : IsStrictArtinianObject E := hstrictE.1
    haveI : IsStrictNoetherianObject E := hstrictE.2
    exact ⟨inferInstance, inferInstance⟩
  · -- Distance bound: d(P, Q) ≤ ε₀ by phase confinement
    set Q := σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin
    -- Forward: Q-HN factors → phase confinement → σ-intervalProp
    have forward : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
        σ.slicing.intervalProp C
          (Q.phiMinus C E hE - ε₀ - δ) (Q.phiPlus C E hE + ε₀ + δ) E := by
      intro E hE δ hδ
      obtain ⟨G, hnG, hfirstG, hlastG⟩ := HNFiltration.exists_both_nonzero C Q hE
      apply intervalProp_of_postnikovTower C σ.slicing G.toPostnikovTower
      intro i
      by_cases hGi : IsZero (G.toPostnikovTower.factor i)
      · exact Or.inl hGi
      · have hsem := G.semistable i
        change σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin (G.φ i) _ at hsem
        rcases hsem with hZ_i | ⟨a_i, b_i, hab_i, hthin_i, _, _, hSS_i⟩
        · exact absurd hZ_i hGi
        · have ⟨hlo, hhi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab_i
            hε₀ hε₀2 hthin_i hsin hSS_i
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
          (σ.slicing.phiMinus C E hE - ε₀ - δ)
          (σ.slicing.phiPlus C E hE + ε₀ + δ) E := by
      intro E hE δ hδ
      obtain ⟨F, hnF, hfirstF, hlastF⟩ :=
        HNFiltration.exists_both_nonzero C σ.slicing hE
      apply intervalProp_of_postnikovTower C Q F.toPostnikovTower
      intro i
      by_cases hFi : IsZero (F.toPostnikovTower.factor i)
      · exact Or.inl hFi
      · have hFi_le : F.φ i ≤ σ.slicing.phiPlus C E hE := by
          rw [σ.slicing.phiPlus_eq C E hE F hnF hfirstF]
          exact F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        have hFi_ge : σ.slicing.phiMinus C E hE ≤ F.φ i := by
          rw [σ.slicing.phiMinus_eq C E hE F hnF hlastF]
          exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
        -- Factor i is σ-semistable of phase F.φ i. By reverse phase confinement,
        -- it lies in Q-interval (F.φ i - ε₀ - δ, F.φ i + ε₀ + δ).
        have hQint := sigma_semistable_intervalProp C σ W hW
          hε₀ hε₀2 hε₀8 hWide hsin (F.semistable i) hFi hδ
        -- Widen to (phiMinus - ε₀ - δ, phiPlus + ε₀ + δ) using monotonicity
        exact Q.intervalProp_mono C (by linarith) (by linarith) hQint
    -- Combine: |σ.phiPlus - Q.phiPlus| ≤ ε₀ and |σ.phiMinus - Q.phiMinus| ≤ ε₀
    apply slicingDist_le_of_phase_bounds
    · -- |σ.phiPlus(E) - Q.phiPlus(E)| ≤ ε₀
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiPlus(E) ≤ σ.phiPlus(E) + ε₀
        by_contra h; push_neg at h
        have := Q.phiPlus_lt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < -(σ.slicing.phiPlus C E hE -
            Q.phiPlus C E hE) - ε₀))
        linarith
      · -- σ.phiPlus(E) ≤ Q.phiPlus(E) + ε₀
        by_contra h; push_neg at h
        have := σ.slicing.phiPlus_lt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiPlus C E hE -
            Q.phiPlus C E hE - ε₀))
        linarith
    · -- |σ.phiMinus(E) - Q.phiMinus(E)| ≤ ε₀
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiMinus(E) - ε₀ ≤ σ.phiMinus(E)
        by_contra h; push_neg at h
        have := σ.slicing.phiMinus_gt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < -(σ.slicing.phiMinus C E hE -
            Q.phiMinus C E hE) - ε₀))
        linarith
      · -- σ.phiMinus(E) ≤ Q.phiMinus(E) + ε₀
        by_contra h; push_neg at h
        have := Q.phiMinus_gt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiMinus C E hE -
            Q.phiMinus C E hE - ε₀))
        linarith

variable [IsTriangulated C] in
/-- **Local connectedness of `Stab(D)`**: every basis neighbourhood is contained in
the topological connected component of its centre.

This is the path-connectedness content of Bridgeland's Theorem 1.2 proof (§7).
For `τ ∈ basisNhd(σ, ε)`, the linear interpolation `W_t = Z(σ) + t·(Z(τ) − Z(σ))`
and `γ(t) = bridgeland_7_1(σ, W_t, ε₀)` define a path from `σ` to `τ`.
Path-continuity at `t₀` follows from applying Theorem 7.1 centred at `γ(t₀)` with
a small `ε′`, then **Lemma 6.4** (uniqueness for same `Z` and `d < 1`) identifies
the result with `γ(t)`. The image of `[0, 1]` is therefore preconnected. -/
theorem basisNhd_subset_connectedComponent (σ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    basisNhd C σ ε ⊆ {τ | ConnectedComponents.mk τ = ConnectedComponents.mk σ} := by
  sorry


end CategoryTheory.Triangulated
