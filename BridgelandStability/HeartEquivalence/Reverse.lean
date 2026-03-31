/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.HeartEquivalence.Forward

/-!
# Reverse Direction and Roundtrips

Construction of a stability condition from heart stability data
(Proposition 5.3, reverse direction), the roundtrip identity, and
infrastructure for the heart short exact sequence bridge used in
the deformation theorem.
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

section Proposition53

variable [IsTriangulated C]

/-! ## Reverse Direction and Roundtrips -/

theorem StabilityCondition.stabilityFunctionOnHeart_hasHN_local
    (σ : StabilityCondition C) :
    @StabilityFunction.HasHNProperty (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian) (σ.stabilityFunctionOnHeart C) := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  intro E hE
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hE <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  suffices hmain :
      ∀ (m : ℕ) {X : t.heart.FullSubcategory} (hXobj : ¬IsZero X.obj)
        (F : HNFiltration C σ.slicing.P X.obj) (hnF : 0 < F.n) (hFm : F.n ≤ m)
        (hfirst : ¬IsZero (F.triangle ⟨0, hnF⟩).obj₃),
        ∃ G : AbelianHNFiltration (σ.stabilityFunctionOnHeart C) X,
          G.φ ⟨G.n - 1, by have := G.hn; lia⟩ = σ.slicing.phiMinus C X.obj hXobj by
    obtain ⟨F, hnF, hfirst, _⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEobj
    exact ⟨(hmain F.n hEobj F hnF le_rfl hfirst).choose⟩
  intro m
  induction m with
  | zero =>
      intro X hXobj F hnF hFm
      lia
  | succ m ih =>
      intro X hXobj F hnF hFm hfirst
      have hX : ¬IsZero X := fun hZ ↦ hXobj ((t.heart).ι.map_isZero hZ)
      have hXheart := (σ.slicing.toTStructure_heart_iff C X.obj).mp X.property
      by_cases h1 : F.n = 1
      · let φ := F.φ ⟨0, hnF⟩
        have hlast : ¬IsZero (F.triangle ⟨F.n - 1, by lia⟩).obj₃ := by
          have hidx : (⟨F.n - 1, by lia⟩ : Fin F.n) = ⟨0, hnF⟩ := Fin.ext (by lia)
          simpa [hidx] using hfirst
        have hall : ∀ i : Fin F.n, F.φ i = φ := by
          intro i
          have hidx : i = ⟨0, hnF⟩ := Fin.ext (by lia)
          subst hidx
          rfl
        have hP : (σ.slicing.P φ) X.obj := σ.slicing.semistable_of_HN_all_eq C F hall
        have hφm : σ.slicing.phiMinus C X.obj hXobj = φ := by
          rw [σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast]
          have hidx : (⟨F.n - 1, by lia⟩ : Fin F.n) = ⟨0, hnF⟩ := Fin.ext (by lia)
          simp [φ, hidx]
        have hφp : σ.slicing.phiPlus C X.obj hXobj = φ := by
          simpa [φ] using (σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst)
        have hφ : φ ∈ Set.Ioc (0 : ℝ) 1 := by
          constructor
          · linarith [gt_phases_of_gtProp C σ.slicing hXobj hXheart.1, hφm]
          · linarith [σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2, hφp]
        have hss :
            @StabilityFunction.IsSemistable _ _ t.heartFullSubcategoryAbelian
              (σ.stabilityFunctionOnHeart C) X :=
          σ.stabilityFunctionOnHeart_isSemistable_of_mem_P_phi C hφ X hP hX
        obtain ⟨G, hG⟩ :=
          StabilityFunction.exists_hn_with_last_phase_of_semistable_local
            (σ.stabilityFunctionOnHeart C) hss
        refine ⟨G, ?_⟩
        calc
          G.φ ⟨G.n - 1, by have := G.hn; lia⟩ =
              @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                (σ.stabilityFunctionOnHeart C) X := hG
          _ = φ := σ.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi C hφ X hP hX
          _ = σ.slicing.phiMinus C X.obj hXobj := hφm.symm
      · have htwo : 2 ≤ F.n := by lia
        by_cases hlast : IsZero (F.triangle ⟨F.n - 1, by lia⟩).obj₃
        · let F' := F.dropLast C (by lia) hlast
          have hnF' : 0 < F'.n := F'.n_pos C hXobj
          have hF'm : F'.n ≤ m := by
            change F.n - 1 ≤ m
            lia
          have hfirst' : ¬IsZero (F'.triangle ⟨0, hnF'⟩).obj₃ := by
            simpa [F', HNFiltration.dropLast, HNFiltration.prefix] using hfirst
          exact ih hXobj F' hnF' hF'm hfirst'
        · have hall_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
            intro i
            constructor
            · calc
                0 < σ.slicing.phiMinus C X.obj hXobj :=
                  gt_phases_of_gtProp C σ.slicing hXobj hXheart.1
                _ = F.φ ⟨F.n - 1, by lia⟩ :=
                  σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast
                _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
            · calc
                F.φ i ≤ F.φ ⟨0, hnF⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
                _ = σ.slicing.phiPlus C X.obj hXobj := by
                  symm
                  exact σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst
                _ ≤ 1 := σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2
          let FX : HNFiltration C σ.slicing.P (F.chain.obj ⟨F.n - 1, by lia⟩) :=
            F.prefix C (F.n - 1) (by lia) (by lia)
          have hFXn : 0 < FX.n := by
            change 0 < F.n - 1
            lia
          have hFXheart : t.heart (F.chain.obj ⟨F.n - 1, by lia⟩) := by
            rw [σ.slicing.toTStructure_heart_iff C]
            constructor
            · exact HNFiltration.chain_obj_gtProp C σ.slicing F (F.n - 1) (by lia) (by lia) 0
                (fun j ↦ (hall_mem ⟨j, by lia⟩).1)
            · exact HNFiltration.chain_obj_leProp C σ.slicing F (F.n - 1) (by lia) (by lia) 1
                (fun j ↦ (hall_mem ⟨j, by lia⟩).2)
          let X' : t.heart.FullSubcategory := ⟨F.chain.obj ⟨F.n - 1, by lia⟩, hFXheart⟩
          have hfirstFX : ¬IsZero (FX.triangle ⟨0, hFXn⟩).obj₃ := by
            simpa [FX, HNFiltration.prefix] using hfirst
          have hX'obj : ¬IsZero X'.obj := by
            intro hZ
            have hzero :
                ∀ f : (FX.triangle ⟨0, hFXn⟩).obj₃ ⟶ F.chain.obj ⟨F.n - 1, by lia⟩, f = 0 :=
              fun f ↦ hZ.eq_of_tgt _ _
            exact hfirstFX <|
              HNFiltration.isZero_factor_zero_of_hom_eq_zero C σ.slicing FX hFXn hzero
          obtain ⟨GX, hGX⟩ := ih hX'obj FX hFXn (by
            change F.n - 1 ≤ m
            lia) hfirstFX
          let jLast : Fin F.n := ⟨F.n - 1, by lia⟩
          have hBheart : t.heart (F.triangle jLast).obj₃ := by
            rw [σ.slicing.toTStructure_heart_iff C]
            exact ⟨σ.slicing.gtProp_of_semistable C (F.φ jLast) 0 _ (F.semistable jLast)
                (hall_mem jLast).1,
              σ.slicing.leProp_of_semistable C (F.φ jLast) 1 _ (F.semistable jLast)
                (hall_mem jLast).2⟩
          let B : t.heart.FullSubcategory := ⟨(F.triangle jLast).obj₃, hBheart⟩
          have hB : ¬IsZero B := fun hZ ↦ hlast ((t.heart).ι.map_isZero hZ)
          have hBss :
              @StabilityFunction.IsSemistable _ _ t.heartFullSubcategoryAbelian
                (σ.stabilityFunctionOnHeart C) B :=
            σ.stabilityFunctionOnHeart_isSemistable_of_mem_P_phi C (hall_mem jLast)
              B (F.semistable jLast) hB
          have hBphase :
              @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                (σ.stabilityFunctionOnHeart C) B = F.φ jLast :=
            σ.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi C (hall_mem jLast)
              B (F.semistable jLast) hB
          have hX'gt :
              σ.slicing.gtProp C (F.φ jLast) X'.obj :=
            HNFiltration.chain_obj_gtProp C σ.slicing F (F.n - 1) (by lia) (by lia)
              (F.φ jLast) <|
              fun j ↦ by
                have hjlt : (⟨j.val, by grind⟩ : Fin F.n) < jLast :=
                  Fin.mk_lt_mk.mpr (by grind)
                exact F.hφ hjlt
          have hphase_lt :
              @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                (σ.stabilityFunctionOnHeart C) B <
                  GX.φ ⟨GX.n - 1, by have := GX.hn; lia⟩ := by
            calc
              @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                  (σ.stabilityFunctionOnHeart C) B = F.φ jLast := hBphase
              _ < σ.slicing.phiMinus C X'.obj hX'obj :=
                gt_phases_of_gtProp C σ.slicing hX'obj hX'gt
              _ = GX.φ ⟨GX.n - 1, by have := GX.hn; lia⟩ := hGX.symm
          let Tlast := F.triangle jLast
          let e₁ := Classical.choice (F.triangle_obj₁ jLast)
          let e₂ := Classical.choice (F.triangle_obj₂ jLast)
          have hobj₂_eq : F.chain.obj' (F.n - 1 + 1) (by lia) = F.chain.right := by
            simp only [ComposableArrows.obj']
            congr 1
            ext
            simp
            lia
          let e₂X : Tlast.obj₂ ≅ X.obj :=
            e₂.trans ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
          let i : X' ⟶ X := ObjectProperty.homMk (e₁.inv ≫ Tlast.mor₁ ≫ e₂X.hom)
          let q : X ⟶ B := ObjectProperty.homMk (e₂X.inv ≫ Tlast.mor₂)
          let δ : B.obj ⟶ X'.obj⟦(1 : ℤ)⟧ := Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hTlast : Triangle.mk i.hom q.hom δ ∈ distTriang C := by
            refine isomorphic_distinguished _ (F.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm e₂X.symm (Iso.refl _)
              (by simp [Tlast, i, e₂X]) (by simp [Tlast, q, e₂X]) (by simp [Tlast, δ])
          have hiq_hom : i.hom ≫ q.hom = 0 := by
            have := comp_distTriang_mor_zero₁₂ _ hTlast
            simpa using this
          have hiq : i ≫ q = 0 := by
            ext
            exact hiq_hom
          have hKer : IsLimit (KernelFork.ofι i hiq) := by
            simpa [hiq] using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
              (TStructure.heart_hι t) i q δ hTlast
          have hCok : IsColimit (CokernelCofork.ofπ q hiq) := by
            simpa [hiq] using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
              (TStructure.heart_hι t) i q δ hTlast
          let eB : cokernel i ≅ B :=
            IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel i) hCok
          haveI : Mono i := Fork.IsLimit.mono hKer
          obtain ⟨G, hG⟩ := StabilityFunction.append_hn_filtration_of_mono_local
            (σ.stabilityFunctionOnHeart C) i GX eB hBss hphase_lt
          refine ⟨G, ?_⟩
          calc
            G.φ ⟨G.n - 1, by have := G.hn; lia⟩ =
                @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                  (σ.stabilityFunctionOnHeart C) B := hG
            _ = F.φ jLast := hBphase
            _ = σ.slicing.phiMinus C X.obj hXobj := by
              symm
              exact σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast

/-- **Proposition 5.3a / forward direction.**
Every stability condition `σ` determines heart stability data:
1. The t-structure is `σ.slicing.toTStructure`.
2. Boundedness follows from the HN filtration axiom.
3. The stability function on the heart `P((0, 1])` is the restriction of `Z`.
4. The HN property on the heart is obtained by taking the slicing HN filtration of
   a heart object and reading it as an abelian HN filtration, exactly as in
   Bridgeland's proof of Proposition 5.3.

The key identification is that semistable objects of phase `φ ∈ (0, 1]` in the
heart are exactly the objects of `P(φ)`, and the slicing's HN filtration of a
heart object is exactly an HN filtration in the sense of
`StabilityFunction`. -/
def StabilityCondition.toHeartStabilityData
    (σ : StabilityCondition C) : HeartStabilityData C where
  t := σ.slicing.toTStructure
  bounded := σ.slicing.toTStructure_bounded C
  Z := σ.stabilityFunctionOnHeart C
  hasHN := σ.stabilityFunctionOnHeart_hasHN_local C

/-- Normalize a real phase into the standard Bridgeland interval `(0,1]`. -/
noncomputable def phaseBase
    (φ : ℝ) : ℝ :=
  toIocMod zero_lt_one (0 : ℝ) φ

/-- Record the integral shift needed to move a phase into `(0,1]`. -/
noncomputable def phaseIndex
    (φ : ℝ) : ℤ :=
  toIocDiv zero_lt_one (0 : ℝ) φ

theorem phaseBase_mem
    (φ : ℝ) :
    phaseBase φ ∈ Set.Ioc (0 : ℝ) 1 := by
  simpa [phaseBase] using
    (toIocMod_mem_Ioc zero_lt_one (0 : ℝ) φ)

theorem phaseBase_add_phaseIndex
    (φ : ℝ) :
    phaseBase φ + phaseIndex φ = φ := by
  simpa [phaseBase, phaseIndex] using
    (toIocMod_add_toIocDiv_mul zero_lt_one (0 : ℝ) φ)

theorem phaseBase_add_one
    (φ : ℝ) :
    phaseBase (φ + (1 : ℝ)) = phaseBase φ := by
  change toIocMod zero_lt_one (0 : ℝ) (φ + (1 : ℝ)) = toIocMod zero_lt_one (0 : ℝ) φ
  convert toIocMod_add_intCast_mul zero_lt_one (0 : ℝ) φ 1 using 1
  ring_nf

theorem phaseIndex_add_one
    (φ : ℝ) :
    phaseIndex (φ + (1 : ℝ)) = phaseIndex φ + (1 : ℤ) := by
  change toIocDiv zero_lt_one (0 : ℝ) (φ + (1 : ℝ)) = toIocDiv zero_lt_one (0 : ℝ) φ + (1 : ℤ)
  convert toIocDiv_add_intCast_mul zero_lt_one (0 : ℝ) φ 1 using 1
  ring_nf

theorem phaseBase_eq_of_mem_Ioc
    {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1) :
    phaseBase φ = φ :=
  (toIocMod_eq_self zero_lt_one).2 (by simpa using hφ)

theorem phaseIndex_eq_zero_of_mem_Ioc
    {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1) :
    phaseIndex φ = 0 :=
  (toIocDiv_eq_of_sub_zsmul_mem_Ioc (hp := zero_lt_one) (a := (0 : ℝ))
    (b := φ) (n := (0 : ℤ))) (by simpa using hφ)

/-- Semistability in the heart with respect to the heart stability function. -/
abbrev HeartSemistable
    (h : HeartStabilityData C) (E : h.t.heart.FullSubcategory) : Prop :=
  @StabilityFunction.IsSemistable _ _ h.t.heartFullSubcategoryAbelian h.Z E

/-- The phase of a heart object measured by the heart stability function. -/
abbrev HeartPhase
    (h : HeartStabilityData C) (E : h.t.heart.FullSubcategory) : ℝ :=
  @StabilityFunction.phase _ _ h.t.heartFullSubcategoryAbelian h.Z E

/-- Bridgeland's reverse-direction phase slices, before packaging them into a full
slicing: objects whose `[-n]`-shift lies in the heart and is semistable there of
phase `ψ`, together with the zero object. -/
def shiftedHeartSemistable
    (h : HeartStabilityData C) (ψ : ℝ) (n : ℤ) : ObjectProperty C :=
  fun X ↦
    IsZero X ∨
      ∃ hX : h.t.heart (X⟦(-n : ℤ)⟧),
        let XH : h.t.heart.FullSubcategory := ⟨X⟦(-n : ℤ)⟧, hX⟩
        HeartSemistable (C := C) h XH ∧ HeartPhase (C := C) h XH = ψ

/-- The ambient phase predicate attached to heart stability data: normalize the phase
into `(0,1]`, then shift the object back by the corresponding integer. -/
def phasePredicate
    (h : HeartStabilityData C) (φ : ℝ) : ObjectProperty C :=
  shiftedHeartSemistable (C := C) h (phaseBase φ) (phaseIndex φ)

theorem shiftedHeartSemistable_zero_iff
    (h : HeartStabilityData C) (ψ : ℝ) (X : C) :
    shiftedHeartSemistable (C := C) h ψ 0 X ↔
      IsZero X ∨
        ∃ hX : h.t.heart X,
          let XH : h.t.heart.FullSubcategory := ⟨X, hX⟩
          HeartSemistable (C := C) h XH ∧ HeartPhase (C := C) h XH = ψ := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  let e0 : X⟦(0 : ℤ)⟧ ≅ X := (shiftFunctorZero C ℤ).app X
  constructor
  · intro hX
    rcases hX with hX | ⟨hX0, hXss, hXphase⟩
    · exact Or.inl hX
    · have hX : h.t.heart X := (h.t.heart).prop_of_iso e0 hX0
      let X0H : h.t.heart.FullSubcategory := ⟨X⟦(0 : ℤ)⟧, hX0⟩
      let XH : h.t.heart.FullSubcategory := ⟨X, hX⟩
      let eH : X0H ≅ XH := ObjectProperty.isoMk _ e0
      exact Or.inr ⟨hX, h.Z.isSemistable_of_iso eH hXss, by
        rw [← hXphase]
        exact (h.Z.phase_eq_of_iso eH).symm⟩
  · intro hX
    rcases hX with hX | ⟨hX0, hXss, hXphase⟩
    · exact Or.inl hX
    · have hX : h.t.heart (X⟦(0 : ℤ)⟧) := (h.t.heart).prop_of_iso e0.symm hX0
      let XH : h.t.heart.FullSubcategory := ⟨X, hX0⟩
      let X0H : h.t.heart.FullSubcategory := ⟨X⟦(0 : ℤ)⟧, hX⟩
      let eH : XH ≅ X0H := ObjectProperty.isoMk _ e0.symm
      exact Or.inr ⟨hX, h.Z.isSemistable_of_iso eH hXss, by
        rw [← hXphase]
        exact (h.Z.phase_eq_of_iso eH).symm⟩

theorem phasePredicate_iff_of_mem_Ioc
    (h : HeartStabilityData C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1) (X : C) :
    phasePredicate (C := C) h φ X ↔
      IsZero X ∨
        ∃ hX : h.t.heart X,
          let XH : h.t.heart.FullSubcategory := ⟨X, hX⟩
          HeartSemistable (C := C) h XH ∧ HeartPhase (C := C) h XH = φ := by
  simpa [phasePredicate, phaseBase_eq_of_mem_Ioc hφ, phaseIndex_eq_zero_of_mem_Ioc hφ] using
    (shiftedHeartSemistable_zero_iff (C := C) h φ X)

theorem arg_add_lt_max_local {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ upperHalfPlaneUnion) (h₂ : z₂ ∈ upperHalfPlaneUnion)
    (hne : Complex.arg z₁ ≠ Complex.arg z₂) :
    Complex.arg (z₁ + z₂) < max (Complex.arg z₁) (Complex.arg z₂) := by
  exact arg_add_lt_max h₁ h₂ hne

theorem heart_phase_le_of_epi
    (h : HeartStabilityData C)
    {E Q : h.t.heart.FullSubcategory} (p : E ⟶ Q) [Epi p]
    (hss : HeartSemistable (C := C) h E) (hQ : ¬IsZero Q) :
    HeartPhase (C := C) h E ≤ HeartPhase (C := C) h Q := by
  exact phase_le_of_epi h.Z p hss hQ

theorem heart_hom_zero_of_semistable_phase_gt
    (h : HeartStabilityData C)
    {E F : h.t.heart.FullSubcategory}
    (hE : HeartSemistable (C := C) h E) (hF : HeartSemistable (C := C) h F)
    (hph : HeartPhase (C := C) h F < HeartPhase (C := C) h E) (f : E ⟶ F) : f = 0 := by
  exact hom_zero_of_semistable_phase_gt h.Z hE hF hph f

theorem phasePredicate_hom_zero_of_mem_Ioc
    (h : HeartStabilityData C)
    {φ₁ φ₂ : ℝ}
    (hφ₁ : φ₁ ∈ Set.Ioc (0 : ℝ) 1)
    (hφ₂ : φ₂ ∈ Set.Ioc (0 : ℝ) 1)
    {E F : C}
    (hE : phasePredicate (C := C) h φ₁ E)
    (hF : phasePredicate (C := C) h φ₂ F)
    (hgap : φ₂ < φ₁)
    (f : E ⟶ F) : f = 0 := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  rcases (phasePredicate_iff_of_mem_Ioc (C := C) h hφ₁ E).1 hE with hEZ | ⟨hEheart, hEss, hEphase⟩
  · exact hEZ.eq_of_src f 0
  rcases (phasePredicate_iff_of_mem_Ioc (C := C) h hφ₂ F).1 hF with hFZ | ⟨hFheart, hFss, hFphase⟩
  · exact hFZ.eq_of_tgt f 0
  let EH : h.t.heart.FullSubcategory := ⟨E, hEheart⟩
  let FH : h.t.heart.FullSubcategory := ⟨F, hFheart⟩
  have hphase : h.Z.phase FH < h.Z.phase EH := by
    calc
      h.Z.phase FH = φ₂ := hFphase
      _ < φ₁ := hgap
      _ = h.Z.phase EH := hEphase.symm
  have hzero : (ObjectProperty.homMk f : EH ⟶ FH) = 0 :=
    heart_hom_zero_of_semistable_phase_gt (C := C) h hEss hFss hphase (ObjectProperty.homMk f)
  exact congr_arg (·.hom) hzero

theorem shiftedHeartSemistable_closedUnderIso
    (h : HeartStabilityData C) (ψ : ℝ) (n : ℤ) :
    (shiftedHeartSemistable (C := C) h ψ n).IsClosedUnderIsomorphisms := by
  refine ⟨?_⟩
  intro X Y e hX
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  rcases hX with hX | ⟨hXheart, hXss, hXphase⟩
  · exact Or.inl (hX.of_iso e.symm)
  · let eShift : X⟦(-n : ℤ)⟧ ≅ Y⟦(-n : ℤ)⟧ := ((shiftFunctor C (-n : ℤ)).mapIso e)
    have hYheart : h.t.heart (Y⟦(-n : ℤ)⟧) :=
      (h.t.heart).prop_of_iso eShift hXheart
    let XH : h.t.heart.FullSubcategory := ⟨X⟦(-n : ℤ)⟧, hXheart⟩
    let YH : h.t.heart.FullSubcategory := ⟨Y⟦(-n : ℤ)⟧, hYheart⟩
    let eH : XH ≅ YH := ObjectProperty.isoMk _ eShift
    exact Or.inr ⟨hYheart, h.Z.isSemistable_of_iso eH hXss, by
      rw [← hXphase]
      change h.Z.phase YH = h.Z.phase XH
      simpa using (h.Z.phase_eq_of_iso eH).symm⟩

theorem phasePredicate_closedUnderIso
    (h : HeartStabilityData C) (φ : ℝ) :
    (phasePredicate (C := C) h φ).IsClosedUnderIsomorphisms :=
  shiftedHeartSemistable_closedUnderIso (C := C) h
    (phaseBase φ) (phaseIndex φ)

instance phasePredicate_instClosedUnderIso
    (h : HeartStabilityData C) (φ : ℝ) :
    (phasePredicate (C := C) h φ).IsClosedUnderIsomorphisms :=
  phasePredicate_closedUnderIso (C := C) h φ

theorem shiftedHeartSemistable_shift_iff
    (h : HeartStabilityData C) (ψ : ℝ) (n : ℤ) (X : C) :
    shiftedHeartSemistable (C := C) h ψ n X ↔
      shiftedHeartSemistable (C := C) h ψ (n + 1) (X⟦(1 : ℤ)⟧) := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  let eShift :
      (X⟦(1 : ℤ)⟧)⟦(-(n + 1) : ℤ)⟧ ≅ X⟦(-n : ℤ)⟧ :=
    ((shiftFunctorAdd' C (1 : ℤ) (-(n + 1) : ℤ) (-n : ℤ) (by lia)).app X).symm
  constructor
  · intro hX
    rcases hX with hX | ⟨hXheart, hXss, hXphase⟩
    · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hX)
    · have hYheart : h.t.heart ((X⟦(1 : ℤ)⟧)⟦(-(n + 1) : ℤ)⟧) :=
        (h.t.heart).prop_of_iso eShift.symm hXheart
      let XH : h.t.heart.FullSubcategory := ⟨X⟦(-n : ℤ)⟧, hXheart⟩
      let YH : h.t.heart.FullSubcategory :=
        ⟨(X⟦(1 : ℤ)⟧)⟦(-(n + 1) : ℤ)⟧, hYheart⟩
      let eH : XH ≅ YH := ObjectProperty.isoMk _ eShift.symm
      exact Or.inr ⟨hYheart, h.Z.isSemistable_of_iso eH hXss, by
        rw [← hXphase]
        change h.Z.phase YH = h.Z.phase XH
        simpa using (h.Z.phase_eq_of_iso eH).symm⟩
  · intro hX
    rcases hX with hX | ⟨hXheart, hXss, hXphase⟩
    · exact Or.inl <|
        (((shiftFunctor C (-1 : ℤ)).map_isZero hX).of_iso
          (shiftShiftNeg (X := X) (i := (1 : ℤ))).symm)
    · have hYheart : h.t.heart (X⟦(-n : ℤ)⟧) :=
        (h.t.heart).prop_of_iso eShift hXheart
      let XH : h.t.heart.FullSubcategory :=
        ⟨(X⟦(1 : ℤ)⟧)⟦(-(n + 1) : ℤ)⟧, hXheart⟩
      let YH : h.t.heart.FullSubcategory := ⟨X⟦(-n : ℤ)⟧, hYheart⟩
      let eH : XH ≅ YH := ObjectProperty.isoMk _ eShift
      exact Or.inr ⟨hYheart, h.Z.isSemistable_of_iso eH hXss, by
        rw [← hXphase]
        change h.Z.phase YH = h.Z.phase XH
        simpa using (h.Z.phase_eq_of_iso eH).symm⟩

theorem phasePredicate_shift_iff
    (h : HeartStabilityData C) (φ : ℝ) (X : C) :
    phasePredicate (C := C) h φ X ↔
      phasePredicate (C := C) h (φ + (1 : ℝ)) (X⟦(1 : ℤ)⟧) := by
  simpa [phasePredicate, phaseBase_add_one φ, phaseIndex_add_one φ] using
    (shiftedHeartSemistable_shift_iff (C := C) h
      (phaseBase φ) (phaseIndex φ) X)

theorem phasePredicate_shift_int
    (h : HeartStabilityData C) (φ : ℝ) (X : C) (n : ℤ) :
    phasePredicate (C := C) h φ X ↔
      phasePredicate (C := C) h (φ + (n : ℝ)) (X⟦n⟧) := by
  induction n using Int.induction_on generalizing φ X with
  | zero =>
      constructor
      · intro hX
        have hX' : phasePredicate (C := C) h φ (X⟦(0 : ℤ)⟧) :=
          (phasePredicate (C := C) h φ).prop_of_iso ((shiftFunctorZero C ℤ).app X).symm hX
        simpa using hX'
      · intro hX
        have hX' : phasePredicate (C := C) h φ (X⟦(0 : ℤ)⟧) := by
          simpa using hX
        exact (phasePredicate (C := C) h φ).prop_of_iso ((shiftFunctorZero C ℤ).app X) hX'
  | succ n ih =>
      constructor
      · intro hX
        let Y : C := X⟦(n : ℤ)⟧
        have h0 : phasePredicate (C := C) h (φ + (n : ℝ)) Y := by
          simpa [Y] using ((ih φ X).mp hX)
        have h1 : phasePredicate (C := C) h (φ + (n : ℝ) + 1) (Y⟦(1 : ℤ)⟧) :=
          (phasePredicate_shift_iff (C := C) h (φ + (n : ℝ)) Y).mp h0
        simpa [Y, Nat.cast_succ, add_assoc] using
          (phasePredicate (C := C) h (φ + (n : ℝ) + 1)).prop_of_iso
            ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) (by lia)).app X).symm h1
      · intro hX
        let Y : C := X⟦(n : ℤ)⟧
        have h1 : phasePredicate (C := C) h (φ + (n : ℝ) + 1) (Y⟦(1 : ℤ)⟧) := by
          simpa [Y, Nat.cast_succ, add_assoc] using
            (phasePredicate (C := C) h (φ + ((n + 1 : ℕ) : ℝ))).prop_of_iso
              ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) (by lia)).app X) hX
        have h0 : phasePredicate (C := C) h (φ + (n : ℝ)) Y :=
          (phasePredicate_shift_iff (C := C) h (φ + (n : ℝ)) Y).mpr h1
        exact (ih φ X).mpr (by simpa [Y] using h0)
  | pred n ih =>
      constructor
      · intro hX
        let Y : C := X⟦(-(n : ℤ))⟧
        have h0 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ)) Y := by
          simpa [Y] using ((ih φ X).mp hX)
        have h0' :
            phasePredicate (C := C) h ((φ + (-(n : ℤ) : ℝ) - 1) + 1)
              ((Y⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) := by
          simpa [Y, sub_eq_add_neg, add_assoc] using
            (phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ))).prop_of_iso
              (shiftNegShift (X := Y) (i := (1 : ℤ))).symm h0
        have h1 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧) :=
          (phasePredicate_shift_iff (C := C) h (φ + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧)).mpr h0'
        have h2 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ) - 1)
            ((shiftFunctor C (Int.negSucc n)).obj X) :=
          (phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ) - 1)).prop_of_iso
            ((shiftFunctorAdd' C (-(n : ℤ)) (-1 : ℤ) (Int.negSucc n) (by lia)).app X).symm h1
        simpa [Y, Int.negSucc_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2
      · intro hX
        let Y : C := X⟦(-(n : ℤ))⟧
        have hX' : phasePredicate (C := C) h (φ + (Int.negSucc n : ℝ))
            ((shiftFunctor C (Int.negSucc n)).obj X) := by
          simpa [Int.negSucc_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hX
        have h1 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧) := by
          have h2 : phasePredicate (C := C) h (φ + (Int.negSucc n : ℝ))
              ((shiftFunctor C (-1 : ℤ)).obj Y) :=
            (phasePredicate (C := C) h (φ + (Int.negSucc n : ℝ))).prop_of_iso
              ((shiftFunctorAdd' C (-(n : ℤ)) (-1 : ℤ) (Int.negSucc n) (by lia)).app X) hX'
          simpa [Y, Int.negSucc_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2
        have h0' :
            phasePredicate (C := C) h ((φ + (-(n : ℤ) : ℝ) - 1) + 1)
              ((Y⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) :=
          (phasePredicate_shift_iff (C := C) h (φ + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧)).mp h1
        have h0 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ)) Y := by
          have h0'' : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ))
              ((shiftFunctor C (1 : ℤ)).obj ((shiftFunctor C (-1 : ℤ)).obj Y)) := by
              simpa [sub_eq_add_neg, add_assoc] using h0'
          exact (phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ))).prop_of_iso
            (shiftNegShift (X := Y) (i := (1 : ℤ))) h0''
        exact (ih φ X).mpr (by simpa [Y] using h0)

theorem phaseIndex_lt_phase
    (φ : ℝ) :
    (phaseIndex φ : ℝ) < φ := by
  have hmem := phaseBase_mem φ
  have hpos : 0 < phaseBase φ := hmem.1
  nlinarith [phaseBase_add_phaseIndex φ]

theorem phase_le_phaseIndex_add_one
    (φ : ℝ) :
    φ ≤ (phaseIndex φ : ℝ) + 1 := by
  have hmem := phaseBase_mem φ
  have hle : phaseBase φ ≤ 1 := hmem.2
  nlinarith [phaseBase_add_phaseIndex φ]

theorem phaseIndex_le_of_lt
    {φ₁ φ₂ : ℝ} (hlt : φ₂ < φ₁) :
    phaseIndex φ₂ ≤ phaseIndex φ₁ := by
  by_contra hle
  have hgt : phaseIndex φ₁ < phaseIndex φ₂ := lt_of_not_ge hle
  have hstep : (phaseIndex φ₁ : ℝ) + 1 ≤ phaseIndex φ₂ := by
    exact_mod_cast (Int.add_one_le_iff.mpr hgt)
  linarith [phaseIndex_lt_phase φ₂, phase_le_phaseIndex_add_one φ₁]

theorem phasePredicate_hom_zero
    (h : HeartStabilityData C)
    {φ₁ φ₂ : ℝ} {E F : C}
    (hE : phasePredicate (C := C) h φ₁ E)
    (hF : phasePredicate (C := C) h φ₂ F)
    (hgap : φ₂ < φ₁)
    (f : E ⟶ F) : f = 0 := by
  let n₁ := phaseIndex φ₁
  let n₂ := phaseIndex φ₂
  let ψ₁ := phaseBase φ₁
  let ψ₂ := phaseBase φ₂
  rcases hE with hEZ | ⟨hEheart, hEss, hEphase⟩
  · exact hEZ.eq_of_src f 0
  rcases hF with hFZ | ⟨hFheart, hFss, hFphase⟩
  · exact hFZ.eq_of_tgt f 0
  have hle : n₂ ≤ n₁ := phaseIndex_le_of_lt hgap
  by_cases hidx : n₂ = n₁
  · let EH : h.t.heart.FullSubcategory := ⟨E⟦(-n₁ : ℤ)⟧, by simpa [n₁] using hEheart⟩
    let FH : h.t.heart.FullSubcategory := ⟨F⟦(-n₁ : ℤ)⟧, by simpa [n₁, n₂, hidx] using hFheart⟩
    have hEss' : HeartSemistable (C := C) h EH := by
      simpa [EH, n₁] using hEss
    have hFss' : HeartSemistable (C := C) h FH := by
      simpa [FH, n₁, n₂, hidx] using hFss
    have hEphase' : HeartPhase (C := C) h EH = ψ₁ := by
      simpa [EH, ψ₁, n₁] using hEphase
    have hFphase' : HeartPhase (C := C) h FH = ψ₂ := by
      simpa [FH, ψ₂, n₁, n₂, hidx] using hFphase
    have hψ : ψ₂ < ψ₁ := by
      have hφ₂ : φ₂ = ψ₂ + (n₁ : ℝ) := by
        simpa [ψ₂, n₁, n₂, hidx] using (phaseBase_add_phaseIndex φ₂).symm
      have hφ₁ : φ₁ = ψ₁ + (n₁ : ℝ) := by
        simpa [ψ₁, n₁] using (phaseBase_add_phaseIndex φ₁).symm
      linarith [hgap, hφ₂, hφ₁]
    let g : EH.obj ⟶ FH.obj := (shiftFunctor C (-n₁ : ℤ)).map f
    have hg_zero :
        (ObjectProperty.homMk g : EH ⟶ FH) = 0 :=
      heart_hom_zero_of_semistable_phase_gt (C := C) h hEss' hFss' (by
        rw [hFphase', hEphase']
        exact hψ) (ObjectProperty.homMk g)
    have hmap : g = 0 := congr_arg (·.hom) hg_zero
    exact (shiftFunctor C (-n₁ : ℤ)).map_injective (by simpa [g] using hmap)
  · let EH : h.t.heart.FullSubcategory := ⟨E⟦(-n₁ : ℤ)⟧, by simpa [n₁] using hEheart⟩
    let FH : h.t.heart.FullSubcategory := ⟨F⟦(-n₂ : ℤ)⟧, by simpa [n₂] using hFheart⟩
    let d : ℤ := n₁ - n₂
    have hdpos : 0 < d := by
      dsimp [d]
      lia
    let eE : EH.obj⟦d⟧ ≅ E⟦(-n₂ : ℤ)⟧ :=
      ((shiftFunctorAdd' C (-n₁ : ℤ) d (-n₂ : ℤ) (by
        dsimp [d]
        lia)).app E).symm
    let g : EH.obj⟦d⟧ ⟶ FH.obj := eE.hom ≫ (shiftFunctor C (-n₂ : ℤ)).map f
    haveI : h.t.IsLE EH.obj 0 := by simpa [EH, n₁] using hEheart.1
    haveI : h.t.IsGE FH.obj 0 := by simpa [FH, n₂] using hFheart.2
    haveI : h.t.IsLE (EH.obj⟦d⟧) (-d) :=
      h.t.isLE_shift EH.obj 0 d (-d) (by lia)
    have hg : g = 0 := by
      simpa using h.t.zero_of_isLE_of_isGE g (-d) 0 (by lia)
        (show h.t.IsLE (EH.obj⟦d⟧) (-d) by infer_instance)
        (show h.t.IsGE FH.obj 0 by infer_instance)
    have hshift : (shiftFunctor C (-n₂ : ℤ)).map f = 0 := by
      apply (cancel_epi eE.hom).mp
      simpa [g] using hg
    exact (shiftFunctor C (-n₂ : ℤ)).map_injective (by simpa using hshift)

/-- A local reverse-direction package: the induced phase family from heart stability
data, together with the phase axioms proved in this file. This isolates the
part of Bridgeland Proposition 5.3 already formalized here, before the ambient
central charge on `K₀ C` and the full HN existence for the induced slices are
packaged. -/
structure PhasePackage where
  /-- The heart-side input data of Proposition 5.3. -/
  heartData : HeartStabilityData C
  /-- The induced phase predicate on the ambient triangulated category. -/
  P : ℝ → ObjectProperty C
  /-- The phase predicates are closed under isomorphism. -/
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  /-- The zero object lies in every phase. -/
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)
  /-- Shifting by `[1]` raises the phase by `1`. -/
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  /-- Morphisms from higher phase to lower phase vanish. -/
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0

/-- Forget the reverse-direction phase package back to the original heart data. -/
def PhasePackage.toHeartStabilityData
    (σ : PhasePackage C) : HeartStabilityData C :=
  σ.heartData

/-- **Proposition 5.3b / reverse direction, packaged so far.**
Heart stability data determines the ambient phase family `P(φ)` together with the
isomorphism, shift, and Hom-vanishing axioms of a Bridgeland slicing. The two
remaining reverse-direction steps, not yet packaged here, are:
1. constructing the ambient central charge `K₀ C →+ ℂ`;
2. proving HN existence for the induced phase family. -/
def HeartStabilityData.toPhasePackage
    (h : HeartStabilityData C) : PhasePackage C where
  heartData := h
  P := phasePredicate (C := C) h
  closedUnderIso := phasePredicate_closedUnderIso (C := C) h
  zero_mem := fun _ ↦ Or.inl (isZero_zero C)
  shift_iff := phasePredicate_shift_iff (C := C) h
  hom_vanishing := fun _φ₁ _φ₂ _A _B hlt hA hB f ↦
    phasePredicate_hom_zero (C := C) h hA hB hlt f

/-- The corresponding reverse-direction package extracted from an honest stability
condition. -/
def StabilityCondition.toPhasePackage
    (σ : StabilityCondition C) : PhasePackage C :=
  (σ.toHeartStabilityData C).toPhasePackage C

/-- **Proposition 5.3c / left inverse, at the pre-stability level.**
Starting from a stability condition `σ`, extracting heart data, and reconstructing
the in-file reverse-direction pre-stability package agrees with the direct
definition of that package from `σ`. -/
theorem StabilityCondition.roundtrip
    (σ : StabilityCondition C) :
    (σ.toHeartStabilityData C).toPhasePackage C = σ.toPhasePackage C := by
  rfl

/-- **Proposition 5.3c / right inverse, at the heart-data level.**
For the in-file reverse-direction package, forgetting back to heart data recovers
the original input exactly. -/
theorem HeartStabilityData.roundtrip
    (h : HeartStabilityData C) :
    (h.toPhasePackage C).toHeartStabilityData C = h := by
  rfl

end Proposition53

/-! ## §5: Lemma 5.2 consequences — P(φ) closure properties

### FALSE: P(φ) is NOT closed under subobjects in the heart

**Counterexample** (elliptic curve, standard stability condition `Z(E) = -deg(E) + i·rank(E)`):
Take `F` = semistable rank 2 bundle of degree 2 on an elliptic curve `E`.
Then `F ∈ P(3/4)` (since `arg(Z(F)) = arg(-2 + 2i) = 3π/4`).
A nonzero section `O_E → F` gives a sub-line-bundle `O_E ↪ F` in the heart `Coh(E)`.
But `O_E ∈ P(1/2)` (since `arg(Z(O_E)) = arg(i) = π/2`), so `O_E ∉ P(3/4)`.

**Why the see-saw argument fails**: For the triangle `A → E → Q → A⟦1⟧` with `E ∈ P(φ)`:
- `φ⁺(A) ≤ φ` (from `phiPlus_triangle_le`), so `Im(Z(A) · rot) ≤ 0`
- `φ⁻(Q) ≥ φ` (from `phiMinus_triangle_le`), so `Im(Z(Q) · rot) ≥ 0`
- Sum `= Im(Z(E) · rot) = 0` — but the terms have **opposite signs**, so sum `= 0`
  does NOT force each to be zero.

Compare with `P_phi_of_heart_triangle` (in `Deformation.lean`), which IS correct: it
requires BOTH `K` and `Q` to have phases `≤ φ` (and `> φ - 1`), ensuring same-sign
terms in the sum. -/

section PhaseSubcategoryProperties

variable [IsTriangulated C]

-- NOTE: The theorems `P_phi_closed_under_subobjects_in_heart` and
-- `P_phi_closed_under_quotients_in_heart` that were previously here are
-- MATHEMATICALLY FALSE and have been deleted. See the section comment above
-- for a counterexample.
--
-- The correct results for P(φ) closure are:
-- 1. `P_phi_of_heart_triangle` (Deformation.lean): if BOTH K and Q have
--    phases in (φ-1, φ], then K ∈ P(φ) and Q ∈ P(φ).
-- 2. For Bridgeland's arguments (Lemma 7.6, 7.7), the quasi-abelian
--    structure of P((a,b)) is needed. Strict subobjects in the quasi-abelian
--    category DO stay in the interval, but arbitrary heart-subobjects do NOT
--    stay in P(φ).

end PhaseSubcategoryProperties

/-! ## §7: Deformation infrastructure — heart SES bridge -/

section DeformationInfrastructure

variable [IsTriangulated C]

omit [IsTriangulated C] in
set_option backward.isDefEq.respectTransparency false in
/-- **Heart SES to distinguished triangle.**
Given a short exact sequence in the abelian heart (as objects and morphisms
in the ambient category `C` that lie in the heart), there is a distinguished
triangle extending it.

This is the fundamental bridge between abelian exact sequences in the heart
and triangulated exact triangles in the ambient category. It is used in
Lemma 7.6 (small-gap hom-vanishing) to translate kernel/image/cokernel
decompositions into phase bound arguments. -/
theorem TStructure.heart_shortExact_triangle
    (t : TStructure C) {A B Q : C}
    (hA : t.heart A) (hB : t.heart B) (hQ : t.heart Q)
    (f : A ⟶ B) (g : B ⟶ Q) (hfg : f ≫ g = 0)
    (hmono : Mono f) (hepi : Epi g)
    (hexact : ∀ {W : C} (α : W ⟶ B), α ≫ g = 0 →
      ∃ (β : W ⟶ A), β ≫ f = α) :
    ∃ (h : Q ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  -- Work in the heart abelian subcategory (letI for transparent instance reduction)
  letI := t.hasHeartFullSubcategory
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  let A' : t.heart.FullSubcategory := ⟨A, hA⟩
  let B' : t.heart.FullSubcategory := ⟨B, hB⟩
  let Q' : t.heart.FullSubcategory := ⟨Q, hQ⟩
  let f' : A' ⟶ B' := ObjectProperty.homMk f
  let g' : B' ⟶ Q' := ObjectProperty.homMk g
  -- g' is epi in the heart (faithful inclusion preserves the epi test)
  haveI : Epi g' := ⟨fun {Z} h₁ h₂ hh ↦ by
    ext; exact (cancel_epi g).mp (by
      simpa [ObjectProperty.FullSubcategory.comp_hom] using
        congr_arg InducedCategory.Hom.hom hh)⟩
  -- Get a distinguished triangle from the epi g' via the heart's abelian structure
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (heart_hι t) (heart_admissible t) g'
  -- hT : Triangle.mk (ι.map i) (ι.map g') δ ∈ distTriang C
  -- Factor ι.map i through f via hexact (i ≫ g' = 0 from the triangle)
  have h_ig : (ι.map i) ≫ g = 0 :=
    comp_distTriang_mor_zero₁₂ _ hT
  obtain ⟨β_hom, hβ_hom⟩ := hexact _ h_ig
  let β : K ⟶ A' := ObjectProperty.homMk β_hom
  have hβf : β ≫ f' = i := ι.map_injective (by
    rw [Functor.map_comp]; change β_hom ≫ f = ι.map i; exact hβ_hom)
  -- i is a kernel of g' in the heart (from the distinguished triangle)
  have hKer :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang (heart_hι t) i g' δ hT
  -- f' ≫ g' = 0 in the heart
  have hfg' : f' ≫ g' = 0 := ι.map_injective (by
    rw [Functor.map_comp, Functor.map_zero]; change f ≫ g = 0; exact hfg)
  -- Lift f' through the kernel i to get γ : A' ⟶ K with γ ≫ i = f'
  let γ : A' ⟶ K := hKer.lift (KernelFork.ofι f' hfg')
  have hγi : γ ≫ i = f' := Fork.IsLimit.lift_ι hKer
  -- β and γ are mutually inverse (both are kernel maps for g')
  have hβγ : β ≫ γ = 𝟙 K :=
    Fork.IsLimit.hom_ext hKer (by simp [hγi, hβf])
  have hγβ : γ ≫ β = 𝟙 A' := by
    haveI : Mono f' := ⟨fun {Z} h₁ h₂ hh ↦ by
      ext; exact (cancel_mono f).mp (by
        simpa [ObjectProperty.FullSubcategory.comp_hom] using
          congr_arg InducedCategory.Hom.hom hh)⟩
    rw [← cancel_mono f', Category.assoc, hβf, hγi, Category.id_comp]
  -- Construct the isomorphism K ≅ A' in the heart
  let eKA : K ≅ A' :=
    { hom := β, inv := γ, hom_inv_id := hβγ, inv_hom_id := hγβ }
  -- Transport the distinguished triangle via eKA
  -- T = Triangle.mk (ι.map i) (ι.map g') δ ∈ distTriang C
  -- T' = Triangle.mk f g h with h = δ ≫ (shiftFunctor C (1 : ℤ)).map (ι.map β)
  -- iso: T' ≅ T given by (ι.mapIso eKA.symm, id, id)
  refine ⟨δ ≫ ((shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)), ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (ι.mapIso eKA.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · -- comm₁: f ≫ 𝟙 = (ι.map γ) ≫ (ι.map i)
    simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom,
      Triangle.mk_mor₁]
    -- After simp: f = ι.map eKA.inv ≫ t.ιHeart.map i
    -- eKA.inv = γ and t.ιHeart = ι (via let), so:
    change f = ι.map γ ≫ ι.map i
    rw [← Functor.map_comp, hγi]; rfl
  · -- comm₂: g ≫ 𝟙 = 𝟙 ≫ (ι.map g')
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl
  · -- comm₃: (δ ≫ F.map (ι.map β)) ≫ F.map (ι.map γ) = 𝟙 ≫ δ
    simp only [Iso.refl_hom, Category.id_comp, Triangle.mk_mor₃, Functor.mapIso_hom,
      Iso.symm_hom]
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp, ← ι.map_comp, hβγ,
      ι.map_id, Functor.map_id, Category.comp_id]

end DeformationInfrastructure

end CategoryTheory.Triangulated
