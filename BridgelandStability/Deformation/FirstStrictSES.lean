/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.Pullback

/-!
# First Strict Short Exact Sequence

Max-phase strict subobjects, first destabilizing strict SES for objects
that are not W-semistable.
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

theorem SkewedStabilityFunction.semistable_of_iso
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    {E E' : C} (e : E ≅ E') {ψ : ℝ} (h : ssf.Semistable C E ψ) :
    ssf.Semistable C E' ψ := by
  refine ⟨(s.intervalProp C a b).prop_of_iso e h.1, ?_, ?_, ?_, ?_⟩
  · exact fun hE' ↦ h.2.1 ((Iso.isZero_iff e).mpr hE')
  · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
    exact h.2.2.1
  · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
    exact h.2.2.2.1
  · intro K Q f₁ f₂ f₃ hT hK hQ hKne
    have hT' : Triangle.mk (f₁ ≫ e.inv) (e.hom ≫ f₂) f₃ ∈ distTriang C :=
      isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
          (by simp) (by simp) (by simp))
    exact h.2.2.2.2 hT' hK hQ hKne

variable [IsTriangulated C] in
/-- A maximal-phase strict subobject of a non-semistable interval object cannot be `⊤`. -/
theorem SkewedStabilityFunction.maxPhase_strictSubobject_ne_top_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hM_ne : M ≠ ⊥) (hM_strict : IsStrictMono M.arrow)
    (hM_max : ∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    M ≠ ⊤ := by
  intro hM_top
  apply hns
  have hM_ss :=
    ssf.semistable_of_maxPhase_strictSubobject (C := C) (σ := σ)
      (a := a) (b := b) hM_ne hM_strict hM_max hW_interval
  subst hM_top
  have hphase :
      wPhaseOf
          (ssf.W
            (K₀.of C (((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj))) ssf.α =
        wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
    let eC :
        (((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj) ≅ X.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (asIso (⊤ : Subobject X).arrow)
    simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
  let eC :
      (((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj) ≅ X.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
      (asIso (⊤ : Subobject X).arrow)
  have hTop_ss := semistable_of_iso
    (C := C) (s := σ.slicing) (a := a) (b := b)
    eC hM_ss
  simpa [hphase] using hTop_ss

variable [IsTriangulated C] in
/-- In a non-semistable interval object, a maximal-phase strict subobject has strictly
larger phase than the ambient object. -/
theorem SkewedStabilityFunction.phase_gt_of_maxPhase_strictSubobject_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hX : ¬IsZero X)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hM_ne : M ≠ ⊥) (hM_strict : IsStrictMono M.arrow)
    (hM_max : ∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
  let phaseObj : σ.slicing.IntervalCat C a b → ℝ := fun Y ↦
    wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hX_obj : ¬IsZero X.obj := by
    intro hZ
    exact hX (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  by_contra hle
  push_neg at hle
  apply hns
  refine ⟨X.property, hX_obj, hW_interval X.property hX_obj, rfl, ?_⟩
  intro K Q f₁ f₂ f₃ hT hK hQ hKne
  let KI : σ.slicing.IntervalCat C a b := ⟨K, hK⟩
  let QI : σ.slicing.IntervalCat C a b := ⟨Q, hQ⟩
  let iKX : KI ⟶ X := ObjectProperty.homMk f₁
  let gXQ : X ⟶ QI := ObjectProperty.homMk f₂
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk iKX gXQ (by
      ext
      simpa [iKX, gXQ] using comp_distTriang_mor_zero₁₂ _ hT)
  have hT' : Triangle.mk S.f.hom S.g.hom f₃ ∈ distTriang C := by
    simpa [S, iKX, gXQ] using hT
  have hK_strict : IsStrictMono iKX :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b) hT').1
  letI : Mono iKX := hK_strict.mono
  let B : Subobject X := Subobject.mk iKX
  have hKI_ne : ¬IsZero KI := by
    intro hZ
    exact hKne (((σ.slicing.intervalProp C a b).ι).map_isZero hZ)
  have hB_ne : B ≠ ⊥ := by
    intro hB
    have hzero : iKX = 0 := by
      exact (Subobject.mk_eq_bot_iff_zero).mp
        (show Subobject.mk iKX = ⊥ by simpa [B] using hB)
    have hId : 𝟙 KI = 0 := by
      apply (cancel_mono iKX).1
      simpa [hzero]
    exact hKI_ne ((IsZero.iff_id_eq_zero KI).mpr hId)
  have hB_strict : IsStrictMono B.arrow := by
    simpa [B] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) iKX hK_strict)
  have hPhaseB : phaseObj KI ≤ phaseObj M := by
    have hPhaseSub : phaseObj (B : σ.slicing.IntervalCat C a b) ≤ phaseObj M :=
      hM_max B hB_ne hB_strict
    have hIsoK :
        phaseObj KI = phaseObj (B : σ.slicing.IntervalCat C a b) := by
      let eC : (B : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (Subobject.underlyingIso iKX)
      simpa [phaseObj] using congrArg (fun x => wPhaseOf (ssf.W x) ssf.α)
        (K₀.of_iso C eC).symm
    exact hIsoK.trans_le hPhaseSub
  simpa [phaseObj, KI] using hPhaseB.trans hle

variable [IsTriangulated C] in
/-- Strict-Artinian descent for the first strict short exact sequence: starting from a
non-semistable thin-interval object, repeatedly pass to a proper strict subobject of larger
phase until the descent terminates at a semistable strict subobject. This is the faithful
Section 7 substitute for the older finite-enumeration wrapper. -/
theorem SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} [IsStrictArtinianObject X] (hX : ¬IsZero X)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    ∃ M : Subobject X,
      M ≠ ⊥ ∧
      M ≠ ⊤ ∧
      IsStrictMono M.arrow ∧
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
      StrictShortExact
        (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) := by
  let phaseSub : StrictSubobject X → ℝ := fun B ↦
    wPhaseOf (ssf.W (K₀.of C ((B.1 : σ.slicing.IntervalCat C a b).obj))) ssf.α
  let P : StrictSubobject X → Prop := fun B =>
    ∀ hBne : ¬IsZero (B.1 : σ.slicing.IntervalCat C a b),
      ¬ ssf.Semistable C ((B.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub B) →
      ∃ D : StrictSubobject X,
        D < B ∧
        ssf.Semistable C ((D.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub D) ∧
        phaseSub B < phaseSub D
  have hP : ∀ B : StrictSubobject X, P B := by
    intro B
    refine (show WellFounded ((· < ·) : StrictSubobject X → StrictSubobject X → Prop) from
      wellFounded_lt).induction B ?_
    intro B ih hBne hnsB
    obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hphaseBA⟩ :=
      ssf.exists_phase_gt_strictSubobject_of_not_semistable
        (C := C) (σ := σ) (a := a) (b := b) (X := (B.1 : σ.slicing.IntervalCat C a b))
        hBne hW_interval hnsB
    let Csub : Subobject X := intervalLiftSub (C := C) (X := X) B.1 A
    have hC_ne_bot : Csub ≠ ⊥ :=
      intervalLiftSub_ne_bot (C := C) (X := X) B.1 hA_ne_bot
    have hC_strict : IsStrictMono Csub.arrow :=
      intervalLiftSub_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.2 hA_strict
    let Cstr : StrictSubobject X := ⟨Csub, hC_strict⟩
    have hC_lt_B : Cstr < B := by
      simpa [Cstr, Csub] using
        (intervalLiftSub_lt (C := C) (X := X) B.1 hA_ne_top)
    have hC_ne : ¬IsZero (Cstr.1 : σ.slicing.IntervalCat C a b) :=
      intervalSubobject_not_isZero_of_ne_bot
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hC_ne_bot
    have hphaseBC : phaseSub B < phaseSub Cstr := by
      dsimp [phaseSub, Cstr, Csub]
      rw [intervalLiftSub_wPhase_eq (C := C) (s := σ.slicing) (ssf := ssf) B.1 A]
      exact hphaseBA
    by_cases hssC :
        ssf.Semistable C ((Cstr.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub Cstr)
    · exact ⟨Cstr, hC_lt_B, hssC, hphaseBC⟩
    · obtain ⟨D, hD_lt_C, hssD, hphaseCD⟩ := ih Cstr hC_lt_B hC_ne hssC
      exact ⟨D, lt_trans hD_lt_C hC_lt_B, hssD, lt_trans hphaseBC hphaseCD⟩
  obtain ⟨B, hB_ne_bot, hB_ne_top, hB_strict, hphaseXB⟩ :=
    ssf.exists_phase_gt_strictSubobject_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hX hW_interval hns
  let Bstr : StrictSubobject X := ⟨B, hB_strict⟩
  have hB_ne : ¬IsZero (Bstr.1 : σ.slicing.IntervalCat C a b) :=
    intervalSubobject_not_isZero_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hB_ne_bot
  have hphaseXB' :
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α < phaseSub Bstr := by
    simpa [phaseSub, Bstr] using hphaseXB
  by_cases hssB :
      ssf.Semistable C ((Bstr.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub Bstr)
  · refine ⟨B, hB_ne_bot, hB_ne_top, hB_strict, ?_, hphaseXB, ?_⟩
    · simpa [phaseSub, Bstr] using hssB
    · exact interval_strictShortExact_cokernel_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.arrow hB_strict
  · obtain ⟨D, hD_lt_B, hssD, hphaseBD⟩ := hP Bstr hB_ne hssB
    have hD_ne_top : D.1 ≠ ⊤ := by
      intro hD
      have htop_le : (⊤ : Subobject X) ≤ B := by
        have hle : D.1 ≤ B := hD_lt_B.le
        simpa [hD] using hle
      exact hB_ne_top (top_le_iff.mp htop_le)
    have hD_ne_bot : D.1 ≠ ⊥ := by
      intro hD
      exact hssD.2.1
        (((σ.slicing.intervalProp C a b).ι).map_isZero
          ((intervalSubobject_isZero_iff_eq_bot
            (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) D.1).mpr hD))
    refine ⟨D.1, hD_ne_bot, hD_ne_top, D.2, ?_, ?_, ?_⟩
    · simpa [phaseSub] using hssD
    · exact lt_trans hphaseXB' hphaseBD
    · exact interval_strictShortExact_cokernel_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) D.1.arrow D.2

variable [IsTriangulated C] in
/-- Finiteness of subobjects in the left-heart image of an interval object implies finiteness of
its strict-subobject set in the thin interval category. This is the paper-faithful local
finite-length input for the first strict short exact sequence. -/
theorem Slicing.IntervalCat.finite_strictSubobjects_of_finite_leftHeartSubobjects
    (s : Slicing C) {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b}
    (hX : Finite (Subobject ((Slicing.IntervalCat.toLeftHeart
      (C := C) (s := s) a b (Fact.out : b - a ≤ 1)).obj X))) :
    Finite {B : Subobject X // B ≠ ⊥ ∧ IsStrictMono B.arrow} := by
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let φ : {B : Subobject X // B ≠ ⊥ ∧ IsStrictMono B.arrow} → Subobject (FL.obj X) :=
    fun B ↦ by
      letI : Mono (FL.map B.1.arrow) :=
        Slicing.IntervalCat.mono_toLeftHeart_of_strictMono
          (C := C) (s := s) (a := a) (b := b) B.1.arrow B.2.2
      exact Subobject.mk (FL.map B.1.arrow)
  exact Finite.of_injective φ (fun B₁ B₂ hEq ↦ by
    letI : Mono (FL.map B₁.1.arrow) :=
      Slicing.IntervalCat.mono_toLeftHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) B₁.1.arrow B₁.2.2
    letI : Mono (FL.map B₂.1.arrow) :=
      Slicing.IntervalCat.mono_toLeftHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) B₂.1.arrow B₂.2.2
    apply Subtype.ext
    simpa [Subobject.mk_arrow] using Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
      (FL.preimageIso (Subobject.isoOfMkEqMk _ _ hEq))
      (FL.map_injective (by
        simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
        exact Subobject.ofMkLEMk_comp hEq.le)))

variable [IsTriangulated C] in
/-- Bridgeland's first strict short exact sequence in a thin category: if an interval object is
not `W`-semistable, there is a proper strict subobject of maximal `W`-phase, and its inclusion
gives a strict short exact sequence `0 → A → E → B → 0`.

The faithful local-finiteness input here is finiteness of the thin category's
strict-subobject set, not an ambient `Finite (Subobject X.obj)` statement in `C`. -/
theorem SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hT_fin : Set.Finite {M : Subobject X | M ≠ ⊥ ∧ IsStrictMono M.arrow})
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    ∃ M : Subobject X,
      M ≠ ⊥ ∧
      M ≠ ⊤ ∧
      IsStrictMono M.arrow ∧
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
      StrictShortExact
        (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) := by
  obtain ⟨M, hM_ne, hM_strict, hM_max, _⟩ :=
    ssf.exists_maxPhase_maximal_strictSubobject_of_finite
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hX hT_fin
  have hM_ne_top : M ≠ ⊤ :=
    ssf.maxPhase_strictSubobject_ne_top_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hns hM_ne hM_strict hM_max hW_interval
  have hM_ss :
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) :=
    ssf.semistable_of_maxPhase_strictSubobject
      (C := C) (σ := σ) (a := a) (b := b) hM_ne hM_strict hM_max hW_interval
  have hphase_gt :
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
    ssf.phase_gt_of_maxPhase_strictSubobject_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hX hns hM_ne hM_strict hM_max hW_interval
  have hS : StrictShortExact
      (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) :=
    interval_strictShortExact_cokernel_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) M.arrow hM_strict
  exact ⟨M, hM_ne, hM_ne_top, hM_strict, hM_ss, hphase_gt, hS⟩


end CategoryTheory.Triangulated
