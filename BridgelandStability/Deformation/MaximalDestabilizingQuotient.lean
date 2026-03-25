/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.StrictShortExactSequence

/-!
# Deformation of Stability Conditions — MDQ

ThinFiniteLengthInInterval, IsStrictMDQ, MDQ existence
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

omit [IsTriangulated C] in
/-- The thin interval category `P((a,b))` has strict finite length when every interval object is
both strict artinian and strict noetherian. This is the finite-length hypothesis used in the mdq
construction. -/
def ThinFiniteLengthInInterval (σ : StabilityCondition C) (a b : ℝ)
    [Fact (a < b)] [Fact (b - a ≤ 1)] : Prop :=
  ∀ Y : σ.slicing.IntervalCat C a b,
    IsStrictArtinianObject Y ∧ IsStrictNoetherianObject Y

theorem ThinFiniteLengthInInterval.of_wide
    (σ : StabilityCondition C) {ε₀ t a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (ha : t - 4 * ε₀ ≤ a) (hb : b ≤ t + 4 * ε₀)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8) :
    ThinFiniteLengthInInterval (C := C) σ a b := by
  let a' : ℝ := t - 4 * ε₀
  let b' : ℝ := t + 4 * ε₀
  letI : Fact (a' < b') := ⟨by
    dsimp [a', b']
    linarith⟩
  letI : Fact (b' - a' ≤ 1) := ⟨by
    dsimp [a', b']
    linarith⟩
  let hIncl : σ.slicing.intervalProp C a b ≤ σ.slicing.intervalProp C a' b' := by
    intro F hF
    exact σ.slicing.intervalProp_mono C ha hb hF
  intro X
  exact interval_thinFiniteLength_of_inclusion_strict
    (C := C) (s₁ := σ.slicing) (s₂ := σ.slicing)
    (a₁ := a) (b₁ := b) (a₂ := a') (b₂ := b') hIncl (hWide t) X

theorem ThinFiniteLengthInInterval.of_ambient
    (σ : StabilityCondition C) {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : σ.slicing.intervalProp C a₁ b₁ ≤ σ.slicing.intervalProp C a₂ b₂)
    (hFinite : ∀ Y : σ.slicing.IntervalCat C a₂ b₂,
      IsArtinianObject Y ∧ IsNoetherianObject Y) :
    ThinFiniteLengthInInterval (C := C) σ a₁ b₁ := by
  intro X
  exact interval_thinFiniteLength_of_inclusion
    (C := C) (s₁ := σ.slicing) (s₂ := σ.slicing)
    (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h hFinite X

theorem thinFiniteLength_of_node78_window
    (σ : StabilityCondition C) {ε₀ t : ℝ}
    [Fact (t - 3 * ε₀ < t + 5 * ε₀)]
    [Fact ((t + 5 * ε₀) - (t - 3 * ε₀) ≤ 1)]
    (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8) :
    ThinFiniteLengthInInterval (C := C) σ (t - 3 * ε₀) (t + 5 * ε₀) := by
  refine ThinFiniteLengthInInterval.of_wide
    (C := C) σ (t := t + ε₀) hε₀ hε₀8 ?_ ?_ hWide
  · dsimp
    linarith
  · dsimp
    linarith

/-- Faithful strict finite-length quotient selection for thin interval categories:
every nonzero interval object admits a semistable strict quotient whose phase is at most
that of the object. This is the strict-kernel analogue of Proposition 2.4's first
quotient-selection step, and uses only strict chain conditions, not finite enumeration
of all subobjects. -/
theorem SkewedStabilityFunction.exists_semistable_strictQuotient_le_phase_of_finiteLength
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X) :
    ∃ M : Subobject X, M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
      ssf.Semistable C (cokernel M.arrow).obj
        (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α) ∧
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
  let phaseQ : Subobject X → ℝ := fun M ↦
    wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  have h :
      ∀ S : StrictSubobject X, ¬IsZero (cokernel S.1.arrow) →
        ∃ T : StrictSubobject X,
          S.1 ≤ T.1 ∧
          ssf.Semistable C (cokernel T.1.arrow).obj (phaseQ T.1) ∧
          phaseQ T.1 ≤ phaseQ S.1 := by
    intro S hQS_ne
    revert hQS_ne
    induction S using IsWellFounded.induction
      (· > · : StrictSubobject X → StrictSubobject X → Prop) with
    | ind S ih =>
        intro hQS_ne
        have hS_ne_top : S.1 ≠ ⊤ := by
          intro hS_top
          haveI : IsIso S.1.arrow := (Subobject.isIso_iff_mk_eq_top S.1.arrow).2
            (by simpa [Subobject.mk_arrow] using hS_top)
          exact hQS_ne (isZero_cokernel_of_epi S.1.arrow)
        let QS : σ.slicing.IntervalCat C a b := cokernel S.1.arrow
        letI : IsStrictArtinianObject QS := (hFiniteLength QS).1
        by_cases hQS_ss : ssf.Semistable C QS.obj (phaseQ S.1)
        · exact ⟨S, le_rfl, hQS_ss, le_rfl⟩
        · obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hA_ss, hA_phase_gt, _⟩ :=
            ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
              (C := C) (σ := σ) (a := a) (b := b) (X := QS) hQS_ne hQS_ss hW_interval
          let pbA : Subobject X := (Subobject.pullback (cokernel.π S.1.arrow)).obj A
          have hpb_strict : IsStrictMono pbA.arrow :=
            interval_pullback_arrow_strictMono_of_strictMono
              (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π S.1.arrow) A hA_strict
          let T : StrictSubobject X := ⟨pbA, hpb_strict⟩
          have hS_lt_T : S < T := by
            apply lt_of_lt_of_le
              (interval_lt_pullback_cokernel_of_ne_bot
                (C := C) (s := σ.slicing) (a := a) (b := b) (M := S.1) (B := A) hA_ne_bot)
            exact le_rfl
          have hpb_ne_top : pbA ≠ ⊤ :=
            interval_pullback_cokernel_ne_top_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hA_ne_top hA_strict
          have hQT_ne : ¬IsZero (cokernel pbA.arrow) :=
            interval_cokernel_nonzero_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hpb_ne_top hpb_strict
          obtain ⟨U, hTU_le, hU_ss, hU_phase⟩ := ih T hS_lt_T hQT_ne
          have hpb_phase_eq :
              phaseQ pbA =
                wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
            dsimp [phaseQ, pbA]
            rw [ssf.Wobj_cokernel_pullback_eq
              (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) S.1 S.2
              (B := A) hA_strict]
          have hpb_phase_lt : phaseQ pbA < phaseQ S.1 := by
            rw [hpb_phase_eq]
            exact ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
              (C := C) (σ := σ) (a := a) (b := b)
              hA_ne_bot hA_ne_top hA_strict hA_phase_gt hW_interval hWindow hWidth
          exact ⟨U, le_trans hS_lt_T.le hTU_le, hU_ss, le_trans hU_phase hpb_phase_lt.le⟩
  let S0 : StrictSubobject X := ⟨⊥,
    intervalSubobject_bot_arrow_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b)⟩
  have hS0_ne : ¬IsZero (cokernel S0.1.arrow) := by
    let eI : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    intro hZ
    exact hX (hZ.of_iso eI.symm)
  obtain ⟨T, _, hT_ss, hT_phase_le⟩ := h S0 hS0_ne
  have hT_ne_top : T.1 ≠ ⊤ := by
    intro hT_top
    haveI : IsIso T.1.arrow := (Subobject.isIso_iff_mk_eq_top T.1.arrow).2
      (by simpa [Subobject.mk_arrow] using hT_top)
    have hzero_obj : IsZero (cokernel T.1.arrow).obj :=
      ((σ.slicing.intervalProp C a b).ι).map_isZero (isZero_cokernel_of_epi T.1.arrow)
    exact hT_ss.2.1 hzero_obj
  have hphase0 :
      phaseQ S0.1 = wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
    let eI : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    let eC : (cokernel ((⊥ : Subobject X).arrow)).obj ≅ X.obj :=
      (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
    simpa [phaseQ, S0] using
      congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
  exact ⟨T.1, hT_ne_top, T.2, hT_ss, hT_phase_le.trans_eq hphase0⟩

variable [IsTriangulated C] in
/-- A strict maximally destabilizing quotient in a thin interval category. This is the
quasi-abelian analogue of `StabilityFunction.IsMDQ`: the quotient is strict epi, nonzero,
semistable, minimal among semistable strict quotients, and equality of phase forces
factorization through it. -/
structure IsStrictMDQ
    (σ : StabilityCondition C) {a b : ℝ}
    (ssf : SkewedStabilityFunction C σ.slicing a b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X B : σ.slicing.IntervalCat C a b} (q : X ⟶ B) : Prop where
  strictEpi : IsStrictEpi q
  nonzero : ¬IsZero B.obj
  semistable :
    ssf.Semistable C B.obj
      (wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α)
  minimal :
    ∀ {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B'), IsStrictEpi q' →
      ¬IsZero B'.obj →
      ssf.Semistable C B'.obj
        (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α ∧
        (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α =
            wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α →
          ∃ t : B ⟶ B', q' = q ≫ t)

/-- A semistable interval object is its own strict mdq. -/
theorem IsStrictMDQ.id_of_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X : σ.slicing.IntervalCat C a b}
    (hss : ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α)) :
    IsStrictMDQ (C := C) σ ssf (𝟙 X) where
  strictEpi := by
    simpa using (isStrictEpi_of_isIso (f := 𝟙 X))
  nonzero := hss.2.1
  semistable := hss
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    refine ⟨?_, ?_⟩
    · exact ssf.phase_le_of_strictQuotient_of_window
        (C := C) (σ := σ) (a := a) (b := b) hss hW_interval hWindow hWidth q' hq' hB'_nz
    · intro hEq
      exact ⟨q', (Category.id_comp q').symm⟩

/-- Precomposing a strict mdq with an isomorphism of sources preserves the strict mdq property. -/
theorem IsStrictMDQ.precomposeIso
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X X' B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q) (e : X' ≅ X) :
    IsStrictMDQ (C := C) σ ssf (e.hom ≫ q) where
  strictEpi :=
    Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) e.hom q
      (isStrictEpi_of_isIso (f := e.hom)) hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    let q'' : X ⟶ B' := e.inv ≫ q'
    have hq'' : IsStrictEpi q'' :=
      Slicing.IntervalCat.comp_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) e.inv q'
        (isStrictEpi_of_isIso (f := e.inv)) hq'
    refine ⟨(hq.minimal q'' hq'' hB'_nz hB'_ss).1, ?_⟩
    intro hEq
    obtain ⟨t, ht⟩ := (hq.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
    refine ⟨t, ?_⟩
    change q' = (e.hom ≫ q) ≫ t
    calc
      q' = e.hom ≫ (e.inv ≫ q') := by simp
      _ = e.hom ≫ (q ≫ t) := by simpa [q''] using congrArg (fun f : X ⟶ B' => e.hom ≫ f) ht
      _ = (e.hom ≫ q) ≫ t := by rw [Category.assoc]

/-- If `p` and `p ≫ q` are strict epimorphisms in a thin interval category, then `q` is a
strict epimorphism. This is detected in the left heart, where it reduces to the usual
epimorphism factor property in an abelian category. -/
theorem interval_strictEpi_of_strictEpi_comp
    (σ : StabilityCondition C) {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Q B : σ.slicing.IntervalCat C a b}
    (p : X ⟶ Q) (q : Q ⟶ B)
    (hpq : IsStrictEpi (p ≫ q)) :
    IsStrictEpi q := by
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := σ.slicing) a b (Fact.out : b - a ≤ 1)
  haveI : Epi (FL.map (p ≫ q)) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) (p ≫ q) hpq
  have hfac : FL.map p ≫ FL.map q = FL.map (p ≫ q) := by simp
  haveI : Epi (FL.map q) := epi_of_epi_fac hfac
  exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
    (C := C) (s := σ.slicing) (a := a) (b := b) q

/-- If a strict mdq factors through a strict epi `X ↠ Q`, then the induced quotient `Q ↠ B`
is again a strict mdq. -/
theorem IsStrictMDQ.of_strictEpi_factor
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Q B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q) {p : X ⟶ Q}
    (hp : IsStrictEpi p) {πQ : Q ⟶ B} (hfac : p ≫ πQ = q) :
    IsStrictMDQ (C := C) σ ssf πQ where
  strictEpi := by
    apply interval_strictEpi_of_strictEpi_comp (C := C) (σ := σ) (a := a) (b := b) p πQ
    simpa [hfac] using hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    have hcomp : IsStrictEpi (p ≫ q') :=
      Slicing.IntervalCat.comp_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) p q' hp hq'
    refine ⟨(hq.minimal (p ≫ q') hcomp hB'_nz hB'_ss).1, ?_⟩
    intro hEq
    obtain ⟨t, ht⟩ := (hq.minimal (p ≫ q') hcomp hB'_nz hB'_ss).2 hEq
    refine ⟨t, ?_⟩
    haveI : Epi p := hp.epi
    apply (cancel_epi p).1
    calc
      p ≫ q' = q ≫ t := ht
      _ = (p ≫ πQ) ≫ t := by simp [hfac]
      _ = p ≫ (πQ ≫ t) := by rw [Category.assoc]

/-- The phase of a strict mdq is bounded above by the phase of any nonzero strict quotient
of its source. -/
theorem IsStrictMDQ.phase_le_of_strictQuotient
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X B Q : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    (p : X ⟶ Q) (hp : IsStrictEpi p) (hQ : ¬IsZero Q.obj) :
    wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
      wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α := by
  obtain ⟨M, hM_ne_top, hM_strict, hM_ss, hM_phase⟩ :=
    ssf.exists_semistable_strictQuotient_le_phase_of_finiteLength
      (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
      (X := Q) (fun hZ => hQ (((σ.slicing.intervalProp C a b).ι).map_isZero hZ))
  have hcomp : IsStrictEpi (p ≫ cokernel.π M.arrow) :=
    Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) p (cokernel.π M.arrow) hp
      (isStrictEpi_cokernel M.arrow)
  have hcokM_obj_ne : ¬IsZero (cokernel M.arrow).obj := by
    intro hZ
    exact (interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne_top hM_strict)
      (Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  exact (hq.minimal (p ≫ cokernel.π M.arrow) hcomp
    hcokM_obj_ne
    hM_ss).1.trans hM_phase

/-- If a nonzero strict quotient of the source has the same phase as a strict mdq, then it is
already semistable. Otherwise a destabilizing semistable strict subobject would produce a
smaller-phase strict quotient, contradicting mdq minimality. -/
theorem IsStrictMDQ.isSemistable_of_strictQuotient_phase_eq
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X B Q : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    (p : X ⟶ Q) (hp : IsStrictEpi p) (hQ : ¬IsZero Q.obj)
    (hEq :
      wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α =
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α) :
    ssf.Semistable C Q.obj
      (wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α) := by
  letI : IsStrictArtinianObject Q := (hFiniteLength Q).1
  by_contra hQ_ns
  obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hA_ss, hA_phase_gt, _⟩ :=
    ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
      (C := C) (σ := σ) (a := a) (b := b) (X := Q)
      (fun hZ => hQ (((σ.slicing.intervalProp C a b).ι).map_isZero hZ))
      hQ_ns hW_interval
  have hcomp : IsStrictEpi (p ≫ cokernel.π A.arrow) :=
    Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) p (cokernel.π A.arrow) hp
      (isStrictEpi_cokernel A.arrow)
  have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
    intro hZ
    exact (interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hA_ne_top hA_strict)
      (Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hmin :
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α :=
    IsStrictMDQ.phase_le_of_strictQuotient
      (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
      hq (p ≫ cokernel.π A.arrow) hcomp hcokA_obj_ne
  have hlt :
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α := by
    calc
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α :=
        ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
          (C := C) (σ := σ) (a := a) (b := b)
          hA_ne_bot hA_ne_top hA_strict hA_phase_gt hW_interval hWindow hWidth
      _ = wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α := hEq
  exact (not_lt_of_ge hmin) hlt

/-- Equality of phase with a strict mdq forces factorization through that mdq. -/
theorem IsStrictMDQ.factor_of_phase_eq_of_strictQuotient
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X B Q : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    (p : X ⟶ Q) (hp : IsStrictEpi p) (hQ : ¬IsZero Q.obj)
    (hEq :
      wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α =
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α) :
    ∃ t : B ⟶ Q, p = q ≫ t := by
  have hQ_ss := IsStrictMDQ.isSemistable_of_strictQuotient_phase_eq
    (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
    hq p hp hQ hEq
  obtain ⟨t, ht⟩ := (hq.minimal p hp hQ hQ_ss).2 hEq
  exact ⟨t, ht⟩

/-- Recursive mdq step in a thin interval category: if `0 → A → X → X' → 0` is a strict short
exact sequence with `A` semistable of larger phase, then any strict mdq of `X'` pulls back to a
strict mdq of `X`, provided maps from higher-phase semistables to lower-phase semistables vanish.

This is the quasi-abelian analogue of the Proposition 2.4/Bridgeland 7.7b transport step. -/
theorem IsStrictMDQ.comp_of_destabilizing_semistable_subobject
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {U_hom : ℝ}
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (_hE : ssf.Semistable C E.obj
          (wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α))
        (_hF : ssf.Semistable C F.obj
          (wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α)),
        wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α →
        wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α < U_hom →
        ∀ f : E ⟶ F, f = 0)
    {X : σ.slicing.IntervalCat C a b} {A : Subobject X}
    (hA_ss :
      ssf.Semistable C (A : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α))
    (hA_strict : IsStrictMono A.arrow)
    (hA_phase :
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hA_top : A ≠ ⊤)
    (hA_phase_upper :
      wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α < U_hom)
    {B : σ.slicing.IntervalCat C a b} {q : cokernel A.arrow ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q) :
    IsStrictMDQ (C := C) σ ssf (cokernel.π A.arrow ≫ q) where
  strictEpi :=
    Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π A.arrow) q
      (isStrictEpi_cokernel A.arrow) hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
      intro hZ
      letI : Epi q := hq.strictEpi.epi
      have hzero : q = 0 := zero_of_source_iso_zero _ <|
        (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ).isoZero
      exact hq.nonzero (((σ.slicing.intervalProp C a b).ι).map_isZero
        (IsZero.of_epi_eq_zero q hzero))
    have hB_le_cok :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α :=
      IsStrictMDQ.phase_le_of_strictQuotient
        (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
        hq (𝟙 (cokernel A.arrow)) (isStrictEpi_of_isIso (f := 𝟙 _)) hcokA_obj_ne
    have hA_ne_bot : A ≠ ⊥ := by
      intro hA_bot
      exact hA_ss.2.1 (((σ.slicing.intervalProp C a b).ι).map_isZero
        ((intervalSubobject_isZero_iff_eq_bot
          (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) A).mpr hA_bot))
    have hCok_lt_A :
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
      lt_trans
        (ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
          (C := C) (σ := σ) (a := a) (b := b)
          hA_ne_bot hA_top hA_strict
          hA_phase hW_interval hWindow hWidth)
        hA_phase
    have hB_lt_A :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
      lt_of_le_of_lt hB_le_cok hCok_lt_A
    by_cases hle :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α
    · refine ⟨hle, ?_⟩
      intro hEq
      have hB'_lt_A :
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
            wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
        rw [hEq]
        exact hB_lt_A
      have hzero : A.arrow ≫ q' = 0 := hHom hA_ss hB'_ss hB'_lt_A hA_phase_upper (A.arrow ≫ q')
      let q'' : cokernel A.arrow ⟶ B' := cokernel.desc A.arrow q' hzero
      have hq'' : IsStrictEpi q'' := by
        apply interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) (cokernel.π A.arrow) q''
        simpa [q''] using hq'
      obtain ⟨t, ht⟩ := (hq.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
      refine ⟨t, ?_⟩
      calc
        q' = cokernel.π A.arrow ≫ q'' := by
          symm
          exact cokernel.π_desc A.arrow q' hzero
        _ = cokernel.π A.arrow ≫ (q ≫ t) := by rw [ht]
        _ = (cokernel.π A.arrow ≫ q) ≫ t := by rw [Category.assoc]
    · have hlt :
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
            wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α :=
        lt_of_not_ge hle
      have hB'_lt_A :
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
            wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
        lt_trans hlt hB_lt_A
      have hzero : A.arrow ≫ q' = 0 := hHom hA_ss hB'_ss hB'_lt_A hA_phase_upper (A.arrow ≫ q')
      let q'' : cokernel A.arrow ⟶ B' := cokernel.desc A.arrow q' hzero
      have hq'' : IsStrictEpi q'' := by
        apply interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) (cokernel.π A.arrow) q''
        simpa [q''] using hq'
      have hmin :
          wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α :=
        (hq.minimal q'' hq'' hB'_nz hB'_ss).1
      exact False.elim ((not_lt_of_ge hmin) hlt)

/-- Existence of strict maximally destabilizing quotients under the paper-faithful strict
finite-length hypothesis on the thin interval category. -/
theorem SkewedStabilityFunction.exists_strictMDQ_of_finiteLength
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {U_hom : ℝ}
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (_hE : ssf.Semistable C E.obj
          (wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α))
        (_hF : ssf.Semistable C F.obj
          (wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α)),
        wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α →
        wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α < U_hom →
        ∀ f : E ⟶ F, f = 0)
    (hDestabBound : ∀ {Y : σ.slicing.IntervalCat C a b} (_ : ¬IsZero Y)
      {A : Subobject Y}
      (_ : ssf.Semistable C (A : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α))
      (_ : IsStrictMono A.arrow)
      (_ : wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α),
      wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α < U_hom)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X) :
    ∃ (B : σ.slicing.IntervalCat C a b) (q : X ⟶ B), IsStrictMDQ (C := C) σ ssf q := by
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  suffices h :
      ∀ (S : StrictSubobject X), ¬IsZero (cokernel S.1.arrow) →
        ∃ (B : σ.slicing.IntervalCat C a b) (q : cokernel S.1.arrow ⟶ B),
          IsStrictMDQ (C := C) σ ssf q by
    let S0 : StrictSubobject X := ⟨⊥,
      intervalSubobject_bot_arrow_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b)⟩
    have hS0_ne : ¬IsZero (cokernel S0.1.arrow) := by
      let e0 : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
        rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      intro hZ
      exact hX (hZ.of_iso e0.symm)
    obtain ⟨B, q, hq⟩ := h S0 hS0_ne
    let e0 : cokernel S0.1.arrow ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    exact ⟨B, e0.inv ≫ q, IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b) hq e0.symm⟩
  intro S
  induction S using IsWellFounded.induction
      (· > · : StrictSubobject X → StrictSubobject X → Prop) with
  | ind S ih =>
      intro hQS_ne
      let QS : σ.slicing.IntervalCat C a b := cokernel S.1.arrow
      letI : IsStrictArtinianObject QS := (hFiniteLength QS).1
      letI : IsStrictNoetherianObject QS := (hFiniteLength QS).2
      let ψQS : ℝ := wPhaseOf (ssf.W (K₀.of C QS.obj)) ssf.α
      by_cases hQS_ss : ssf.Semistable C QS.obj ψQS
      · exact ⟨QS, 𝟙 _, IsStrictMDQ.id_of_semistable
          (C := C) (σ := σ) (a := a) (b := b) hW_interval hWindow hWidth hQS_ss⟩
      · obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hA_ss, hA_phase_gt, _⟩ :=
          ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
            (C := C) (σ := σ) (a := a) (b := b) (X := QS) hQS_ne hQS_ss hW_interval
        let Tsub : Subobject X := (Subobject.pullback (cokernel.π S.1.arrow)).obj A
        have hT_strict : IsStrictMono Tsub.arrow :=
          interval_pullback_arrow_strictMono_of_strictMono
            (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π S.1.arrow) A hA_strict
        let T : StrictSubobject X := ⟨Tsub, hT_strict⟩
        have hS_lt_T : S < T := by
          apply lt_of_lt_of_le
            (interval_lt_pullback_cokernel_of_ne_bot
              (C := C) (s := σ.slicing) (a := a) (b := b) (M := S.1) (B := A) hA_ne_bot)
          exact le_rfl
        have hQT_ne : ¬IsZero (cokernel Tsub.arrow) :=
          interval_cokernel_nonzero_of_ne_top
            (C := C) (s := σ.slicing) (a := a) (b := b)
            (interval_pullback_cokernel_ne_top_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hA_ne_top hA_strict)
            hT_strict
        obtain ⟨B, qT, hqT⟩ := ih T hS_lt_T hQT_ne
        let eT : cokernel Tsub.arrow ≅ cokernel A.arrow :=
          interval_cokernel_pullbackTopIso
            (C := C) (s := σ.slicing) (a := a) (b := b) S.1 hA_strict
        let qA : cokernel A.arrow ⟶ B := eT.inv ≫ qT
        have hqA : IsStrictMDQ (C := C) σ ssf qA :=
          IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b) hqT eT.symm
        exact ⟨B, cokernel.π A.arrow ≫ qA,
          IsStrictMDQ.comp_of_destabilizing_semistable_subobject
            (C := C) (σ := σ) (a := a) (b := b)
            hFiniteLength hW_interval hWindow hWidth hHom hA_ss hA_strict hA_phase_gt hA_ne_top
            (hDestabBound hQS_ne hA_ss hA_strict hA_phase_gt) hqA⟩

/-- The interval-theoretic kernel subobject of `q` is a limit kernel fork for `q`. -/
noncomputable def interval_kernelSubobject_isLimitKernelFork
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (q : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kernelSubobject q).arrow (kernelSubobject_arrow_comp (f := q))) := by
  refine KernelFork.IsLimit.ofι' (kernelSubobject q).arrow (kernelSubobject_arrow_comp (f := q))
    (fun {W} g hg ↦ ?_)
  let u : W ⟶ kernel q := kernel.lift q g hg
  refine ⟨u ≫ (kernelSubobjectIso q).inv, ?_⟩
  calc
    (u ≫ (kernelSubobjectIso q).inv) ≫ (kernelSubobject q).arrow
        = u ≫ kernel.ι q := by simp [Category.assoc]
    _ = g := kernel.lift_ι q g hg

/-- A strict epimorphism in the interval category gives a strict short exact sequence with its
kernel subobject. -/
theorem interval_strictShortExact_of_kernelSubobject_strictEpi
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (q : X ⟶ Y) (hq : IsStrictEpi q) :
    StrictShortExact
      (ShortComplex.mk (kernelSubobject q).arrow q (kernelSubobject_arrow_comp (f := q))) :=
  interval_strictShortExact_of_kernel_strictEpi
    (C := C) (s := s) (a := a) (b := b)
    (ShortComplex.mk (kernelSubobject q).arrow q (kernelSubobject_arrow_comp (f := q)))
    (interval_kernelSubobject_isLimitKernelFork (C := C) (s := s) (a := a) (b := b) q) hq

theorem Subobject.map_eq_mk {D : Type*} [Category D] {E : D}
    (K : Subobject E) (S : Subobject (K : D)) :
    (Subobject.map K.arrow).obj S = Subobject.mk (S.arrow ≫ K.arrow) := by
  calc
    (Subobject.map K.arrow).obj S = (Subobject.map K.arrow).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ K.arrow) := by
      simpa using (Subobject.map_mk S.arrow K.arrow)

/-- The subobject obtained by mapping `S ≤ K ≤ E` along `K.arrow` is canonically isomorphic to
`S` itself. -/
noncomputable def Subobject.mapSubIso {D : Type*} [Category D] {E : D}
    (K : Subobject E) (S : Subobject (K : D)) :
    ((Subobject.map K.arrow).obj S : D) ≅ (S : D) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ K.arrow) (Subobject.map_eq_mk K S)

theorem interval_kernelSubobject_ne_top_of_strictEpi_nonzero
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} {q : X ⟶ Y} (hq : IsStrictEpi q) (hY : ¬IsZero Y.obj) :
    kernelSubobject q ≠ ⊤ := by
  intro hK
  haveI : Epi q := hq.epi
  haveI : IsIso (kernelSubobject q).arrow := (Subobject.isIso_iff_mk_eq_top _).2
    (by simpa [Subobject.mk_arrow] using hK)
  have hzero : q = 0 := by
    apply (cancel_epi ((kernelSubobject q).arrow)).1
    simp [kernelSubobject_arrow_comp (f := q)]
  have hY_zero : IsZero Y := IsZero.of_epi_eq_zero q hzero
  exact hY (((s.intervalProp C a b).ι).map_isZero hY_zero)

/-- Lemma 3.4 in the quotient form needed for Bridgeland's class `G`: a nonzero strict
quotient of an object from the inner strip `P((a + 2ε₀, b - 4ε₀))`, taken inside the
thin category `P((a, b))`, has `W`-phase strictly bigger than `a + ε₀`. -/
theorem wPhaseOf_gt_of_strictQuotient_of_inner_strip
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {X B : σ.slicing.IntervalCat C a b}
    (hX_inner : σ.slicing.intervalProp C (a + 2 * ε₀) (b - 4 * ε₀) X.obj)
    (q : X ⟶ B) (hq : IsStrictEpi q) (hBne : ¬IsZero B.obj) :
    a + ε₀ < wPhaseOf (W (K₀.of C B.obj)) ((a + b) / 2) := by
  have hXne : ¬IsZero X.obj := by
    intro hXZ
    have hXI : IsZero X :=
      Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hXZ
    letI : Epi q := hq.epi
    have hq0 : q = 0 := zero_of_source_iso_zero _ hXI.isoZero
    exact hBne (((σ.slicing.intervalProp C a b).ι).map_isZero (IsZero.of_epi_eq_zero q hq0))
  have hinner_lo := σ.slicing.phiMinus_gt_of_intervalProp C hXne hX_inner
  have hinner_hi := σ.slicing.phiPlus_lt_of_intervalProp C hXne hX_inner
  have hab_inner : a + 2 * ε₀ < b - 4 * ε₀ := by
    have hmono := σ.slicing.phiMinus_le_phiPlus C (E := X.obj) hXne
    linarith
  let K : σ.slicing.IntervalCat C a b := kernelSubobject q
  have hK_gt : σ.slicing.gtProp C a K.obj :=
    σ.slicing.gtProp_of_intervalProp C K.property
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := σ.slicing) (a := a) (b := b)
      (interval_strictShortExact_of_kernelSubobject_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) q hq)
  have hBminus :
      a + 2 * ε₀ < σ.slicing.phiMinus C B.obj hBne := by
    refine σ.slicing.phiMinus_gt_of_triangle_with_gtProp C (hQ := hBne)
      (a := a + 2 * ε₀)
      (hE_gt := fun _ ↦ σ.slicing.phiMinus_gt_of_intervalProp C hXne hX_inner)
      (c := a) (hK_gt := hK_gt) ?_ hT
    linarith
  have hBge : σ.slicing.geProp C (a + 2 * ε₀) B.obj :=
    σ.slicing.geProp_of_phiMinus_ge C hBne (le_of_lt hBminus)
  have hBge' : σ.slicing.geProp C ((a + ε₀) + ε₀) B.obj := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hBge
  exact wPhaseOf_gt_of_geProp_target
    (C := C) (σ := σ) (W := W) (hW := hW) (a := a) (b := b) (ψ := a + ε₀) (ε₀ := ε₀)
    (E := B.obj)
    (hI := B.property) (hEne := hBne) (hGe := hBge') hε₀ hε₀2
    (by linarith) (by linarith) hthin hsin

theorem IsStrictMDQ.kernelSubobject_ne_bot_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α)) :
    kernelSubobject q ≠ ⊥ := by
  intro hK
  have hker_zero : IsZero (kernelSubobject q : σ.slicing.IntervalCat C a b) :=
    (intervalSubobject_isZero_iff_eq_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) (kernelSubobject q)).mpr hK
  have hzero : (kernelSubobject q).arrow = 0 := hker_zero.eq_of_src _ _
  haveI : Mono q := Preadditive.mono_of_kernel_zero <|
    zero_of_source_iso_zero _ (hker_zero.of_iso (kernelSubobjectIso q).symm).isoZero
  haveI : IsIso q := IsStrictEpi.isIso hq.strictEpi
  have eX : X.obj ≅ B.obj := ((σ.slicing.intervalProp C a b).ι).mapIso (asIso q)
  have hssX : ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α) := by
    have hphase :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α =
          wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
      simpa using congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eX).symm
    exact hphase ▸
      (ssf.semistable_of_iso
        (C := C) (s := σ.slicing) (a := a) (b := b) eX.symm hq.semistable)
  exact hns hssX

theorem IsStrictMDQ.phase_lt_of_strictQuotient_of_kernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    {A : Subobject (kernelSubobject q : σ.slicing.IntervalCat C a b)}
    (hA_top : A ≠ ⊤) (hA_strict : IsStrictMono A.arrow) :
    wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
  let M : Subobject X := kernelSubobject q
  have hM_strict : IsStrictMono M.arrow := by
    simpa [M] using intervalSubobject_arrow_strictMono_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) (kernel.ι q) (isStrictMono_kernel q)
  let liftA : Subobject X := intervalLiftSub (C := C) (X := X) M A
  have hLift_strict : IsStrictMono liftA.arrow := by
    simpa [liftA, M] using
      intervalLiftSub_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) (M := M) hM_strict (A := A) hA_strict
  have hLift_lt : liftA < M := by
    simpa [liftA, M] using intervalLiftSub_lt (C := C) (X := X) M hA_top
  have hLift_ne_top : liftA ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hLift_lt le_top)
  have hcokLift_ne : ¬IsZero (cokernel liftA.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hLift_ne_top hLift_strict
  have hcokLift_obj_ne : ¬IsZero (cokernel liftA.arrow).obj := by
    intro hZ
    exact hcokLift_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hLift_phase_ge :
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α :=
    IsStrictMDQ.phase_le_of_strictQuotient
      (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
      hq (cokernel.π liftA.arrow) (isStrictEpi_cokernel liftA.arrow) hcokLift_obj_ne
  have hMp_nonzero : M.arrow ≫ cokernel.π liftA.arrow ≠ 0 := by
    intro hzero
    have hKer : IsLimit (KernelFork.ofι liftA.arrow (cokernel.condition liftA.arrow)) :=
      interval_fIsKernel_of_strictShortExact
        (C := C) (s := σ.slicing) (a := a) (b := b)
        (interval_strictShortExact_cokernel_of_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) liftA.arrow hLift_strict)
    let u : (M : σ.slicing.IntervalCat C a b) ⟶ (liftA : σ.slicing.IntervalCat C a b) :=
      hKer.lift (KernelFork.ofι M.arrow hzero)
    have hu : u ≫ liftA.arrow = M.arrow := hKer.fac _ Limits.WalkingParallelPair.zero
    have hM_le_lift : M ≤ liftA := Subobject.le_of_comm u hu
    exact (not_le_of_gt hLift_lt) hM_le_lift
  have hLift_phase_gt :
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α := by
    refine lt_of_le_of_ne hLift_phase_ge ?_
    intro hEq
    obtain ⟨t, ht⟩ := IsStrictMDQ.factor_of_phase_eq_of_strictQuotient
      (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
      hq (cokernel.π liftA.arrow) (isStrictEpi_cokernel liftA.arrow) hcokLift_obj_ne hEq.symm
    apply hMp_nonzero
    calc
      M.arrow ≫ cokernel.π liftA.arrow = M.arrow ≫ (q ≫ t) := by rw [ht]
      _ = (M.arrow ≫ q) ≫ t := by simp [Category.assoc]
      _ = 0 := by simp [M]
  have hcokM_ne : ¬IsZero (cokernel M.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b)
      (interval_kernelSubobject_ne_top_of_strictEpi_nonzero
        (C := C) (s := σ.slicing) (a := a) (b := b) hq.strictEpi hq.nonzero) hM_strict
  have hcokM_obj_ne : ¬IsZero (cokernel M.arrow).obj := by
    intro hZ
    exact hcokM_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hcokA_ne : ¬IsZero (cokernel A.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict
  have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
    intro hZ
    exact hcokA_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hB_window :
      L < wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α < U := hWindow B.property hq.nonzero
  have hLift_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α < U :=
    hWindow (cokernel liftA.arrow).property hcokLift_obj_ne
  have hA_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α < U :=
    hWindow (cokernel A.arrow).property hcokA_obj_ne
  have hUpper : U <
      wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α + 1 := by
    linarith [hLift_window.1]
  have hLower :
      wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α - 1 < L := by
    linarith [hLift_window.2]
  have hB_range :
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ∈
        Set.Ioo
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α - 1)
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α + 1) := by
    constructor <;> linarith
  have hA_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∈
        Set.Ioo
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α - 1)
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α + 1) := by
    constructor <;> linarith
  have hB_Wne : ssf.W (K₀.of C B.obj) ≠ 0 :=
    hW_interval B.property hq.nonzero
  have hsumX :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C B.obj) := by
    simpa [map_add] using
      ssf.strict_additive
        (C := C) (s := σ.slicing) (a := a) (b := b)
        (interval_strictShortExact_of_kernelSubobject_strictEpi
          (C := C) (s := σ.slicing) (a := a) (b := b) q hq.strictEpi)
  have hsumC :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [map_add] using
      ssf.strict_additive
        (C := C) (s := σ.slicing) (a := a) (b := b)
        (interval_strictShortExact_cokernel_of_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) M.arrow hM_strict)
  have hWB_eq :
      ssf.W (K₀.of C B.obj) = ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    apply add_left_cancel (a := ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj))
    exact hsumX.symm.trans hsumC
  have hM_Wne : ssf.W (K₀.of C (cokernel M.arrow).obj) ≠ 0 := by
    intro hzero
    exact hB_Wne (hWB_eq.trans hzero)
  let ψM : ℝ := wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α
  have hM_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ∈
        Set.Ioo
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α - 1)
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α + 1) := by
    simpa [hWB_eq] using hB_range
  have hLift_phase_gt_M :
      ψM < wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α := by
    dsimp [ψM]
    rw [← hWB_eq]
    exact hLift_phase_gt
  have hsum :
      ssf.W (K₀.of C (cokernel liftA.arrow).obj) =
        ssf.W (K₀.of C (cokernel A.arrow).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [liftA, M] using
      ssf.Wobj_liftSub_cokernel_eq_add
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict hA_strict
  have hA_phase_gt_lift :
      wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α :=
    wPhaseOf_seesaw_strict hsum.symm rfl hLift_phase_gt_M hM_Wne hM_range hA_range
  exact lt_trans hLift_phase_gt hA_phase_gt_lift

end CategoryTheory.Triangulated
