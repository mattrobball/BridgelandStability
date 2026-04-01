/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel

/-!
# Deformation of Stability Conditions — Lemma77

Paper-facing HN existence and Postnikov extension closure (Lemma 7.7)
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

section

variable [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/- The faithful 7.7 recursion with the paper's `G/H`-style input exposed explicitly:
for a fixed interval object `X`, it is enough to know a lower phase bound for all
proper strict quotients of `X`; the recursive kernel step propagates that bound to
smaller strict subobjects. The older `hn_exists_in_thin_interval` theorem is recovered
by feeding in the global lower window bound. -/
theorem SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound
    (σ : StabilityCondition.WithClassMap C v) {a b : ℝ}
    {ssf : SkewedStabilityFunction C v σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.wNe F)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < ssf.wPhase F ∧
        ssf.wPhase F < U)
    (hWidth : U - L < 1)
    {U_hom : ℝ}
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (_hE : ssf.Semistable C E.obj
          (ssf.wPhase E.obj))
        (_hF : ssf.Semistable C F.obj
          (ssf.wPhase F.obj)),
        ssf.wPhase F.obj <
          ssf.wPhase E.obj →
        ssf.wPhase E.obj < U_hom →
        ∀ f : E ⟶ F, f = 0)
    (hDestabBound : ∀ {Y : σ.slicing.IntervalCat C a b} (_ : ¬IsZero Y)
      {A : Subobject Y}
      (_ : ssf.Semistable C (A : σ.slicing.IntervalCat C a b).obj
        (ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj))
      (_ : IsStrictMono A.arrow)
      (_ : ssf.wPhase Y.obj <
        ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj),
      ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj < U_hom)
    (t : ℝ)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X) :
    (∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
      t < ssf.wPhase (cokernel A.arrow).obj) →
    let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, t < G.φ j ∧ G.φ j < U := by
  intro hquot
  let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
  letI : IsStrictArtinianObject X := (hFiniteLength X).1
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  let S0 : StrictSubobject X := ⟨⊤, isStrictMono_of_isIso⟩
  let Psub : StrictSubobject X → Prop := fun S =>
      ¬IsZero (S.1 : σ.slicing.IntervalCat C a b) →
        ∀ t : ℝ,
          (∀ A : Subobject (S.1 : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
            IsStrictMono A.arrow →
            t < ssf.wPhase (cokernel A.arrow).obj) →
          ∃ G : HNFiltration C Psem (S.1 : σ.slicing.IntervalCat C a b).obj,
            ∀ j, t < G.φ j ∧ G.φ j < U
  have h :
      ∀ S : StrictSubobject X, Psub S := by
    intro S
    refine (show WellFounded ((· < ·) : StrictSubobject X → StrictSubobject X → Prop) from
      wellFounded_lt).induction S ?_
    intro S ih hS t hquot
    let Y : σ.slicing.IntervalCat C a b := S.1
    have hS_obj : ¬IsZero Y.obj := fun hZ =>
      hS (Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    let ψY : ℝ := ssf.wPhase Y.obj
    by_cases hss : ssf.Semistable C Y.obj ψY
    · let Gsingle : HNFiltration C Psem Y.obj := HNFiltration.single C Y.obj ψY hss
      refine ⟨Gsingle, ?_⟩
      intro j
      have hbot_ne_top : (⊥ : Subobject Y) ≠ ⊤ := fun hEq =>
        (intervalSubobject_top_ne_bot_of_not_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hS) hEq.symm
      have hbot_strict : IsStrictMono ((⊥ : Subobject Y).arrow) :=
        intervalSubobject_bot_arrow_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b)
      have hbot_gt :
          t < ssf.wPhase (cokernel ((⊥ : Subobject Y).arrow)).obj :=
        hquot ⊥ hbot_ne_top hbot_strict
      have hbot_eq :
          ssf.wPhase (cokernel ((⊥ : Subobject Y).arrow)).obj = ψY := by
        let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
          rw [show ((⊥ : Subobject Y).arrow) = 0 by simp [Subobject.bot_arrow]]
          exact cokernelZeroIsoTarget
        let eC : (cokernel ((⊥ : Subobject Y).arrow)).obj ≅ Y.obj :=
          (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
        simp only [ψY]; exact ssf.wPhase_iso eC
      have hψY_hi : ψY < U := (hWindow Y.property hS_obj).2
      have hsingle_n : Gsingle.n = 1 := by
        simp [Gsingle, HNFiltration.single]
      have hj_lt : j.val < 1 := hsingle_n ▸ j.is_lt
      have hj0 : j.val = 0 := by lia
      have hj : j = ⟨0, by simp [Gsingle, HNFiltration.single]⟩ :=
        Fin.ext hj0
      subst j
      have hψY_gt : t < ψY := by
        exact hbot_eq ▸ hbot_gt
      exact ⟨by simpa [Gsingle, HNFiltration.single] using hψY_gt, hψY_hi⟩
    · letI : IsStrictArtinianObject Y := (hFiniteLength Y).1
      letI : IsStrictNoetherianObject Y := (hFiniteLength Y).2
      obtain ⟨B, q, hq⟩ := ssf.exists_strictMDQ_of_finiteLength
        (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth hHom
        hDestabBound (X := Y) hS
      let K : Subobject Y := kernelSubobject q
      have hK_ne_bot : K ≠ ⊥ :=
        IsStrictMDQ.kernelSubobject_ne_bot_of_not_semistable
          (C := C) (σ := σ) (a := a) (b := b) hq hss
      have hK_ne_top : K ≠ ⊤ :=
        interval_kernelSubobject_ne_top_of_strictEpi_nonzero
          (C := C) (s := σ.slicing) (a := a) (b := b) hq.strictEpi hq.nonzero
      have hK_strict : IsStrictMono K.arrow := by
        simpa [K] using
          (intervalSubobject_arrow_strictMono_of_strictMono
            (C := C) (s := σ.slicing) (a := a) (b := b) (kernel.ι q) (isStrictMono_kernel q))
      let T : Subobject X := intervalLiftSub (C := C) (X := X) S.1 K
      have hT_ne_bot : T ≠ ⊥ :=
        intervalLiftSub_ne_bot (C := C) (X := X) S.1 hK_ne_bot
      have hT_strict : IsStrictMono T.arrow :=
        intervalLiftSub_arrow_strictMono_of_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) S.2 hK_strict
      let Tstr : StrictSubobject X := ⟨T, hT_strict⟩
      have hT_lt : Tstr < S := by
        simpa [Tstr, T] using
          (intervalLiftSub_lt (C := C) (X := X) S.1 hK_ne_top)
      have hT_ne : ¬IsZero (T : σ.slicing.IntervalCat C a b) :=
        intervalSubobject_not_isZero_of_ne_bot
          (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hT_ne_bot
      let ψB : ℝ := ssf.wPhase B.obj
      have hψB_gt : t < ψB := by
        have hgtK :
            t < ssf.wPhase (cokernel K.arrow).obj :=
          hquot K hK_ne_top hK_strict
        simpa [ψB] using hgtK.trans_eq
          (wPhaseOf_cokernel_kernelSubobject_eq
            (C := C) (s := σ.slicing) (a := a) (b := b) (ssf := ssf) q hq.strictEpi)
      have hψB_hi : ψB < U := by
        simpa [ψB] using (hWindow B.property hq.nonzero).2
      have hquot_T :
          ∀ A : Subobject (T : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
            IsStrictMono A.arrow →
            ψB < ssf.wPhase (cokernel A.arrow).obj := by
        intro A hA_top hA_strict
        let eK : (T : σ.slicing.IntervalCat C a b) ≅ (K : σ.slicing.IntervalCat C a b) := by
          dsimp [T, intervalLiftSub]
          exact Subobject.isoOfEqMk _ (K.arrow ≫ S.1.arrow) rfl
        let A' : Subobject (K : σ.slicing.IntervalCat C a b) := (Subobject.map eK.hom).obj A
        have hA'_top : A' ≠ ⊤ := by
          intro hA'
          apply hA_top
          apply (Subobject.map_obj_injective eK.hom)
          calc
            (Subobject.map eK.hom).obj A = A' := by rfl
            _ = ⊤ := hA'
            _ = (Subobject.map eK.hom).obj (⊤ : Subobject (T : σ.slicing.IntervalCat C a b)) := by
              rw [Subobject.map_top, Subobject.mk_eq_top_of_isIso eK.hom]
        have hA'_strict : IsStrictMono A'.arrow := by
          have hcomp : IsStrictMono (A.arrow ≫ eK.hom) :=
            Slicing.IntervalCat.comp_strictMono
              (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow eK.hom
              hA_strict isStrictMono_of_isIso
          have hEq : A' = Subobject.mk (A.arrow ≫ eK.hom) := by
            simpa [A'] using (Subobject.map_eq_mk_mono eK.hom A)
          rw [hEq]
          simpa using
            (intervalSubobject_arrow_strictMono_of_strictMono
              (C := C) (s := σ.slicing) (a := a) (b := b) (A.arrow ≫ eK.hom) hcomp)
        have hphase_A :
            ssf.wPhase (cokernel A.arrow).obj =
              ssf.wPhase (cokernel A'.arrow).obj := by
          let eA : (A : σ.slicing.IntervalCat C a b) ≅ (A' : σ.slicing.IntervalCat C a b) :=
            (Subobject.mapMonoIso eK.hom A).symm
          have hw : A.arrow ≫ eK.hom = eA.hom ≫ A'.arrow := by
            simp [eA, A', Subobject.mapMonoIso]
          let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
            cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA eK hw
          let eC' :=
            (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC
          exact ssf.wPhase_iso eC'
        have hgtA' :
            ψB < ssf.wPhase (cokernel A'.arrow).obj := by
          simpa [ψB] using
            (IsStrictMDQ.phase_lt_of_strictQuotient_of_kernel
              (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
              hq (A := A') hA'_top hA'_strict)
        rw [hphase_A]
        exact hgtA'
      obtain ⟨GT, hGT⟩ := ih Tstr hT_lt hT_ne ψB hquot_T
      let eK : (T : σ.slicing.IntervalCat C a b) ≅ (K : σ.slicing.IntervalCat C a b) := by
        dsimp [T, intervalLiftSub]
        exact Subobject.isoOfEqMk _ (K.arrow ≫ S.1.arrow) rfl
      let GK : HNFiltration C Psem (K : σ.slicing.IntervalCat C a b).obj :=
        GT.ofIso C ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eK)
      have hGK : ∀ j, ψB < GK.φ j ∧ GK.φ j < U := by
        simpa [GK] using hGT
      let SQ : ShortComplex (σ.slicing.IntervalCat C a b) :=
        ShortComplex.mk K.arrow q (kernelSubobject_arrow_comp (f := q))
      have hSQ : StrictShortExact SQ :=
        interval_strictShortExact_of_kernelSubobject_strictEpi
          (C := C) (s := σ.slicing) (a := a) (b := b) q hq.strictEpi
      let H : HNFiltration C Psem Y.obj :=
        HNFiltration.appendStrictFactor (C := C) (s := σ.slicing) (a := a) (b := b)
          (P := Psem) (S := SQ) GK hSQ ψB hq.semistable (fun j ↦ (hGK j).1)
      refine ⟨H, ?_⟩
      intro j
      by_cases hj : j.val < GK.n
      · have hGj := hGK ⟨j.val, hj⟩
        have hGj' : t < GK.φ ⟨j.val, hj⟩ ∧ GK.φ ⟨j.val, hj⟩ < U :=
          ⟨lt_trans hψB_gt hGj.1, hGj.2⟩
        simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hj] using hGj'
      · have hj_lt : j.val < GK.n + 1 := by
          simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor] using j.is_lt
        have hjEq : j.val = GK.n := by lia
        have hG_last : GK.n < H.n := by
          simp [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor]
        have hjLast : j = ⟨GK.n, hG_last⟩ := Fin.ext hjEq
        subst j
        have hjFalse : ¬GK.n < GK.n := lt_irrefl _
        simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hjFalse,
          ψB] using ⟨hψB_gt, hψB_hi⟩
  have hS0_ne : ¬IsZero (S0.1 : σ.slicing.IntervalCat C a b) := by
    intro hZ
    let e0 : (S0.1 : σ.slicing.IntervalCat C a b) ≅ X :=
      asIso S0.1.arrow
    exact hX (hZ.of_iso e0.symm)
  have hS0_quot :
      ∀ A : Subobject (S0.1 : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
        IsStrictMono A.arrow →
        t < ssf.wPhase (cokernel A.arrow).obj := by
    intro A hA_top hA_strict
    let e0 : (S0.1 : σ.slicing.IntervalCat C a b) ≅ X :=
      asIso S0.1.arrow
    let A' : Subobject X := (Subobject.map e0.hom).obj A
    have hA'_top : A' ≠ ⊤ := by
      intro hA'
      apply hA_top
      apply (Subobject.map_obj_injective e0.hom)
      calc
        (Subobject.map e0.hom).obj A = A' := by rfl
        _ = ⊤ := hA'
        _ = (Subobject.map e0.hom).obj (⊤ : Subobject (S0.1 : σ.slicing.IntervalCat C a b)) := by
          rw [Subobject.map_top, Subobject.mk_eq_top_of_isIso e0.hom]
    have hA'_strict : IsStrictMono A'.arrow := by
      have hcomp : IsStrictMono (A.arrow ≫ e0.hom) :=
        Slicing.IntervalCat.comp_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow e0.hom
          hA_strict isStrictMono_of_isIso
      have hEq : A' = Subobject.mk (A.arrow ≫ e0.hom) := by
        simpa [A'] using (Subobject.map_eq_mk_mono e0.hom A)
      rw [hEq]
      simpa using
        (intervalSubobject_arrow_strictMono_of_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) (A.arrow ≫ e0.hom) hcomp)
    have hphase_A :
        ssf.wPhase (cokernel A.arrow).obj =
          ssf.wPhase (cokernel A'.arrow).obj := by
      let eA : (A : σ.slicing.IntervalCat C a b) ≅ (A' : σ.slicing.IntervalCat C a b) :=
        (Subobject.mapMonoIso e0.hom A).symm
      have hw : A.arrow ≫ e0.hom = eA.hom ≫ A'.arrow := by
        simp [eA, A', Subobject.mapMonoIso]
      let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
        cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA e0 hw
      let eC' :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC
      exact ssf.wPhase_iso eC'
    rw [hphase_A]
    exact hquot A' hA'_top hA'_strict
  obtain ⟨G0, hG0⟩ := h S0 hS0_ne t hS0_quot
  let eTop : (S0.1 : σ.slicing.IntervalCat C a b).obj ≅ X.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso (asIso S0.1.arrow)
  refine ⟨G0.ofIso C eTop, ?_⟩
  intro j
  simpa using hG0 j

theorem SkewedStabilityFunction.hn_exists_in_thin_interval
    (σ : StabilityCondition.WithClassMap C v) {a b : ℝ}
    {ssf : SkewedStabilityFunction C v σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.wNe F)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < ssf.wPhase F ∧
        ssf.wPhase F < U)
    (hWidth : U - L < 1)
    {U_hom : ℝ}
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (_hE : ssf.Semistable C E.obj
          (ssf.wPhase E.obj))
        (_hF : ssf.Semistable C F.obj
          (ssf.wPhase F.obj)),
        ssf.wPhase F.obj <
          ssf.wPhase E.obj →
        ssf.wPhase E.obj < U_hom →
        ∀ f : E ⟶ F, f = 0)
    (hDestabBound : ∀ {Y : σ.slicing.IntervalCat C a b} (_ : ¬IsZero Y)
      {A : Subobject Y}
      (_ : ssf.Semistable C (A : σ.slicing.IntervalCat C a b).obj
        (ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj))
      (_ : IsStrictMono A.arrow)
      (_ : ssf.wPhase Y.obj <
        ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj),
      ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj < U_hom)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X) :
    let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, L < G.φ j ∧ G.φ j < U := by
  have hL :
      ∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
        L < ssf.wPhase (cokernel A.arrow).obj := by
    intro A hA_top hA_strict
    have hcokA_ne : ¬IsZero (cokernel A.arrow).obj := fun hZ =>
      (interval_cokernel_nonzero_of_ne_top
        (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict)
        (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    exact (hWindow (cokernel A.arrow).property hcokA_ne).1
  exact
    SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound
      (C := C) (σ := σ) (a := a) (b := b) (ssf := ssf)
      hFiniteLength hW_interval hWindow hWidth hHom hDestabBound L X hX hL

/- Quotient-form wrapper for the faithful 7.7 recursion. This is the interface closest
to Bridgeland's classes `G` and `H`: the lower phase bound is stated directly for
nonzero strict quotients `X ↠ B`, and converted internally to the kernel/cokernel
subobject language used by the recursion. -/
theorem SkewedStabilityFunction.hn_exists_in_thin_interval_of_strictQuotientLowerBound
    (σ : StabilityCondition.WithClassMap C v) {a b : ℝ}
    {ssf : SkewedStabilityFunction C v σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.wNe F)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < ssf.wPhase F ∧
        ssf.wPhase F < U)
    (hWidth : U - L < 1)
    {U_hom : ℝ}
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (_hE : ssf.Semistable C E.obj
          (ssf.wPhase E.obj))
        (_hF : ssf.Semistable C F.obj
          (ssf.wPhase F.obj)),
        ssf.wPhase F.obj <
          ssf.wPhase E.obj →
        ssf.wPhase E.obj < U_hom →
        ∀ f : E ⟶ F, f = 0)
    (hDestabBound : ∀ {Y : σ.slicing.IntervalCat C a b} (_ : ¬IsZero Y)
      {A : Subobject Y}
      (_ : ssf.Semistable C (A : σ.slicing.IntervalCat C a b).obj
        (ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj))
      (_ : IsStrictMono A.arrow)
      (_ : ssf.wPhase Y.obj <
        ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj),
      ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj < U_hom)
    (t : ℝ)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X)
    (hquot :
      ∀ {B : σ.slicing.IntervalCat C a b} (q : X ⟶ B), IsStrictEpi q → ¬IsZero B.obj →
        t < ssf.wPhase B.obj) :
    let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, t < G.φ j ∧ G.φ j < U := by
  have hquot' :
      ∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
        t < ssf.wPhase (cokernel A.arrow).obj := by
    intro A hA_top hA_strict
    have hcokA_ne : ¬IsZero (cokernel A.arrow).obj := fun hZ =>
      (interval_cokernel_nonzero_of_ne_top
        (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict)
        (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    exact hquot (cokernel.π A.arrow) (isStrictEpi_cokernel A.arrow) hcokA_ne
  exact
    SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound
      (C := C) (σ := σ) (a := a) (b := b) (ssf := ssf)
      hFiniteLength hW_interval hWindow hWidth hHom hDestabBound t X hX hquot'

end

/-! ### Extension-closure of `intervalProp` over Postnikov towers -/

/-- All intermediate chain objects of a PostnikovTower satisfy `intervalProp` when
all factors do. This is the induction underlying `intervalProp_of_postnikovTower`,
extracted so that it can be applied to intermediate chain objects (e.g., for
Lemma 3.4 arguments on PostnikovTower triangles). -/
lemma intervalProp_chain_of_postnikovTower (s : Slicing C) {E : C} {a b : ℝ}
    (P : PostnikovTower C E)
    (hfactors : ∀ i, s.intervalProp C a b (P.factor i))
    (k : ℕ) (hk : k ≤ P.n) :
    s.intervalProp C a b (P.chain.obj' k (by lia)) := by
  induction k with
  | zero =>
    rw [show P.chain.obj' 0 (by lia) = P.chain.left from rfl]
    exact Or.inl P.base_isZero
  | succ k ih =>
    set T := P.triangle ⟨k, by lia⟩
    have hT := P.triangle_dist ⟨k, by lia⟩
    have e₁ := Classical.choice (P.triangle_obj₁ ⟨k, by lia⟩)
    have e₂ := Classical.choice (P.triangle_obj₂ ⟨k, by lia⟩)
    have h₁ : s.intervalProp C a b T.obj₁ := by
      rcases ih (by lia) with hZ | ⟨F, hF⟩
      · exact Or.inl ((Iso.isZero_iff e₁.symm).mp hZ)
      · exact Or.inr ⟨F.ofIso C e₁.symm, hF⟩
    have h₃ : s.intervalProp C a b T.obj₃ := hfactors ⟨k, by lia⟩
    have h₂ : s.intervalProp C a b T.obj₂ :=
      s.intervalProp_of_triangle C h₁ h₃ hT
    rcases h₂ with hZ | ⟨F, hF⟩
    · exact Or.inl ((Iso.isZero_iff e₂).mp hZ)
    · exact Or.inr ⟨F.ofIso C e₂, hF⟩

/-- Extension-closure of `intervalProp` over Postnikov towers: if all factors of a
Postnikov tower have HN phases in `(a, b)`, then the total object does too.

This follows by induction on the tower length, applying `intervalProp_of_triangle`
at each step. -/
lemma intervalProp_of_postnikovTower (s : Slicing C) {E : C} {a b : ℝ}
    (P : PostnikovTower C E)
    (hfactors : ∀ i, s.intervalProp C a b (P.factor i)) :
    s.intervalProp C a b E := by
  suffices h : ∀ k (hk : k ≤ P.n),
      s.intervalProp C a b (P.chain.obj' k (by lia)) by
    have hchain := h P.n le_rfl
    rw [show P.chain.obj' P.n (by lia) = P.chain.right from rfl] at hchain
    rcases hchain with hZ | ⟨F, hF⟩
    · exact Or.inl ((Iso.isZero_iff (Classical.choice P.top_iso)).mp hZ)
    · exact Or.inr ⟨F.ofIso C (Classical.choice P.top_iso), hF⟩
  exact fun k hk => intervalProp_chain_of_postnikovTower C s P hfactors k hk

/-- Extension-closure of `gtProp` over Postnikov towers. -/
lemma gtProp_of_postnikovTower (s : Slicing C) {E : C} {t : ℝ}
    (P : PostnikovTower C E)
    (hfactors : ∀ i, s.gtProp C t (P.factor i)) :
    s.gtProp C t E := by
  suffices h : ∀ k (hk : k ≤ P.n),
      s.gtProp C t (P.chain.obj' k (by lia)) by
    have hchain := h P.n le_rfl
    rw [show P.chain.obj' P.n (by lia) = P.chain.right from rfl] at hchain
    exact (s.gtProp C t).prop_of_iso (Classical.choice P.top_iso) hchain
  intro k
  induction k with
  | zero =>
      intro _
      rw [show P.chain.obj' 0 (by lia) = P.chain.left from rfl]
      exact Or.inl P.base_isZero
  | succ k ih =>
      intro hk
      have hchain_k := ih (by lia)
      set T := P.triangle ⟨k, by lia⟩
      have hT := P.triangle_dist ⟨k, by lia⟩
      have e₁ := Classical.choice (P.triangle_obj₁ ⟨k, by lia⟩)
      have e₂ := Classical.choice (P.triangle_obj₂ ⟨k, by lia⟩)
      have h₁ : s.gtProp C t T.obj₁ := (s.gtProp C t).prop_of_iso e₁.symm hchain_k
      have h₃ : s.gtProp C t T.obj₃ := hfactors ⟨k, by lia⟩
      have h₂ : s.gtProp C t T.obj₂ := s.gtProp_of_triangle C t h₁ h₃ hT
      exact (s.gtProp C t).prop_of_iso e₂ h₂

/-- Extension-closure of `ltProp` over Postnikov towers. -/
lemma ltProp_of_postnikovTower (s : Slicing C) {E : C} {t : ℝ}
    (P : PostnikovTower C E)
    (hfactors : ∀ i, s.ltProp C t (P.factor i)) :
    s.ltProp C t E := by
  suffices h : ∀ k (hk : k ≤ P.n),
      s.ltProp C t (P.chain.obj' k (by lia)) by
    have hchain := h P.n le_rfl
    rw [show P.chain.obj' P.n (by lia) = P.chain.right from rfl] at hchain
    exact (s.ltProp C t).prop_of_iso (Classical.choice P.top_iso) hchain
  intro k
  induction k with
  | zero =>
      intro _
      rw [show P.chain.obj' 0 (by lia) = P.chain.left from rfl]
      exact Or.inl P.base_isZero
  | succ k ih =>
      intro hk
      have hchain_k := ih (by lia)
      set T := P.triangle ⟨k, by lia⟩
      have hT := P.triangle_dist ⟨k, by lia⟩
      have e₁ := Classical.choice (P.triangle_obj₁ ⟨k, by lia⟩)
      have e₂ := Classical.choice (P.triangle_obj₂ ⟨k, by lia⟩)
      have h₁ : s.ltProp C t T.obj₁ := (s.ltProp C t).prop_of_iso e₁.symm hchain_k
      have h₃ : s.ltProp C t T.obj₃ := hfactors ⟨k, by lia⟩
      have h₂ : s.ltProp C t T.obj₂ := s.ltProp_of_triangle C t h₁ h₃ hT
      exact (s.ltProp C t).prop_of_iso e₂ h₂

end CategoryTheory.Triangulated
