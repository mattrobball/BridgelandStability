/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.PhiPlusMDQ

/-!
# HN Existence via φ⁺ Reduction
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
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

variable [IsTriangulated C] in
/-- **W-phase upper bound from φ⁺ bound.** If `E ∈ P((a, b))` with `φ⁺(E) < b - 4ε`
and the interval is wide enough (`6ε ≤ b - a`), then `ψ(E) < b - 3ε`.

Proof: `φ⁺(E) < b - 4ε` and `φ⁻(E) > a` give `E ∈ P((a, b-4ε))`.
Apply `wPhaseOf_lt_of_intervalProp` with interval `(a, b-4ε)` and perturbation `ε`.
The `hα_le` condition `(a+b)/2 ≤ (b-4ε) + ε = b-3ε` follows from `6ε ≤ b-a`. -/
theorem wPhaseOf_lt_of_phiPlus_lt
    (σ : StabilityCondition.WithClassMap C v) (W : Λ →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (h_wide : 6 * ε ≤ b - a)
    {E : C} (hE : ¬IsZero E)
    (hI : σ.slicing.intervalProp C a b E)
    (hphiPlus : σ.slicing.phiPlus C E hE < b - 4 * ε) :
    wPhaseOf ((σ.skewedStabilityFunction_of_near C W hW hab).W (cl C v E))
      ((σ.skewedStabilityFunction_of_near C W hW hab).α) < b - 3 * ε := by
  -- E ∈ P((a, b-4ε)) from intrinsic phases
  have hab4 : a < b - 4 * ε := by linarith
  have hI_narrow : σ.slicing.intervalProp C a (b - 4 * ε) E :=
    σ.slicing.intervalProp_of_intrinsic_phases C hE
      (σ.slicing.phiMinus_gt_of_intervalProp C hE hI) hphiPlus
  -- Perturbation bounds at α = (a+b)/2 using the ORIGINAL interval (a, b)
  have hthin_orig : b - a < 1 := by linarith
  have hpert := hperturb_of_stabSeminorm C σ W hW hthin_orig hε hε2 hsin
  -- hα_le: (a+b)/2 ≤ (b-4ε) + ε = b-3ε (from h_wide: 6ε ≤ b-a → (a+b)/2 ≤ b-3ε)
  have hα_le : (a + b) / 2 ≤ (b - 4 * ε) + ε := by linarith
  -- W-nonzero for factors in P((a, b-4ε)) ⊂ P((a, b))
  have hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b - 4 * ε → W (cl C v F) ≠ 0 :=
    fun F φ hP hFne _ _ => σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  -- Perturbation at α = (a+b)/2 in the format for wPhaseOf_lt_of_intervalProp
  -- Factors at φ ∈ (a, b-4ε) ⊂ (a, b) get bounds at α = (a+b)/2 from hpert
  have hperturb_fmt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b - 4 * ε →
      (b - 4 * ε) + ε - 1 < wPhaseOf (W (cl C v F)) ((a + b) / 2) ∧
      wPhaseOf (W (cl C v F)) ((a + b) / 2) < (b - 4 * ε) + ε := by
    intro F φ hP hFne haφ hφb
    have hφb_orig : φ < b := by linarith
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb_orig
    constructor
    · -- (b-4ε)+ε-1 = b-3ε-1. ψ(F) > φ-ε > a-ε. a-ε > b-3ε-1 from hthin.
      have : a - ε > b - 3 * ε - 1 := by linarith
      linarith
    · -- ψ(F) < φ+ε < (b-4ε)+ε = b-3ε
      linarith
  -- Apply wPhaseOf_lt_of_intervalProp at α = (a+b)/2
  -- Result: wPhaseOf(W(E), (a+b)/2) < (b-4ε)+ε = b-3ε
  have h := wPhaseOf_lt_of_intervalProp C σ hE W (α := (a + b) / 2)
    hα_le hI_narrow hW_ne hperturb_fmt
  -- ssf.W = W and ssf.α = (a+b)/2 by definition of skewedStabilityFunction_of_near
  simp only [StabilityCondition.WithClassMap.skewedStabilityFunction_of_near]
  linarith

/-! ### HN existence with φ⁺ reduction -/

variable [IsTriangulated C] in
/-- **HN existence with φ⁺ reduction** (Bridgeland p.23–24).

Drops both `hHom` and `hDestabBound` from
`hn_exists_in_thin_interval_of_strictQuotientLowerBound`. Instead takes perturbation
data and a quotient lower bound `t ≥ a + ε`.

At each step of the HN recursion:
1. Call `exists_strictMDQ_with_quotient_bound` (which handles hHom and hDestabBound internally)
2. Extract kernel, lift to smaller strict subobject
3. Recurse with the MDQ phase as new lower bound -/
theorem hn_exists_with_phiPlus_reduction
    (σ : StabilityCondition.WithClassMap C v) (W : Λ →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4) (hε8 : ε < 1 / 8)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hFL : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      (σ.skewedStabilityFunction_of_near C W hW hab).W (cl C v F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf ((σ.skewedStabilityFunction_of_near C W hW hab).W (cl C v F))
        (σ.skewedStabilityFunction_of_near C W hW hab).α ∧
        wPhaseOf ((σ.skewedStabilityFunction_of_near C W hW hab).W (cl C v F))
          (σ.skewedStabilityFunction_of_near C W hW hab).α < U)
    (hWidth : U - L < 1)
    (t : ℝ) (ht : a + ε ≤ t)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X)
    (hquot : ∀ {B : σ.slicing.IntervalCat C a b} (q : X ⟶ B),
      IsStrictEpi q → ¬IsZero B.obj →
        t < wPhaseOf ((σ.skewedStabilityFunction_of_near C W hW hab).W (cl C v B.obj))
          (σ.skewedStabilityFunction_of_near C W hW hab).α)
    -- Window-interval compatibility
    (hL_a : a ≤ L + ε)
    -- Width condition (needed for wPhaseOf_lt_of_intervalProp's hα_le)
    (h_wide : 6 * ε ≤ b - a)
    -- φ⁺ upper bound (propagates through kernels via phiPlus_triangle_le)
    (hphiPlus_X : ∀ (hXne : ¬IsZero X.obj),
      σ.slicing.phiPlus C X.obj hXne < b - 4 * ε) :
    let ssf := σ.skewedStabilityFunction_of_near C W hW hab
    let Psem : ℝ → ObjectProperty C := fun ψ F => ssf.Semistable C F ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, t < G.φ j ∧ G.φ j < U := by
  letI : IsTriangulated C := ‹IsTriangulated C›
  -- Follows Lemma77.lean:71-303 with MDQ call swapped and φ⁺ invariant threaded.
  let ssf := σ.skewedStabilityFunction_of_near C W hW hab
  let Psem : ℝ → ObjectProperty C := fun ψ F => ssf.Semistable C F ψ
  letI : IsStrictArtinianObject X := (hFL X).1
  letI : IsStrictNoetherianObject X := (hFL X).2
  let S0 : StrictSubobject X := ⟨⊤, isStrictMono_of_isIso⟩
  -- Induction predicate: same as Lemma77 + φ⁺ invariant
  let Psub : StrictSubobject X → Prop := fun S =>
      ¬IsZero (S.1 : σ.slicing.IntervalCat C a b) →
        ∀ t : ℝ, a + ε ≤ t →
          (∀ A : Subobject (S.1 : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
            IsStrictMono A.arrow →
            t < ssf.wPhase (cokernel A.arrow).obj) →
          (∀ (hYne : ¬IsZero (S.1 : σ.slicing.IntervalCat C a b).obj),
            σ.slicing.phiPlus C (S.1 : σ.slicing.IntervalCat C a b).obj hYne <
              b - 4 * ε) →
          ∃ G : HNFiltration C Psem (S.1 : σ.slicing.IntervalCat C a b).obj,
            ∀ j, t < G.φ j ∧ G.φ j < U
  have h : ∀ S : StrictSubobject X, Psub S := by
    intro S
    refine (show WellFounded ((· < ·) : StrictSubobject X → StrictSubobject X → Prop) from
      wellFounded_lt).induction S ?_
    intro S ih hS t ht_lo hquot hphiPlus_Y
    let Y : σ.slicing.IntervalCat C a b := S.1
    have hS_obj : ¬IsZero Y.obj := fun hZ =>
      hS (Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    let ψY : ℝ := ssf.wPhase Y.obj
    by_cases hss : ssf.Semistable C Y.obj ψY
    · -- SEMISTABLE CASE: single-factor HN filtration (verbatim from Lemma77)
      let Gsingle : HNFiltration C Psem Y.obj := HNFiltration.single C Y.obj ψY hss
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
      have hj_lt : j.val < 1 := by
        lia
      have hj0 : j.val = 0 := by lia
      have hj : j = ⟨0, by simp [Gsingle, HNFiltration.single]⟩ :=
        Fin.ext hj0
      subst j
      have hψY_gt : t < ψY := by exact hbot_eq ▸ hbot_gt
      exact ⟨by simpa [Gsingle, HNFiltration.single] using hψY_gt, hψY_hi⟩
    · -- NON-SEMISTABLE CASE: find MDQ, extract kernel, recurse
      letI : IsStrictArtinianObject Y := (hFL Y).1
      letI : IsStrictNoetherianObject Y := (hFL Y).2
      -- Derive ψ(Y) < b - 3ε from φ⁺(Y) < b - 4ε
      have hψ_Y_upper : ssf.wPhase Y.obj < b - 3 * ε :=
        wPhaseOf_lt_of_phiPlus_lt C σ W hW hab hε hε2 hthin hsin h_wide hS_obj
          Y.property (hphiPlus_Y hS_obj)
      -- Derive ψ(Y) > t from quotient bound applied to ⊥
      have hψ_Y_lo : t < ψY := by
        have hbot_ne_top : (⊥ : Subobject Y) ≠ ⊤ := fun hEq =>
          (intervalSubobject_top_ne_bot_of_not_isZero
            (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hS) hEq.symm
        have hbot_strict : IsStrictMono ((⊥ : Subobject Y).arrow) :=
          intervalSubobject_bot_arrow_strictMono
            (C := C) (s := σ.slicing) (a := a) (b := b)
        have hbot_gt := hquot ⊥ hbot_ne_top hbot_strict
        let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
          rw [show ((⊥ : Subobject Y).arrow) = 0 by simp [Subobject.bot_arrow]]
          exact cokernelZeroIsoTarget
        let eC := (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
        have hbot_eq : ssf.wPhase (cokernel ((⊥ : Subobject Y).arrow)).obj = ψY := by
          simp only [ψY]; exact ssf.wPhase_iso eC
        linarith
      -- Construct hQuotLo_ss from hquot (weaken: all quotients → semistable quotients)
      have hQuotLo_ss : ∀ {B' : σ.slicing.IntervalCat C a b} (q' : Y ⟶ B'),
          IsStrictEpi q' → ¬IsZero B'.obj →
          ssf.Semistable C B'.obj (ssf.wPhase B'.obj) →
          t < ssf.wPhase B'.obj := by
        intro B' q' hq' hB'_ne _hB'_ss
        -- kernel(q') is a strict subobject with cokernel ≅ B'
        let K' : Subobject Y := kernelSubobject q'
        have hK'_ne_top :=
          interval_kernelSubobject_ne_top_of_strictEpi_nonzero
            (C := C) (s := σ.slicing) (a := a) (b := b) hq' hB'_ne
        have hK'_strict : IsStrictMono K'.arrow := by
          simpa [K'] using intervalSubobject_arrow_strictMono_of_strictMono
            (C := C) (s := σ.slicing) (a := a) (b := b) (kernel.ι q') (isStrictMono_kernel q')
        have hgt := hquot K' hK'_ne_top hK'_strict
        simpa using hgt.trans_eq
          (wPhaseOf_cokernel_kernelSubobject_eq
            (C := C) (s := σ.slicing) (a := a) (b := b) (ssf := ssf) q' hq')
      -- CALL MDQ (the key difference from Lemma77)
      obtain ⟨B, q, hq⟩ := exists_strictMDQ_with_quotient_bound
        (C := C) σ (ssf := ssf) hFL hW_interval hWindow hWidth
        W hW hε hε2 hε8 hab hthin hsin rfl hL_a ht_lo
        (hX := hS) hQuotLo_ss hψ_Y_lo hψ_Y_upper
      -- Extract kernel (verbatim from Lemma77:133-156)
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
      -- Phase bounds on B (verbatim from Lemma77:157-166)
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
      -- Quotient bound propagation to T (verbatim from Lemma77:167-215)
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
              (C := C) (σ := σ) (a := a) (b := b) hFL hW_interval hWindow hWidth
              hq (A := A') hA'_top hA'_strict)
        rw [hphase_A]
        exact hgtA'
      -- φ⁺ propagation: φ⁺(K) ≤ φ⁺(Y) < b - 4ε via phiPlus_triangle_le
      have hK_ne_obj : ¬IsZero (K : σ.slicing.IntervalCat C a b).obj := by
        intro hZ; exact (intervalSubobject_not_isZero_of_ne_bot
          (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hK_ne_bot)
          (Slicing.IntervalCat.isZero_of_obj_isZero
            (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
      have hphiPlus_K : ∀ (hKne : ¬IsZero (K : σ.slicing.IntervalCat C a b).obj),
          σ.slicing.phiPlus C (K : σ.slicing.IntervalCat C a b).obj hKne < b - 4 * ε := by
        intro hKne
        -- Extract distinguished triangle K → Y → B from the strict SES
        let SQ : ShortComplex (σ.slicing.IntervalCat C a b) :=
          ShortComplex.mk K.arrow q (kernelSubobject_arrow_comp (f := q))
        have hSQ : StrictShortExact SQ :=
          interval_strictShortExact_of_kernelSubobject_strictEpi
            (C := C) (s := σ.slicing) (a := a) (b := b) q hq.strictEpi
        obtain ⟨δ, hT_dist⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
          (C := C) (s := σ.slicing) (a := a) (b := b) hSQ
        have hab1 : b ≤ a + 1 := by linarith [Fact.out (p := b - a ≤ 1)]
        have hle := σ.slicing.phiPlus_triangle_le C hKne hS_obj hab1
          (K : σ.slicing.IntervalCat C a b).property B.property hT_dist
        linarith [hphiPlus_Y hS_obj]
      -- Transport φ⁺ bound to T via T ≅ K
      have hphiPlus_T : ∀ (hTne : ¬IsZero (T : σ.slicing.IntervalCat C a b).obj),
          σ.slicing.phiPlus C (T : σ.slicing.IntervalCat C a b).obj hTne < b - 4 * ε := by
        intro hTne
        let eK : (T : σ.slicing.IntervalCat C a b) ≅ (K : σ.slicing.IntervalCat C a b) := by
          dsimp [T, intervalLiftSub]
          exact Subobject.isoOfEqMk _ (K.arrow ≫ S.1.arrow) rfl
        have eC := ((σ.slicing.intervalProp C a b).ι).mapIso eK
        -- phiPlus(T) ≤ phiPlus(K) since T ≅ K (iso of interval objects → same HN filtrations)
        have hle : σ.slicing.phiPlus C (T : σ.slicing.IntervalCat C a b).obj hTne ≤
            σ.slicing.phiPlus C (K : σ.slicing.IntervalCat C a b).obj hK_ne_obj := by
          -- Get the chosen filtration for K and transport to T
          let FK := (HNFiltration.exists_nonzero_first C σ.slicing hK_ne_obj).choose
          let hn := (HNFiltration.exists_nonzero_first C σ.slicing hK_ne_obj).choose_spec.choose
          let FT : HNFiltration C σ.slicing.P (T : σ.slicing.IntervalCat C a b).obj :=
            FK.ofIso C eC.symm
          exact σ.slicing.phiPlus_le_phiPlus_of_hn C hTne FT hn
        linarith [hphiPlus_K hK_ne_obj]
      -- RECURSIVE CALL
      obtain ⟨GT, hGT⟩ := ih Tstr hT_lt hT_ne ψB (le_of_lt (lt_of_le_of_lt ht_lo hψB_gt))
        hquot_T hphiPlus_T
      -- Assemble HN filtration (verbatim from Lemma77:217-250)
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
        have hjFalse : ¬GK.n < GK.n := by lia
        simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hjFalse,
          ψB] using ⟨hψB_gt, hψB_hi⟩
  -- BOOTSTRAP from S₀ = ⊤ to X (modified from Lemma77:251-303)
  have hS0_ne : ¬IsZero (S0.1 : σ.slicing.IntervalCat C a b) := by
    intro hZ
    let e0 : (S0.1 : σ.slicing.IntervalCat C a b) ≅ X :=
      asIso S0.1.arrow
    exact hX (hZ.of_iso e0.symm)
  -- Convert strict-epi hquot to subobject form
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
    -- Convert: apply hquot to cokernel.π A'.arrow (a strict epi from X)
    have hA'_nonzero : ¬IsZero (cokernel A'.arrow).obj := fun hZ =>
      (interval_cokernel_nonzero_of_ne_top
        (C := C) (s := σ.slicing) (a := a) (b := b) hA'_top hA'_strict)
        (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    exact hquot (cokernel.π A'.arrow) (isStrictEpi_cokernel A'.arrow) hA'_nonzero
  -- φ⁺ bound for S₀ (transport from X via S₀.1 ≅ X)
  have hphiPlus_S0 : ∀ (hS0ne : ¬IsZero (S0.1 : σ.slicing.IntervalCat C a b).obj),
      σ.slicing.phiPlus C (S0.1 : σ.slicing.IntervalCat C a b).obj hS0ne < b - 4 * ε := by
    intro hS0ne
    have e0 : (S0.1 : σ.slicing.IntervalCat C a b) ≅ X := asIso S0.1.arrow
    have eC := ((σ.slicing.intervalProp C a b).ι).mapIso e0
    have hX_ne : ¬IsZero X.obj := by
      intro hZ; exact hX (Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    -- phiPlus(S0.1) ≤ phiPlus(X) since S0.1 ≅ X
    have hle : σ.slicing.phiPlus C (S0.1 : σ.slicing.IntervalCat C a b).obj hS0ne ≤
        σ.slicing.phiPlus C X.obj hX_ne := by
      let FX := (HNFiltration.exists_nonzero_first C σ.slicing hX_ne).choose
      let hn := (HNFiltration.exists_nonzero_first C σ.slicing hX_ne).choose_spec.choose
      exact σ.slicing.phiPlus_le_phiPlus_of_hn C hS0ne (FX.ofIso C eC.symm) hn
    linarith [hphiPlus_X hX_ne]
  obtain ⟨G0, hG0⟩ := h S0 hS0_ne t ht hS0_quot hphiPlus_S0
  let eTop : (S0.1 : σ.slicing.IntervalCat C a b).obj ≅ X.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso (asIso S0.1.arrow)
  refine ⟨G0.ofIso C eTop, ?_⟩
  intro j
  simpa using hG0 j

end CategoryTheory.Triangulated
