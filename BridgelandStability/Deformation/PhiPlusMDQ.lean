/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.PhiPlusReduction

/-!
# MDQ with Quotient Bound for φ⁺ Reduction
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

/-- **Phase lower bound via Im argument** (generalized `wPhaseOf_gt_of_intervalProp`).

If `E ∈ P((c, d))` and every σ-semistable factor of phase `φ ∈ (c, d)` has
`W`-phase strictly between `ψ` and `ψ + 1`, then `wPhaseOf(W(E), α) > ψ`.

This replaces the `hα_ge : c - (c - ψ) ≤ α` condition in `wPhaseOf_gt_of_intervalProp`
with a direct width bound `ψ - 1 < wPhaseOf(W(E), α)`, which is derivable from
`U - L < 1` in the MDQ recursion context. -/
theorem wPhaseOf_gt_of_narrow_interval
    (σ : StabilityCondition.WithClassMap C v)
    {E : C} (hE : ¬IsZero E)
    (W : Λ →+ ℂ) {α : ℝ} {ψ : ℝ}
    {c d : ℝ}
    (hI : σ.slicing.intervalProp C c d E)
    (hE_width : ψ - 1 < wPhaseOf (W (cl C v E)) α)
    (hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        c < φ → φ < d → W (cl C v F) ≠ 0)
    (hfactors : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        c < φ → φ < d →
        ψ < wPhaseOf (W (cl C v F)) α ∧
        wPhaseOf (W (cl C v F)) α < ψ + 1) :
    ψ < wPhaseOf (W (cl C v E)) α := by
  have him : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      c < φ → φ < d →
      0 < (W (cl C v F) *
        Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
    intro F φ hP hFne hcφ hφd
    obtain ⟨hlo, hhi⟩ := hfactors F φ hP hFne hcφ hφd
    have hWne := hW_ne F φ hP hFne hcφ hφd
    exact im_pos_of_phase_above (norm_pos_iff.mpr hWne) (wPhaseOf_compat _ _) hlo hhi
  have him_pos := im_W_pos_of_intervalProp C σ hE W hI him
  by_contra h
  push Not at h
  set θ := wPhaseOf (W (cl C v E)) α
  have hw := wPhaseOf_compat (W (cl C v E)) α
  rw [hw, im_ofReal_mul_exp_mul_exp_neg] at him_pos
  have hsin : Real.sin (Real.pi * (θ - ψ)) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hE_width])
  linarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (W (cl C v E))) hsin]

/-- **MDQ existence with φ⁺ case split** (Bridgeland p.23).

Same recursion as `exists_strictMDQ_of_finiteLength` but replaces:
- `hHom` → perturbation data + W-semistable quotient lower bound
- `hDestabBound` → `phiPlus_bound_of_destabilizing_subobject` (when `φ⁺ ≤ ψ + ε`)

When `φ⁺(QS) > ψ(QS) + ε`, the σ-phase split branch applies. The degenerate cases
(X_hi = 0, Ahi = ⊤) are excluded by `wPhaseOf_gt_of_narrow_interval`. -/
theorem exists_strictMDQ_with_quotient_bound
    (σ : StabilityCondition.WithClassMap C v) {a b : ℝ}
    {ssf : SkewedStabilityFunction C v σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F → ssf.wNe F)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < ssf.wPhase F ∧ ssf.wPhase F < U)
    (hWidth : U - L < 1)
    -- Perturbation data (replaces hHom)
    (W : Λ →+ ℂ) (hW_stab : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4) (hε8 : ε < 1 / 8)
    (hab : a < b) (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hssf : ssf = σ.skewedStabilityFunction_of_near C W hW_stab hab)
    -- Window-interval compatibility (L ≥ a - ε, trivially true in Theorem71)
    (hL_a : a ≤ L + ε)
    -- W-semistable quotient lower bound (for comp_of_destabilizing_with_quotient_bound)
    {t_lo : ℝ} (ht_lo : a + ε ≤ t_lo)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hQuotLo_ss : ∀ {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B'),
      IsStrictEpi q' → ¬IsZero B'.obj →
      ssf.Semistable C B'.obj (ssf.wPhase B'.obj) →
      t_lo < ssf.wPhase B'.obj)
    -- Phase lower bound on X (derived from quotient lower bound on ⊥ in caller)
    (hψ_X_lo : t_lo < ssf.wPhase X.obj)
    -- Phase upper bound on X (from phiPlus < b - 4ε via wPhaseOf_lt_of_intervalProp)
    (hψ_X_upper : ssf.wPhase X.obj < b - 3 * ε) :
    ∃ (B : σ.slicing.IntervalCat C a b) (q : X ⟶ B), IsStrictMDQ (C := C) σ ssf q := by
  -- Follow exists_strictMDQ_of_finiteLength (MDQ.lean:619-681)
  -- Key change: remove hψ_lo from the recursion predicate. Instead, derive
  -- t_lo < ψ(QS) AFTER the recursive call using: ψ(B) > t_lo (quotient bound)
  -- + ψ(B) ≤ ψ(cokernel(A.arrow)) < ψ(QS) (seesaw).
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  suffices h :
      ∀ (S : StrictSubobject X), ¬IsZero (cokernel S.1.arrow) →
        ssf.wPhase (cokernel S.1.arrow).obj < b - 3 * ε →
        (∀ {B' : σ.slicing.IntervalCat C a b} (q' : cokernel S.1.arrow ⟶ B'),
          IsStrictEpi q' → ¬IsZero B'.obj →
          ssf.Semistable C B'.obj (ssf.wPhase B'.obj) →
          t_lo < ssf.wPhase B'.obj) →
        ∃ (B : σ.slicing.IntervalCat C a b) (q : cokernel S.1.arrow ⟶ B),
          IsStrictMDQ (C := C) σ ssf q by
    let S0 : StrictSubobject X := ⟨⊥,
      intervalSubobject_bot_arrow_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b)⟩
    have hS0_ne : ¬IsZero (cokernel S0.1.arrow) := by
      let e0 : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
        rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      intro hZ; exact hX (hZ.of_iso e0.symm)
    have hQLo0 : ∀ {B' : σ.slicing.IntervalCat C a b} (q' : cokernel S0.1.arrow ⟶ B'),
        IsStrictEpi q' → ¬IsZero B'.obj →
        ssf.Semistable C B'.obj (ssf.wPhase B'.obj) →
        t_lo < ssf.wPhase B'.obj := by
      intro B' q' hq' hB'_ne hB'_ss
      let e0 : cokernel S0.1.arrow ≅ X := by
        rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      exact hQuotLo_ss (e0.inv ≫ q')
        (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
          e0.inv q' (isStrictEpi_of_isIso (f := e0.inv)) hq') hB'_ne hB'_ss
    have hψ_S0 : ssf.wPhase (cokernel S0.1.arrow).obj < b - 3 * ε := by
      -- cokernel(⊥.arrow) ≅ X, so ψ is the same
      have e0 : cokernel S0.1.arrow ≅ X := by
        rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      have hiso : (cokernel S0.1.arrow).obj ≅ X.obj :=
        ((σ.slicing.intervalProp C a b).ι).mapIso e0
      have : ssf.W (cl C v (cokernel S0.1.arrow).obj) = ssf.W (cl C v X.obj) := by
        congr 1; exact cl_iso C v hiso
      rw [ssf.wPhase_congr this]
      exact hψ_X_upper
    obtain ⟨B, q, hq⟩ := h S0 hS0_ne hψ_S0 hQLo0
    let e0 : cokernel S0.1.arrow ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    exact ⟨B, e0.inv ≫ q,
      IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b) hq e0.symm⟩
  intro S
  induction S using IsWellFounded.induction
      (· > · : StrictSubobject X → StrictSubobject X → Prop) with
  | ind S ih =>
      intro hQS_ne hψ_QS_upper hQLo_S
      let QS : σ.slicing.IntervalCat C a b := cokernel S.1.arrow
      letI : IsStrictArtinianObject QS := (hFiniteLength QS).1
      letI : IsStrictNoetherianObject QS := (hFiniteLength QS).2
      let ψQS : ℝ := ssf.wPhase QS.obj
      have hQS_obj_ne : ¬IsZero QS.obj := by
        intro hZ; exact hQS_ne (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
      by_cases hQS_ss : ssf.Semistable C QS.obj ψQS
      · exact ⟨QS, 𝟙 _, IsStrictMDQ.id_of_semistable
          (C := C) (σ := σ) (a := a) (b := b) hW_interval hWindow hWidth hQS_ss⟩
      · by_cases hphiPlus_QS :
            σ.slicing.phiPlus C QS.obj hQS_obj_ne ≤ ψQS + ε
        · -- DESTABILIZING BRANCH (φ⁺(QS) ≤ ψ(QS) + ε)
          obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hA_ss, hA_phase_gt, _⟩ :=
            ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
              (C := C) (σ := σ) (a := a) (b := b) (X := QS) hQS_ne hQS_ss hW_interval
          have hA_phase_upper :
              ssf.wPhase (A : σ.slicing.IntervalCat C a b).obj < b - ε := by
            subst hssf
            exact phiPlus_bound_of_destabilizing_subobject C σ W hW_stab hab hε hε2 hthin hsin
              hQS_obj_ne hphiPlus_QS hψ_QS_upper hA_ss hA_strict
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
          let eT : cokernel Tsub.arrow ≅ cokernel A.arrow :=
            interval_cokernel_pullbackTopIso
              (C := C) (s := σ.slicing) (a := a) (b := b) S.1 hA_strict
          -- Propagate quotient lower bound
          have hQLo_T : ∀ {B' : σ.slicing.IntervalCat C a b}
              (q' : cokernel Tsub.arrow ⟶ B'),
              IsStrictEpi q' → ¬IsZero B'.obj →
              ssf.Semistable C B'.obj (ssf.wPhase B'.obj) →
              t_lo < ssf.wPhase B'.obj := by
            intro B' q' hq' hB'_ne hB'_ss
            exact hQLo_S (cokernel.π A.arrow ≫ (eT.inv ≫ q'))
              (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
                (cokernel.π A.arrow) (eT.inv ≫ q')
                (isStrictEpi_cokernel A.arrow)
                (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
                  eT.inv q' (isStrictEpi_of_isIso (f := eT.inv)) hq'))
              hB'_ne hB'_ss
          -- Propagate class H upper bound via seesaw
          have hψ_cok_lt : ssf.wPhase (cokernel A.arrow).obj < ψQS :=
            ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
              (C := C) (σ := σ) (a := a) (b := b)
              hA_ne_bot hA_ne_top hA_strict hA_phase_gt hW_interval hWindow hWidth
          -- ψ upper bound for cokernel(Tsub.arrow) via iso to cokernel(A.arrow)
          have hψ_T_upper :
              ssf.wPhase (cokernel Tsub.arrow).obj < b - 3 * ε := by
            have hiso_T : (cokernel Tsub.arrow).obj ≅ (cokernel A.arrow).obj :=
              ((σ.slicing.intervalProp C a b).ι).mapIso eT
            have : ssf.W (cl C v (cokernel Tsub.arrow).obj) =
                ssf.W (cl C v (cokernel A.arrow).obj) := by
              congr 1; exact cl_iso C v hiso_T
            have hEq : ssf.wPhase (cokernel Tsub.arrow).obj = ssf.wPhase (cokernel A.arrow).obj := by
              exact ssf.wPhase_congr this
            rw [hEq]
            linarith
          -- RECURSIVE CALL
          obtain ⟨B, qT, hqT⟩ := ih T hS_lt_T hQT_ne hψ_T_upper hQLo_T
          let qA : cokernel A.arrow ⟶ B := eT.inv ≫ qT
          have hqA : IsStrictMDQ (C := C) σ ssf qA :=
            IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b) hqT eT.symm
          -- Derive t_lo < ψ(QS) from: ψ(B) > t_lo + ψ(B) ≤ ψ(cok(A)) < ψ(QS)
          have hB_phase_lo : t_lo < ssf.wPhase B.obj :=
            hQLo_S (cokernel.π A.arrow ≫ qA)
              (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
                (cokernel.π A.arrow) qA (isStrictEpi_cokernel A.arrow) hqA.strictEpi)
              hqA.nonzero hqA.semistable
          have hψ_lo_S : t_lo < ψQS := by
            have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
              intro hZ
              letI : Epi qA := hqA.strictEpi.epi
              have hzero : qA = 0 := zero_of_source_iso_zero _ <|
                (Slicing.IntervalCat.isZero_of_obj_isZero
                  (C := C) (s := σ.slicing) (a := a) (b := b) hZ).isoZero
              exact hqA.nonzero (((σ.slicing.intervalProp C a b).ι).map_isZero
                (IsZero.of_epi_eq_zero qA hzero))
            have hB_le_cok : ssf.wPhase B.obj ≤ ssf.wPhase (cokernel A.arrow).obj :=
              IsStrictMDQ.phase_le_of_strictQuotient
                (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
                hqA (𝟙 (cokernel A.arrow)) (isStrictEpi_of_isIso (f := 𝟙 _)) hcokA_obj_ne
            linarith
          -- COMPOSE using comp_of_destabilizing_with_quotient_bound (sorry-free!)
          exact ⟨B, cokernel.π A.arrow ≫ qA,
            comp_of_destabilizing_with_quotient_bound
              (C := C) (σ := σ) (a := a) (b := b)
              hFiniteLength hW_interval hWindow hWidth
              W hW_stab hε hε2 hε8 hab hthin hsin hssf ht_lo hψ_lo_S hQLo_S
              hA_ss hA_strict hA_phase_gt hA_ne_top hA_phase_upper hqA⟩
        · -- Case 3: φ⁺(QS) > ψ(QS) + ε → φ⁺ SPLIT BRANCH
          push Not at hphiPlus_QS -- hphiPlus_QS : ψQS + ε < φ⁺(QS)
          -- Extract σ-HN filtration from QS.property (intervalProp definition)
          rcases QS.property with hQSZ | ⟨F_QS, hF_QS⟩
          · exact absurd hQSZ (by
              intro hZ; exact hQS_ne (Slicing.IntervalCat.isZero_of_obj_isZero
                (C := C) (s := σ.slicing) (a := a) (b := b)
                (((σ.slicing.intervalProp C a b).ι).map_isZero
                  (Slicing.IntervalCat.isZero_of_obj_isZero
                    (C := C) (s := σ.slicing) (a := a) (b := b) hZ))))
          · have hFn : 0 < F_QS.n := by
              by_contra h; push Not at h
              exact hQS_obj_ne (F_QS.toPostnikovTower.zero_isZero (show F_QS.n = 0 by lia))
            -- Split at cutoff t_cut = ψQS + ε
            let t_cut : ℝ := ψQS + ε
            obtain ⟨X_hi, QS_lo, f_hi, g_lo, δ_split, hT_split, hX_hi_gt, hQS_lo_le,
                hX_hi_phiPlus⟩ :=
              σ.slicing.exists_split_at_cutoff C F_QS hF_QS hFn (t := t_cut)
            -- X_hi ≠ 0: follows from φ⁺(QS) > ψ + ε and leProp(ψ + ε) on QS_lo
            -- If X_hi = 0 then QS ≅ QS_lo ∈ leProp(t_cut), so φ⁺(QS) ≤ t_cut,
            -- contradicting φ⁺(QS) > t_cut.
            have hX_hi_ne : ¬IsZero X_hi := by
              intro hX_hi_zero
              -- X_hi = 0 → QS_lo has all the σ-phases of QS (via the triangle)
              -- QS_lo ∈ leProp(t_cut) means all σ-phases ≤ t_cut
              -- But φ⁺(QS) > t_cut means QS has a σ-phase > t_cut. Contradiction.
              -- More precisely: X_hi = 0 → g_lo is iso → phiPlus(QS) ≤ phiPlus(QS_lo)
              haveI : IsIso g_lo := by
                have : IsIso (Triangle.mk f_hi g_lo δ_split).mor₂ :=
                  (Triangle.isZero₁_iff_isIso₂ _ hT_split).mp hX_hi_zero
                exact this
              -- QS.obj ≅ QS_lo
              have e_lo : QS.obj ≅ QS_lo := asIso g_lo
              -- QS_lo ∈ leProp(t_cut) → phiPlus(QS_lo) ≤ t_cut
              -- Since QS.obj ≅ QS_lo, phiPlus(QS.obj) ≤ t_cut
              have hQS_le : σ.slicing.leProp C t_cut QS.obj := by
                rcases hQS_lo_le with hZ | ⟨F_lo, hn_lo, hmax_lo⟩
                · left; exact hZ.of_iso e_lo
                · right; exact ⟨F_lo.ofIso C e_lo.symm, hn_lo, hmax_lo⟩
              have hle := σ.slicing.phiPlus_le_of_leProp C hQS_obj_ne hQS_le
              linarith
            -- X_hi ≠ 0: genuine σ-phase split
            -- t_cut < b (from phiMinus > t_cut and phiPlus < b for X_hi)
            have ht_cut_lt_b : t_cut < b := by
              have h1 := σ.slicing.phiMinus_gt_of_gtProp C hX_hi_ne hX_hi_gt
              have h2 := hX_hi_phiPlus hX_hi_ne
              linarith [σ.slicing.phiMinus_le_phiPlus C X_hi hX_hi_ne]
            -- X_hi ∈ P((a,b)): phiMinus > t_cut > a, phiPlus < b
            have hX_hi_int : σ.slicing.intervalProp C a b X_hi :=
              σ.slicing.intervalProp_of_intrinsic_phases C hX_hi_ne
                (by have h1 := σ.slicing.phiMinus_gt_of_gtProp C hX_hi_ne hX_hi_gt
                    have h2 := (hWindow QS.property hQS_obj_ne).1
                    linarith [hL_a])
                (hX_hi_phiPlus hX_hi_ne)
            -- QS_lo ∈ ltProp(b) (from leProp(t_cut) + t_cut < b)
            have hQS_lo_ltb : σ.slicing.ltProp C b QS_lo := by
              rcases hQS_lo_le with hZ | ⟨F_lo, hn_lo, hmax_lo⟩
              · exact Or.inl hZ
              · exact Or.inr ⟨F_lo, hn_lo, lt_of_le_of_lt hmax_lo ht_cut_lt_b⟩
            -- X_hi ∈ geProp(b-1) (from gtProp(t_cut) + b-1 < t_cut)
            have hX_hi_geb : σ.slicing.geProp C (b - 1) X_hi := by
              apply σ.slicing.geProp_of_gtProp
              apply σ.slicing.gtProp_anti (t₂ := t_cut)
              · have h2 := (hWindow QS.property hQS_obj_ne).1
                linarith [Fact.out (p := b - a ≤ 1), hL_a]
              · exact hX_hi_gt
            -- QS_lo ∈ P((a,b)) via third_intervalProp_of_triangle
            have hQS_lo_int : σ.slicing.intervalProp C a b QS_lo :=
              σ.slicing.third_intervalProp_of_triangle C (Fact.out : a < b) QS.property
                hX_hi_geb hQS_lo_ltb hT_split
            -- Lift to IntervalCat and get strict SES
            let X_hi_I : σ.slicing.IntervalCat C a b := ⟨X_hi, hX_hi_int⟩
            let QS_lo_I : σ.slicing.IntervalCat C a b := ⟨QS_lo, hQS_lo_int⟩
            let f_hi_I : X_hi_I ⟶ QS := ObjectProperty.homMk f_hi
            let g_lo_I : QS ⟶ QS_lo_I := ObjectProperty.homMk g_lo
            -- Strict SES from the distinguished triangle
            have hSC := Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
              (C := C) (s := σ.slicing) (a := a) (b := b)
              (S := ShortComplex.mk f_hi_I g_lo_I (by
                apply ((σ.slicing.intervalProp C a b).ι).map_injective
                exact comp_distTriang_mor_zero₁₂ _ hT_split))
              hT_split
            -- X_hi_I as strict subobject of QS → pullback to T > S
            haveI : Mono f_hi_I := hSC.1.mono
            let Ahi : Subobject QS := Subobject.mk f_hi_I
            have hAhi_strict : IsStrictMono Ahi.arrow := by
              simpa [Ahi] using intervalSubobject_arrow_strictMono_of_strictMono
                (C := C) (s := σ.slicing) (a := a) (b := b) f_hi_I hSC.1
            have hAhi_ne_bot : Ahi ≠ ⊥ := by
              intro h
              have hAhi_zero : IsZero (Ahi : σ.slicing.IntervalCat C a b) :=
                (intervalSubobject_isZero_iff_eq_bot
                  (C := C) (s := σ.slicing) (a := a) (b := b) (X := QS) Ahi).mpr h
              have eAhi : (Ahi : σ.slicing.IntervalCat C a b) ≅ X_hi_I :=
                Subobject.isoOfEqMk Ahi f_hi_I rfl
              exact hX_hi_ne (((σ.slicing.intervalProp C a b).ι).map_isZero
                (hAhi_zero.of_iso eAhi.symm))
            have hAhi_ne_top : Ahi ≠ ⊤ := by
              -- If Ahi = ⊤ then f_hi_I is iso → QS ≅ X_hi → QS ∈ gtProp(t_cut).
              -- QS ∈ P((t_cut, b)), and the Im argument gives ψ(QS) > ψ(QS). Contradiction.
              intro hAhi_top
              -- Ahi = ⊤ means f_hi_I : X_hi_I ⟶ QS is iso
              have hf_iso : IsIso f_hi_I :=
                (Subobject.isIso_iff_mk_eq_top f_hi_I).mpr hAhi_top
              -- QS ∈ gtProp(t_cut) via closedUnderIso (X_hi ∈ gtProp(t_cut))
              have hQS_gt : σ.slicing.gtProp C t_cut QS.obj :=
                (σ.slicing.gtProp C t_cut).prop_of_iso
                  (((σ.slicing.intervalProp C a b).ι).mapIso (asIso f_hi_I))
                  hX_hi_gt
              -- QS ∈ P((t_cut, b)): narrow interval
              have hQS_narrow : σ.slicing.intervalProp C t_cut b QS.obj :=
                σ.slicing.intervalProp_of_intrinsic_phases C hQS_obj_ne
                  (σ.slicing.phiMinus_gt_of_gtProp C hQS_obj_ne hQS_gt)
                  (σ.slicing.phiPlus_lt_of_intervalProp C hQS_obj_ne QS.property)
              -- Width bound: ψ_QS - 1 < ψ(QS) (from hWindow width)
              have hQS_width : ψQS - 1 < ssf.wPhase QS.obj := by
                linarith
              -- Perturbation bounds for σ-semistable factors
              subst hssf
              have hpert := hperturb_of_stabSeminorm C σ W hW_stab
                (by linarith : b - a < 1) hε hε2 hsin
              -- Factor bounds: ψ_QS < ψ(F) < ψ_QS + 1 for F ∈ P(φ) with t_cut < φ < b
              have hfactors : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
                  t_cut < φ → φ < b →
                  ψQS < wPhaseOf (W (cl C v F)) ((a + b) / 2) ∧
                  wPhaseOf (W (cl C v F)) ((a + b) / 2) < ψQS + 1 := by
                intro F φ hP hFne htφ hφb
                have haφ : a < φ := by
                  have h2 := (hWindow QS.property hQS_obj_ne).1
                  linarith [hL_a]
                obtain ⟨hlo_pert, hhi_pert⟩ := hpert F φ hP hFne haφ hφb
                -- Lower: φ - ε > ψQS since φ > t_cut = ψQS + ε
                -- Upper: ψ(F) < φ + ε < b + ε and ψ_QS > a - ε → diff < b-a+2ε < 1
                refine ⟨by linarith, ?_⟩
                have hψ_QS_lo : a - ε < ψQS := by
                  have := (hWindow QS.property hQS_obj_ne).1; linarith [hL_a]
                linarith
              have hW_ne_narrow : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
                  t_cut < φ → φ < b →
                  W (cl C v F) ≠ 0 := by
                intro F φ hP hFne htφ hφb
                exact σ.W_ne_zero_of_seminorm_lt_one C W hW_stab hP hFne
              -- Apply wPhaseOf_gt_of_narrow_interval: ψ_QS < ψ_QS, contradiction
              exact absurd
                (wPhaseOf_gt_of_narrow_interval C σ hQS_obj_ne W hQS_narrow
                  hQS_width hW_ne_narrow hfactors)
                (lt_irrefl _)
            -- Pullback through cokernel.π S.1.arrow
            let Tsub : Subobject X :=
              (Subobject.pullback (cokernel.π S.1.arrow)).obj Ahi
            have hT_strict : IsStrictMono Tsub.arrow :=
              interval_pullback_arrow_strictMono_of_strictMono
                (C := C) (s := σ.slicing) (a := a) (b := b)
                (cokernel.π S.1.arrow) Ahi hAhi_strict
            let T : StrictSubobject X := ⟨Tsub, hT_strict⟩
            have hS_lt_T : S < T := by
              apply lt_of_lt_of_le
                (interval_lt_pullback_cokernel_of_ne_bot
                  (C := C) (s := σ.slicing) (a := a) (b := b)
                  (M := S.1) (B := Ahi) hAhi_ne_bot)
              exact le_rfl
            have hQT_ne : ¬IsZero (cokernel Tsub.arrow) :=
              interval_cokernel_nonzero_of_ne_top
                (C := C) (s := σ.slicing) (a := a) (b := b)
                (interval_pullback_cokernel_ne_top_of_ne_top
                  (C := C) (s := σ.slicing) (a := a) (b := b) hAhi_ne_top hAhi_strict)
                hT_strict
            let eT : cokernel Tsub.arrow ≅ cokernel Ahi.arrow :=
              interval_cokernel_pullbackTopIso
                (C := C) (s := σ.slicing) (a := a) (b := b) S.1 hAhi_strict
            -- Propagate quotient lower bound
            have hQLo_T : ∀ {B' : σ.slicing.IntervalCat C a b}
                (q' : cokernel Tsub.arrow ⟶ B'),
                IsStrictEpi q' → ¬IsZero B'.obj →
                ssf.Semistable C B'.obj (ssf.wPhase B'.obj) →
                t_lo < ssf.wPhase B'.obj := by
              intro B' q' hq' hB'_ne hB'_ss
              exact hQLo_S (cokernel.π Ahi.arrow ≫ (eT.inv ≫ q'))
                (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
                  (cokernel.π Ahi.arrow) (eT.inv ≫ q')
                  (isStrictEpi_cokernel Ahi.arrow)
                  (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
                    eT.inv q' (isStrictEpi_of_isIso (f := eT.inv)) hq'))
                hB'_ne hB'_ss
            -- Step 1: ψ(X_hi) > ψ(QS) via narrow interval Im argument
            have hψ_Xhi_gt : ψQS < ssf.wPhase X_hi := by
              have hX_hi_narrow : σ.slicing.intervalProp C t_cut b X_hi :=
                σ.slicing.intervalProp_of_intrinsic_phases C hX_hi_ne
                  (σ.slicing.phiMinus_gt_of_gtProp C hX_hi_ne hX_hi_gt)
                  (hX_hi_phiPlus hX_hi_ne)
              -- Width bound: derive BEFORE subst so ssf.W/α match hWindow
              have hXhi_width : ψQS - 1 <
                  ssf.wPhase X_hi := by
                have h1 := (hWindow hX_hi_int hX_hi_ne).1
                have h2 := (hWindow QS.property hQS_obj_ne).2
                linarith [hWidth]
              subst hssf
              have hpert := hperturb_of_stabSeminorm C σ W hW_stab
                (by linarith : b - a < 1) hε hε2 hsin
              have hfactors : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
                  t_cut < φ → φ < b →
                  ψQS < wPhaseOf (W (cl C v F)) ((a + b) / 2) ∧
                  wPhaseOf (W (cl C v F)) ((a + b) / 2) < ψQS + 1 := by
                intro F φ hP hFne htφ hφb
                have haφ : a < φ := by
                  have h2 := (hWindow QS.property hQS_obj_ne).1
                  linarith [hL_a]
                obtain ⟨hlo_pert, hhi_pert⟩ := hpert F φ hP hFne haφ hφb
                refine ⟨by linarith, ?_⟩
                have hψ_QS_lo : a - ε < ψQS := by
                  have := (hWindow QS.property hQS_obj_ne).1; linarith [hL_a]
                linarith
              have hW_ne_narrow : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
                  t_cut < φ → φ < b → W (cl C v F) ≠ 0 := by
                intro F φ hP hFne _ _
                exact σ.W_ne_zero_of_seminorm_lt_one C W hW_stab hP hFne
              exact wPhaseOf_gt_of_narrow_interval C σ hX_hi_ne W hX_hi_narrow
                hXhi_width hW_ne_narrow hfactors
            -- Step 2: ψ(Ahi) > ψ(QS) via iso transport Ahi ≅ X_hi_I
            have eAhi : (Ahi : σ.slicing.IntervalCat C a b) ≅ X_hi_I :=
              Subobject.isoOfEqMk Ahi f_hi_I rfl
            have hψ_Ahi_gt : ψQS < ssf.wPhase (Ahi : σ.slicing.IntervalCat C a b).obj := by
              have hiso : (Ahi : σ.slicing.IntervalCat C a b).obj ≅ X_hi_I.obj :=
                ((σ.slicing.intervalProp C a b).ι).mapIso eAhi
              have : ssf.W (cl C v (Ahi : σ.slicing.IntervalCat C a b).obj) =
                  ssf.W (cl C v X_hi) := by
                congr 1; exact cl_iso C v hiso
              have hEq : ssf.wPhase (Ahi : σ.slicing.IntervalCat C a b).obj =
                  ssf.wPhase X_hi := by
                exact ssf.wPhase_congr this
              rw [hEq]
              exact hψ_Xhi_gt
            -- Step 3: Seesaw → ψ(cokernel Ahi.arrow) < ψ(QS)
            have hψ_cokAhi_lt :
                ssf.wPhase (cokernel Ahi.arrow).obj < ψQS :=
              ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
                (C := C) (σ := σ) (a := a) (b := b)
                hAhi_ne_bot hAhi_ne_top hAhi_strict hψ_Ahi_gt hW_interval hWindow hWidth
            -- Step 4: ψ upper bound for cokernel(Tsub.arrow) via iso to cokernel(Ahi.arrow)
            have hψ_T_upper :
                ssf.wPhase (cokernel Tsub.arrow).obj <
                  b - 3 * ε := by
              have hiso_T : (cokernel Tsub.arrow).obj ≅ (cokernel Ahi.arrow).obj :=
                ((σ.slicing.intervalProp C a b).ι).mapIso eT
              have : ssf.W (cl C v (cokernel Tsub.arrow).obj) =
                  ssf.W (cl C v (cokernel Ahi.arrow).obj) := by
                congr 1; exact cl_iso C v hiso_T
              have hEq : ssf.wPhase (cokernel Tsub.arrow).obj = ssf.wPhase (cokernel Ahi.arrow).obj := by
                exact ssf.wPhase_congr this
              rw [hEq]
              linarith
            -- Step 5: Recursive call
            obtain ⟨B, qT, hqT⟩ := ih T hS_lt_T hQT_ne hψ_T_upper hQLo_T
            -- Step 6: Transport MDQ through eT
            let qAhi : cokernel Ahi.arrow ⟶ B := eT.inv ≫ qT
            have hqAhi : IsStrictMDQ (C := C) σ ssf qAhi :=
              IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b)
                hqT eT.symm
            -- Step 7: ψ(B) ≤ ψ(cokernel Ahi.arrow) via MDQ + identity quotient
            have hcokAhi_obj_ne : ¬IsZero (cokernel Ahi.arrow).obj := by
              intro hZ
              letI : Epi qAhi := hqAhi.strictEpi.epi
              have hzero : qAhi = 0 := zero_of_source_iso_zero _ <|
                (Slicing.IntervalCat.isZero_of_obj_isZero
                  (C := C) (s := σ.slicing) (a := a) (b := b) hZ).isoZero
              exact hqAhi.nonzero (((σ.slicing.intervalProp C a b).ι).map_isZero
                (IsZero.of_epi_eq_zero qAhi hzero))
            have hB_le_cokAhi :
                ssf.wPhase B.obj ≤ ssf.wPhase (cokernel Ahi.arrow).obj :=
              IsStrictMDQ.phase_le_of_strictQuotient
                (C := C) (σ := σ) (a := a) (b := b)
                hFiniteLength hW_interval hWindow hWidth
                hqAhi (𝟙 (cokernel Ahi.arrow)) (isStrictEpi_of_isIso (f := 𝟙 _))
                hcokAhi_obj_ne
            -- Step 8: geProp for Ahi.obj (source of Hom vanishing)
            have hX_hi_ge : σ.slicing.geProp C t_cut X_hi := by
              apply σ.slicing.geProp_of_gtProp; exact hX_hi_gt
            have hAhi_ge : σ.slicing.geProp C t_cut
                (Ahi : σ.slicing.IntervalCat C a b).obj :=
              (σ.slicing.geProp C t_cut).prop_of_iso
                (((σ.slicing.intervalProp C a b).ι).mapIso eAhi).symm hX_hi_ge
            -- Step 9: Construct MDQ via cokernel.π Ahi.arrow ≫ qAhi : QS ⟶ B
            -- Minimality: for any W-semistable quotient B' with ψ(B') ≤ ψ(B),
            -- phase chain ψ(B') ≤ ψ(cok Ahi) < ψQS gives B' ∈ ltProp(t_cut),
            -- while Ahi ∈ geProp(t_cut), so Ahi.arrow ≫ q' = 0 and q' factors
            -- through cokernel(Ahi.arrow) for MDQ minimality.
            have hvanish_helper : ∀ {B' : σ.slicing.IntervalCat C a b}
                (q' : QS ⟶ B'),
                ssf.Semistable C B'.obj
                  (ssf.wPhase B'.obj) →
                ssf.wPhase B'.obj ≤ ssf.wPhase B.obj →
                Ahi.arrow ≫ q' = 0 := by
              intro B' q' hB'_ss hle
              have hψ_B'_lt : ssf.wPhase B'.obj < ψQS :=
                lt_of_le_of_lt (le_trans hle hB_le_cokAhi) hψ_cokAhi_lt
              have hB'_lt : σ.slicing.ltProp C t_cut B'.obj := by
                subst hssf
                exact ltProp_of_wSemistable_phase_lt C σ W hW_stab hab hε hε2
                  hthin hsin hB'_ss (by linarith)
              exact ((σ.slicing.intervalProp C a b).ι).map_injective <| by
                simp only [Functor.map_comp, Functor.map_zero]
                exact σ.slicing.zero_of_geProp_ltProp_general C t_cut hAhi_ge hB'_lt _
            exact ⟨B, cokernel.π Ahi.arrow ≫ qAhi, {
              strictEpi := Slicing.IntervalCat.comp_strictEpi
                (C := C) (s := σ.slicing) (a := a) (b := b)
                (cokernel.π Ahi.arrow) qAhi
                (isStrictEpi_cokernel Ahi.arrow) hqAhi.strictEpi
              nonzero := hqAhi.nonzero
              semistable := hqAhi.semistable
              minimal := by
                intro B' q' hq' hB'_nz hB'_ss
                by_cases hle :
                    ssf.wPhase B.obj ≤ ssf.wPhase B'.obj
                · refine ⟨hle, ?_⟩
                  intro hEq
                  have hzero := hvanish_helper q' hB'_ss (by rw [hEq])
                  let q'' : cokernel Ahi.arrow ⟶ B' :=
                    cokernel.desc Ahi.arrow q' hzero
                  have hq'' : IsStrictEpi q'' :=
                    interval_strictEpi_of_strictEpi_comp
                      (C := C) (σ := σ) (a := a) (b := b)
                      (cokernel.π Ahi.arrow) q'' <| by
                        simpa [q''] using hq'
                  obtain ⟨t, ht⟩ := (hqAhi.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
                  exact ⟨t, by
                    have h1 : q' = cokernel.π Ahi.arrow ≫ q'' := by
                      symm; exact cokernel.π_desc Ahi.arrow q' hzero
                    rw [h1, ht]; simp only [Category.assoc]⟩
                · have hlt :
                      ssf.wPhase B'.obj < ssf.wPhase B.obj :=
                    lt_of_not_ge hle
                  have hzero := hvanish_helper q' hB'_ss (le_of_lt hlt)
                  let q'' : cokernel Ahi.arrow ⟶ B' :=
                    cokernel.desc Ahi.arrow q' hzero
                  have hq'' : IsStrictEpi q'' :=
                    interval_strictEpi_of_strictEpi_comp
                      (C := C) (σ := σ) (a := a) (b := b)
                      (cokernel.π Ahi.arrow) q'' <| by
                        simpa [q''] using hq'
                  have hmin :
                      ssf.wPhase B.obj ≤ ssf.wPhase B'.obj :=
                    (hqAhi.minimal q'' hq'' hB'_nz hB'_ss).1
                  exact False.elim ((not_lt_of_ge hmin) hlt)
            }⟩

end CategoryTheory.Triangulated
