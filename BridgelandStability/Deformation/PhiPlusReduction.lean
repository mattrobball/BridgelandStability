/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Deformation.TStructure

/-!
# Deformation of Stability Conditions — φ⁺ Reduction

Bridgeland p.23: the φ⁺ reduction for the MDQ recursion.

## Main results

* `phiPlus_bound_of_destabilizing_subobject`: if `φ⁺(Y) < ψ(Y) + ε` and `ψ(Y) < b−3ε`,
  then any destabilizing W-semistable strict subobject `A` has `ψ(A) < b−ε`. (sorry-free)
* `hom_eq_zero_of_enveloped_semistable`: Hom vanishing for two ssf-semistable objects
  whose W-phases are both in `[a+ε, b−ε]`. Uses `hom_eq_zero_of_deformedPred`. (sorry-free)
* `comp_of_destabilizing_with_quotient_bound`: MDQ composition lemma that replaces
  universal `hHom` with a quotient lower bound + deformedPred conversion. (sorry-free)
* `exists_strictMDQ_with_quotient_bound`: MDQ recursion using the new composition.
* `hn_exists_with_phiPlus_reduction`: HN existence dropping `hHom`/`hDestabBound`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### φ⁺ bound on destabilizing subobjects -/

/-- **φ⁺ bound on destabilizing subobjects** (Bridgeland p.23).
If `Y` is in `IntervalCat(a,b)` with `φ⁺(Y) < ψ(Y) + ε` and `ψ(Y) < b − 3ε`,
and `A` is a W-semistable strict subobject with `ψ(A) > ψ(Y)`, then `ψ(A) < b − ε`.

**Proof**: `phiPlus_triangle_le` gives `φ⁺(A) ≤ φ⁺(Y)`. Phase confinement gives
`ψ(A) − ε < φ⁻(A) ≤ φ⁺(A)`. Combining: `ψ(A) < φ⁺(Y) + ε < ψ(Y) + 2ε < b − ε`. -/
theorem phiPlus_bound_of_destabilizing_subobject
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {Y : σ.slicing.IntervalCat C a b} (hYne : ¬IsZero Y.obj)
    (hphiPlus : σ.slicing.phiPlus C Y.obj hYne <
      wPhaseOf (W (K₀.of C Y.obj)) ((a + b) / 2) + ε)
    (hψ_upper : wPhaseOf (W (K₀.of C Y.obj)) ((a + b) / 2) < b - 3 * ε)
    {A : Subobject Y}
    (hA_ss : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C
      (A : σ.slicing.IntervalCat C a b).obj
      (wPhaseOf (W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ((a + b) / 2)))
    (hA_strict : IsStrictMono A.arrow)
    (_hA_dest : wPhaseOf (W (K₀.of C Y.obj)) ((a + b) / 2) <
      wPhaseOf (W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ((a + b) / 2)) :
    wPhaseOf (W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ((a + b) / 2) <
      b - ε := by
  let AI : σ.slicing.IntervalCat C a b := (A : σ.slicing.IntervalCat C a b)
  have hA_ne : ¬IsZero AI.obj := hA_ss.2.1
  have hSES := interval_strictShortExact_cokernel_of_strictMono
    (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow hA_strict
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := σ.slicing) (a := a) (b := b) hSES
  have hab1 : b ≤ a + 1 := by linarith [Fact.out (p := b - a ≤ 1)]
  have hphiPlus_le := σ.slicing.phiPlus_triangle_le C hA_ne hYne
    hab1 AI.property (cokernel A.arrow).property hT
  have hconf := phase_confinement_from_stabSeminorm C σ W hW hab hε hε2 hthin hsin hA_ss
  have hmin_le_max := σ.slicing.phiMinus_le_phiPlus C AI.obj hA_ne
  linarith

/-! ### Hom vanishing for enveloped ssf-semistable objects -/

/-- Hom vanishing for two ssf-semistable objects whose W-phases are both in `[a+ε, b−ε]`.
Converts both to `deformedPred` using `(a, b)` as the witness interval, then applies
`hom_eq_zero_of_deformedPred`.

This is the localized version of `hHom` that avoids the universal quantifier problem:
it only requires the enveloping condition for the two specific objects involved. -/
theorem hom_eq_zero_of_enveloped_semistable
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4) (hε8 : ε < 1 / 8)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E F : σ.slicing.IntervalCat C a b}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    (hssf : ssf = σ.skewedStabilityFunction_of_near C W hW hab)
    (hE : ssf.Semistable C E.obj (wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α))
    (hF : ssf.Semistable C F.obj (wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α))
    (hgap : wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α)
    -- Enveloping: both phases in [a+ε, b−ε]
    (hE_lo : a + ε ≤ wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α)
    (hE_hi : wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α ≤ b - ε)
    (hF_lo : a + ε ≤ wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α)
    (hF_hi : wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α ≤ b - ε)
    (f : E ⟶ F) : f = 0 := by
  subst hssf
  -- Convert E to deformedPred using (a, b) as witness interval
  have hE_dp : σ.deformedPred C W hW ε hε hε2 hsin
      (wPhaseOf (W (K₀.of C E.obj)) ((a + b) / 2)) E.obj :=
    Or.inr ⟨a, b, hab, hthin, hE_lo, hE_hi, hE⟩
  -- Convert F to deformedPred using (a, b) as witness interval
  have hF_dp : σ.deformedPred C W hW ε hε hε2 hsin
      (wPhaseOf (W (K₀.of C F.obj)) ((a + b) / 2)) F.obj :=
    Or.inr ⟨a, b, hab, hthin, hF_lo, hF_hi, hF⟩
  -- Apply Lemma 7.6 (sorry-free)
  have h0 := σ.hom_eq_zero_of_deformedPred C W hW hε hε2 hε8 hsin hE_dp hF_dp hgap f.hom
  ext; exact h0

/-! ### MDQ composition with quotient bound -/

variable [IsTriangulated C] in
/-- MDQ composition with quotient-bound Hom vanishing (Bridgeland p.23).

Same as `comp_of_destabilizing_semistable_subobject` but replaces the universal `hHom`
with a quotient lower bound: all W-semistable strict quotients of `X` have `ψ > t_lo`.
Combined with `ψ(A) < U_hom`, both objects are in `[a+ε, b−ε]`, enabling
`hom_eq_zero_of_deformedPred` for Hom vanishing.

This avoids the unsolvable universal hHom problem (which requires interval independence
for objects near the boundary `a`). -/
theorem comp_of_destabilizing_with_quotient_bound
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
    -- Perturbation data for deformedPred conversion
    (W : K₀ C →+ ℂ) (hW_stab : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4) (hε8 : ε < 1 / 8)
    (hab : a < b) (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hssf : ssf = σ.skewedStabilityFunction_of_near C W hW_stab hab)
    -- Quotient lower bound
    {t_lo : ℝ} (ht_lo : a + ε ≤ t_lo)
    {X : σ.slicing.IntervalCat C a b}
    -- Phase lower bound on X itself (from outer recursion's quotient lower bound on ⊥)
    (hψ_X_lo : t_lo < wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α)
    (hQuotLo : ∀ {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B'),
      IsStrictEpi q' → ¬IsZero B'.obj →
      ssf.Semistable C B'.obj (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
      t_lo < wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α)
    -- Destabilizing subobject data
    {A : Subobject X}
    (hA_ss : ssf.Semistable C (A : σ.slicing.IntervalCat C a b).obj
      (wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α))
    (hA_strict : IsStrictMono A.arrow)
    (hA_phase : wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hA_top : A ≠ ⊤)
    (hA_phase_upper :
      wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α < b - ε)
    -- MDQ on cokernel
    {B : σ.slicing.IntervalCat C a b} {q : cokernel A.arrow ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q) :
    IsStrictMDQ (C := C) σ ssf (cokernel.π A.arrow ≫ q) where
  strictEpi := by
    exact Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π A.arrow) q
      (isStrictEpi_cokernel A.arrow) hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    -- Setup (same as original comp_of_destabilizing)
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
          hA_ne_bot hA_top hA_strict hA_phase hW_interval hWindow hWidth)
        hA_phase
    have hB_lt_A :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
      lt_of_le_of_lt hB_le_cok hCok_lt_A
    -- KEY NEW CONTENT: local Hom vanishing via deformedPred
    -- B' is a W-semistable strict quotient of X → quotient lower bound applies
    have hB'_lo : a + ε ≤ wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α :=
      le_of_lt (lt_of_le_of_lt ht_lo (hQuotLo q' hq' hB'_nz hB'_ss))
    -- A has ψ(A) > ψ(X) > t_lo ≥ a + ε (using hA_phase and hψ_X_lo)
    have hA_lo : a + ε ≤ wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
      le_of_lt (lt_of_le_of_lt ht_lo (lt_trans hψ_X_lo hA_phase))
    -- Helper: prove A.arrow ≫ q' = 0 via deformedPred
    have hvanish : ∀ (hB'_lt_A :
        wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α),
        A.arrow ≫ q' = 0 := by
      intro hB'_lt_A
      exact hom_eq_zero_of_enveloped_semistable (C := C) σ W hW_stab hab hε hε2 hε8 hthin hsin
        hssf hA_ss hB'_ss hB'_lt_A hA_lo (le_of_lt hA_phase_upper) hB'_lo
        (le_of_lt (lt_trans (by linarith [hB_lt_A]) hA_phase_upper))
        (A.arrow ≫ q')
    -- Case split (same structure as original)
    by_cases hle :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α
    · refine ⟨hle, ?_⟩
      intro hEq
      have hB'_lt_A :
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
            wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
        rw [hEq]; exact hB_lt_A
      have hzero : A.arrow ≫ q' = 0 := hvanish hB'_lt_A
      let q'' : cokernel A.arrow ⟶ B' := cokernel.desc A.arrow q' hzero
      have hq'' : IsStrictEpi q'' := by
        apply interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) (cokernel.π A.arrow) q''
          (isStrictEpi_cokernel A.arrow)
        simpa [q''] using hq'
      obtain ⟨t, ht⟩ := (hq.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
      refine ⟨t, ?_⟩
      calc
        q' = cokernel.π A.arrow ≫ q'' := by
          symm; exact cokernel.π_desc A.arrow q' hzero
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
      have hzero : A.arrow ≫ q' = 0 := hvanish hB'_lt_A
      let q'' : cokernel A.arrow ⟶ B' := cokernel.desc A.arrow q' hzero
      have hq'' : IsStrictEpi q'' := by
        apply interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) (cokernel.π A.arrow) q''
          (isStrictEpi_cokernel A.arrow)
        simpa [q''] using hq'
      have hmin :
          wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α :=
        (hq.minimal q'' hq'' hB'_nz hB'_ss).1
      exact False.elim ((not_lt_of_ge hmin) hlt)

variable [IsTriangulated C] in
/-- **MDQ lifting through σ-phase split** (Bridgeland p.23 "I can always assume φ⁺(E) < ψ(E)+ε").

Given `E ∈ IntervalCat(a,b)` with a strict SES `0 → X_hi → E → E_lo → 0` from the
σ-phase split at cutoff `t_cut`, where `X_hi ∈ geProp(t_cut)` and `E_lo ∈ leProp(t_cut)`,
and an MDQ `q : E_lo → B` for `E_lo`, the composite `E ↠ E_lo ↠ B` is an MDQ for `E`.

**Proof sketch** (Bridgeland p.23): For any W-semistable quotient `p : E → B'`
with `ψ(B') ≤ ψ(B)`: phase confinement gives `φ⁺(B') < ψ(B') + ε ≤ ψ(B) + ε`.
Since `B` is a quotient of `E_lo` (all σ-phases `≤ t_cut`), the seesaw on the split
gives `ψ(B) ≤ ψ(E)`, hence `φ⁺(B') < ψ(E) + ε = t_cut`. So `B' ∈ ltProp(t_cut)`
while `X_hi ∈ geProp(t_cut)`, giving `Hom(X_hi, B') = 0` by
`zero_of_geProp_ltProp_general`. Hence `E → B'` factors through `E → E_lo → B'`. -/
theorem mdq_of_sigma_phase_split
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
    -- The object E being split
    {E : σ.slicing.IntervalCat C a b}
    -- The σ-phase split data
    {X_hi E_lo : σ.slicing.IntervalCat C a b}
    {p_hi : X_hi ⟶ E} {p_lo : E ⟶ E_lo}
    (_hp_hi : IsStrictMono p_hi) (hp_lo : IsStrictEpi p_lo)
    -- σ-phase separation: X_hi has high phases, E_lo has low phases
    {t_cut : ℝ}
    (hX_hi_ge : σ.slicing.geProp C t_cut X_hi.obj)
    (_hE_lo_lt : σ.slicing.ltProp C t_cut E_lo.obj)
    -- Distinguished triangle in C
    {δ : E_lo.obj ⟶ X_hi.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk p_hi.hom p_lo.hom δ ∈ distTriang C)
    -- Cokernel compatibility: p_lo is the cokernel of p_hi (from the strict SES)
    (hcokernel : ∀ {D : σ.slicing.IntervalCat C a b} (f : E ⟶ D),
      p_hi ≫ f = 0 → ∃ r : E_lo ⟶ D, f = p_lo ≫ r)
    -- MDQ of the low part
    {B : σ.slicing.IntervalCat C a b} {q : E_lo ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    -- Phase confinement: W-semistable objects with ψ ≤ ψ(B) have all σ-phases < t_cut
    -- (follows from phiPlus_lt_of_wSemistable + ψ(B) + ε ≤ t_cut at the call site)
    (hPhaseConf : ∀ {F : σ.slicing.IntervalCat C a b}
      (_ : ssf.Semistable C F.obj (wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α)),
      wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α →
      σ.slicing.ltProp C t_cut F.obj) :
    IsStrictMDQ (C := C) σ ssf (p_lo ≫ q) where
  strictEpi :=
    Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
      p_lo q hp_lo hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    -- Helper: prove p_hi.hom ≫ q'.hom = 0 when ψ(B') ≤ ψ(B)
    -- X_hi ∈ geProp(t_cut), B' ∈ ltProp(t_cut) from hPhaseConf → Hom = 0
    have hvanish : wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α →
        p_hi.hom ≫ q'.hom = 0 := by
      intro hle
      have hB'_lt := hPhaseConf hB'_ss hle
      exact σ.slicing.zero_of_geProp_ltProp_general C t_cut
        hX_hi_ge hB'_lt (p_hi.hom ≫ q'.hom)
    -- Case split
    by_cases hle :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α
    · refine ⟨hle, ?_⟩
      intro hEq
      -- ψ(B') = ψ(B), so B' ∈ ltProp(t_cut)
      have hzero_C : p_hi.hom ≫ q'.hom = 0 := hvanish (le_of_eq hEq)
      -- Factor E → B' through E_lo
      have hzero : p_hi ≫ q' = 0 := by ext; exact hzero_C
      -- p_hi is the kernel inclusion: cokernel(p_hi) ≅ E_lo via p_lo
      -- The factoring: q' factors through p_lo because the short complex is exact
      -- p_hi ≫ q' = 0 means q'.hom factors through cokernel(p_hi.hom) in C.
      -- In IntervalCat, p_lo is the cokernel of p_hi (from the strict SES).
      -- So q' factors through p_lo.
      -- Factor q' through p_lo using cokernel property
      obtain ⟨q'', hq'_eq⟩ := hcokernel q' hzero
      have hq'' : IsStrictEpi q'' := by
        apply interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) p_lo q'' hp_lo
        simpa [hq'_eq] using hq'
      obtain ⟨t, ht⟩ := (hq.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
      refine ⟨t, ?_⟩
      calc q' = p_lo ≫ q'' := hq'_eq
        _ = p_lo ≫ (q ≫ t) := by rw [ht]
        _ = (p_lo ≫ q) ≫ t := by rw [Category.assoc]
    · have hlt :
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
            wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α :=
        lt_of_not_ge hle
      have hzero_C : p_hi.hom ≫ q'.hom = 0 := hvanish (le_of_lt hlt)
      have hzero : p_hi ≫ q' = 0 := by ext; exact hzero_C
      -- Factor through p_lo → MDQ minimality → contradiction
      obtain ⟨q'', hq'_eq⟩ := hcokernel q' hzero
      have hq'' : IsStrictEpi q'' := by
        apply interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) p_lo q'' hp_lo
        simpa [hq'_eq] using hq'
      have hmin :
          wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α :=
        (hq.minimal q'' hq'' hB'_nz hB'_ss).1
      exact False.elim ((not_lt_of_ge hmin) hlt)

set_option maxHeartbeats 800000 in
/-- **MDQ existence with φ⁺ case split** (Bridgeland p.23).

Same recursion as `exists_strictMDQ_of_finiteLength` but replaces:
- `hHom` → perturbation data + W-semistable quotient lower bound
- `hDestabBound` → `phiPlus_bound_of_destabilizing_subobject` (when `φ⁺ < ψ + ε`)

When `φ⁺(QS) ≥ ψ(QS) + ε`, the σ-phase split branch applies (sorry: requires σ-phase
splitting infrastructure). -/
theorem exists_strictMDQ_with_quotient_bound
    [IsTriangulated C]
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
    -- Perturbation data (replaces hHom)
    (W : K₀ C →+ ℂ) (hW_stab : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
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
      ssf.Semistable C B'.obj (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
      t_lo < wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α)
    -- Phase lower bound on X (derived from quotient lower bound on ⊥ in caller)
    (hψ_X_lo : t_lo < wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α) :
    ∃ (B : σ.slicing.IntervalCat C a b) (q : X ⟶ B), IsStrictMDQ (C := C) σ ssf q := by
  -- Follow exists_strictMDQ_of_finiteLength (MDQ.lean:619-681)
  -- Key change: remove hψ_lo from the recursion predicate. Instead, derive
  -- t_lo < ψ(QS) AFTER the recursive call using: ψ(B) > t_lo (quotient bound)
  -- + ψ(B) ≤ ψ(cokernel(A.arrow)) < ψ(QS) (seesaw).
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  suffices h :
      ∀ (S : StrictSubobject X), ¬IsZero (cokernel S.1.arrow) →
        (∀ {B' : σ.slicing.IntervalCat C a b} (q' : cokernel S.1.arrow ⟶ B'),
          IsStrictEpi q' → ¬IsZero B'.obj →
          ssf.Semistable C B'.obj (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
          t_lo < wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
        ∃ (B : σ.slicing.IntervalCat C a b) (q : cokernel S.1.arrow ⟶ B),
          IsStrictMDQ (C := C) σ ssf q by
    let S0 : StrictSubobject X := ⟨⊥,
      intervalSubobject_bot_arrow_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b)⟩
    have hS0_ne : ¬IsZero (cokernel S0.1.arrow) := by
      let e0 : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
        rw [show ((⊥ : Subobject X).arrow) = 0 by simpa [Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      intro hZ; exact hX (hZ.of_iso e0.symm)
    have hQLo0 : ∀ {B' : σ.slicing.IntervalCat C a b} (q' : cokernel S0.1.arrow ⟶ B'),
        IsStrictEpi q' → ¬IsZero B'.obj →
        ssf.Semistable C B'.obj (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
        t_lo < wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α := by
      intro B' q' hq' hB'_ne hB'_ss
      let e0 : cokernel S0.1.arrow ≅ X := by
        rw [show ((⊥ : Subobject X).arrow) = 0 by simpa [S0, Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      exact hQuotLo_ss (e0.inv ≫ q')
        (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
          e0.inv q' (isStrictEpi_of_isIso (f := e0.inv)) hq') hB'_ne hB'_ss
    obtain ⟨B, q, hq⟩ := h S0 hS0_ne hQLo0
    let e0 : cokernel S0.1.arrow ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simpa [S0, Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    exact ⟨B, e0.inv ≫ q,
      IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b) hq e0.symm⟩
  intro S
  induction S using IsWellFounded.induction
      (· > · : StrictSubobject X → StrictSubobject X → Prop) with
  | ind S ih =>
      intro hQS_ne hQLo_S
      let QS : σ.slicing.IntervalCat C a b := cokernel S.1.arrow
      letI : IsStrictArtinianObject QS := (hFiniteLength QS).1
      letI : IsStrictNoetherianObject QS := (hFiniteLength QS).2
      let ψQS : ℝ := wPhaseOf (ssf.W (K₀.of C QS.obj)) ssf.α
      have hQS_obj_ne : ¬IsZero QS.obj := by
        intro hZ; exact hQS_ne (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
      by_cases hQS_ss : ssf.Semistable C QS.obj ψQS
      · exact ⟨QS, 𝟙 _, IsStrictMDQ.id_of_semistable
          (C := C) (σ := σ) (a := a) (b := b) hW_interval hWindow hWidth hQS_ss⟩
      · by_cases hphiPlus_QS :
            σ.slicing.phiPlus C QS.obj hQS_obj_ne < ψQS + ε ∧ ψQS < b - 3 * ε
        · -- DESTABILIZING BRANCH (φ⁺(QS) < ψ(QS) + ε AND ψ(QS) < b - 3ε)
          obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hA_ss, hA_phase_gt, _⟩ :=
            ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
              (C := C) (σ := σ) (a := a) (b := b) (X := QS) hQS_ne hQS_ss hW_interval
          have hA_phase_upper :
              wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α < b - ε := by
            subst hssf
            exact phiPlus_bound_of_destabilizing_subobject C σ W hW_stab hab hε hε2 hthin hsin
              hQS_obj_ne hphiPlus_QS.1 hphiPlus_QS.2 hA_ss hA_strict hA_phase_gt
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
              ssf.Semistable C B'.obj (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
              t_lo < wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α := by
            intro B' q' hq' hB'_ne hB'_ss
            exact hQLo_S (cokernel.π A.arrow ≫ (eT.inv ≫ q'))
              (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
                (cokernel.π A.arrow) (eT.inv ≫ q')
                (isStrictEpi_cokernel A.arrow)
                (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
                  eT.inv q' (isStrictEpi_of_isIso (f := eT.inv)) hq'))
              hB'_ne hB'_ss
          -- Propagate class H upper bound via seesaw
          have hψ_cok_lt : wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α < ψQS :=
            ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
              (C := C) (σ := σ) (a := a) (b := b)
              hA_ne_bot hA_ne_top hA_strict hA_phase_gt hW_interval hWindow hWidth
          -- RECURSIVE CALL
          obtain ⟨B, qT, hqT⟩ := ih T hS_lt_T hQT_ne hQLo_T
          let qA : cokernel A.arrow ⟶ B := eT.inv ≫ qT
          have hqA : IsStrictMDQ (C := C) σ ssf qA :=
            IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b) hqT eT.symm
          -- Derive t_lo < ψ(QS) from: ψ(B) > t_lo + ψ(B) ≤ ψ(cok(A)) < ψ(QS)
          have hB_phase_lo : t_lo < wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α :=
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
            have hB_le_cok : wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
                wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α :=
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
        · -- Case 3: φ⁺(QS) ≥ ψ(QS) + ε OR ψ(QS) ≥ b - 3ε → φ⁺ SPLIT BRANCH
          -- Extract σ-HN filtration from QS.property (intervalProp definition)
          rcases QS.property with hQSZ | ⟨F_QS, hF_QS⟩
          · exact absurd hQSZ (by
              intro hZ; exact hQS_ne (Slicing.IntervalCat.isZero_of_obj_isZero
                (C := C) (s := σ.slicing) (a := a) (b := b)
                (((σ.slicing.intervalProp C a b).ι).map_isZero
                  (Slicing.IntervalCat.isZero_of_obj_isZero
                    (C := C) (s := σ.slicing) (a := a) (b := b) hZ))))
          · have hFn : 0 < F_QS.n := by
              by_contra h; push_neg at h
              exact hQS_obj_ne (F_QS.toPostnikovTower.zero_isZero (show F_QS.n = 0 by omega))
            -- Split at cutoff t_cut = ψQS + ε
            let t_cut : ℝ := ψQS + ε
            obtain ⟨X_hi, QS_lo, f_hi, g_lo, δ_split, hT_split, hX_hi_gt, hQS_lo_le,
                hX_hi_phiPlus⟩ :=
              σ.slicing.exists_split_at_cutoff C F_QS hF_QS hFn (t := t_cut)
            -- X_hi ∈ gtProp(t_cut), QS_lo ∈ leProp(t_cut)
            -- Both are in P((a, b)) since their σ-phases come from F_QS which has phases in (a, b)
            -- The composition QS → QS_lo → B is MDQ for QS via σ-phase Hom vanishing
            -- (Hom(X_hi, B') = 0 for any W-semistable B' with ψ(B') ≤ ψ(QS))
            -- This requires: X_hi and QS_lo in IntervalCat(a,b), strict SES,
            -- σ-phase factoring, recursive MDQ for QS_lo, well-foundedness
            -- Case split on X_hi being zero (degenerate split)
            by_cases hX_hi_zero : IsZero X_hi
            · -- X_hi = 0: the split is trivial, QS ≅ QS_lo.
              -- mor₂ of the triangle is an iso.
              haveI : IsIso (Triangle.mk f_hi g_lo δ_split).mor₂ :=
                (Triangle.isZero₁_iff_isIso₂ _ hT_split).mp hX_hi_zero
              -- QS_lo is nonzero (since QS is nonzero)
              -- The MDQ of QS can be obtained by composing with the iso.
              -- But this case (ψ ≥ b-3ε, φ⁺ < ψ+ε) requires the paper's class H
              -- framework: these objects don't arise in the HN recursion for inner-strip
              -- objects. Sorry: class H exclusion argument.
              sorry
            · -- X_hi ≠ 0: genuine σ-phase split
              have hX_hi_ne : ¬IsZero X_hi := hX_hi_zero
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
                -- Ahi ≅ X_hi_I (from Subobject.mk), so X_hi is zero — contradiction
                sorry
              have hAhi_ne_top : Ahi ≠ ⊤ := by
                -- If Ahi = ⊤ then f_hi_I is iso, so g_lo_I = 0 (from triangle),
                -- so QS_lo = 0. But QS_lo ∈ leProp(t_cut) captures the low σ-phases.
                -- If X_hi ≠ 0, there exist phases > t_cut, so not all of QS.
                -- Actually: Ahi = ⊤ means X_hi ≅ QS. Then QS has all phases > t_cut.
                -- But QS ∈ P((a,b)) has phases in (a,b). And φ⁺(QS) ≥ ψQS + ε
                -- (we're in the ¬hphiPlus_QS branch). But Ahi = ⊤ means QS ∈ gtProp(t_cut),
                -- and QS is semistable iff it has a single phase. But QS is NOT semistable
                -- (by hQS_ss). So QS has multiple phases, some > t_cut and some ≤ t_cut.
                -- Wait, Ahi = ⊤ means ALL of QS has phases > t_cut (X_hi = QS).
                -- Then QS_lo = 0. But then QS has all phases > t_cut = ψQS + ε.
                -- Phase confinement: phiPlus(QS) < ψQS + ε ← contradicts φ⁺ ≥ ψ + ε?
                -- Actually, φ⁺(QS) is phiPlus. If all phases > ψQS + ε:
                -- phiMinus > ψQS + ε > ψQS. But phase confinement of any semistable
                -- FACTOR says phase - ε < ψ of that factor < phase + ε.
                -- If QS has all σ-phases > ψQS + ε, then phiMinus > ψQS + ε.
                -- Phase confinement for QS itself: ψQS - ε < phiMinus.
                -- So ψQS + ε < phiMinus < ... ψQS - ε < phiMinus ← contradiction
                -- with phiMinus > ψQS + ε if ψQS + ε > ψQS - ε, which is always true.
                -- Hmm, this doesn't directly give a contradiction.
                sorry
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
                  ssf.Semistable C B'.obj (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
                  t_lo < wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α := by
                intro B' q' hq' hB'_ne hB'_ss
                exact hQLo_S (cokernel.π Ahi.arrow ≫ (eT.inv ≫ q'))
                  (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
                    (cokernel.π Ahi.arrow) (eT.inv ≫ q')
                    (isStrictEpi_cokernel Ahi.arrow)
                    (Slicing.IntervalCat.comp_strictEpi (C := C) (s := σ.slicing) (a := a) (b := b)
                      eT.inv q' (isStrictEpi_of_isIso (f := eT.inv)) hq'))
                  hB'_ne hB'_ss
              -- Recursive call
              obtain ⟨B, qT, hqT⟩ := ih T hS_lt_T hQT_ne hQLo_T
              let qAhi : cokernel Ahi.arrow ⟶ B := eT.inv ≫ qT
              have hqAhi : IsStrictMDQ (C := C) σ ssf qAhi :=
                IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b) hqT eT.symm
              -- Final composition: need to relate cokernel(Ahi.arrow) to QS_lo_I
              -- and apply mdq_of_sigma_phase_split (or direct iso transport)
              sorry -- iso cokernel(Ahi.arrow) ≅ QS_lo_I + mdq_of_sigma_phase_split

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
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4) (hε8 : ε < 1 / 8)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hFL : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      (σ.skewedStabilityFunction_of_near C W hW hab).W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf ((σ.skewedStabilityFunction_of_near C W hW hab).W (K₀.of C F))
        (σ.skewedStabilityFunction_of_near C W hW hab).α ∧
        wPhaseOf ((σ.skewedStabilityFunction_of_near C W hW hab).W (K₀.of C F))
          (σ.skewedStabilityFunction_of_near C W hW hab).α < U)
    (hWidth : U - L < 1)
    (t : ℝ)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X)
    (hquot : ∀ {B : σ.slicing.IntervalCat C a b} (q : X ⟶ B),
      IsStrictEpi q → ¬IsZero B.obj →
        t < wPhaseOf ((σ.skewedStabilityFunction_of_near C W hW hab).W (K₀.of C B.obj))
          (σ.skewedStabilityFunction_of_near C W hW hab).α) :
    let ssf := σ.skewedStabilityFunction_of_near C W hW hab
    let Psem : ℝ → ObjectProperty C := fun ψ F => ssf.Semistable C F ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, t < G.φ j ∧ G.φ j < U := by
  -- Follows hn_exists_in_thin_interval_of_quotientLowerBound (Lemma77.lean:33)
  -- using exists_strictMDQ_with_quotient_bound instead of exists_strictMDQ_of_finiteLength.
  -- The structure is identical: well-founded induction on StrictSubobject X (descending),
  -- find MDQ at each step, extract kernel, lift to smaller subobject, recurse.
  -- The only change: exists_strictMDQ_with_quotient_bound replaces exists_strictMDQ_of_finiteLength,
  -- taking perturbation data + quotient lower bound instead of hHom + hDestabBound.
  sorry -- Follows Lemma77.lean:33-250 verbatim with the MDQ call swapped.

end CategoryTheory.Triangulated
