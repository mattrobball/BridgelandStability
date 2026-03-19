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

* `phiPlus_bound_of_destabilizing_subobject`: if `φ⁺(Y) ≤ ψ(Y) + ε` and `ψ(Y) < b−3ε`,
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
If `Y` is in `IntervalCat(a,b)` with `φ⁺(Y) ≤ ψ(Y) + ε` and `ψ(Y) < b − 3ε`,
and `A` is a W-semistable strict subobject with `ψ(A) > ψ(Y)`, then `ψ(A) < b − ε`.

**Proof**: `phiPlus_triangle_le` gives `φ⁺(A) ≤ φ⁺(Y)`. Phase confinement gives
`ψ(A) − ε < φ⁻(A) ≤ φ⁺(A)`. Combining: `ψ(A) < φ⁺(Y) + ε ≤ ψ(Y) + 2ε < b − ε`. -/
theorem phiPlus_bound_of_destabilizing_subobject
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {Y : σ.slicing.IntervalCat C a b} (hYne : ¬IsZero Y.obj)
    (hphiPlus : σ.slicing.phiPlus C Y.obj hYne ≤
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

/-- **Phase lower bound via Im argument** (generalized `wPhaseOf_gt_of_intervalProp`).

If `E ∈ P((c, d))` and every σ-semistable factor of phase `φ ∈ (c, d)` has
`W`-phase strictly between `ψ` and `ψ + 1`, then `wPhaseOf(W(E), α) > ψ`.

This replaces the `hα_ge : c - (c - ψ) ≤ α` condition in `wPhaseOf_gt_of_intervalProp`
with a direct width bound `ψ - 1 < wPhaseOf(W(E), α)`, which is derivable from
`U - L < 1` in the MDQ recursion context. -/
theorem wPhaseOf_gt_of_narrow_interval
    (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {α : ℝ} {ψ : ℝ}
    {c d : ℝ}
    (hI : σ.slicing.intervalProp C c d E)
    (hE_width : ψ - 1 < wPhaseOf (W (K₀.of C E)) α)
    (hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        c < φ → φ < d → W (K₀.of C F) ≠ 0)
    (hfactors : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        c < φ → φ < d →
        ψ < wPhaseOf (W (K₀.of C F)) α ∧
        wPhaseOf (W (K₀.of C F)) α < ψ + 1) :
    ψ < wPhaseOf (W (K₀.of C E)) α := by
  have him : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      c < φ → φ < d →
      0 < (W (K₀.of C F) *
        Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
    intro F φ hP hFne hcφ hφd
    obtain ⟨hlo, hhi⟩ := hfactors F φ hP hFne hcφ hφd
    have hWne := hW_ne F φ hP hFne hcφ hφd
    exact im_pos_of_phase_above (norm_pos_iff.mpr hWne) (wPhaseOf_compat _ _) hlo hhi
  have him_pos := im_W_pos_of_intervalProp C σ hE W hI him
  by_contra h
  push_neg at h
  set θ := wPhaseOf (W (K₀.of C E)) α
  have hw := wPhaseOf_compat (W (K₀.of C E)) α
  rw [hw] at him_pos
  rw [mul_assoc, ← Complex.exp_add] at him_pos
  have harg : ↑(Real.pi * θ) * Complex.I +
      -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (θ - ψ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero] at him_pos
  have hsin : Real.sin (Real.pi * (θ - ψ)) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hE_width])
  linarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (W (K₀.of C E))) hsin]

set_option maxHeartbeats 800000 in
/-- **MDQ existence with φ⁺ case split** (Bridgeland p.23).

Same recursion as `exists_strictMDQ_of_finiteLength` but replaces:
- `hHom` → perturbation data + W-semistable quotient lower bound
- `hDestabBound` → `phiPlus_bound_of_destabilizing_subobject` (when `φ⁺ ≤ ψ + ε`)

When `φ⁺(QS) > ψ(QS) + ε`, the σ-phase split branch applies. The degenerate cases
(X_hi = 0, Ahi = ⊤) are excluded by `wPhaseOf_gt_of_narrow_interval`. -/
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
    (hψ_X_lo : t_lo < wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α)
    -- Phase upper bound on X (from phiPlus < b - 4ε via wPhaseOf_lt_of_intervalProp)
    (hψ_X_upper : wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α < b - 3 * ε) :
    ∃ (B : σ.slicing.IntervalCat C a b) (q : X ⟶ B), IsStrictMDQ (C := C) σ ssf q := by
  -- Follow exists_strictMDQ_of_finiteLength (MDQ.lean:619-681)
  -- Key change: remove hψ_lo from the recursion predicate. Instead, derive
  -- t_lo < ψ(QS) AFTER the recursive call using: ψ(B) > t_lo (quotient bound)
  -- + ψ(B) ≤ ψ(cokernel(A.arrow)) < ψ(QS) (seesaw).
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  suffices h :
      ∀ (S : StrictSubobject X), ¬IsZero (cokernel S.1.arrow) →
        wPhaseOf (ssf.W (K₀.of C (cokernel S.1.arrow).obj)) ssf.α < b - 3 * ε →
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
    have hψ_S0 : wPhaseOf (ssf.W (K₀.of C (cokernel S0.1.arrow).obj)) ssf.α < b - 3 * ε := by
      -- cokernel(⊥.arrow) ≅ X, so ψ is the same
      have e0 : cokernel S0.1.arrow ≅ X := by
        rw [show ((⊥ : Subobject X).arrow) = 0 by simpa [S0, Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      have hiso : (cokernel S0.1.arrow).obj ≅ X.obj :=
        ((σ.slicing.intervalProp C a b).ι).mapIso e0
      have : ssf.W (K₀.of C (cokernel S0.1.arrow).obj) = ssf.W (K₀.of C X.obj) := by
        congr 1; exact K₀.of_iso C hiso
      rw [this]; exact hψ_X_upper
    obtain ⟨B, q, hq⟩ := h S0 hS0_ne hψ_S0 hQLo0
    let e0 : cokernel S0.1.arrow ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simpa [S0, Subobject.bot_arrow]]
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
      let ψQS : ℝ := wPhaseOf (ssf.W (K₀.of C QS.obj)) ssf.α
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
              wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α < b - ε := by
            subst hssf
            exact phiPlus_bound_of_destabilizing_subobject C σ W hW_stab hab hε hε2 hthin hsin
              hQS_obj_ne hphiPlus_QS hψ_QS_upper hA_ss hA_strict hA_phase_gt
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
          -- ψ upper bound for cokernel(Tsub.arrow) via iso to cokernel(A.arrow)
          have hψ_T_upper :
              wPhaseOf (ssf.W (K₀.of C (cokernel Tsub.arrow).obj)) ssf.α < b - 3 * ε := by
            have hiso_T : (cokernel Tsub.arrow).obj ≅ (cokernel A.arrow).obj :=
              ((σ.slicing.intervalProp C a b).ι).mapIso eT
            have : ssf.W (K₀.of C (cokernel Tsub.arrow).obj) =
                ssf.W (K₀.of C (cokernel A.arrow).obj) := by
              congr 1; exact K₀.of_iso C hiso_T
            rw [this]; linarith
          -- RECURSIVE CALL
          obtain ⟨B, qT, hqT⟩ := ih T hS_lt_T hQT_ne hψ_T_upper hQLo_T
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
        · -- Case 3: φ⁺(QS) > ψ(QS) + ε → φ⁺ SPLIT BRANCH
          push_neg at hphiPlus_QS -- hphiPlus_QS : ψQS + ε < φ⁺(QS)
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
              have hQS_width : ψQS - 1 < wPhaseOf (ssf.W (K₀.of C QS.obj)) ssf.α := by
                linarith
              -- Perturbation bounds for σ-semistable factors
              subst hssf
              have hpert := hperturb_of_stabSeminorm C σ W hW_stab
                (by linarith : b - a < 1) hε hε2 hsin
              -- Factor bounds: ψ_QS < ψ(F) < ψ_QS + 1 for F ∈ P(φ) with t_cut < φ < b
              have hfactors : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
                  t_cut < φ → φ < b →
                  ψQS < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
                  wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < ψQS + 1 := by
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
                  W (K₀.of C F) ≠ 0 := by
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
            -- Step 1: ψ(X_hi) > ψ(QS) via narrow interval Im argument
            have hψ_Xhi_gt : ψQS < wPhaseOf (ssf.W (K₀.of C X_hi)) ssf.α := by
              have hX_hi_narrow : σ.slicing.intervalProp C t_cut b X_hi :=
                σ.slicing.intervalProp_of_intrinsic_phases C hX_hi_ne
                  (σ.slicing.phiMinus_gt_of_gtProp C hX_hi_ne hX_hi_gt)
                  (hX_hi_phiPlus hX_hi_ne)
              -- Width bound: derive BEFORE subst so ssf.W/α match hWindow
              have hXhi_width : ψQS - 1 <
                  wPhaseOf (ssf.W (K₀.of C X_hi)) ssf.α := by
                have h1 := (hWindow hX_hi_int hX_hi_ne).1
                have h2 := (hWindow QS.property hQS_obj_ne).2
                linarith [hWidth]
              subst hssf
              have hpert := hperturb_of_stabSeminorm C σ W hW_stab
                (by linarith : b - a < 1) hε hε2 hsin
              have hfactors : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
                  t_cut < φ → φ < b →
                  ψQS < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
                  wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < ψQS + 1 := by
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
                  t_cut < φ → φ < b → W (K₀.of C F) ≠ 0 := by
                intro F φ hP hFne _ _
                exact σ.W_ne_zero_of_seminorm_lt_one C W hW_stab hP hFne
              exact wPhaseOf_gt_of_narrow_interval C σ hX_hi_ne W hX_hi_narrow
                hXhi_width hW_ne_narrow hfactors
            -- Step 2: ψ(Ahi) > ψ(QS) via iso transport Ahi ≅ X_hi_I
            have eAhi : (Ahi : σ.slicing.IntervalCat C a b) ≅ X_hi_I :=
              Subobject.isoOfEqMk Ahi f_hi_I rfl
            have hψ_Ahi_gt : ψQS <
                wPhaseOf (ssf.W (K₀.of C (Ahi : σ.slicing.IntervalCat C a b).obj))
                  ssf.α := by
              have hiso : (Ahi : σ.slicing.IntervalCat C a b).obj ≅ X_hi_I.obj :=
                ((σ.slicing.intervalProp C a b).ι).mapIso eAhi
              have : ssf.W (K₀.of C (Ahi : σ.slicing.IntervalCat C a b).obj) =
                  ssf.W (K₀.of C X_hi) := by
                congr 1; exact K₀.of_iso C hiso
              rw [this]; exact hψ_Xhi_gt
            -- Step 3: Seesaw → ψ(cokernel Ahi.arrow) < ψ(QS)
            have hψ_cokAhi_lt :
                wPhaseOf (ssf.W (K₀.of C (cokernel Ahi.arrow).obj)) ssf.α < ψQS :=
              ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
                (C := C) (σ := σ) (a := a) (b := b)
                hAhi_ne_bot hAhi_ne_top hAhi_strict hψ_Ahi_gt hW_interval hWindow hWidth
            -- Step 4: ψ upper bound for cokernel(Tsub.arrow) via iso to cokernel(Ahi.arrow)
            have hψ_T_upper :
                wPhaseOf (ssf.W (K₀.of C (cokernel Tsub.arrow).obj)) ssf.α <
                  b - 3 * ε := by
              have hiso_T : (cokernel Tsub.arrow).obj ≅ (cokernel Ahi.arrow).obj :=
                ((σ.slicing.intervalProp C a b).ι).mapIso eT
              have : ssf.W (K₀.of C (cokernel Tsub.arrow).obj) =
                  ssf.W (K₀.of C (cokernel Ahi.arrow).obj) := by
                congr 1; exact K₀.of_iso C hiso_T
              rw [this]; linarith
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
                wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
                  wPhaseOf (ssf.W (K₀.of C (cokernel Ahi.arrow).obj)) ssf.α :=
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
                  (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
                wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α ≤
                  wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α →
                Ahi.arrow ≫ q' = 0 := by
              intro B' q' hB'_ss hle
              have hψ_B'_lt : wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α < ψQS :=
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
                    wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
                      wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α
                · refine ⟨hle, ?_⟩
                  intro hEq
                  have hzero := hvanish_helper q' hB'_ss (by rw [hEq])
                  let q'' : cokernel Ahi.arrow ⟶ B' :=
                    cokernel.desc Ahi.arrow q' hzero
                  have hq'' : IsStrictEpi q'' := by
                    apply interval_strictEpi_of_strictEpi_comp
                      (C := C) (σ := σ) (a := a) (b := b)
                      (cokernel.π Ahi.arrow) q''
                      (isStrictEpi_cokernel Ahi.arrow)
                    simpa [q''] using hq'
                  obtain ⟨t, ht⟩ := (hqAhi.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
                  exact ⟨t, by
                    have h1 : q' = cokernel.π Ahi.arrow ≫ q'' := by
                      symm; exact cokernel.π_desc Ahi.arrow q' hzero
                    rw [h1, ht]; simp only [Category.assoc]⟩
                · have hlt :
                      wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
                        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α :=
                    lt_of_not_ge hle
                  have hzero := hvanish_helper q' hB'_ss (le_of_lt hlt)
                  let q'' : cokernel Ahi.arrow ⟶ B' :=
                    cokernel.desc Ahi.arrow q' hzero
                  have hq'' : IsStrictEpi q'' := by
                    apply interval_strictEpi_of_strictEpi_comp
                      (C := C) (σ := σ) (a := a) (b := b)
                      (cokernel.π Ahi.arrow) q''
                      (isStrictEpi_cokernel Ahi.arrow)
                    simpa [q''] using hq'
                  have hmin :
                      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
                        wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α :=
                    (hqAhi.minimal q'' hq'' hB'_nz hB'_ss).1
                  exact False.elim ((not_lt_of_ge hmin) hlt)
            }⟩

/-- **W-phase upper bound from φ⁺ bound.** If `E ∈ P((a, b))` with `φ⁺(E) < b - 4ε`
and the interval is wide enough (`6ε ≤ b - a`), then `ψ(E) < b - 3ε`.

Proof: `φ⁺(E) < b - 4ε` and `φ⁻(E) > a` give `E ∈ P((a, b-4ε))`.
Apply `wPhaseOf_lt_of_intervalProp` with interval `(a, b-4ε)` and perturbation `ε`.
The `hα_le` condition `(a+b)/2 ≤ (b-4ε) + ε = b-3ε` follows from `6ε ≤ b-a`. -/
theorem wPhaseOf_lt_of_phiPlus_lt
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (h_wide : 6 * ε ≤ b - a)
    {E : C} (hE : ¬IsZero E)
    (hI : σ.slicing.intervalProp C a b E)
    (hphiPlus : σ.slicing.phiPlus C E hE < b - 4 * ε) :
    wPhaseOf ((σ.skewedStabilityFunction_of_near C W hW hab).W (K₀.of C E))
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
      a < φ → φ < b - 4 * ε → W (K₀.of C F) ≠ 0 :=
    fun F φ hP hFne _ _ => σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  -- Perturbation at α = (a+b)/2 in the format for wPhaseOf_lt_of_intervalProp
  -- Factors at φ ∈ (a, b-4ε) ⊂ (a, b) get bounds at α = (a+b)/2 from hpert
  have hperturb_fmt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b - 4 * ε →
      (b - 4 * ε) + ε - 1 < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
      wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < (b - 4 * ε) + ε := by
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
  simp only [StabilityCondition.skewedStabilityFunction_of_near]
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
    (t : ℝ) (ht : a + ε ≤ t)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X)
    (hquot : ∀ {B : σ.slicing.IntervalCat C a b} (q : X ⟶ B),
      IsStrictEpi q → ¬IsZero B.obj →
        t < wPhaseOf ((σ.skewedStabilityFunction_of_near C W hW hab).W (K₀.of C B.obj))
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
            t < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α) →
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
    have hS_obj : ¬IsZero Y.obj := by
      intro hZ
      exact hS (Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
    by_cases hss : ssf.Semistable C Y.obj ψY
    · -- SEMISTABLE CASE: single-factor HN filtration (verbatim from Lemma77)
      refine ⟨HNFiltration.single C Y.obj ψY hss, ?_⟩
      intro j
      have hbot_ne_top : (⊥ : Subobject Y) ≠ ⊤ := by
        intro hEq
        exact (intervalSubobject_top_ne_bot_of_not_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hS) hEq.symm
      have hbot_strict : IsStrictMono ((⊥ : Subobject Y).arrow) :=
        intervalSubobject_bot_arrow_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b)
      have hbot_gt :
          t < wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α :=
        hquot ⊥ hbot_ne_top hbot_strict
      have hbot_eq :
          wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α = ψY := by
        let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
          rw [show ((⊥ : Subobject Y).arrow) = 0 by simpa [Subobject.bot_arrow]]
          exact cokernelZeroIsoTarget
        let eC : (cokernel ((⊥ : Subobject Y).arrow)).obj ≅ Y.obj :=
          (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
        simpa [ψY] using
          congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
      have hψY_hi : ψY < U := (hWindow Y.property hS_obj).2
      have hj_lt : j.val < 1 := by
        simpa [HNFiltration.single] using j.is_lt
      have hj0 : j.val = 0 := by omega
      have hj : j = ⟨0, by simpa [HNFiltration.single] using (show 0 < 1 by omega)⟩ :=
        Fin.ext hj0
      subst j
      have hψY_gt : t < ψY := by exact hbot_eq ▸ hbot_gt
      exact ⟨by simpa [HNFiltration.single] using hψY_gt, hψY_hi⟩
    · -- NON-SEMISTABLE CASE: find MDQ, extract kernel, recurse
      letI : IsStrictArtinianObject Y := (hFL Y).1
      letI : IsStrictNoetherianObject Y := (hFL Y).2
      -- Derive ψ(Y) < b - 3ε from φ⁺(Y) < b - 4ε
      have hψ_Y_upper : wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α < b - 3 * ε :=
        wPhaseOf_lt_of_phiPlus_lt C σ W hW hab hε hε2 hthin hsin h_wide hS_obj
          Y.property (hphiPlus_Y hS_obj)
      -- Derive ψ(Y) > t from quotient bound applied to ⊥
      have hψ_Y_lo : t < ψY := by
        have hbot_ne_top : (⊥ : Subobject Y) ≠ ⊤ := by
          intro hEq
          exact (intervalSubobject_top_ne_bot_of_not_isZero
            (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hS) hEq.symm
        have hbot_strict : IsStrictMono ((⊥ : Subobject Y).arrow) :=
          intervalSubobject_bot_arrow_strictMono
            (C := C) (s := σ.slicing) (a := a) (b := b)
        have hbot_gt := hquot ⊥ hbot_ne_top hbot_strict
        let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
          rw [show ((⊥ : Subobject Y).arrow) = 0 by simpa [Subobject.bot_arrow]]
          exact cokernelZeroIsoTarget
        let eC := (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
        have hbot_eq : wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj))
            ssf.α = ψY := by
          simpa [ψY] using congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
        linarith
      -- Construct hQuotLo_ss from hquot (weaken: all quotients → semistable quotients)
      have hQuotLo_ss : ∀ {B' : σ.slicing.IntervalCat C a b} (q' : Y ⟶ B'),
          IsStrictEpi q' → ¬IsZero B'.obj →
          ssf.Semistable C B'.obj (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
          t < wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α := by
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
      let ψB : ℝ := wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α
      have hψB_gt : t < ψB := by
        have hgtK :
            t < wPhaseOf (ssf.W (K₀.of C (cokernel K.arrow).obj)) ssf.α :=
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
            ψB < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
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
            wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α =
              wPhaseOf (ssf.W (K₀.of C (cokernel A'.arrow).obj)) ssf.α := by
          let eA : (A : σ.slicing.IntervalCat C a b) ≅ (A' : σ.slicing.IntervalCat C a b) :=
            (Subobject.mapMonoIso eK.hom A).symm
          have hw : A.arrow ≫ eK.hom = eA.hom ≫ A'.arrow := by
            simpa [eA, A', Subobject.mapMonoIso, Subobject.map_eq_mk_mono, Category.assoc]
          let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
            cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA eK hw
          let eC' :=
            (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC
          simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC')
        have hgtA' :
            ψB < wPhaseOf (ssf.W (K₀.of C (cokernel A'.arrow).obj)) ssf.α := by
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
        have hGj' : t < GK.φ ⟨j.val, hj⟩ ∧ GK.φ ⟨j.val, hj⟩ < U := by
          exact ⟨lt_trans hψB_gt hGj.1, hGj.2⟩
        simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hj] using hGj'
      · have hj_lt : j.val < GK.n + 1 := by
          simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor] using j.is_lt
        have hjEq : j.val = GK.n := by omega
        have hG_last : GK.n < H.n := by
          simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor] using
            (show GK.n < GK.n + 1 by omega)
        have hjLast : j = ⟨GK.n, hG_last⟩ := Fin.ext hjEq
        subst j
        have hjFalse : ¬GK.n < GK.n := by omega
        simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hjFalse,
          ψB] using ⟨hψB_gt, hψB_hi⟩
  -- BOOTSTRAP from S₀ = ⊤ to X (modified from Lemma77:251-303)
  have hS0_ne : ¬IsZero (S0.1 : σ.slicing.IntervalCat C a b) := by
    intro hZ
    let e0 : (S0.1 : σ.slicing.IntervalCat C a b) ≅ X := by
      exact asIso S0.1.arrow
    exact hX (hZ.of_iso e0.symm)
  -- Convert strict-epi hquot to subobject form
  have hS0_quot :
      ∀ A : Subobject (S0.1 : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
        IsStrictMono A.arrow →
        t < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
    intro A hA_top hA_strict
    let e0 : (S0.1 : σ.slicing.IntervalCat C a b) ≅ X := by
      exact asIso S0.1.arrow
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
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α =
          wPhaseOf (ssf.W (K₀.of C (cokernel A'.arrow).obj)) ssf.α := by
      let eA : (A : σ.slicing.IntervalCat C a b) ≅ (A' : σ.slicing.IntervalCat C a b) :=
        (Subobject.mapMonoIso e0.hom A).symm
      have hw : A.arrow ≫ e0.hom = eA.hom ≫ A'.arrow := by
        simpa [eA, A', Subobject.mapMonoIso, Subobject.map_eq_mk_mono, Category.assoc]
      let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
        cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA e0 hw
      let eC' :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC
      simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC')
    rw [hphase_A]
    -- Convert: apply hquot to cokernel.π A'.arrow (a strict epi from X)
    have hA'_nonzero : ¬IsZero (cokernel A'.arrow).obj := by
      intro hZ
      exact (interval_cokernel_nonzero_of_ne_top
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
