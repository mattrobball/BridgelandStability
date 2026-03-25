/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.TStructure

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
    (hA_strict : IsStrictMono A.arrow) :
    wPhaseOf (W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ((a + b) / 2) <
      b - ε := by
  let AI : σ.slicing.IntervalCat C a b := (A : σ.slicing.IntervalCat C a b)
  have hA_ne : ¬IsZero AI.obj := hA_ss.2.1
  have hSES := interval_strictShortExact_cokernel_of_strictMono
    (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow hA_strict
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := σ.slicing) (a := a) (b := b) hSES
  have hab1 : b ≤ a + 1 := by linarith
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
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4) (hε8 : ε < 1 / 8)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E F : C}
    (hE : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E
      (wPhaseOf (W (K₀.of C E)) ((a + b) / 2)))
    (hF : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C F
      (wPhaseOf (W (K₀.of C F)) ((a + b) / 2)))
    (hgap : wPhaseOf (W (K₀.of C F)) ((a + b) / 2) <
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2))
    -- Enveloping: both phases in [a+ε, b−ε]
    (hE_lo : a + ε ≤ wPhaseOf (W (K₀.of C E)) ((a + b) / 2))
    (hE_hi : wPhaseOf (W (K₀.of C E)) ((a + b) / 2) ≤ b - ε)
    (hF_lo : a + ε ≤ wPhaseOf (W (K₀.of C F)) ((a + b) / 2))
    (hF_hi : wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ≤ b - ε)
    (f : E ⟶ F) : f = 0 := by
  -- Convert E to deformedPred using (a, b) as witness interval
  have hE_dp : σ.deformedPred C W hW ε
      (wPhaseOf (W (K₀.of C E)) ((a + b) / 2)) E :=
    Or.inr ⟨a, b, hab, hthin, hE_lo, hE_hi, hE⟩
  -- Convert F to deformedPred using (a, b) as witness interval
  have hF_dp : σ.deformedPred C W hW ε
      (wPhaseOf (W (K₀.of C F)) ((a + b) / 2)) F :=
    Or.inr ⟨a, b, hab, hthin, hF_lo, hF_hi, hF⟩
  -- Apply Lemma 7.6 (sorry-free)
  exact σ.hom_eq_zero_of_deformedPred C W hW hε hε2 hε8 hsin hE_dp hF_dp hgap f

/-! ### MDQ composition with quotient bound -/
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
  strictEpi :=
    Slicing.IntervalCat.comp_strictEpi
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
    have hA_ne_bot : A ≠ ⊥ := fun hA_bot =>
      hA_ss.2.1 (((σ.slicing.intervalProp C a b).ι).map_isZero
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
      subst hssf
      ext
      exact hom_eq_zero_of_enveloped_semistable
        (C := C) (σ := σ) (W := W) (hW := hW_stab) hab hε hε2 hε8 hthin hsin
        hA_ss hB'_ss hB'_lt_A hA_lo (le_of_lt hA_phase_upper) hB'_lo
        (le_of_lt (lt_trans hB'_lt_A hA_phase_upper))
        (A.arrow ≫ q').hom
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
      have hq'' : IsStrictEpi q'' :=
        interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) (cokernel.π A.arrow) q''
          (by simpa [q''] using hq')
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
      have hq'' : IsStrictEpi q'' :=
        interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) (cokernel.π A.arrow) q''
          (by simpa [q''] using hq')
      have hmin :
          wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α :=
        (hq.minimal q'' hq'' hB'_nz hB'_ss).1
      exact False.elim ((not_lt_of_ge hmin) hlt)

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
    -- The object E being split
    {E : σ.slicing.IntervalCat C a b}
    -- The σ-phase split data
    {X_hi E_lo : σ.slicing.IntervalCat C a b}
    {p_hi : X_hi ⟶ E} {p_lo : E ⟶ E_lo}
    (hp_lo : IsStrictEpi p_lo)
    -- σ-phase separation: X_hi has high phases, E_lo has low phases
    {t_cut : ℝ}
    (hX_hi_ge : σ.slicing.geProp C t_cut X_hi.obj)
    -- Distinguished triangle in C
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
      have hq'' : IsStrictEpi q'' :=
        interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) p_lo q''
          (by simpa [hq'_eq] using hq')
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
      have hq'' : IsStrictEpi q'' :=
        interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) p_lo q''
          (by simpa [hq'_eq] using hq')
      have hmin :
          wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α :=
        (hq.minimal q'' hq'' hB'_nz hB'_ss).1
      exact False.elim ((not_lt_of_ge hmin) hlt)

end CategoryTheory.Triangulated
