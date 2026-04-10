/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.Seminorm
public import BridgelandStability.StabilityFunction.Uniqueness
public import BridgelandStability.IntervalCategory.FiniteLength
public import BridgelandStability.TStructure.HeartAbelian

/-!
# Deformation of Stability Conditions — Setup

Setup for deformation of stability conditions (ε₀ extraction, phase confinement basics)
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

/-! ### Node 7.0: ε₀ extraction from local finiteness -/

/-- **Node 7.0: Extraction of ε₀**. Given a stability condition `σ`, extract a positive
real `ε₀ < 1/8` such that for all `t`, every object in `P((t - 4ε₀, t + 4ε₀))` has
finite length. The width `8ε₀` is chosen to fit inside the local finiteness
parameter `2η`. -/
@[informal "Test tag for CI workflow"]
theorem StabilityCondition.WithClassMap.exists_epsilon0 (σ : StabilityCondition.WithClassMap C v) :
    ∃ ε₀ : ℝ, ∃ hε₀ : 0 < ε₀, ∃ hε₀' : ε₀ < 1 / 8,
      ∀ t : ℝ,
        let a := t - 4 * ε₀
        let b := t + 4 * ε₀
        letI : Fact (a < b) := ⟨by
          dsimp [a, b]
          linarith⟩
        letI : Fact (b - a ≤ 1) := ⟨by
          dsimp [a, b]
          linarith⟩
        ∀ (E : σ.slicing.IntervalCat C a b),
          IsStrictArtinianObject E ∧ IsStrictNoetherianObject E := by
  obtain ⟨η, hη, hη', hlf⟩ := σ.locallyFinite.intervalFinite
  refine ⟨η / 4, by positivity, by linarith, ?_⟩
  intro t
  dsimp
  intro E
  let a : ℝ := t - 4 * (η / 4)
  let b : ℝ := t + 4 * (η / 4)
  have ha : a = t - η := by
    dsimp [a]
    ring
  have hb : b = t + η := by
    dsimp [b]
    ring
  letI : Fact (a < b) := ⟨by
    dsimp [a, b]
    linarith⟩
  letI : Fact (b - a ≤ 1) := ⟨by
    dsimp [a, b]
    linarith⟩
  suffices
      ∀ {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)],
        a = t - η → b = t + η →
        ∀ E : σ.slicing.IntervalCat C a b,
          IsStrictArtinianObject E ∧ IsStrictNoetherianObject E by
    simpa [a, b] using this (a := a) (b := b) ha hb E
  intro a b _ _ ha hb E
  subst a b
  simpa using hlf t E

/-- Variant of ε₀ extraction providing 2ε₀-intervals for the sector bound. -/
theorem StabilityCondition.WithClassMap.exists_epsilon0_sector (σ : StabilityCondition.WithClassMap C v) :
    ∃ ε₀ : ℝ, ∃ hε₀ : 0 < ε₀, ∃ hε₀' : ε₀ < 1 / 4,
      ∀ t : ℝ,
        let a := t - 2 * ε₀
        let b := t + 2 * ε₀
        letI : Fact (a < b) := ⟨by
          dsimp [a, b]
          linarith⟩
        letI : Fact (b - a ≤ 1) := ⟨by
          dsimp [a, b]
          linarith⟩
        ∀ (E : σ.slicing.IntervalCat C a b),
          IsStrictArtinianObject E ∧ IsStrictNoetherianObject E := by
  obtain ⟨η, hη, hη', hlf⟩ := σ.locallyFinite.intervalFinite
  refine ⟨η / 2, by positivity, by linarith, ?_⟩
  intro t
  dsimp
  intro E
  let a : ℝ := t - 2 * (η / 2)
  let b : ℝ := t + 2 * (η / 2)
  have ha : a = t - η := by
    dsimp [a]
    ring
  have hb : b = t + η := by
    dsimp [b]
    ring
  letI : Fact (a < b) := ⟨by
    dsimp [a, b]
    linarith⟩
  letI : Fact (b - a ≤ 1) := ⟨by
    dsimp [a, b]
    linarith⟩
  suffices
      ∀ {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)],
        a = t - η → b = t + η →
        ∀ E : σ.slicing.IntervalCat C a b,
          IsStrictArtinianObject E ∧ IsStrictNoetherianObject E by
    simpa [a, b] using this (a := a) (b := b) ha hb E
  intro a b _ _ ha hb E
  subst a b
  simpa using hlf t E

section FiniteLengthDefs

omit [IsTriangulated C]

/-- The local-finiteness input on windows of radius `2 ε₀`: every interval
`P((t - 2 ε₀, t + 2 ε₀))` has strict finite length. This is the thin-sector
hypothesis used to start the deformation argument. -/
def SectorFiniteLength (σ : StabilityCondition.WithClassMap C v) (ε₀ : ℝ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) : Prop :=
  ∀ t : ℝ,
    let a := t - 2 * ε₀
    let b := t + 2 * ε₀
    letI : Fact (a < b) := ⟨by
      dsimp [a, b]
      linarith⟩
    letI : Fact (b - a ≤ 1) := ⟨by
      dsimp [a, b]
      linarith⟩
    ∀ E : σ.slicing.IntervalCat C a b,
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E

/-- The wide local-finiteness input used in Bridgeland's p.24 Nodes 7.8–7.9: every interval of
radius `4 ε₀` has strict finite length. This is the witness needed to apply Lemma 7.7 in the
windows `P((t - 3 ε₀, t + 5 ε₀))` and `P((t - 3 ε₀, t + 5 ε₀ + δ))`. -/
def WideSectorFiniteLength (σ : StabilityCondition.WithClassMap C v) (ε₀ : ℝ)
    (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8) : Prop :=
  ∀ t : ℝ,
    let a := t - 4 * ε₀
    let b := t + 4 * ε₀
    letI : Fact (a < b) := ⟨by
      dsimp [a, b]
      linarith⟩
    letI : Fact (b - a ≤ 1) := ⟨by
      dsimp [a, b]
      linarith⟩
    ∀ E : σ.slicing.IntervalCat C a b,
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E

end FiniteLengthDefs

/-! ### Phase confinement for nearby stability conditions -/

/-- **Phase confinement**. If `d(σ.P, τ.P) < ε` and `E` is `τ`-semistable of phase `φ`,
then `E` lies in the `σ`-interval subcategory `P((φ - ε, φ + ε))`. This is the
fundamental input for the deformation construction. -/
theorem intervalProp_of_semistable_near (σ τ : StabilityCondition.WithClassMap C v) {E : C} {φ ε : ℝ}
    (hE : ¬IsZero E) (hτ : (τ.slicing.P φ) E)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε) :
    σ.slicing.intervalProp C (φ - ε) (φ + ε) E := by
  have hbds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hτ hd
  right
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  refine ⟨F, fun i ↦ ?_⟩
  have hP_bds := hbds.1
  have hM_bds := hbds.2
  rw [Set.mem_Ioo] at hP_bds hM_bds
  constructor
  · calc φ - ε < σ.slicing.phiMinus C E hE := hM_bds.1
      _ = F.φ ⟨F.n - 1, by lia⟩ := σ.slicing.phiMinus_eq C E hE F hn hlast
      _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
  · calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
      _ = σ.slicing.phiPlus C E hE :=
          (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
      _ < φ + ε := hP_bds.2

section

omit [IsTriangulated C]

/-- Embedding an interval in a wider one centered at the same point. -/
theorem intervalProp_widen (s : Slicing C) {E : C} {φ ε ε' : ℝ}
    (hI : s.intervalProp C (φ - ε) (φ + ε) E) (hle : ε ≤ ε') :
    s.intervalProp C (φ - ε') (φ + ε') E :=
  s.intervalProp_mono C (by linarith) (by linarith) hI

/-! ### Intrinsic phase bounds from interval membership -/

/-- If `E ∈ P((φ - ε, φ + ε))` and `E` is nonzero, then both `φ⁺(E)` and `φ⁻(E)` lie
in `(φ - ε, φ + ε)`. This uses the existing `phiPlus/phiMinus_gt/lt_of_intervalProp`
lemmas. -/
theorem phiPlus_phiMinus_in_interval (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {φ ε : ℝ} (hI : s.intervalProp C (φ - ε) (φ + ε) E) :
    φ - ε < s.phiPlus C E hE ∧ s.phiPlus C E hE < φ + ε ∧
    φ - ε < s.phiMinus C E hE ∧ s.phiMinus C E hE < φ + ε :=
  ⟨s.phiPlus_gt_of_intervalProp C hE hI, s.phiPlus_lt_of_intervalProp C hE hI,
   s.phiMinus_gt_of_intervalProp C hE hI, s.phiMinus_lt_of_intervalProp C hE hI⟩

end

/-- If `d(P, Q) < ε` and `E` is `τ`-semistable of phase `φ`, then both `σ.φ⁺(E)` and
`σ.φ⁻(E)` lie in `(φ - ε, φ + ε)`. -/
theorem phiPlus_phiMinus_near (σ τ : StabilityCondition.WithClassMap C v) {E : C} {φ ε : ℝ}
    (hE : ¬IsZero E) (hτ : (τ.slicing.P φ) E)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε) :
    φ - ε < σ.slicing.phiPlus C E hE ∧ σ.slicing.phiPlus C E hE < φ + ε ∧
    φ - ε < σ.slicing.phiMinus C E hE ∧ σ.slicing.phiMinus C E hE < φ + ε :=
  phiPlus_phiMinus_in_interval C σ.slicing hE
    (intervalProp_of_semistable_near C σ τ hE hτ hd)

/-! ### Distance bound infrastructure -/

/-- If `σ` and `τ` have pointwise phase bounds, then `d(P, Q) ≤ ε`. -/
theorem StabilityCondition.WithClassMap.slicingDist_le_of_near (σ τ : StabilityCondition.WithClassMap C v)
    {ε : ℝ}
    (hP : ∀ (E : C) (hE : ¬IsZero E),
      |σ.slicing.phiPlus C E hE - τ.slicing.phiPlus C E hE| ≤ ε)
    (hM : ∀ (E : C) (hE : ¬IsZero E),
      |σ.slicing.phiMinus C E hE - τ.slicing.phiMinus C E hE| ≤ ε) :
    slicingDist C σ.slicing τ.slicing ≤ ENNReal.ofReal ε :=
  slicingDist_le_of_phase_bounds C σ.slicing τ.slicing hP hM

end CategoryTheory.Triangulated
