/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.FirstStrictSES

/-!
# Deformation of Stability Conditions — StrictSES

Lower inclusion, interval inclusion, target subinterval, target envelope
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

section

variable [IsTriangulated C]

namespace SkewedStabilityFunction

/-- A convenient left-heart version of the first strict short exact sequence wrapper. If the
left-heart image of `X` has finite subobject lattice, then `X` admits Bridgeland's first strict
short exact sequence whenever it is not `W`-semistable. -/
theorem exists_first_strictShortExact_of_not_semistable_of_finite_leftHeartSubobjects
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hX_left : Finite (Subobject ((Slicing.IntervalCat.toLeftHeart
      (C := C) (s := σ.slicing) a b (Fact.out : b - a ≤ 1)).obj X)))
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
  let T : Set (Subobject X) := {M | M ≠ ⊥ ∧ IsStrictMono M.arrow}
  have hT_type : Finite T := by
    simpa [T] using
      (Slicing.IntervalCat.finite_strictSubobjects_of_finite_leftHeartSubobjects
        (C := C) (s := σ.slicing) (a := a) (b := b) hX_left)
  have hT_fin : T.Finite := by
    letI : Finite T := hT_type
    letI : Fintype T := Fintype.ofFinite T
    exact T.toFinite
  exact ssf.exists_first_strictShortExact_of_not_semistable
    (C := C) (σ := σ) (a := a) (b := b) hX hT_fin hns hW_interval

end SkewedStabilityFunction

lemma interval_pullback_cokernel_bot_eq
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow) :
    (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ = M := by
  apply le_antisymm
  · set P := (Subobject.pullback (cokernel.π M.arrow)).obj ⊥
    have hP : P.arrow ≫ cokernel.π M.arrow = 0 := by
      have := (Subobject.isPullback (cokernel.π M.arrow)
        (⊥ : Subobject (cokernel M.arrow))).w
      simp only [Subobject.bot_arrow, comp_zero] at this
      rw [this]
    exact Subobject.le_of_comm
      (hM.isLimitKernelFork.lift (KernelFork.ofι P.arrow hP))
      (hM.isLimitKernelFork.fac _ Limits.WalkingParallelPair.zero)
  · exact interval_le_pullback_cokernel
      (C := C) (s := s) (a := a) (b := b) M ⊥

lemma interval_cokernel_nonzero_of_ne_top
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X} (hM : M ≠ ⊤)
    (hM_strict : IsStrictMono M.arrow) :
    ¬IsZero (cokernel M.arrow) := by
  intro hZ
  haveI : Epi M.arrow := Preadditive.epi_of_isZero_cokernel M.arrow hZ
  haveI : IsIso M.arrow := hM_strict.isIso
  exact hM (Subobject.eq_top_of_isIso_arrow M)

lemma interval_pullback_ofLE_comm
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X}
    {A' B' : Subobject (cokernel M.arrow)} (h : A' ≤ B') :
    let q := cokernel.π M.arrow
    let pbA := (Subobject.pullback q).obj A'
    let pbB := (Subobject.pullback q).obj B'
    let hpb : pbA ≤ pbB := (Subobject.pullback q).monotone h
    Subobject.ofLE pbA pbB hpb ≫ Subobject.pullbackπ q B' =
      Subobject.pullbackπ q A' ≫ Subobject.ofLE A' B' h := by
  let q := cokernel.π M.arrow
  let pbA := (Subobject.pullback q).obj A'
  let pbB := (Subobject.pullback q).obj B'
  let hpb : pbA ≤ pbB := (Subobject.pullback q).monotone h
  apply (cancel_mono B'.arrow).mp
  simp only [Category.assoc, Subobject.ofLE_arrow]
  calc
    Subobject.ofLE pbA pbB hpb ≫ (Subobject.pullbackπ q B' ≫ B'.arrow)
        = Subobject.ofLE pbA pbB hpb ≫ (pbB.arrow ≫ q) := by
            rw [(Subobject.isPullback q B').w]
    _ = (Subobject.ofLE pbA pbB hpb ≫ pbB.arrow) ≫ q := by
          rw [Category.assoc]
    _ = pbA.arrow ≫ q := by rw [Subobject.ofLE_arrow]
    _ = Subobject.pullbackπ q A' ≫ A'.arrow := (Subobject.isPullback q A').w.symm

lemma SkewedStabilityFunction.Wobj_pullback_eq_add
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow)
    (B : Subobject (cokernel M.arrow)) :
    ssf.W (K₀.of C (((Subobject.pullback (cokernel.π M.arrow)).obj B : Subobject X) :
      s.IntervalCat C a b).obj) =
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
        ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) := by
  let S : ShortComplex (s.IntervalCat C a b) :=
    ShortComplex.mk
      (Subobject.ofLE M _ (interval_le_pullback_cokernel
        (C := C) (s := s) (a := a) (b := b) M B))
      (Subobject.pullbackπ (cokernel.π M.arrow) B)
      (interval_ofLE_pullbackπ_eq_zero (C := C) (s := s) (a := a) (b := b) M B)
  have hS :
      StrictShortExact S :=
    interval_strictShortExact_ofLE_pullbackπ_cokernel
      (C := C) (s := s) (a := a) (b := b) M hM B
  simpa [S] using ssf.strict_additive (C := C) (s := s) (a := a) (b := b) hS

lemma interval_lt_pullback_cokernel_of_ne_bot
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X}
    {B : Subobject (cokernel M.arrow)} (hB : B ≠ ⊥) :
    M < (Subobject.pullback (cokernel.π M.arrow)).obj B := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  have hle : M ≤ pbB :=
    interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B
  have hne : M ≠ pbB := by
    intro hEq
    let heqObj : Subobject.underlying.obj M = Subobject.underlying.obj pbB :=
      congrArg Subobject.underlying.obj hEq
    have hi : Subobject.ofLE M pbB hle = eqToHom heqObj := by
      apply (cancel_mono pbB.arrow).1
      calc
        Subobject.ofLE M pbB hle ≫ pbB.arrow = M.arrow := Subobject.ofLE_arrow hle
        _ = eqToHom heqObj ≫ pbB.arrow := (Subobject.arrow_congr M pbB hEq).symm
    have hzero :
        Subobject.pullbackπ q B = 0 := by
      have hcomp := interval_ofLE_pullbackπ_eq_zero
        (C := C) (s := s) (a := a) (b := b) M B
      rw [hi] at hcomp
      letI : Epi (eqToHom heqObj) := by infer_instance
      exact (cancel_epi (eqToHom heqObj)).1 (by simpa using hcomp)
    have hπ : IsStrictEpi (Subobject.pullbackπ q B) :=
      interval_pullbackπ_strictEpi_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) q (isStrictEpi_cokernel M.arrow) B
    haveI : Epi (Subobject.pullbackπ q B) := hπ.epi
    have hBZ : IsZero (B : s.IntervalCat C a b) :=
      (IsZero.iff_id_eq_zero _).mpr <|
        (cancel_epi (Subobject.pullbackπ q B)).1 (by
          rw [hzero]
          simp)
    exact hB ((intervalSubobject_isZero_iff_eq_bot
      (C := C) (s := s) (a := a) (b := b) (X := cokernel M.arrow) B).mp hBZ)
  exact lt_of_le_of_ne hle hne

lemma interval_pullback_cokernel_ne_top_of_ne_top
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X}
    {B : Subobject (cokernel M.arrow)} (hB : B ≠ ⊤) (hB_strict : IsStrictMono B.arrow) :
    (Subobject.pullback (cokernel.π M.arrow)).obj B ≠ ⊤ := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  intro hpb_top
  have hpb_iso : IsIso pbB.arrow := by
    let heqObj : Subobject.underlying.obj pbB = Subobject.underlying.obj (⊤ : Subobject X) :=
      congrArg Subobject.underlying.obj hpb_top
    have harr : pbB.arrow = eqToHom heqObj ≫ (⊤ : Subobject X).arrow := by
      simpa using (Subobject.arrow_congr pbB ⊤ hpb_top).symm
    rw [harr]
    infer_instance
  let r : X ⟶ (B : s.IntervalCat C a b) :=
    inv pbB.arrow ≫ Subobject.pullbackπ q B
  have hr : r ≫ B.arrow = q := by
    calc
      r ≫ B.arrow = inv pbB.arrow ≫ (Subobject.pullbackπ q B ≫ B.arrow) := by
        simp [r]
      _ = inv pbB.arrow ≫ (pbB.arrow ≫ q) := by rw [(Subobject.isPullback q B).w]
      _ = q := by simp
  haveI : Epi q := by infer_instance
  haveI : Epi B.arrow := epi_of_epi_fac hr
  haveI : IsIso B.arrow := hB_strict.isIso
  exact hB (Subobject.eq_top_of_isIso_arrow B)

lemma SkewedStabilityFunction.Wobj_cokernel_pullback_eq
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow)
    {B : Subobject (cokernel M.arrow)} (hB : IsStrictMono B.arrow) :
    ssf.W (K₀.of C (cokernel ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow).obj) =
      ssf.W (K₀.of C (cokernel B.arrow).obj) := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  have hpb_strict : IsStrictMono pbB.arrow :=
    interval_pullback_arrow_strictMono_of_strictMono
      (C := C) (s := s) (a := a) (b := b) q B hB
  have hXM :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) M.arrow hM)
  have hXpb :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (pbB : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel pbB.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) pbB.arrow hpb_strict)
  have hQB :
      ssf.W (K₀.of C (cokernel M.arrow).obj) =
        ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel B.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) B.arrow hB)
  have hpb_add :
      ssf.W (K₀.of C (pbB : s.IntervalCat C a b).obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) :=
    Wobj_pullback_eq_add
      (C := C) (s := s) (a := a) (b := b) (ssf := ssf) M hM B
  rw [hpb_add, add_assoc] at hXpb
  have hsum₁ :
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel pbB.arrow).obj)) := by
    calc
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj)
          = ssf.W (K₀.of C X.obj) := hXM.symm
      _ = ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel pbB.arrow).obj)) := hXpb
  have hsum₂ :
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel B.arrow).obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel pbB.arrow).obj)) := by
    rw [hQB] at hsum₁
    simpa [add_assoc] using hsum₁
  have hsum₃ :
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel B.arrow).obj)) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel pbB.arrow).obj)) := by
    simpa [add_assoc] using hsum₂
  have hsum₄ :
      ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel B.arrow).obj) =
        ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel pbB.arrow).obj) := by
    exact add_left_cancel hsum₃
  have hsum₅ :
      ssf.W (K₀.of C (cokernel B.arrow).obj) =
        ssf.W (K₀.of C (cokernel pbB.arrow).obj) := by
    exact add_left_cancel hsum₄
  exact hsum₅.symm

lemma SkewedStabilityFunction.Wobj_liftSub_cokernel_eq_add
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow)
    {A : Subobject (M : s.IntervalCat C a b)} (hA : IsStrictMono A.arrow) :
    let liftA := intervalLiftSub (C := C) (X := X) M A
    ssf.W (K₀.of C (cokernel liftA.arrow).obj) =
      ssf.W (K₀.of C (cokernel A.arrow).obj) +
        ssf.W (K₀.of C (cokernel M.arrow).obj) := by
  let liftA := intervalLiftSub (C := C) (X := X) M A
  have hcomp : IsStrictMono (A.arrow ≫ M.arrow) :=
    Slicing.IntervalCat.comp_strictMono
      (C := C) (s := s) (a := a) (b := b) A.arrow M.arrow hA hM
  have hLift : IsStrictMono liftA.arrow := by
    simpa [liftA, intervalLiftSub] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s) (a := a) (b := b) (A.arrow ≫ M.arrow) hcomp)
  have hXM :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) M.arrow hM)
  have hMA :
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) =
        ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel A.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) A.arrow hA)
  have hXA :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (liftA : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel liftA.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) liftA.arrow hLift)
  have hAeq :
      ssf.W (K₀.of C (liftA : s.IntervalCat C a b).obj) =
        ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) := by
    let eC : (liftA : s.IntervalCat C a b).obj ≅ (A : s.IntervalCat C a b).obj :=
      (Slicing.IntervalCat.ι (C := C) (s := s) a b).mapIso
        (Subobject.underlyingIso (A.arrow ≫ M.arrow))
    simpa [liftA, intervalLiftSub] using congrArg ssf.W (K₀.of_iso C eC)
  rw [hMA, add_assoc] at hXM
  rw [hAeq] at hXA
  have hsum :
      ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel A.arrow).obj) +
            ssf.W (K₀.of C (cokernel M.arrow).obj) =
        ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel liftA.arrow).obj) := by
    calc
      ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel A.arrow).obj) +
            ssf.W (K₀.of C (cokernel M.arrow).obj)
          = ssf.W (K₀.of C X.obj) := by simpa [add_assoc] using hXM.symm
      _ = ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel liftA.arrow).obj) := hXA
  have hsumA :
      ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (cokernel A.arrow).obj) +
            ssf.W (K₀.of C (cokernel M.arrow).obj)) =
        ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel liftA.arrow).obj) := by
    simpa [add_assoc] using hsum
  have hsum' :
      ssf.W (K₀.of C (cokernel A.arrow).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) =
        ssf.W (K₀.of C (cokernel liftA.arrow).obj) := by
    exact add_left_cancel hsumA
  simpa [liftA, add_comm, add_left_comm, add_assoc] using hsum'.symm

/-- The strict quotient attached to a minimal-phase strict kernel is semistable, provided
all nonzero objects in the thin interval have `W`-phases in a common open window of width `< 1`.
-/
theorem SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hFinSub : ∀ Y : σ.slicing.IntervalCat C a b, Finite (Subobject Y))
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_lt : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow → M < B →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1) :
    ssf.Semistable C (cokernel M.arrow).obj
      (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α) := by
  let Y : σ.slicing.IntervalCat C a b := cokernel M.arrow
  have hY_ne : ¬IsZero Y :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne_top hM_strict
  have hY_obj_ne : ¬IsZero Y.obj := by
    intro hZ
    exact hY_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hY_window : L < ψY ∧ ψY < U := by
    simpa [Y, ψY] using hWindow Y.property hY_obj_ne
  by_contra hns
  haveI : Finite (Subobject Y) := hFinSub Y
  obtain ⟨B, hB_ne, hB_strict, hB_max, _⟩ :=
    ssf.exists_maxPhase_maximal_strictSubobject
      (C := C) (σ := σ) (a := a) (b := b) (X := Y) hY_ne
  have hB_ne_top : B ≠ ⊤ :=
    ssf.maxPhase_strictSubobject_ne_top_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := Y) hns hB_ne hB_strict hB_max hW_interval
  have hB_phase_gt :
      ψY < wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
    simpa [Y, ψY] using
      ssf.phase_gt_of_maxPhase_strictSubobject_of_not_semistable
        (C := C) (σ := σ) (a := a) (b := b) (X := Y) (M := B)
        hY_ne hns hB_max hW_interval
  let pbB : Subobject X := (Subobject.pullback (cokernel.π M.arrow)).obj B
  have hpb_strict : IsStrictMono pbB.arrow :=
    interval_pullback_arrow_strictMono_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π M.arrow) B hB_strict
  have hpb_ne_top : pbB ≠ ⊤ :=
    interval_pullback_cokernel_ne_top_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hMltpb : M < pbB :=
    interval_lt_pullback_cokernel_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne
  have hpb_quot_gt :
      ψY < wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α := by
    simpa [Y, ψY] using hM_lt pbB hpb_ne_top hpb_strict hMltpb
  have hcokB_ne : ¬IsZero (cokernel B.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_obj_ne : ¬IsZero (cokernel B.arrow).obj := by
    intro hZ
    exact hcokB_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hcokB_phase_gt :
      ψY < wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α := by
    rw [← ssf.Wobj_cokernel_pullback_eq
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict
      (B := B) hB_strict]
    exact hpb_quot_gt
  have hB_obj_ne : ¬IsZero (B : σ.slicing.IntervalCat C a b).obj := by
    intro hZ
    exact intervalSubobject_not_isZero_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hB_ne <|
        Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ
  have hB_window :
      L < wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α < U := by
    exact hWindow (B : σ.slicing.IntervalCat C a b).property hB_obj_ne
  have hcokB_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel B.arrow).property hcokB_obj_ne
  have hUpper : U < ψY + 1 := by
    grind
  have hLower : ψY - 1 < L := by
    grind
  have hB_range :
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ∈
        Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> linarith
  have hcokB_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α ∈ Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> linarith
  have hB_Wne : ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj) ≠ 0 :=
    hW_interval (B : σ.slicing.IntervalCat C a b).property hB_obj_ne
  have haddY :
      ssf.W (K₀.of C Y.obj) =
        ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel B.arrow).obj) := by
    simpa [Y, map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.arrow hB_strict)
  have hcokB_phase_lt :
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α < ψY := by
    exact wPhaseOf_seesaw_dual haddY.symm rfl hB_phase_gt hB_Wne hB_range hcokB_range
  grind

theorem semistable_of_lower_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b ψ ε₀ : ℝ} (ha₁ : a₁ < b) (ha₂ : a₂ < b) (ha : a₂ ≤ a₁)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW ha₁).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a₁ + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin₂ : b - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW ha₂).Semistable C E ψ := by
  have hEI₂ : σ.slicing.intervalProp C a₂ b E :=
    σ.slicing.intervalProp_mono C ha (show b ≤ b by grind) hSS.1
  have henv_lo₂ : a₂ + ε₀ ≤ ψ := by
    grind
  have hthin₂' : b - a₂ < 1 := by
    grind
  refine semistable_of_target_envelope_triangleTest
    (C := C) (σ := σ) (W := W) (hW := hW) ha₁ hSS ha₂ hEI₂ hε₀ henv_lo₂ henv_hi
    hthin₂ ?_
  intro K Q f₁ f₂ f₃ hT hKI hQI hKne
  letI : Fact (a₂ < b) := ⟨ha₂⟩
  letI : Fact (b - a₂ ≤ 1) := ⟨by grind⟩
  letI : Fact (a₁ < b) := ⟨ha₁⟩
  letI : Fact (b - a₁ ≤ 1) := ⟨by grind⟩
  let KI₂ : σ.slicing.IntervalCat C a₂ b := ⟨K, hKI⟩
  let EI₂ : σ.slicing.IntervalCat C a₂ b := ⟨E, hEI₂⟩
  let QI₂ : σ.slicing.IntervalCat C a₂ b := ⟨Q, hQI⟩
  let iK : KI₂ ⟶ EI₂ := ObjectProperty.homMk f₁
  let qE : EI₂ ⟶ QI₂ := ObjectProperty.homMk f₂
  let S₀ : ShortComplex (σ.slicing.IntervalCat C a₂ b) :=
    ShortComplex.mk iK qE (by
      ext
      simpa [iK, qE] using comp_distTriang_mor_zero₁₂ _ hT)
  have hT₂ : Triangle.mk iK.hom qE.hom f₃ ∈ distTriang C := by
    simpa [iK, qE] using hT
  have hiK_strict : IsStrictMono iK :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a₂) (b := b) (S := S₀) hT₂).1
  obtain ⟨X, Y, fX, gY, δY, hTK, hX₁, hY_le⟩ :=
    exists_lower_boundary_triangle (C := C) (s := σ.slicing) ha₁ hKI
  have hX₂ : σ.slicing.intervalProp C a₂ b X :=
    σ.slicing.intervalProp_mono C ha (show b ≤ b by grind) hX₁
  have hY₂ : σ.slicing.intervalProp C a₂ b Y :=
    intervalProp_of_lower_boundary_triangle (C := C) (s := σ.slicing)
      ha₁ ha hKI hX₁ hY_le hTK
  let XI₁ : σ.slicing.IntervalCat C a₁ b := ⟨X, hX₁⟩
  let XI₂ : σ.slicing.IntervalCat C a₂ b := ⟨X, hX₂⟩
  let YI₂ : σ.slicing.IntervalCat C a₂ b := ⟨Y, hY₂⟩
  let EI₁ : σ.slicing.IntervalCat C a₁ b := ⟨E, hSS.1⟩
  let xK : XI₂ ⟶ KI₂ := ObjectProperty.homMk fX
  let kY : KI₂ ⟶ YI₂ := ObjectProperty.homMk gY
  let S₁ : ShortComplex (σ.slicing.IntervalCat C a₂ b) :=
    ShortComplex.mk xK kY (by
      ext
      simpa [xK, kY] using comp_distTriang_mor_zero₁₂ _ hTK)
  have hTK₂ : Triangle.mk xK.hom kY.hom δY ∈ distTriang C := by
    simpa [xK, kY] using hTK
  have hxK_strict : IsStrictMono xK :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a₂) (b := b) (S := S₁) hTK₂).1
  by_cases hYZ : IsZero Y
  · have hK₁ : σ.slicing.intervalProp C a₁ b K :=
      σ.slicing.intervalProp_of_triangle C hX₁ (Or.inl hYZ) hTK
    have hK_ge₁ : σ.slicing.geProp C (b - 1) K :=
      (σ.slicing.intervalProp_implies_rightWindow
        (C := C) (a := a₁) (b := b) (by grind) hK₁).1
    have hQ_lt : σ.slicing.ltProp C b Q :=
      (σ.slicing.intervalProp_implies_rightWindow
        (C := C) (a := a₂) (b := b) (by grind) hQI).2
    have hQ₁ : σ.slicing.intervalProp C a₁ b Q :=
      σ.slicing.third_intervalProp_of_triangle C ha₁ hSS.1 hK_ge₁ hQ_lt hT
    have hK_phase₁ :
        wPhaseOf (W (K₀.of C K)) ((a₁ + b) / 2) ≤ ψ :=
      hSS.2.2.2.2 hT hK₁ hQ₁ hKne
    have hK_eq :
        wPhaseOf (W (K₀.of C K)) ((a₁ + b) / 2) =
          wPhaseOf (W (K₀.of C K)) ((a₂ + b) / 2) :=
      wPhaseOf_eq_of_intervalProp_lower_inclusion
        (C := C) (σ := σ) (W := W) (hW := hW) ha₁ ha hK₁ hKne
        hε₀ hε₀2 hthin₂ hsin
    rw [← hK_eq]
    exact hK_phase₁
  · by_cases hXZ : IsZero X
    · have hY_phase_lt :
          wPhaseOf (W (K₀.of C Y)) ((a₂ + b) / 2) < ψ :=
        wPhaseOf_lt_of_lower_boundary_triangle
          (C := C) (σ := σ) (W := W) (hW := hW) ha₁ ha
          hKI hX₁ hY_le hYZ hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin hTK
      haveI : IsIso gY :=
        (Triangle.isZero₁_iff_isIso₂ (Triangle.mk fX gY δY) hTK).mp hXZ
      have hKY : W (K₀.of C K) = W (K₀.of C Y) := by
        simpa using congrArg W (K₀.of_iso C (asIso gY))
      rw [hKY]
      exact le_of_lt hY_phase_lt
    · let xE₂ : XI₂ ⟶ EI₂ := xK ≫ iK
      have hxE₂_strict : IsStrictMono xE₂ :=
        Slicing.IntervalCat.comp_strictMono
          (C := C) (s := σ.slicing) (a := a₂) (b := b) xK iK hxK_strict hiK_strict
      let xE₁ : XI₁ ⟶ EI₁ := ObjectProperty.homMk (fX ≫ f₁)
      have hmonoRH :
          Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := σ.slicing) a₁ b
            (Fact.out : b - a₁ ≤ 1)).map xE₁) := by
        simpa [Slicing.IntervalCat.toRightHeart, xE₁, xE₂] using
          (Slicing.IntervalCat.mono_toRightHeart_of_strictMono
            (C := C) (s := σ.slicing) (a := a₂) (b := b) xE₂ hxE₂_strict)
      have hxE₁_strict : IsStrictMono xE₁ := by
        letI :
            Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := σ.slicing) a₁ b
              (Fact.out : b - a₁ ≤ 1)).map xE₁) := hmonoRH
        exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart
          (C := C) (s := σ.slicing) (a := a₁) (b := b) xE₁
      let SX : ShortComplex (σ.slicing.IntervalCat C a₁ b) :=
        ShortComplex.mk xE₁ (cokernel.π xE₁) (cokernel.condition xE₁)
      have hSX : StrictShortExact SX :=
        interval_strictShortExact_cokernel_of_strictMono
          (C := C) (s := σ.slicing) (a := a₁) (b := b) xE₁ hxE₁_strict
      obtain ⟨δX, hTX⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
        (C := C) (s := σ.slicing) (a := a₁) (b := b) hSX
      have hX_phase₁ :
          wPhaseOf (W (K₀.of C X)) ((a₁ + b) / 2) ≤ ψ :=
        hSS.2.2.2.2 hTX hX₁ (cokernel xE₁).property hXZ
      have hX_eq :
          wPhaseOf (W (K₀.of C X)) ((a₁ + b) / 2) =
            wPhaseOf (W (K₀.of C X)) ((a₂ + b) / 2) :=
        wPhaseOf_eq_of_intervalProp_lower_inclusion
          (C := C) (σ := σ) (W := W) (hW := hW) ha₁ ha hX₁ hXZ
          hε₀ hε₀2 hthin₂ hsin
      have hX_phase_le :
          wPhaseOf (W (K₀.of C X)) ((a₂ + b) / 2) ≤ ψ := by
        rw [← hX_eq]
        exact hX_phase₁
      have hY_phase_lt :
          wPhaseOf (W (K₀.of C Y)) ((a₂ + b) / 2) < ψ :=
        wPhaseOf_lt_of_lower_boundary_triangle
          (C := C) (σ := σ) (W := W) (hW := hW) ha₁ ha
          hKI hX₁ hY_le hYZ hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin hTK
      have hsum :
          W (K₀.of C K) = W (K₀.of C X) + W (K₀.of C Y) := by
        simpa [map_add] using congrArg W
          (K₀.of_triangle C (Triangle.mk fX gY δY) hTK)
      have hX_range :
          wPhaseOf (W (K₀.of C X)) ((a₂ + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hX₂ hXZ hε₀ hε₀2 henv_lo₂ henv_hi
          hthin₂ hsin
      have hY_range :
          wPhaseOf (W (K₀.of C Y)) ((a₂ + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hY₂ hYZ hε₀ hε₀2 henv_lo₂ henv_hi
          hthin₂ hsin
      have hK_range :
          wPhaseOf (W (K₀.of C K)) ((a₂ + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hKI hKne hε₀ hε₀2 henv_lo₂ henv_hi
          hthin₂ hsin
      have hX_range' :
          wPhaseOf (W (K₀.of C X)) ((a₂ + b) / 2) ∈ Set.Ioc (ψ - 1) ψ := by
        exact ⟨hX_range.1, hX_phase_le⟩
      have hYW_ne : W (K₀.of C Y) ≠ 0 := by
        exact σ.W_ne_zero_of_intervalProp C W hthin₂'
          (stabSeminorm_lt_cos_of_hsin_hthin
            (C := C) (σ := σ) (W := W) ha₂ hε₀ hthin₂ hsin) hYZ hY₂
      have hK_phase_lt :
          wPhaseOf (W (K₀.of C K)) ((a₂ + b) / 2) < ψ :=
        wPhaseOf_lt_of_add_le_lt hsum.symm hX_range' hY_phase_lt hYW_ne hY_range hK_range
      exact le_of_lt hK_phase_lt

theorem semistable_of_interval_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b₁ b₂ ψ ε₀ : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a₁ + ε₀ ≤ ψ) (henv_hi : ψ ≤ b₁ - ε₀)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1)
  (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  have hthin_mid : b₂ - a₁ + 2 * ε₀ < 1 := by
    grind
  have hab_mid : a₁ < b₂ := by
    grind
  have hmid :
      (σ.skewedStabilityFunction_of_near C W hW hab_mid).Semistable C E ψ :=
    semistable_of_upper_inclusion
      (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hab_mid hb hSS
      hε₀ hε₀2 henv_lo henv_hi hthin_mid hsin
  exact semistable_of_lower_inclusion
    (C := C) (σ := σ) (W := W) (hW := hW) (ha₁ := by grind) hab₂ ha hmid
    hε₀ hε₀2 (by grind) (by grind) hthin₂ hsin

theorem semistable_of_target_subinterval
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a₁ a₂ b₂ b₁ ψ ε₀ : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (ha : a₁ ≤ a₂) (hb : b₂ ≤ b₁)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    (hI₂ : σ.slicing.intervalProp C a₂ b₂ E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv₂_lo : a₂ + ε₀ ≤ ψ) (henv₂_hi : ψ ≤ b₂ - ε₀)
    (hthin₁ : b₁ - a₁ + 2 * ε₀ < 1)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  refine semistable_of_target_envelope_triangleTest
    (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hSS hab₂ hI₂ hε₀ henv₂_lo henv₂_hi
    hthin₂ ?_
  intro K Q f₁ f₂ f₃ hT hKI hQI hKne
  have ha₂b₁ : a₂ < b₁ := by
    grind
  have hthin_mid : b₁ - a₂ + 2 * ε₀ < 1 := by
    grind
  have hKI₁ : σ.slicing.intervalProp C a₁ b₁ K :=
    σ.slicing.intervalProp_mono C ha hb hKI
  have hQI₁ : σ.slicing.intervalProp C a₁ b₁ Q :=
    σ.slicing.intervalProp_mono C ha hb hQI
  have hKI_mid : σ.slicing.intervalProp C a₂ b₁ K :=
    σ.slicing.intervalProp_mono C (show a₂ ≤ a₂ by grind) hb hKI
  have hK_phase₁ :
      wPhaseOf (W (K₀.of C K)) ((a₁ + b₁) / 2) ≤ ψ :=
    hSS.2.2.2.2 hT hKI₁ hQI₁ hKne
  have hK_eq_lower :
      wPhaseOf (W (K₀.of C K)) ((a₂ + b₁) / 2) =
        wPhaseOf (W (K₀.of C K)) ((a₁ + b₁) / 2) :=
    wPhaseOf_eq_of_intervalProp_lower_inclusion
      (C := C) (σ := σ) (W := W) (hW := hW) ha₂b₁ ha hKI_mid hKne
      hε₀ hε₀2 hthin₁ hsin
  have hK_eq_upper :
      wPhaseOf (W (K₀.of C K)) ((a₂ + b₂) / 2) =
        wPhaseOf (W (K₀.of C K)) ((a₂ + b₁) / 2) :=
    wPhaseOf_eq_of_intervalProp_upper_inclusion
      (C := C) (σ := σ) (W := W) (hW := hW) hab₂ hb hKI hKne
      hε₀ hε₀2 hthin_mid hsin
  rw [hK_eq_upper, hK_eq_lower]
  exact hK_phase₁

theorem semistable_of_target_envelope
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b₁ b₂ ψ ε₀ : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    (hI₂ : σ.slicing.intervalProp C a₂ b₂ E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv₁_lo : a₁ + ε₀ ≤ ψ) (henv₁_hi : ψ ≤ b₁ - ε₀)
    (henv₂_lo : a₂ + ε₀ ≤ ψ) (henv₂_hi : ψ ≤ b₂ - ε₀)
    (hthin₁ : b₁ - a₁ + 2 * ε₀ < 1)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  set a : ℝ := max a₁ a₂
  set b : ℝ := min b₁ b₂
  have ha₁ : a₁ ≤ a := by
    dsimp [a]
    exact le_max_left _ _
  have ha₂ : a₂ ≤ a := by
    dsimp [a]
    exact le_max_right _ _
  have hb₁ : b ≤ b₁ := by
    dsimp [b]
    exact min_le_left _ _
  have hb₂ : b ≤ b₂ := by
    dsimp [b]
    exact min_le_right _ _
  have hab : a < b := by
    have hlow₁ : a₁ ≤ ψ - ε₀ := by
      grind
    have hlow₂ : a₂ ≤ ψ - ε₀ := by
      grind
    have hlow : a ≤ ψ - ε₀ := by
      dsimp [a]
      exact max_le_iff.mpr ⟨hlow₁, hlow₂⟩
    have hhigh₁ : ψ + ε₀ ≤ b₁ := by
      grind
    have hhigh₂ : ψ + ε₀ ≤ b₂ := by
      grind
    have hhigh : ψ + ε₀ ≤ b := by
      dsimp [b]
      exact le_min_iff.mpr ⟨hhigh₁, hhigh₂⟩
    grind
  have hI : σ.slicing.intervalProp C a b E := by
    by_cases hEZ : IsZero E
    · exact Or.inl hEZ
    · refine σ.slicing.intervalProp_of_intrinsic_phases C hEZ ?_ ?_
      · dsimp [a]
        exact max_lt_iff.mpr
          ⟨σ.slicing.phiMinus_gt_of_intervalProp C hEZ hSS.1,
            σ.slicing.phiMinus_gt_of_intervalProp C hEZ hI₂⟩
      · dsimp [b]
        exact lt_min_iff.mpr
          ⟨σ.slicing.phiPlus_lt_of_intervalProp C hEZ hSS.1,
            σ.slicing.phiPlus_lt_of_intervalProp C hEZ hI₂⟩
  have henv_lo : a + ε₀ ≤ ψ := by
    have hlow : a ≤ ψ - ε₀ := by
      dsimp [a]
      exact max_le_iff.mpr ⟨by grind, by grind⟩
    grind
  have henv_hi : ψ ≤ b - ε₀ := by
    have hhigh : ψ + ε₀ ≤ b := by
      dsimp [b]
      exact le_min_iff.mpr ⟨by grind, by grind⟩
    grind
  have hthin : b - a + 2 * ε₀ < 1 := by
    have hthin₁' : b - a + 2 * ε₀ ≤ b₁ - a₁ + 2 * ε₀ := by
      grind
    have hthin₂' : b - a + 2 * ε₀ ≤ b₂ - a₂ + 2 * ε₀ := by
      grind
    exact lt_of_le_of_lt hthin₁' hthin₁
  have hmid :
      (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ :=
    semistable_of_target_subinterval
      (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hab
      (show a₁ ≤ a by dsimp [a]; exact le_max_left _ _) (show b ≤ b₁ by
        dsimp [b]
        exact min_le_left _ _) hSS hI hε₀ hε₀2 henv_lo henv_hi hthin₁ hthin hsin
  exact semistable_of_interval_inclusion
    (C := C) (σ := σ) (W := W) (hW := hW) hab hab₂
    (show a₂ ≤ a by dsimp [a]; exact le_max_right _ _) (show b ≤ b₂ by
      dsimp [b]
      exact min_le_right _ _) hmid hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin

/-- A nonzero strict quotient of a `W`-semistable interval object has `W`-phase at least
that of the source object, assuming all nonzero interval objects lie in a common branch
window of width `< 1`. This is the thin-category analogue of the quotient-side
semistability inequality in Proposition 2.4. -/
theorem SkewedStabilityFunction.phase_le_of_strictQuotient_of_window
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : σ.slicing.IntervalCat C a b} {ψ : ℝ}
    (hX : ssf.Semistable C X.obj ψ)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    (p : X ⟶ Y) (hp : IsStrictEpi p)
    (hY : ¬IsZero Y.obj) :
    ψ ≤ wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α := by
  by_cases hKz : IsZero (kernel p).obj
  · have hKz' : IsZero (kernel p) :=
      Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hKz
    have hkernel_zero : kernel.ι p = 0 := zero_of_source_iso_zero _ hKz'.isoZero
    haveI : Mono p := Preadditive.mono_of_kernel_zero hkernel_zero
    haveI : IsIso p := IsStrictEpi.isIso hp
    let eC : X.obj ≅ Y.obj :=
      ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso (asIso p))
    rw [← hX.2.2.2.1, ← K₀.of_iso C eC]
  · have hK : ¬IsZero (kernel p).obj := hKz
    let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
      ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : StrictShortExact S :=
      interval_strictShortExact_of_kernel_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) S (kernelIsKernel p) hp
    obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := σ.slicing) (a := a) (b := b) hS
    have hK_le :
        wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α ≤ ψ :=
      hX.2.2.2.2 hT (kernel p).property Y.property hK
    have hX_phase :
        wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α = ψ := hX.2.2.2.1
    have hX_window :
        L < wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α ∧
          wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α < U := by
      exact hWindow X.property hX.2.1
    have hK_window :
        L < wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α ∧
          wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α < U := by
      exact hWindow (kernel p).property hK
    have hY_window :
        L < wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α ∧
          wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α < U := by
      exact hWindow Y.property hY
    have hK_range :
        wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α ∈ Set.Ioc (ψ - 1) ψ := by
      constructor
      · grind
      · exact hK_le
    have hY_range :
        wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α ∈ Set.Ioo (ψ - 1) (ψ + 1) := by
      constructor
      · grind
      · grind
    have hY_Wne : ssf.W (K₀.of C Y.obj) ≠ 0 := hW_interval Y.property hY
    have hadd :
        ssf.W (K₀.of C X.obj) =
          ssf.W (K₀.of C (kernel p).obj) +
            ssf.W (K₀.of C Y.obj) := by
      simpa [S, map_add] using congrArg ssf.W
        (Slicing.IntervalCat.K0_of_strictShortExact (C := C) (s := σ.slicing)
          (a := a) (b := b) hS)
    exact wPhaseOf_seesaw hadd.symm hX.2.2.2.1 hK_range hY_Wne hY_range

/-- A minimal-phase strict kernel has semistable strict quotient. This is the mdq step used
for the thin-interval HN recursion. The only quotient-side hypothesis needed is plain
phase minimality among proper strict kernels. -/
theorem SkewedStabilityFunction.phase_cokernel_lt_of_phase_gt_strictSubobject
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {Y : σ.slicing.IntervalCat C a b} {A : Subobject Y}
    (hA_ne_bot : A ≠ ⊥) (hA_ne_top : A ≠ ⊤) (hA_strict : IsStrictMono A.arrow)
    (hA_phase_gt :
      wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1) :
    wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α := by
  let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hA_obj_ne : ¬IsZero (A : σ.slicing.IntervalCat C a b).obj := by
    intro hZ
    exact intervalSubobject_not_isZero_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hA_ne_bot <|
        Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ
  have hY_obj_ne : ¬IsZero Y.obj := by
    intro hZ
    have hY_zero : IsZero Y :=
      Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ
    have hA_zero : IsZero (A : σ.slicing.IntervalCat C a b) := IsZero.of_mono A.arrow hY_zero
    exact hA_obj_ne (((σ.slicing.intervalProp C a b).ι).map_isZero hA_zero)
  have hY_window : L < ψY ∧ ψY < U := by
    simpa [ψY] using hWindow Y.property hY_obj_ne
  have hcokA_ne : ¬IsZero (cokernel A.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hA_ne_top hA_strict
  have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
    intro hZ
    exact hcokA_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hA_window :
      L < wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α < U := by
    exact hWindow (A : σ.slicing.IntervalCat C a b).property hA_obj_ne
  have hcokA_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel A.arrow).property hcokA_obj_ne
  have hA_Wne : ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj) ≠ 0 :=
    hW_interval (A : σ.slicing.IntervalCat C a b).property hA_obj_ne
  have hA_range :
      wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α ∈
        Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> dsimp [ψY] <;> grind [hA_window.1, hA_window.2, hY_window.1, hY_window.2]
  have hcokA_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∈
        Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> dsimp [ψY] <;> grind [hcokA_window.1, hcokA_window.2, hY_window.1, hY_window.2]
  have haddY :
      ssf.W (K₀.of C Y.obj) =
        ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel A.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow hA_strict)
  exact wPhaseOf_seesaw_dual haddY.symm rfl hA_phase_gt hA_Wne hA_range hcokA_range

end

end CategoryTheory.Triangulated
