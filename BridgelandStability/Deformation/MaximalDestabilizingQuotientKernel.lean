/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.Deformation.MaximalDestabilizingQuotient

/-!
# Deformation of Stability Conditions — MDQKernel

IsStrictMDQKernel, kernel iteration, legacy HN
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

variable [IsTriangulated C] in
/-- A minimal-phase strict kernel has semistable strict quotient. This is the mdq step used
for the thin-interval HN recursion. The only quotient-side hypothesis needed is plain
phase minimality among proper strict kernels. -/
structure IsStrictMDQKernel
    (σ : StabilityCondition C) {a b : ℝ}
    (ssf : SkewedStabilityFunction C σ.slicing a b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (M : Subobject X) : Prop where
  ne_top : M ≠ ⊤
  strict : IsStrictMono M.arrow
  semistable :
    ssf.Semistable C (cokernel M.arrow).obj
      (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α)
  minimal : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
    wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α

variable [IsTriangulated C] in
/-- A proper strict kernel with semistable quotient of minimal quotient phase packages into the
strict-kernel mdq object used in the faithful Node 7.7 refactor. -/
theorem SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_ss :
      ssf.Semistable C (cokernel M.arrow).obj
        (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α))
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) :
    IsStrictMDQKernel (C := C) σ ssf M := by
  exact ⟨hM_ne_top, hM_strict, hM_ss, hM_min⟩

variable [IsTriangulated C] in
theorem SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel_of_minimal
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hFinSub : ∀ Y : σ.slicing.IntervalCat C a b, Finite (Subobject Y))
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
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
        hY_ne hns hB_ne hB_strict hB_max hW_interval
  let pbB : Subobject X := (Subobject.pullback (cokernel.π M.arrow)).obj B
  have hpb_strict : IsStrictMono pbB.arrow :=
    interval_pullback_arrow_strictMono_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π M.arrow) B hB_strict
  have hpb_ne_top : pbB ≠ ⊤ :=
    interval_pullback_cokernel_ne_top_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_ne : ¬IsZero (cokernel B.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_obj_ne : ¬IsZero (cokernel B.arrow).obj := by
    intro hZ
    exact hcokB_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
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
    linarith [hWidth, hY_window.1]
  have hLower : ψY - 1 < L := by
    linarith [hWidth, hY_window.2]
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
  have hpb_phase_lt :
      wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α < ψY := by
    rw [ssf.Wobj_cokernel_pullback_eq
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict
      (B := B) hB_strict]
    exact hcokB_phase_lt
  have hpb_phase_ge :
      ψY ≤ wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α :=
    hM_min pbB hpb_ne_top hpb_strict
  linarith

variable [IsTriangulated C] in
/-- The quotient-semistability step for Node 7.7 using the paper-faithful strict-Artinian
input. If a proper strict kernel has minimal quotient phase, then its strict quotient is
semistable. The proof follows the same pullback contradiction as the legacy finite-subobject
version, but the destabilising strict subobject of the quotient is now chosen by
strict-Artinian descent rather than by finite enumeration. -/
theorem SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel_of_minimal_of_strictArtinian
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    [IsStrictArtinianObject (cokernel M.arrow)] :
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
  obtain ⟨B, hB_ne, hB_ne_top, hB_strict, _, hB_phase_gt, _⟩ :=
    ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
      (C := C) (σ := σ) (a := a) (b := b) (X := Y) hY_ne hns hW_interval
  let pbB : Subobject X := (Subobject.pullback (cokernel.π M.arrow)).obj B
  have hpb_strict : IsStrictMono pbB.arrow :=
    interval_pullback_arrow_strictMono_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π M.arrow) B hB_strict
  have hpb_ne_top : pbB ≠ ⊤ :=
    interval_pullback_cokernel_ne_top_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_ne : ¬IsZero (cokernel B.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_obj_ne : ¬IsZero (cokernel B.arrow).obj := by
    intro hZ
    exact hcokB_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
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
    linarith [hWidth, hY_window.1]
  have hLower : ψY - 1 < L := by
    linarith [hWidth, hY_window.2]
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
  have hpb_phase_lt :
      wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α < ψY := by
    rw [ssf.Wobj_cokernel_pullback_eq
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict
      (B := B) hB_strict]
    exact hcokB_phase_lt
  have hpb_phase_ge :
      ψY ≤ wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α :=
    hM_min pbB hpb_ne_top hpb_strict
  linarith

variable [IsTriangulated C] in
/-- The strict-Artinian quotient-semistability step packages a minimal-phase strict kernel into
the mdq-kernel structure used by the faithful Lemma 7.7 recursion. -/
theorem SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel_of_strictArtinian
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    [IsStrictArtinianObject (cokernel M.arrow)] :
    IsStrictMDQKernel (C := C) σ ssf M := by
  refine ssf.isStrictMDQKernel_of_minPhase_strictKernel
    (C := C) (σ := σ) (a := a) (b := b) hM_ne_top hM_strict ?_ hM_min
  exact ssf.semistable_cokernel_of_minPhase_strictKernel_of_minimal_of_strictArtinian
    (C := C) (σ := σ) (a := a) (b := b) hM_ne_top hM_strict hM_min
    hW_interval hWindow hWidth

variable [IsTriangulated C] in
/-- Every proper strict quotient of a minimal-phase minimal strict kernel has phase strictly
larger than the phase of the ambient minimal quotient. This is the kernel-recursion step
for thin-interval HN existence. -/
theorem SkewedStabilityFunction.phase_lt_of_strictQuotient_of_minPhase_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_lt : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow → B < M →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {A : Subobject (M : σ.slicing.IntervalCat C a b)} (hA_top : A ≠ ⊤)
    (hA_strict : IsStrictMono A.arrow) :
    wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
  let liftA := intervalLiftSub (C := C) (X := X) M A
  have hLift_strict : IsStrictMono liftA.arrow := by
    simpa [liftA, intervalLiftSub] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) (A.arrow ≫ M.arrow)
        (Slicing.IntervalCat.comp_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow M.arrow hA_strict hM_strict))
  have hLift_lt : liftA < M :=
    intervalLiftSub_lt (C := C) (X := X) M hA_top
  have hLift_ne_top : liftA ≠ ⊤ := ne_top_of_lt hLift_lt
  let ψM : ℝ := wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α
  let ψLift : ℝ := wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α
  have hLift_phase_gt : ψM < ψLift := by
    simpa [ψM, ψLift] using hM_lt liftA hLift_ne_top hLift_strict hLift_lt
  have hcokM_ne : ¬IsZero (cokernel M.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne_top hM_strict
  have hcokA_ne : ¬IsZero (cokernel A.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict
  have hcokLift_ne : ¬IsZero (cokernel liftA.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hLift_ne_top hLift_strict
  have hcokM_obj_ne : ¬IsZero (cokernel M.arrow).obj := by
    intro hZ
    exact hcokM_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
    intro hZ
    exact hcokA_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hcokLift_obj_ne : ¬IsZero (cokernel liftA.arrow).obj := by
    intro hZ
    exact hcokLift_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hLift_window : L < ψLift ∧ ψLift < U := by
    simpa [ψLift] using hWindow (cokernel liftA.arrow).property hcokLift_obj_ne
  have hM_window : L < ψM ∧ ψM < U := by
    simpa [ψM] using hWindow (cokernel M.arrow).property hcokM_obj_ne
  have hA_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel A.arrow).property hcokA_obj_ne
  have hUpper : U < ψLift + 1 := by
    linarith [hWidth, hLift_window.1]
  have hLower : ψLift - 1 < L := by
    linarith [hWidth, hLift_window.2]
  have hM_range : ψM ∈ Set.Ioo (ψLift - 1) (ψLift + 1) := by
    constructor <;> linarith
  have hA_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∈
        Set.Ioo (ψLift - 1) (ψLift + 1) := by
    constructor <;> linarith
  have hM_Wne : ssf.W (K₀.of C (cokernel M.arrow).obj) ≠ 0 :=
    hW_interval (cokernel M.arrow).property hcokM_obj_ne
  have hsum :
      ssf.W (K₀.of C (cokernel liftA.arrow).obj) =
        ssf.W (K₀.of C (cokernel A.arrow).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [liftA] using
      ssf.Wobj_liftSub_cokernel_eq_add
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict hA_strict
  have hA_phase_gt_lift :
      ψLift < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
    exact wPhaseOf_seesaw_strict hsum.symm rfl hLift_phase_gt hM_Wne hM_range hA_range
  linarith

variable [IsTriangulated C] in
theorem thinFiniteLength_cokernel
    (σ : StabilityCondition C) {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow) :
    IsStrictArtinianObject (cokernel M.arrow) ∧
      IsStrictNoetherianObject (cokernel M.arrow) := by
  exact hFiniteLength (cokernel M.arrow)

variable [IsTriangulated C] in
theorem SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel_of_finiteLength
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1) :
    IsStrictMDQKernel (C := C) σ ssf M := by
  letI : IsStrictArtinianObject (cokernel M.arrow) :=
    (thinFiniteLength_cokernel (C := C) (σ := σ) (a := a) (b := b)
      hFiniteLength hM_ne_top hM_strict).1
  refine ssf.isStrictMDQKernel_of_minPhase_strictKernel_of_strictArtinian
    (C := C) (σ := σ) (a := a) (b := b) hM_ne_top hM_strict hM_min
    hW_interval hWindow hWidth

variable [IsTriangulated C] in
/-- Legacy thin-interval HN existence, kept temporarily while Node 7.7 is refactored to the
paper-faithful finite-length interface.

This proof still runs on the stronger surrogate hypothesis `Finite (Subobject Y)` for every
interval object `Y`. Bridgeland's Lemma 7.7 is instead stated for a thin quasi-abelian category
of finite length, i.e. chain conditions on strict subobjects / strict quotients in
`P((a, b))` itself. Do not use this theorem on the critical path of the Section 7 proof. -/
theorem SkewedStabilityFunction.hn_exists_in_thin_interval_of_finiteSubobjects
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFinSub : ∀ Y : σ.slicing.IntervalCat C a b, Finite (Subobject Y))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X) :
    let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, L < G.φ j ∧ G.φ j < U := by
  let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
  suffices h :
      ∀ (k : ℕ) (Y : σ.slicing.IntervalCat C a b), ¬IsZero Y →
        Nat.card (Subobject Y) ≤ k →
        ∀ (t : ℝ),
          (∀ A : Subobject Y, A ≠ ⊤ → IsStrictMono A.arrow →
            t < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α) →
          ∃ G : HNFiltration C Psem Y.obj,
            ∀ j, t < G.φ j ∧ G.φ j < U by
    have hL : ∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
        L < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
      intro A hA_top hA_strict
      have hcokA_ne : ¬IsZero (cokernel A.arrow) :=
        interval_cokernel_nonzero_of_ne_top
          (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict
      have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
        intro hZ
        exact hcokA_ne (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
      exact (hWindow (cokernel A.arrow).property hcokA_obj_ne).1
    exact h _ X hX le_rfl L hL
  intro k
  induction k with
  | zero =>
      intro Y hY hcard t hquot
      haveI : Finite (Subobject Y) := hFinSub Y
      haveI := Fintype.ofFinite (Subobject Y)
      have : 0 < Nat.card (Subobject Y) := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_pos
      omega
  | succ k ih =>
      intro Y hY hcard t hquot
      let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
      have hY_obj_ne : ¬IsZero Y.obj := by
        intro hZ
        exact hY (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
      by_cases hss : ssf.Semistable C Y.obj ψY
      · refine ⟨HNFiltration.single C Y.obj ψY hss, ?_⟩
        intro j
        have hbot_ne_top : (⊥ : Subobject Y) ≠ ⊤ := by
          intro h
          exact (intervalSubobject_top_ne_bot_of_not_isZero
            (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hY) h.symm
        have hbot_strict : IsStrictMono ((⊥ : Subobject Y).arrow) :=
          intervalSubobject_bot_arrow_strictMono
            (C := C) (s := σ.slicing) (a := a) (b := b)
        have hbot_phase_gt :
            t < wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α := by
          exact hquot ⊥ hbot_ne_top hbot_strict
        have hbot_zero :
            ((⊥ : Subobject Y).arrow) =
              (0 : ((⊥ : Subobject Y) : σ.slicing.IntervalCat C a b) ⟶ Y) := by
          simpa using (Subobject.bot_arrow : (⊥ : Subobject Y).arrow = 0)
        let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
          rw [hbot_zero]
          exact cokernelZeroIsoTarget
        let eC : (cokernel ((⊥ : Subobject Y).arrow)).obj ≅ Y.obj :=
          (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
        have hbot_phase_eq :
            wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α = ψY := by
          simpa [ψY] using
            congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
        have hψY_hi : ψY < U := (hWindow Y.property hY_obj_ne).2
        have hj_lt : j.val < 1 := by
          simpa [HNFiltration.single] using j.is_lt
        have hj0 : j.val = 0 := by
          omega
        have hj : j = ⟨0, by simpa [HNFiltration.single] using (show 0 < 1 by omega)⟩ :=
          Fin.ext hj0
        subst j
        have hbot_phase_gt_zero :
            t < wPhaseOf
              (ssf.W (K₀.of C
                (cokernel
                  (0 : ((⊥ : Subobject Y) : σ.slicing.IntervalCat C a b) ⟶ Y)).obj)) ssf.α := by
          simpa [hbot_zero] using hbot_phase_gt
        have hbot_phase_eq_zero :
            wPhaseOf
              (ssf.W (K₀.of C
                (cokernel
                  (0 : ((⊥ : Subobject Y) : σ.slicing.IntervalCat C a b) ⟶ Y)).obj)) ssf.α = ψY := by
          simpa [hbot_zero] using hbot_phase_eq
        have hψY_gt : t < ψY := by
          exact hbot_phase_eq_zero ▸ hbot_phase_gt_zero
        exact ⟨by simpa [HNFiltration.single] using hψY_gt, hψY_hi⟩
      · obtain ⟨M, hM_top, hM_strict, hM_min, hM_lt⟩ :=
          ssf.exists_minPhase_minimal_strictKernel
            (C := C) (σ := σ) (a := a) (b := b) hY hW_interval hss
        by_cases hM_bot : M = ⊥
        · subst hM_bot
          have hss_bot :
              ssf.Semistable C (cokernel ((⊥ : Subobject Y).arrow)).obj
                (wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α) :=
            ssf.semistable_cokernel_of_minPhase_strictKernel_of_minimal
              (C := C) (σ := σ) (a := a) (b := b) hFinSub hM_top hM_strict hM_min
              hW_interval hWindow hWidth
          let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
            rw [show ((⊥ : Subobject Y).arrow) = 0 by simp [Subobject.bot_arrow]]
            exact cokernelZeroIsoTarget
          let eC : (cokernel ((⊥ : Subobject Y).arrow)).obj ≅ Y.obj :=
            (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
          have hphase_bot :
              wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α = ψY := by
            simpa [ψY] using
              congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
          have hssY : ssf.Semistable C Y.obj ψY := by
            exact hphase_bot ▸
              (ssf.semistable_of_iso
                (C := C) (s := σ.slicing) (a := a) (b := b) eC hss_bot)
          exact absurd hssY hss
        · have hM_ne : ¬IsZero (M : σ.slicing.IntervalCat C a b) :=
            intervalSubobject_not_isZero_of_ne_bot
              (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hM_bot
          have hcard_M :
              Nat.card (Subobject (M : σ.slicing.IntervalCat C a b)) <
                Nat.card (Subobject Y) :=
            interval_card_subobject_lt_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hM_top
          let ψQ : ℝ := wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α
          have hψQ_gt : t < ψQ := by
            simpa [ψQ] using hquot M hM_top hM_strict
          have hψQ_ss :
              ssf.Semistable C (cokernel M.arrow).obj ψQ :=
            ssf.semistable_cokernel_of_minPhase_strictKernel_of_minimal
              (C := C) (σ := σ) (a := a) (b := b) hFinSub hM_top hM_strict hM_min
              hW_interval hWindow hWidth
          have hcokM_ne : ¬IsZero (cokernel M.arrow) :=
            interval_cokernel_nonzero_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hM_top hM_strict
          have hcokM_obj_ne : ¬IsZero (cokernel M.arrow).obj := by
            intro hZ
            exact hcokM_ne (Slicing.IntervalCat.isZero_of_obj_isZero
              (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
          have hψQ_hi : ψQ < U := by
            simpa [ψQ] using (hWindow (cokernel M.arrow).property hcokM_obj_ne).2
          have hquot_M :
              ∀ A : Subobject (M : σ.slicing.IntervalCat C a b), A ≠ ⊤ → IsStrictMono A.arrow →
                ψQ < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
            intro A hA_top hA_strict
            simpa [ψQ] using
              (ssf.phase_lt_of_strictQuotient_of_minPhase_strictKernel
                (C := C) (σ := σ) (a := a) (b := b) hM_top hM_strict hM_lt
                hW_interval hWindow hWidth hA_top hA_strict)
          have hcard_M_le : Nat.card (Subobject (M : σ.slicing.IntervalCat C a b)) ≤ k := by
            exact Nat.lt_succ_iff.mp (lt_of_lt_of_le hcard_M hcard)
          obtain ⟨G, hG⟩ := ih (M : σ.slicing.IntervalCat C a b) hM_ne hcard_M_le ψQ hquot_M
          let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
            ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)
          have hS : StrictShortExact S :=
            interval_strictShortExact_cokernel_of_strictMono
              (C := C) (s := σ.slicing) (a := a) (b := b) M.arrow hM_strict
          let H : HNFiltration C Psem Y.obj :=
            HNFiltration.appendStrictFactor (C := C) (s := σ.slicing) (a := a) (b := b)
              (P := Psem) (S := S) G hS ψQ hψQ_ss (fun j => (hG j).1)
          refine ⟨H, ?_⟩
          intro j
          by_cases hj : j.val < G.n
          · have hGj := hG ⟨j.val, hj⟩
            have hGj' : t < G.φ ⟨j.val, hj⟩ ∧ G.φ ⟨j.val, hj⟩ < U := by
              exact ⟨lt_trans hψQ_gt hGj.1, hGj.2⟩
            simpa [H, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hj] using hGj'
          · have hj_lt : j.val < G.n + 1 := by
              simpa [H, HNFiltration.appendStrictFactor, HNFiltration.appendFactor] using j.is_lt
            have hjEq : j.val = G.n := by
              omega
            have hG_last : G.n < H.n := by
              simpa [H, HNFiltration.appendStrictFactor, HNFiltration.appendFactor] using
                (show G.n < G.n + 1 by omega)
            have hjLast : j = ⟨G.n, hG_last⟩ := Fin.ext hjEq
            subst j
            have hjFalse : ¬G.n < G.n := by omega
            simpa [H, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hjFalse,
              ψQ] using ⟨hψQ_gt, hψQ_hi⟩

variable [IsTriangulated C] in
/-- **Node 7.7 (paper-facing statement).** This is the thin-interval HN theorem in the
shape required by Bridgeland's Lemma 7.7: the thin quasi-abelian category `P((a, b))`
itself is assumed to have finite length, encoded as ACC/DCC on strict subobjects.
The remaining input is the semistable Hom-vanishing supplied by Lemma 7.6. -/
theorem Subobject.map_eq_mk_mono
    {D : Type*} [Category D] {X Y : D} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    (Subobject.map f).obj S = Subobject.mk (S.arrow ≫ f) := by
  calc
    (Subobject.map f).obj S = (Subobject.map f).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ f) := by
      simpa using (Subobject.map_mk S.arrow f)

noncomputable def Subobject.mapMonoIso
    {D : Type*} [Category D] {X Y : D} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    ((Subobject.map f).obj S : D) ≅ (S : D) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ f) (Subobject.map_eq_mk_mono f S)

theorem Subobject.ofLE_map_comp_mapMonoIso_hom
    {D : Type*} [Category D] {X Y : D} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
        ((Subobject.map f).monotone h) ≫ (Subobject.mapMonoIso f T).hom =
      (Subobject.mapMonoIso f S).hom ≫ Subobject.ofLE S T h := by
  apply Subobject.eq_of_comp_arrow_eq
  apply (cancel_mono f).1
  simp [Subobject.mapMonoIso, Subobject.map_eq_mk_mono, Category.assoc]

noncomputable def Subobject.cokernelMapMonoIso
    {D : Type*} [Category D] [HasZeroMorphisms D] [HasCokernels D]
    {X Y : D} (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h)) ≅
      cokernel (Subobject.ofLE S T h) :=
  cokernel.mapIso _ _ (Subobject.mapMonoIso f S) (Subobject.mapMonoIso f T)
    (by simpa [Category.assoc] using (Subobject.ofLE_map_comp_mapMonoIso_hom f h))

theorem wPhaseOf_cokernel_mapMono_eq
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    [HasCokernels (s.IntervalCat C a b)]
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    wPhaseOf
        (ssf.W
          (K₀.of C
            (cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
              ((Subobject.map f).monotone h))).obj)) ssf.α =
      wPhaseOf
        (ssf.W (K₀.of C (cokernel (Subobject.ofLE S T h)).obj)) ssf.α := by
  let eC :=
    (Slicing.IntervalCat.ι (C := C) (s := s) a b).mapIso
      (Subobject.cokernelMapMonoIso f h)
  simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)

noncomputable def interval_cokernelTopIso
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    [HasCokernels (s.IntervalCat C a b)]
    {X : s.IntervalCat C a b} (A : Subobject X) :
    cokernel (Subobject.ofLE A ⊤ le_top) ≅ cokernel A.arrow :=
  (cokernelCompIsIso (Subobject.ofLE A ⊤ le_top) (⊤ : Subobject X).arrow).symm ≪≫
    cokernelIsoOfEq (Subobject.ofLE_arrow (X := A) (Y := ⊤) le_top)

theorem wPhaseOf_cokernel_ofLE_top_eq
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ssf : SkewedStabilityFunction C s a b}
    [HasCokernels (s.IntervalCat C a b)]
    {X : s.IntervalCat C a b} (A : Subobject X) :
    wPhaseOf (ssf.W (K₀.of C (cokernel (Subobject.ofLE A ⊤ le_top)).obj)) ssf.α =
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
  let eC :=
    (Slicing.IntervalCat.ι (C := C) (s := s) a b).mapIso
      (interval_cokernelTopIso (C := C) (s := s) (a := a) (b := b) A)
  simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)

theorem wPhaseOf_cokernel_kernelSubobject_eq
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ssf : SkewedStabilityFunction C s a b}
    {E B : s.IntervalCat C a b} (q : E ⟶ B) (hq : IsStrictEpi q) :
    wPhaseOf (ssf.W (K₀.of C (cokernel (kernelSubobject q).arrow).obj)) ssf.α =
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α := by
  have hK_strict : IsStrictMono (kernelSubobject q).arrow := by
    simpa using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s) (a := a) (b := b) (kernel.ι q) (isStrictMono_kernel q))
  have hsumB :
      ssf.W (K₀.of C E.obj) =
        ssf.W (K₀.of C (kernelSubobject q : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C B.obj) := by
    simpa [map_add] using
      ssf.strict_additive
        (C := C) (s := s) (a := a) (b := b)
        (interval_strictShortExact_of_kernelSubobject_strictEpi
          (C := C) (s := s) (a := a) (b := b) q hq)
  have hsumC :
      ssf.W (K₀.of C E.obj) =
        ssf.W (K₀.of C (kernelSubobject q : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel (kernelSubobject q).arrow).obj) := by
    simpa [map_add] using
      ssf.strict_additive
        (C := C) (s := s) (a := a) (b := b)
        (interval_strictShortExact_cokernel_of_strictMono
          (C := C) (s := s) (a := a) (b := b) (kernelSubobject q).arrow hK_strict)
  have hWB :
      ssf.W (K₀.of C B.obj) =
        ssf.W (K₀.of C (cokernel (kernelSubobject q).arrow).obj) := by
    apply add_left_cancel
      (a := ssf.W (K₀.of C (kernelSubobject q : s.IntervalCat C a b).obj))
    exact hsumB.symm.trans hsumC
  simpa [hWB] using congrArg (fun x ↦ wPhaseOf x ssf.α) hWB.symm


end CategoryTheory.Triangulated
