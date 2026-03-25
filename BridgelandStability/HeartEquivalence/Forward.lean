/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.HeartEquivalence.AmplitudeFormulas

/-!
# Forward Direction: StabilityCondition to HeartStabilityData

Construction of the stability function on the heart from a stability
condition on the ambient triangulated category (Proposition 5.3, forward
direction). Includes phase computation, semistability lifting, and
HN filtration assembly in the heart.
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

section Proposition53

variable [IsTriangulated C]

/-! ## Forward: StabilityCondition → HeartStabilityData -/

/-- Restrict a Bridgeland stability condition to the heart of its associated
t-structure, producing the induced stability function on that abelian heart. -/
def StabilityCondition.stabilityFunctionOnHeart
    (σ : StabilityCondition C) :
    @StabilityFunction (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian) := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  exact {
    Zobj := fun E => σ.Z (K₀.of C E.obj)
    map_zero' := fun X hX => by
      simpa using congrArg σ.Z (K₀.of_isZero C (((t.heart).ι.map_isZero hX)))
    additive := fun S hS => by
      letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
      letI : IsNormalMonoCategory t.heart.FullSubcategory := Abelian.toIsNormalMonoCategory
      letI : IsNormalEpiCategory t.heart.FullSubcategory := Abelian.toIsNormalEpiCategory
      letI : Balanced t.heart.FullSubcategory := by infer_instance
      haveI := hS.mono_f
      haveI := hS.epi_g
      obtain ⟨δ, hT⟩ :=
        TStructure.heartFullSubcategory_shortExact_triangle (C := C) t S.f S.g S.zero
          (fun {W} α hα ↦ by
            have hker : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
            exact ⟨hker.lift (KernelFork.ofι α hα), hker.fac _ WalkingParallelPair.zero⟩)
      simpa using congrArg σ.Z (K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT)
    upper := fun E hE => by
      classical
      let ι := (t.heart).ι
      have hEobj : ¬IsZero E.obj := fun hZ ↦
        hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := t.heart) (X := E) hZ)
      have hEheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
      obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEobj
      let P := F.toPostnikovTower
      let s : Finset (Fin F.n) := Finset.univ.filter (fun i => ¬IsZero (P.factor i))
      have hs : s.Nonempty := by
        obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hEobj
        exact ⟨i, by simpa [s, P] using hi⟩
      have hphiMinus : 0 < σ.slicing.phiMinus C E.obj hEobj :=
        gt_phases_of_gtProp C σ.slicing hEobj hEheart.1
      have hphiPlus : σ.slicing.phiPlus C E.obj hEobj ≤ 1 :=
        σ.slicing.phiPlus_le_of_leProp C hEobj hEheart.2
      have hphase_mem : ∀ i ∈ s, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
        intro i hi
        constructor
        · calc
            0 < σ.slicing.phiMinus C E.obj hEobj := hphiMinus
            _ = F.φ ⟨F.n - 1, by lia⟩ := by
              rw [σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast]
            _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
        · calc
            F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C E.obj hEobj := by
              rw [σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst]
            _ ≤ 1 := hphiPlus
      have hterm : ∀ i ∈ s, σ.Z (K₀.of C (P.factor i)) ∈ upperHalfPlaneUnion := by
        intro i hi
        letI : Abelian (σ.slicing.P (F.φ i)).FullSubcategory := σ.P_phi_abelian C (F.φ i)
        let Xi : (σ.slicing.P (F.φ i)).FullSubcategory := ⟨P.factor i, F.semistable i⟩
        have hXi : ¬IsZero Xi := by
          intro hZ
          exact (show ¬IsZero (P.factor i) from by simpa [s, P] using hi)
            ((σ.slicing.P (F.φ i)).ι.map_isZero hZ)
        exact (σ.stabilityFunctionOnPhase C (hphase_mem i hi)).upper Xi hXi
      let f : Fin F.n → ℂ := fun i => σ.Z (K₀.of C (P.factor i))
      have hsum_all : σ.Z (K₀.of C E.obj) = Finset.sum Finset.univ f := by
        rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
      let z : Finset (Fin F.n) := Finset.univ.filter (fun i => IsZero (P.factor i))
      have hzero_filter :
          Finset.sum z f = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simp only [z, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [K₀.of_isZero C hi, map_zero]
      have hsum_filter :
          Finset.sum Finset.univ f = Finset.sum s f := by
        calc
          Finset.sum Finset.univ f = Finset.sum s f + Finset.sum z f := by
            simpa [s, z, f] using
              (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
                (p := fun i : Fin F.n => ¬IsZero (P.factor i)) (f := f)).symm
          _ = Finset.sum s f + 0 := by rw [hzero_filter]
          _ = Finset.sum s f := by simp
      rw [hsum_all, hsum_filter]
      exact sum_mem_upperHalfPlane hs hterm }

theorem StabilityCondition.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi
    (σ : StabilityCondition C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1)
    (E : (σ.slicing.toTStructure.heart).FullSubcategory)
    (hP : σ.slicing.P φ E.obj) (hE : ¬IsZero E) :
    @StabilityFunction.phase _ _ ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      (σ.stabilityFunctionOnHeart C) E = φ := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦
    hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ)
  obtain ⟨m, hm, hmZ⟩ := stabilityCondition_compat_apply (C := C) σ φ E.obj hP hEobj
  have harg : Complex.arg ((m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I)) = Real.pi * φ := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor
    · nlinarith [Real.pi_pos, hφ.1]
    · nlinarith [Real.pi_pos, hφ.2]
  change (1 / Real.pi) * Complex.arg (σ.Z (K₀.of C E.obj)) = φ
  rw [hmZ, harg]
  field_simp [Real.pi_ne_zero]

theorem StabilityCondition.stabilityFunctionOnHeart_phase_le_phiPlus
    (σ : StabilityCondition C)
    (E : (σ.slicing.toTStructure.heart).FullSubcategory) (hE : ¬IsZero E) :
    @StabilityFunction.phase _ _ ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      (σ.stabilityFunctionOnHeart C) E ≤
        σ.slicing.phiPlus C E.obj
          (fun hZ ↦ hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
            (C := C) (P := σ.slicing.toTStructure.heart) (X := E) hZ)) := by
  classical
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦
    hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ)
  have hEheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEobj
  let P := F.toPostnikovTower
  let s : Finset (Fin F.n) := Finset.univ.filter (fun i => ¬IsZero (P.factor i))
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hEobj
    exact ⟨i, by simpa [s, P] using hi⟩
  have hphiMinus : 0 < σ.slicing.phiMinus C E.obj hEobj :=
    gt_phases_of_gtProp C σ.slicing hEobj hEheart.1
  have hphiPlus : σ.slicing.phiPlus C E.obj hEobj ≤ 1 :=
    σ.slicing.phiPlus_le_of_leProp C hEobj hEheart.2
  have hphase_mem : ∀ i ∈ s, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i hi
    constructor
    · calc
        0 < σ.slicing.phiMinus C E.obj hEobj := hphiMinus
        _ = F.φ ⟨F.n - 1, by lia⟩ := by
          rw [σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast]
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C E.obj hEobj := by
          rw [σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst]
        _ ≤ 1 := hphiPlus
  let f : Fin F.n → ℂ := fun i => σ.Z (K₀.of C (P.factor i))
  have hterm : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion := by
    intro i hi
    letI : Abelian (σ.slicing.P (F.φ i)).FullSubcategory := σ.P_phi_abelian C (F.φ i)
    let Xi : (σ.slicing.P (F.φ i)).FullSubcategory := ⟨P.factor i, F.semistable i⟩
    have hXi : ¬IsZero Xi := by
      intro hZ
      exact (show ¬IsZero (P.factor i) from by simpa [s, P] using hi)
        ((σ.slicing.P (F.φ i)).ι.map_isZero hZ)
    simpa [f] using (σ.stabilityFunctionOnPhase C (hphase_mem i hi)).upper Xi hXi
  have harg_factor : ∀ i ∈ s, Complex.arg (f i) = Real.pi * F.φ i := by
    intro i hi
    have hi_ne : ¬IsZero (P.factor i) := by
      simpa [s, P] using hi
    obtain ⟨m, hm, hmZ⟩ := stabilityCondition_compat_apply (C := C) σ (F.φ i) (P.factor i) (F.semistable i) hi_ne
    rw [show f i = (m : ℂ) * Complex.exp (↑(Real.pi * F.φ i) * Complex.I) by
      simpa [f] using hmZ]
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor
    · nlinarith [Real.pi_pos, (hphase_mem i hi).1]
    · nlinarith [Real.pi_pos, (hphase_mem i hi).2]
  have hsum_all : σ.Z (K₀.of C E.obj) = Finset.sum Finset.univ f := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  let z : Finset (Fin F.n) := Finset.univ.filter (fun i => IsZero (P.factor i))
  have hzero_filter :
      Finset.sum z f = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [z, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    change σ.Z (K₀.of C (P.factor i)) = 0
    rw [K₀.of_isZero C hi, map_zero]
  have hsum_filter :
      Finset.sum Finset.univ f = Finset.sum s f := by
    calc
      Finset.sum Finset.univ f = Finset.sum s f + Finset.sum z f := by
        simpa [s, z, f] using
          (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
            (p := fun i : Fin F.n => ¬IsZero (P.factor i)) (f := f)).symm
      _ = Finset.sum s f + 0 := by rw [hzero_filter]
      _ = Finset.sum s f := by simp
  have hsup_le :
      s.sup' hs (Complex.arg ∘ f) ≤ Real.pi * σ.slicing.phiPlus C E.obj hEobj := by
    refine (Finset.sup'_le_iff hs (Complex.arg ∘ f)).2 ?_
    intro i hi
    rw [Function.comp_apply, harg_factor i hi]
    have hle : F.φ i ≤ σ.slicing.phiPlus C E.obj hEobj := by
      calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C E.obj hEobj := by
          rw [σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst]
    nlinarith [Real.pi_pos, hle]
  change (1 / Real.pi) * Complex.arg (σ.Z (K₀.of C E.obj)) ≤ σ.slicing.phiPlus C E.obj hEobj
  rw [hsum_all, hsum_filter]
  have harg_le := arg_sum_le_sup'_of_upperHalfPlane hs hterm
  have harg_le' :
      Complex.arg (Finset.sum s f) ≤ Real.pi * σ.slicing.phiPlus C E.obj hEobj :=
    harg_le.trans hsup_le
  have hmul : (1 / Real.pi) * Complex.arg (Finset.sum s f) ≤
      (1 / Real.pi) * (Real.pi * σ.slicing.phiPlus C E.obj hEobj) :=
    mul_le_mul_of_nonneg_left harg_le' (by positivity)
  simpa [Real.pi_ne_zero] using hmul

theorem StabilityCondition.stabilityFunctionOnHeart_isSemistable_of_mem_P_phi
    (σ : StabilityCondition C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1)
    (E : (σ.slicing.toTStructure.heart).FullSubcategory)
    (hP : σ.slicing.P φ E.obj) (hE : ¬IsZero E) :
    @StabilityFunction.IsSemistable _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      (σ.stabilityFunctionOnHeart C) E := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦
    hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ)
  refine ⟨hE, ?_⟩
  intro B hB
  let B' : t.heart.FullSubcategory := (B : t.heart.FullSubcategory)
  have hBobj : ¬IsZero B'.obj := fun hZ ↦
    hB (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := B') hZ)
  have hphiPlus_le : σ.slicing.phiPlus C B'.obj hBobj ≤ φ := by
    by_contra hgt
    push_neg at hgt
    have hBheart := (σ.slicing.toTStructure_heart_iff C B'.obj).mp B'.property
    obtain ⟨F, hn, hfirst⟩ := HNFiltration.exists_nonzero_first C σ.slicing hBobj
    have htop : σ.slicing.phiPlus C B'.obj hBobj = F.φ ⟨0, hn⟩ :=
      σ.slicing.phiPlus_eq C B'.obj hBobj F hn hfirst
    have hphase_gt : φ < F.φ ⟨0, hn⟩ := by
      rw [← htop]
      exact hgt
    have hphase_mem : F.φ ⟨0, hn⟩ ∈ Set.Ioc (0 : ℝ) 1 := by
      constructor
      · exact lt_trans hφ.1 hphase_gt
      · rw [← htop]
        exact σ.slicing.phiPlus_le_of_leProp C hBobj hBheart.2
    have hA0_heart : t.heart (F.triangle ⟨0, hn⟩).obj₃ := by
      rw [σ.slicing.toTStructure_heart_iff C]
      exact ⟨σ.slicing.gtProp_of_semistable C (F.φ ⟨0, hn⟩) 0 _
          (F.semistable ⟨0, hn⟩) hphase_mem.1,
        σ.slicing.leProp_of_semistable C (F.φ ⟨0, hn⟩) 1 _
          (F.semistable ⟨0, hn⟩) hphase_mem.2⟩
    have hα :
        ∃ α : (F.triangle ⟨0, hn⟩).obj₃ ⟶ B'.obj, α ≠ 0 := by
      by_contra hzero
      push_neg at hzero
      exact hfirst (F.isZero_factor_zero_of_hom_eq_zero C σ.slicing hn hzero)
    rcases hα with ⟨α, hα⟩
    let A0 : t.heart.FullSubcategory := ⟨(F.triangle ⟨0, hn⟩).obj₃, hA0_heart⟩
    let αH : A0 ⟶ B' := ObjectProperty.homMk α
    have hcomp_ne : α ≫ B.arrow.hom ≠ 0 := by
      intro h0
      have h0H : αH ≫ B.arrow = 0 := by
        ext
        exact h0
      have hαH0 : αH = 0 := (cancel_mono B.arrow).mp (by simpa using h0H)
      exact hα (by simpa [αH] using congr_arg (·.hom) hαH0)
    exact hcomp_ne <| σ.slicing.hom_vanishing (F.φ ⟨0, hn⟩) φ _ _ hphase_gt
      (F.semistable ⟨0, hn⟩) hP (α ≫ B.arrow.hom)
  calc
    (σ.stabilityFunctionOnHeart C).phase B' ≤ σ.slicing.phiPlus C B'.obj hBobj :=
      σ.stabilityFunctionOnHeart_phase_le_phiPlus C B' hB
    _ ≤ φ := hphiPlus_le
    _ = (σ.stabilityFunctionOnHeart C).phase E :=
      (σ.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi C hφ E hP hE).symm

section AbelianHelpers

variable {A : Type*} [Category A] [Abelian A]

theorem phase_cokernel_ofLE_congr_local (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂} :
    Z.phase (cokernel (Subobject.ofLE A₁ B₁ h₁)) =
      Z.phase (cokernel (Subobject.ofLE A₂ B₂ h₂)) := by
  subst hA
  subst hB
  rfl

theorem isSemistable_cokernel_ofLE_congr_local (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂}
    (hs : Z.IsSemistable (cokernel (Subobject.ofLE A₂ B₂ h₂))) :
    Z.IsSemistable (cokernel (Subobject.ofLE A₁ B₁ h₁)) := by
  subst hA
  subst hB
  exact hs

omit [Abelian A] in
theorem Subobject.map_eq_mk_mono_local {X Y : A} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    (Subobject.map f).obj S = Subobject.mk (S.arrow ≫ f) := by
  calc
    (Subobject.map f).obj S = (Subobject.map f).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ f) := by
      simpa using (Subobject.map_mk S.arrow f)

/-- The image of a subobject along a monomorphism is canonically isomorphic to
the original subobject. -/
noncomputable def Subobject.mapMonoIso_local {X Y : A} (f : X ⟶ Y) [Mono f]
    (S : Subobject X) :
    ((Subobject.map f).obj S : A) ≅ (S : A) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ f) (Subobject.map_eq_mk_mono_local f S)

omit [Abelian A] in
theorem Subobject.ofLE_map_comp_mapMonoIso_hom_local {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
        ((Subobject.map f).monotone h) ≫ (Subobject.mapMonoIso_local f T).hom =
      (Subobject.mapMonoIso_local f S).hom ≫ Subobject.ofLE S T h := by
  apply Subobject.eq_of_comp_arrow_eq
  apply (cancel_mono f).1
  simp [Subobject.mapMonoIso_local, Category.assoc]

/-- Taking cokernels after mapping a short exact quotient along a monomorphism
does not change the resulting quotient object. -/
noncomputable def Subobject.cokernelMapMonoIso_local {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h)) ≅
      cokernel (Subobject.ofLE S T h) :=
  cokernel.mapIso _ _ (Subobject.mapMonoIso_local f S) (Subobject.mapMonoIso_local f T)
    (by simpa [Category.assoc] using (Subobject.ofLE_map_comp_mapMonoIso_hom_local f h))

theorem phase_cokernel_mapMono_eq_local (Z : StabilityFunction A) {X Y : A} (f : X ⟶ Y)
    [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.phase (cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h))) =
      Z.phase (cokernel (Subobject.ofLE S T h)) :=
  Z.phase_eq_of_iso (Subobject.cokernelMapMonoIso_local f h)

theorem isSemistable_cokernel_mapMono_iff_local (Z : StabilityFunction A) {X Y : A}
    (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.IsSemistable (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
      ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) ↔
      Z.IsSemistable (cokernel (Subobject.ofLE S T h)) := by
  constructor <;> intro hs
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso_local f h) hs
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso_local f h).symm hs

theorem StabilityFunction.exists_hn_with_last_phase_of_semistable_local
    (Z : StabilityFunction A) {E : A} (hss : Z.IsSemistable E) :
    ∃ F : AbelianHNFiltration Z E,
      F.φ ⟨F.n - 1, by have := F.hn; lia⟩ = Z.phase E := by
  refine ⟨{
    n := 1
    hn := Nat.one_pos
    chain := fun i ↦ if i = 0 then ⊥ else ⊤
    chain_strictMono := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ h
      simp only [Fin.lt_def] at h
      have hi0 : i = 0 := by lia
      have hj1 : j = 1 := by lia
      subst hi0; subst hj1
      simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ↓reduceIte,
        Fin.mk_one, one_ne_zero, gt_iff_lt]
      exact lt_of_le_of_ne bot_le
        (Ne.symm (StabilityFunction.subobject_top_ne_bot_of_not_isZero hss.1))
    chain_bot := by simp
    chain_top := by simp
    φ := fun _ ↦ Z.phase E
    φ_anti := fun a b h ↦ by exfalso; exact absurd h (by lia)
    factor_phase := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by lia
      subst hj0
      change Z.phase (cokernel (Subobject.ofLE (⊥ : Subobject E) (⊤ : Subobject E) bot_le)) =
        Z.phase E
      have h₁ :
          Z.phase (cokernel (Subobject.ofLE (⊥ : Subobject E) (⊤ : Subobject E) bot_le)) =
            Z.phase (⊤ : Subobject E) :=
        Z.phase_eq_of_iso (StabilityFunction.Subobject.cokernelBotIso ⊤ bot_le)
      exact h₁.trans (Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow))
    factor_semistable := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by lia
      subst hj0
      change Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ _))
      exact Z.isSemistable_of_iso
        ((asIso (⊤ : Subobject E).arrow).symm ≪≫
          (StabilityFunction.Subobject.cokernelBotIso ⊤ bot_le).symm) hss
  }, by simp⟩

theorem StabilityFunction.append_hn_filtration_of_mono_local
    (Z : StabilityFunction A) {X Y B : A}
    (i : X ⟶ Y) [Mono i] (F : AbelianHNFiltration Z X) (eB : cokernel i ≅ B)
    (hB : Z.IsSemistable B)
    (hlast : Z.phase B < F.φ ⟨F.n - 1, by have := F.hn; lia⟩) :
    ∃ G : AbelianHNFiltration Z Y,
      G.φ ⟨G.n - 1, by have := G.hn; lia⟩ = Z.phase B := by
  let K : Subobject Y := Subobject.mk i
  let eK : cokernel K.arrow ≅ B := by
    let eKi : cokernel K.arrow ≅ cokernel i := by
      refine cokernel.mapIso (f := K.arrow) (f' := i) (Subobject.underlyingIso i) (Iso.refl _)
        ?_
      calc
        K.arrow ≫ (Iso.refl Y).hom = K.arrow := by simp
        _ = (Subobject.underlyingIso i).hom ≫ i := by
          simp [K]
    exact eKi ≪≫ eB
  have hK_ne_top : K ≠ ⊤ := by
    intro hK
    have hmk : Subobject.mk i = ⊤ := by simpa [K] using hK
    haveI : IsIso i := (Subobject.isIso_iff_mk_eq_top i).2 hmk
    exact hB.1 ((isZero_cokernel_of_epi i).of_iso eB.symm)
  have hK_lt_top : K < ⊤ := lt_of_le_of_ne le_top hK_ne_top
  let newChain : Fin (F.n + 2) → Subobject Y := fun j =>
    if h : (j : ℕ) ≤ F.n then
      (Subobject.map i).obj (F.chain ⟨j, by lia⟩)
    else ⊤
  have hNewBot : newChain ⟨0, by lia⟩ = ⊥ := by
    change (Subobject.map i).obj (F.chain ⟨0, by lia⟩) = ⊥
    rw [F.chain_bot]
    simpa using (Subobject.map_bot i)
  have hNewK : newChain ⟨F.n, by lia⟩ = K := by
    simp [newChain, K, Subobject.map_top, F.chain_top]
  have hNewTop : newChain ⟨F.n + 1, by lia⟩ = ⊤ := by
    simp [newChain]
  have hNewMono : StrictMono newChain := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    change newChain ⟨j, by lia⟩ < newChain ⟨j + 1, by lia⟩
    by_cases hjn : j = F.n
    · subst hjn
      rw [hNewK, hNewTop]
      exact hK_lt_top
    · have hjle : j + 1 ≤ F.n := by lia
      simp [newChain, show (j : ℕ) ≤ F.n by lia, hjle]
      apply (Subobject.map i).monotone.strictMono_of_injective (Subobject.map_obj_injective i)
      exact F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
  let φ : Fin (F.n + 1) → ℝ := fun j =>
    if h : (j : ℕ) < F.n then F.φ ⟨j, h⟩ else Z.phase B
  exact ⟨{
    n := F.n + 1
    hn := Nat.succ_pos _
    chain := newChain
    chain_strictMono := hNewMono
    chain_bot := hNewBot
    chain_top := hNewTop
    φ := φ
    φ_anti := by
      intro a b hab
      dsimp [φ]
      by_cases hb : (b : ℕ) < F.n
      · have ha : (a : ℕ) < F.n :=
          lt_trans (Fin.mk_lt_mk.mp hab) hb
        simp [ha, hb]
        exact F.φ_anti (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hab))
      · have ha : (a : ℕ) < F.n := by lia
        have hlast_le :
            F.φ ⟨F.n - 1, by have := F.hn; lia⟩ ≤ F.φ ⟨a, ha⟩ :=
          F.φ_anti.antitone (Fin.mk_le_mk.mpr (by lia))
        simp [ha, hb]
        linarith
    factor_phase := by
      intro j
      by_cases hj : (j : ℕ) < F.n
      · let j' : Fin F.n := ⟨j, hj⟩
        have hcast :
            newChain j.castSucc = (Subobject.map i).obj (F.chain j'.castSucc) := by
          have hj_le : (j : ℕ) ≤ F.n := by lia
          simp [newChain, j', hj_le]
        have hsucc :
            newChain j.succ = (Subobject.map i).obj (F.chain j'.succ) := by
          have hj1_le : (j : ℕ) + 1 ≤ F.n := by lia
          simp [newChain, j', hj1_le]
        have hphase :
            Z.phase (cokernel (Subobject.ofLE ((Subobject.map i).obj (F.chain j'.castSucc))
              ((Subobject.map i).obj (F.chain j'.succ))
              ((Subobject.map i).monotone
                (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))))) =
              F.φ j' :=
          (phase_cokernel_mapMono_eq_local Z i
            (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).trans (F.factor_phase j')
        have hφj : φ j = F.φ j' := by
          simp [φ, hj, j']
        exact ((phase_cokernel_ofLE_congr_local Z hcast hsucc).trans hphase).trans hφj.symm
      · have hj_eq : (j : ℕ) = F.n := by lia
        have hcast : j.castSucc = ⟨F.n, by lia⟩ := Fin.ext hj_eq
        have hsucc : j.succ = ⟨F.n + 1, by lia⟩ := Fin.ext (by simp [hj_eq])
        have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
        have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
        have hφj : φ j = Z.phase B := by
          simp [φ, hj]
        have htarget :
            Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) =
              Z.phase (cokernel K.arrow) :=
          Z.phase_eq_of_iso
            ((cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _).symm)
        have htarget' : Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) = Z.phase B :=
          htarget.trans (Z.phase_eq_of_iso eK)
        exact ((phase_cokernel_ofLE_congr_local Z hcast_obj hsucc_obj).trans htarget').trans
          hφj.symm
    factor_semistable := by
      intro j
      by_cases hj : (j : ℕ) < F.n
      · let j' : Fin F.n := ⟨j, hj⟩
        have hcast :
            newChain j.castSucc = (Subobject.map i).obj (F.chain j'.castSucc) := by
          have hj_le : (j : ℕ) ≤ F.n := by lia
          simp [newChain, j', hj_le]
        have hsucc :
            newChain j.succ = (Subobject.map i).obj (F.chain j'.succ) := by
          have hj1_le : (j : ℕ) + 1 ≤ F.n := by lia
          simp [newChain, j', hj1_le]
        have hsemistable :
            Z.IsSemistable
              (cokernel (Subobject.ofLE ((Subobject.map i).obj (F.chain j'.castSucc))
                ((Subobject.map i).obj (F.chain j'.succ))
                ((Subobject.map i).monotone
                  (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))))) :=
          (isSemistable_cokernel_mapMono_iff_local Z i
            (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).2 (F.factor_semistable j')
        exact isSemistable_cokernel_ofLE_congr_local Z hcast hsucc hsemistable
      · have hj_eq : (j : ℕ) = F.n := by lia
        have hcast : j.castSucc = ⟨F.n, by lia⟩ := Fin.ext hj_eq
        have hsucc : j.succ = ⟨F.n + 1, by lia⟩ := Fin.ext (by simp [hj_eq])
        have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
        have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
        let eTop : B ≅ cokernel (Subobject.ofLE K ⊤ le_top) :=
          eK.symm ≪≫ (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _)
        exact isSemistable_cokernel_ofLE_congr_local Z hcast_obj hsucc_obj <|
          Z.isSemistable_of_iso eTop hB
  }, by simp [φ]⟩

end AbelianHelpers


end Proposition53

end CategoryTheory.Triangulated
