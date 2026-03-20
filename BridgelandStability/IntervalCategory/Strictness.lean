/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.IntervalCategory.QuasiAbelian

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section Preabelian

variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]


/-!
# Strictness Properties of Interval Categories (Part 2)

Strictness transfer through left/right hearts: strict mono ↔ mono in hearts,
preservation of limits/colimits, quasi-abelian instance.
-/

theorem Slicing.IntervalCat.mono_toRightHeart_of_strictMono (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictMono f) :
    Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f) := by
  have hab : b - a ≤ 1 := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let q : Y ⟶ cokernel f := cokernel.π f
  let qH : FR.obj Y ⟶ FR.obj (cokernel f) := FR.map q
  let eQ := Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s) (a := a) (b := b) f
  have hqHeq : qH ≫ eQ.hom = cokernel.π (FR.map f) := by
    simpa [qH, FR, eQ] using Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
      (C := C) (s := s) (a := a) (b := b) f
  have himage_zero : Abelian.image.ι (FR.map f) ≫ qH = 0 := by
    apply (cancel_mono eQ.hom).1
    simpa [Category.assoc, hqHeq] using kernel.condition (cokernel.π (FR.map f))
  have himage_kernel : IsLimit
      (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero) := by
    exact isKernelOfComp (f := qH) eQ.hom (cokernel.π (FR.map f))
      (kernelIsKernel (cokernel.π (FR.map f))) himage_zero hqHeq
  have hkernel_qH : IsLimit (KernelFork.ofι (kernel.ι qH) (kernel.condition qH)) := by
    simpa using kernelIsKernel qH
  let eKh : Abelian.image (FR.map f) ⟶ kernel qH :=
    hkernel_qH.lift (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero)
  have heKh : eKh ≫ kernel.ι qH = Abelian.image.ι (FR.map f) := by
    simpa [eKh, KernelFork.ofι] using
      hkernel_qH.fac (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero)
        Limits.WalkingParallelPair.zero
  let eKi : kernel qH ⟶ Abelian.image (FR.map f) :=
    himage_kernel.lift (KernelFork.ofι (kernel.ι qH) (kernel.condition qH))
  have heKi : eKi ≫ Abelian.image.ι (FR.map f) = kernel.ι qH := by
    simpa [eKi, KernelFork.ofι] using
      himage_kernel.fac (KernelFork.ofι (kernel.ι qH) (kernel.condition qH))
        Limits.WalkingParallelPair.zero
  let eK : Abelian.image (FR.map f) ≅ kernel qH := by
    refine ⟨eKh, eKi, ?_, ?_⟩
    · apply (cancel_mono (Abelian.image.ι (FR.map f))).1
      simpa [Category.assoc, heKh, heKi]
    · apply (cancel_mono (kernel.ι qH)).1
      simpa [Category.assoc, heKh, heKi]
  have heK : eK.hom ≫ kernel.ι qH = Abelian.image.ι (FR.map f) := by
    exact heKh
  let iH : FR.obj X ⟶ kernel qH := Abelian.factorThruImage (FR.map f) ≫ eK.hom
  have hiH : iH ≫ kernel.ι qH = FR.map f := by
    change (Abelian.factorThruImage (FR.map f) ≫ eK.hom) ≫ kernel.ι qH = FR.map f
    rw [Category.assoc, heK, Abelian.image.fac]
  haveI : Epi iH := by
    letI : IsIso eK.hom := ⟨⟨eK.inv, eK.hom_inv_id, eK.inv_hom_id⟩⟩
    exact CategoryTheory.epi_comp'
      (CategoryTheory.Abelian.instEpiFactorThruImage (f := FR.map f)) inferInstance
  have hK_mem : s.intervalProp C a b (kernel qH).obj := by
    exact s.intervalProp_of_epi_rightHeart (C := C) (a := a) (b := b)
      X.property iH
  let KI : s.IntervalCat C a b := ⟨(kernel qH).obj, hK_mem⟩
  let k : KI ⟶ Y := ObjectProperty.homMk (kernel.ι qH).hom
  let i : X ⟶ KI := ObjectProperty.homMk iH.hom
  have hk_zero : k ≫ q = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι qH ≫ qH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition qH)
  have hi : i ≫ k = f := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (iH ≫ kernel.ι qH).hom = (FR.map f).hom
    simpa [hiH]
  have hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let ι' : WH ⟶ FR.obj Y := FR.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (kernel.lift qH ι' hι').hom
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let ι' : WH ⟶ FR.obj Y := FR.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = g.hom
      rw [show (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι qH ι' hι')]
      rfl
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let ι' : WH ⟶ FR.obj Y := FR.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      let mH : WH ⟶ kernel qH := ObjectProperty.homMk m.hom
      have hm' : mH ≫ kernel.ι qH = kernel.lift qH ι' hι' ≫ kernel.ι qH := by
        apply ((t.heart).ι).map_injective
        change m.hom ≫ (kernel.ι qH).hom = (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom
        rw [show (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = ι'.hom by
          exact congrArg InducedCategory.Hom.hom (kernel.lift_ι qH ι' hι')]
        simpa [mH, k] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = kernel.lift qH ι' hι' :=
        Fork.IsLimit.hom_ext (kernelIsKernel qH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (kernel.lift qH ι' hι').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : X ≅ KI := IsLimit.conePointUniqueUpToIso (hf.isLimitKernelFork) hk_limit
  have he : e.hom ≫ k = f := by
    simpa [k, e, KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_hom_comp (hf.isLimitKernelFork) hk_limit
        Limits.WalkingParallelPair.zero
  let j : kernel qH ≅ FR.obj KI := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;> ext <;> simp
  have hk_map : j.inv ≫ kernel.ι qH = FR.map k := by
    apply ((t.heart).ι).map_injective
    change (j.inv ≫ kernel.ι qH).hom = (FR.map k).hom
    simp [FR, k, j]
  have hk_eq : FR.map k = j.inv ≫ kernel.ι qH := hk_map.symm
  let eH : FR.obj X ≅ FR.obj KI := FR.mapIso e
  have hmapf : eH.hom ≫ FR.map k = FR.map f := by
    simpa [eH] using congrArg FR.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
  haveI : Mono (eH.hom ≫ (j.inv ≫ kernel.ι qH)) := inferInstance
  have hfac : FR.map f ≫ 𝟙 _ = eH.hom ≫ (j.inv ≫ kernel.ι qH) := by
    simpa [Category.comp_id, hk_eq, Category.assoc] using hmapf.symm
  exact mono_of_mono_fac hfac

/-- If a morphism in `P((a, b))` becomes a monomorphism in the right heart
`P([b - 1, b))`, then it is a strict monomorphism in `P((a, b))`. -/
theorem Slicing.IntervalCat.strictMono_of_mono_toRightHeart (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y)
    [Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f)] :
    IsStrictMono f := by
  have hab : b - a ≤ 1 := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let eQ := Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s) (a := a) (b := b) f
  let eDiag :
      parallelPair (FR.map (cokernel.π f)) 0 ≅ parallelPair (cokernel.π (FR.map f)) 0 :=
    parallelPair.ext (Iso.refl _) eQ
      (by
        simpa [FR, eQ] using Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
          (C := C) (s := s) (a := a) (b := b) f)
      (by simp)
  have hlim' :
      IsLimit
        (KernelFork.ofι (FR.map f) (by
          apply ((t.heart).ι).map_injective
          change (f ≫ cokernel.π f).hom = 0
          exact congrArg InducedCategory.Hom.hom (cokernel.condition f)) :
          Fork (FR.map (cokernel.π f)) 0) := by
    let c :
        Fork (cokernel.π (FR.map f)) 0 :=
      KernelFork.ofι (FR.map f) (cokernel.condition (FR.map f))
    let s :
        Cofork (FR.map f) 0 :=
      CokernelCofork.ofπ (cokernel.π (FR.map f)) (cokernel.condition (FR.map f))
    have hcanon : IsLimit c :=
      Abelian.monoIsKernelOfCokernel s (cokernelIsCokernel (FR.map f))
    let htrans := (IsLimit.postcomposeInvEquiv eDiag c).symm hcanon
    exact IsLimit.ofIsoLimit htrans <|
      Fork.ext (Iso.refl _) (by
        have hι : c.ι = Fork.ι ((Cones.postcompose eDiag.inv).obj c) := by
          change c.ι = c.ι ≫ eDiag.inv.app WalkingParallelPair.zero
          simp [eDiag]
        simpa [c] using hι)
  have hmap :
      IsLimit (FR.mapCone (KernelFork.ofι f (cokernel.condition f))) :=
    (isLimitMapConeForkEquiv' FR (cokernel.condition f)).symm hlim'
  have hlim : IsLimit (KernelFork.ofι f (cokernel.condition f)) :=
    isLimitOfReflects FR hmap
  exact isStrictMono_of_isLimitKernelFork hlim

/-- The kernel of a morphism in `P((a,b))` is computed by the left heart
`P((a,a+1])`. -/
noncomputable def Slicing.IntervalCat.toLeftHeartKernelIso (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C a).toTStructure
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    FL.obj (kernel f) ≅ kernel (FL.map f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FL.obj X
  let YH : t.heart.FullSubcategory := FL.obj Y
  let fH : XH ⟶ YH := FL.map f
  let π : XH ⟶ cokernel (kernel.ι fH) := cokernel.π (kernel.ι fH)
  classical
  let h₀ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) π
  let K := Classical.choose h₀
  let h₁ := Classical.choose_spec h₀
  let i := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let δ := Classical.choose h₂
  let hT : Triangle.mk i.hom π.hom δ ∈ distTriang C := Classical.choose_spec h₂
  have hKπ :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i π δ hT
  have hKerπ : IsLimit (KernelFork.ofι (kernel.ι fH) (cokernel.condition _)) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  let eK : K ≅ kernel fH := IsLimit.conePointUniqueUpToIso hKπ hKerπ
  have hKGtShift :
      (s.phaseShift C a).gtProp C 0 K.obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a) K.obj).mp
      K.property |>.1
  have hKGt : s.gtProp C a K.obj := (s.phaseShift_gtProp_zero C a K.obj).mp hKGtShift
  have hQLeShift :
      (s.phaseShift C a).leProp C 1 (cokernel (kernel.ι fH)).obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a)
      (cokernel (kernel.ι fH)).obj).mp
      (cokernel (kernel.ι fH)).property |>.2
  have hQLe : s.leProp C (a + 1) (cokernel (kernel.ι fH)).obj :=
    by simpa [add_comm] using
      (s.phaseShift_leProp C a 1 (cokernel (kernel.ι fH)).obj).mp hQLeShift
  have hT' : Triangle.mk i.hom π.hom δ ∈ distTriang C := by
    simpa using hT
  have hK_mem_aux : s.intervalProp C a b K.obj :=
    s.first_intervalProp_of_triangle C hab' X.property hQLe hKGt hT'
  let eK0 : K.obj ≅ (kernel fH).obj :=
    ⟨eK.hom.hom, eK.inv.hom,
      by simpa using congrArg InducedCategory.Hom.hom eK.hom_inv_id,
      by simpa using congrArg InducedCategory.Hom.hom eK.inv_hom_id⟩
  have hKer_mem : s.intervalProp C a b (kernel fH).obj :=
    (s.intervalProp C a b).prop_of_iso eK0 hK_mem_aux
  let KI : s.IntervalCat C a b := ⟨(kernel fH).obj, hKer_mem⟩
  let k : KI ⟶ X := ObjectProperty.homMk (kernel.ι fH).hom
  have hk_zero : k ≫ f = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι fH ≫ fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition fH)
  let hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (kernel.lift fH ι' hι').hom
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = g.hom
      rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
      rfl
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      let mH : WH ⟶ kernel fH := ObjectProperty.homMk m.hom
      have hm' : mH ≫ kernel.ι fH = kernel.lift fH ι' hι' ≫ kernel.ι fH := by
        apply ((t.heart).ι).map_injective
        change m.hom ≫ (kernel.ι fH).hom = (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom
        rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
          exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
        simpa [mH, k] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = kernel.lift fH ι' hι' :=
        Fork.IsLimit.hom_ext (kernelIsKernel fH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (kernel.lift fH ι' hι').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : kernel f ≅ KI := IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk_limit
  let j : FL.obj KI ≅ kernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  exact FL.mapIso e ≪≫ j

theorem Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C a).toTStructure
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    (Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s)
      (a := a) (b := b) f).hom ≫ kernel.ι (FL.map f) = FL.map (kernel.ι f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FL.obj X
  let YH : t.heart.FullSubcategory := FL.obj Y
  let fH : XH ⟶ YH := FL.map f
  let π : XH ⟶ cokernel (kernel.ι fH) := cokernel.π (kernel.ι fH)
  classical
  let h₀ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) π
  let K := Classical.choose h₀
  let h₁ := Classical.choose_spec h₀
  let i := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let δ := Classical.choose h₂
  let hT : Triangle.mk i.hom π.hom δ ∈ distTriang C := Classical.choose_spec h₂
  have hKπ :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i π δ hT
  have hKerπ : IsLimit (KernelFork.ofι (kernel.ι fH) (cokernel.condition _)) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  let eK : K ≅ kernel fH := IsLimit.conePointUniqueUpToIso hKπ hKerπ
  have hKGtShift :
      (s.phaseShift C a).gtProp C 0 K.obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a) K.obj).mp
      K.property |>.1
  have hKGt : s.gtProp C a K.obj := (s.phaseShift_gtProp_zero C a K.obj).mp hKGtShift
  have hQLeShift :
      (s.phaseShift C a).leProp C 1 (cokernel (kernel.ι fH)).obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a)
      (cokernel (kernel.ι fH)).obj).mp
      (cokernel (kernel.ι fH)).property |>.2
  have hQLe : s.leProp C (a + 1) (cokernel (kernel.ι fH)).obj :=
    by simpa [add_comm] using
      (s.phaseShift_leProp C a 1 (cokernel (kernel.ι fH)).obj).mp hQLeShift
  have hT' : Triangle.mk i.hom π.hom δ ∈ distTriang C := by
    simpa using hT
  have hK_mem_aux : s.intervalProp C a b K.obj :=
    s.first_intervalProp_of_triangle C hab' X.property hQLe hKGt hT'
  let eK0 : K.obj ≅ (kernel fH).obj :=
    ⟨eK.hom.hom, eK.inv.hom,
      by simpa using congrArg InducedCategory.Hom.hom eK.hom_inv_id,
      by simpa using congrArg InducedCategory.Hom.hom eK.inv_hom_id⟩
  have hKer_mem : s.intervalProp C a b (kernel fH).obj :=
    (s.intervalProp C a b).prop_of_iso eK0 hK_mem_aux
  let KI : s.IntervalCat C a b := ⟨(kernel fH).obj, hKer_mem⟩
  let k : KI ⟶ X := ObjectProperty.homMk (kernel.ι fH).hom
  have hk_zero : k ≫ f = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι fH ≫ fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition fH)
  let hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (kernel.lift fH ι' hι').hom
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = g.hom
      rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
      rfl
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      let mH : WH ⟶ kernel fH := ObjectProperty.homMk m.hom
      have hm' : mH ≫ kernel.ι fH = kernel.lift fH ι' hι' ≫ kernel.ι fH := by
        apply ((t.heart).ι).map_injective
        change m.hom ≫ (kernel.ι fH).hom = (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom
        rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
          exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
        simpa [mH, k] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = kernel.lift fH ι' hι' :=
        Fork.IsLimit.hom_ext (kernelIsKernel fH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (kernel.lift fH ι' hι').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : kernel f ≅ KI := IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk_limit
  let j : FL.obj KI ≅ kernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  have hk_map : j.hom ≫ kernel.ι fH = FL.map k := by
    apply ((t.heart).ι).map_injective
    change (j.hom ≫ kernel.ι fH).hom = (FL.map k).hom
    simp [FL, k, j]
  have he : e.hom ≫ k = kernel.ι f := by
    simpa [e, KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel f) hk_limit
        Limits.WalkingParallelPair.zero
  ext
  let hgoal := congrArg InducedCategory.Hom.hom he
  convert hgoal using 1
  · change (((FL.mapIso e).hom ≫ j.hom) ≫ kernel.ι fH).hom = (e.hom ≫ k).hom
    rw [Category.assoc, hk_map]
    rfl

/-- A strict epimorphism in `P((a, b))` becomes an epimorphism in the left heart
`P((a, a + 1])`. -/
theorem Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi (s : Slicing C)
    {X Y : s.IntervalCat C a b} (g : X ⟶ Y) (hg : IsStrictEpi g) :
    Epi ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map g) := by
  have hab : b - a ≤ 1 := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let k : kernel g ⟶ X := kernel.ι g
  let kH : FL.obj (kernel g) ⟶ FL.obj X := FL.map k
  let eK := Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s) (a := a) (b := b) g
  let eQ : cokernel kH ≅ cokernel (kernel.ι (FL.map g)) :=
    cokernel.mapIso kH (kernel.ι (FL.map g)) eK (Iso.refl _)
      (by
        simpa [kH, FL] using
          (Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
            (C := C) (s := s) (a := a) (b := b) g).symm)
  let d : cokernel kH ⟶ FL.obj Y := eQ.hom ≫ Abelian.factorThruCoimage (FL.map g)
  have hd : cokernel.π kH ≫ d = FL.map g := by
    calc
      cokernel.π kH ≫ d
          = cokernel.π kH ≫ eQ.hom ≫ Abelian.factorThruCoimage (FL.map g) := by
            simp [d, Category.assoc]
      _ = cokernel.π (kernel.ι (FL.map g)) ≫ Abelian.factorThruCoimage (FL.map g) := by
            simp [eQ, Category.assoc]
      _ = FL.map g := Abelian.coimage.fac (FL.map g)
  haveI : Mono d := by
    letI : CategoryTheory.NonPreadditiveAbelian t.heart.FullSubcategory :=
      CategoryTheory.Abelian.nonPreadditiveAbelian (C := t.heart.FullSubcategory)
    letI : IsIso eQ.hom := ⟨⟨eQ.inv, eQ.hom_inv_id, eQ.inv_hom_id⟩⟩
    letI : Mono eQ.hom := by infer_instance
    change Mono (eQ.hom ≫ Abelian.factorThruCoimage (FL.map g))
    exact CategoryTheory.mono_comp'
      (hg := inferInstance)
      (hf := CategoryTheory.Abelian.instMonoFactorThruCoimage (f := FL.map g))
  have hQ_mem : s.intervalProp C a b (cokernel kH).obj :=
    s.intervalProp_of_mono_leftHeart (C := C) (a := a) (b := b) Y.property d
  let QI : s.IntervalCat C a b := ⟨(cokernel kH).obj, hQ_mem⟩
  let p : X ⟶ QI := ObjectProperty.homMk (cokernel.π kH).hom
  have hp_zero : k ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kH ≫ cokernel.π kH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition kH)
  have hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g' hg' ↦ ?_) (fun {W'} g' hg' ↦ ?_)
      (fun {W'} g' hg' m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let π' : FL.obj X ⟶ WH := FL.map g'
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg'
      exact ObjectProperty.homMk (cokernel.desc kH π' hπ').hom
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let π' : FL.obj X ⟶ WH := FL.map g'
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg'
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = g'.hom
      rw [show (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc kH π' hπ')]
      rfl
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let π' : FL.obj X ⟶ WH := FL.map g'
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg'
      let mH : cokernel kH ⟶ WH := ObjectProperty.homMk m.hom
      have hm' : cokernel.π kH ≫ mH = cokernel.π kH ≫ cokernel.desc kH π' hπ' := by
        apply ((t.heart).ι).map_injective
        change (cokernel.π kH).hom ≫ m.hom =
          (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom
        rw [show (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = π'.hom by
          exact congrArg InducedCategory.Hom.hom (cokernel.π_desc kH π' hπ')]
        simpa [mH, p] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = cokernel.desc kH π' hπ' :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel kH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (cokernel.desc kH π' hπ').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : QI ≅ Y := IsColimit.coconePointUniqueUpToIso hp_colim (hg.isColimitCokernelCofork)
  have he : p ≫ e.hom = g := by
    simpa [p, e, CokernelCofork.ofπ] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hp_colim (hg.isColimitCokernelCofork)
        Limits.WalkingParallelPair.one
  let j : FL.obj QI ≅ cokernel kH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;> ext <;> simp
  have hj : FL.map p ≫ j.hom = cokernel.π kH := by
    apply ((t.heart).ι).map_injective
    change (FL.map p).hom ≫ (j.hom).hom = (cokernel.π kH).hom
    have hmap : (FL.map p).hom = (cokernel.π kH).hom := by
      change p.hom = (cokernel.π kH).hom
      rfl
    rw [hmap]
    simp [j]
  have hp_eq : FL.map p = cokernel.π kH ≫ j.inv := by
    letI : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
    letI : Mono j.hom := by infer_instance
    exact (cancel_mono j.hom).1 (by simpa [Category.assoc] using hj)
  have hp_epi : Epi (FL.map p) := by
    letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
    haveI : Epi (cokernel.π kH ≫ j.inv) := inferInstance
    simpa [hp_eq]
  let eH : FL.obj QI ≅ FL.obj Y := FL.mapIso e
  have hmapg : FL.map p ≫ eH.hom = FL.map g := by
    simpa [eH] using congrArg FL.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  haveI : Epi (FL.map p ≫ eH.hom) := inferInstance
  simpa [hmapg]

/-- If a morphism in `P((a, b))` becomes an epimorphism in the left heart
`P((a, a + 1])`, then it is a strict epimorphism in `P((a, b))`. -/
theorem Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart (s : Slicing C)
    {X Y : s.IntervalCat C a b} (g : X ⟶ Y)
    [Epi ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map g)] :
    IsStrictEpi g := by
  have hab : b - a ≤ 1 := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let eK := Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s) (a := a) (b := b) g
  let eDiag :
      parallelPair (FL.map (kernel.ι g)) 0 ≅ parallelPair (kernel.ι (FL.map g)) 0 :=
    parallelPair.ext eK (Iso.refl _)
      (by
        simpa [FL, eK] using (Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
          (C := C) (s := s) (a := a) (b := b) g).symm)
      (by simp)
  have hcolim' :
      IsColimit
        (CokernelCofork.ofπ (FL.map g) (by
          apply ((t.heart).ι).map_injective
          change (kernel.ι g ≫ g).hom = 0
          exact congrArg InducedCategory.Hom.hom (kernel.condition g)) :
          Cofork (FL.map (kernel.ι g)) 0) := by
    let c :
        Cofork (kernel.ι (FL.map g)) 0 :=
      CokernelCofork.ofπ (FL.map g) (kernel.condition (FL.map g))
    have hcanon : IsColimit c :=
      Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι (FL.map g))
        (kernel.condition (FL.map g))) (kernelIsKernel (FL.map g))
    let htrans := (IsColimit.precomposeHomEquiv eDiag c).symm hcanon
    exact IsColimit.ofIsoColimit htrans <|
      Cofork.ext (Iso.refl _) (by
        have hπ :
            Cofork.π ((Cocone.precompose eDiag.hom).obj c) =
              eDiag.hom.app WalkingParallelPair.one ≫ c.π := by
          change eDiag.hom.app WalkingParallelPair.one ≫ c.π =
            eDiag.hom.app WalkingParallelPair.one ≫ c.π
          rfl
        have h₁ :
            Cofork.π ((Cocone.precompose eDiag.hom).obj c) ≫
                (Iso.refl ((Cocone.precompose eDiag.hom).obj c).pt).hom =
              eDiag.hom.app WalkingParallelPair.one ≫ c.π := by
          simpa [Category.assoc] using congrArg
            (fun k => k ≫ (Iso.refl ((Cocone.precompose eDiag.hom).obj c).pt).hom) hπ
        have h₂ : eDiag.hom.app WalkingParallelPair.one ≫ c.π = FL.map g := by
          simp [c, eDiag]
        exact h₁.trans h₂)
  have hmap :
      IsColimit (FL.mapCocone (CokernelCofork.ofπ g (kernel.condition g))) :=
    (isColimitMapCoconeCoforkEquiv' FL (kernel.condition g)).symm hcolim'
  have hcolim : IsColimit (CokernelCofork.ofπ g (kernel.condition g)) :=
    isColimitOfReflects FL hmap
  exact isStrictEpi_of_isColimitCokernelCofork hcolim


end Preabelian

end CategoryTheory.Triangulated
