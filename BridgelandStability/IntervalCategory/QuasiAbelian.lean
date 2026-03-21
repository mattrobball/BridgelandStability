/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.IntervalCategory.TwoHeartEmbedding

/-!
# Quasi-Abelian Structure of Interval Categories

Preabelian and quasi-abelian structure, strict morphisms, local finiteness,
skewed stability functions, and K₀ relations for interval subcategories.
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


section Preabelian

variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The left ambient abelian heart `P((a,a+1])`. -/
abbrev Slicing.LeftHeart (s : Slicing C) (a : ℝ) :=
  ((s.phaseShift C a).toTStructure).heart.FullSubcategory

/-- The right ambient abelian heart `P([b-1,b))`. -/
abbrev Slicing.RightHeart (s : Slicing C) (b : ℝ) :=
  ((s.phaseShift C (b - 1)).toTStructureGE).heart.FullSubcategory

theorem Slicing.intervalCat_hasKernel (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) : HasKernel f := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (s := s) (C := C) a b hab
  let XH : t.heart.FullSubcategory := FL.obj X
  let YH : t.heart.FullSubcategory := FL.obj Y
  let fH : XH ⟶ YH := FL.map f
  let π : XH ⟶ cokernel (kernel.ι fH) := cokernel.π (kernel.ι fH)
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) π
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
      by exact congrArg InducedCategory.Hom.hom eK.hom_inv_id,
      by exact congrArg InducedCategory.Hom.hom eK.inv_hom_id⟩
  have hKer_mem : s.intervalProp C a b (kernel fH).obj :=
    (s.intervalProp C a b).prop_of_iso eK0 hK_mem_aux
  let KI : s.IntervalCat C a b := ⟨(kernel fH).obj, hKer_mem⟩
  let k : KI ⟶ X := ObjectProperty.homMk (kernel.ι fH).hom
  have hk_zero : k ≫ f = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι fH ≫ fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition fH)
  refine ⟨⟨KernelFork.ofι k hk_zero, ?_⟩⟩
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
      change m.hom ≫ (kernel.ι fH).hom =
        (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom
      rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
      simpa [mH, k] using congrArg InducedCategory.Hom.hom hm
    have hmEq : mH = kernel.lift fH ι' hι' :=
      Fork.IsLimit.hom_ext (kernelIsKernel fH) hm'
    apply ((s.intervalProp C a b).ι).map_injective
    change m.hom = (kernel.lift fH ι' hι').hom
    simpa [mH] using congrArg InducedCategory.Hom.hom hmEq

noncomputable instance Slicing.intervalCat_hasKernels (s : Slicing C) :
    HasKernels (s.IntervalCat C a b) :=
  ⟨fun {X Y} f ↦ Slicing.intervalCat_hasKernel (C := C) (s := s)
    (a := a) (b := b) (X := X) (Y := Y) f⟩

theorem Slicing.intervalCat_hasCokernel (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) : HasCokernel f := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (s := s) (C := C) a b hab
  let XH : t.heart.FullSubcategory := FR.obj X
  let YH : t.heart.FullSubcategory := FR.obj Y
  let fH : XH ⟶ YH := FR.map f
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) (cokernel.π fH)
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property |>.1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hQLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 (cokernel fH).obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1))
      (cokernel fH).obj).mp
      (cokernel fH).property |>.2
  have hQLt : s.ltProp C b (cokernel fH).obj := by
    simpa [show 1 + (b - 1) = b by grind] using
      (s.phaseShift_ltProp C (b - 1) 1 (cokernel fH).obj).mp hQLtShift
  have hT' : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := by
    simpa using hT
  have hCoker_mem : s.intervalProp C a b (cokernel fH).obj :=
    s.third_intervalProp_of_triangle C hab' Y.property hKGe hQLt hT'
  let QI : s.IntervalCat C a b := ⟨(cokernel fH).obj, hCoker_mem⟩
  let p : Y ⟶ QI := ObjectProperty.homMk (cokernel.π fH).hom
  have hp_zero : f ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (fH ≫ cokernel.π fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition fH)
  refine ⟨⟨CokernelCofork.ofπ p hp_zero, ?_⟩⟩
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
    (fun {W'} g hg m hm ↦ ?_)
  · let WH : t.heart.FullSubcategory := FR.obj W'
    let π' : YH ⟶ WH := FR.map g
    have hπ' : fH ≫ π' = 0 := by
      apply ((t.heart).ι).map_injective
      simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
    exact ObjectProperty.homMk (cokernel.desc fH π' hπ').hom
  · let WH : t.heart.FullSubcategory := FR.obj W'
    let π' : YH ⟶ WH := FR.map g
    have hπ' : fH ≫ π' = 0 := by
      apply ((t.heart).ι).map_injective
      simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
    apply ((s.intervalProp C a b).ι).map_injective
    change (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = g.hom
    rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
      exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
    rfl
  · let WH : t.heart.FullSubcategory := FR.obj W'
    let π' : YH ⟶ WH := FR.map g
    have hπ' : fH ≫ π' = 0 := by
      apply ((t.heart).ι).map_injective
      simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
    let mH : cokernel fH ⟶ WH := ObjectProperty.homMk m.hom
    have hm' : cokernel.π fH ≫ mH = cokernel.π fH ≫ cokernel.desc fH π' hπ' := by
      apply ((t.heart).ι).map_injective
      change (cokernel.π fH).hom ≫ m.hom =
        (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom
      rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
      simpa [mH, p] using congrArg InducedCategory.Hom.hom hm
    have hmEq : mH = cokernel.desc fH π' hπ' :=
      Cofork.IsColimit.hom_ext (cokernelIsCokernel fH) hm'
    apply ((s.intervalProp C a b).ι).map_injective
    change m.hom = (cokernel.desc fH π' hπ').hom
    simpa [mH] using congrArg InducedCategory.Hom.hom hmEq

noncomputable instance Slicing.intervalCat_hasCokernels (s : Slicing C) :
    HasCokernels (s.IntervalCat C a b) :=
  ⟨fun {X Y} f ↦ Slicing.intervalCat_hasCokernel (C := C) (s := s)
    (a := a) (b := b) (X := X) (Y := Y) f⟩

/-- The cokernel of a morphism in `P((a,b))` is computed by the right heart
`P([b - 1, b))`. -/
noncomputable def Slicing.IntervalCat.toRightHeartCokernelIso (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C (b - 1)).toTStructureGE
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    FR.obj (cokernel f) ≅ cokernel (FR.map f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FR.obj X
  let YH : t.heart.FullSubcategory := FR.obj Y
  let fH : XH ⟶ YH := FR.map f
  classical
  let h₀ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) (cokernel.π fH)
  let K := Classical.choose h₀
  let h₁ := Classical.choose_spec h₀
  let i := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let δ := Classical.choose h₂
  let hT : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := Classical.choose_spec h₂
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property |>.1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hQLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 (cokernel fH).obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1))
      (cokernel fH).obj).mp
      (cokernel fH).property |>.2
  have hQLt : s.ltProp C b (cokernel fH).obj := by
    simpa [show 1 + (b - 1) = b by grind] using
      (s.phaseShift_ltProp C (b - 1) 1 (cokernel fH).obj).mp hQLtShift
  have hT' : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := by
    simpa using hT
  have hCoker_mem : s.intervalProp C a b (cokernel fH).obj :=
    s.third_intervalProp_of_triangle C hab' Y.property hKGe hQLt hT'
  let QI : s.IntervalCat C a b := ⟨(cokernel fH).obj, hCoker_mem⟩
  let p : Y ⟶ QI := ObjectProperty.homMk (cokernel.π fH).hom
  have hp_zero : f ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (fH ≫ cokernel.π fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition fH)
  let hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (cokernel.desc fH π' hπ').hom
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = g.hom
      rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
      rfl
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      let mH : cokernel fH ⟶ WH := ObjectProperty.homMk m.hom
      have hm' : cokernel.π fH ≫ mH = cokernel.π fH ≫ cokernel.desc fH π' hπ' := by
        apply ((t.heart).ι).map_injective
        change (cokernel.π fH).hom ≫ m.hom =
          (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom
        rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
          exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
        simpa [mH, p] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = cokernel.desc fH π' hπ' :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel fH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (cokernel.desc fH π' hπ').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : QI ≅ cokernel f := IsColimit.coconePointUniqueUpToIso hp_colim (colimit.isColimit _)
  let eH : FR.obj (cokernel f) ≅ FR.obj QI := FR.mapIso e.symm
  let j : FR.obj QI ≅ cokernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  exact eH ≪≫ j

theorem Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C (b - 1)).toTStructureGE
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    FR.map (cokernel.π f) ≫
      (Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s)
        (a := a) (b := b) f).hom =
      cokernel.π (FR.map f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FR.obj X
  let YH : t.heart.FullSubcategory := FR.obj Y
  let fH : XH ⟶ YH := FR.map f
  classical
  let h₀ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) (cokernel.π fH)
  let K := Classical.choose h₀
  let h₁ := Classical.choose_spec h₀
  let i := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let δ := Classical.choose h₂
  let hT : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := Classical.choose_spec h₂
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property |>.1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hQLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 (cokernel fH).obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1))
      (cokernel fH).obj).mp
      (cokernel fH).property |>.2
  have hQLt : s.ltProp C b (cokernel fH).obj := by
    simpa [show 1 + (b - 1) = b by grind] using
      (s.phaseShift_ltProp C (b - 1) 1 (cokernel fH).obj).mp hQLtShift
  have hT' : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := by
    simpa using hT
  have hCoker_mem : s.intervalProp C a b (cokernel fH).obj :=
    s.third_intervalProp_of_triangle C hab' Y.property hKGe hQLt hT'
  let QI : s.IntervalCat C a b := ⟨(cokernel fH).obj, hCoker_mem⟩
  let p : Y ⟶ QI := ObjectProperty.homMk (cokernel.π fH).hom
  have hp_zero : f ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (fH ≫ cokernel.π fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition fH)
  let hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (cokernel.desc fH π' hπ').hom
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = g.hom
      rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
      rfl
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      let mH : cokernel fH ⟶ WH := ObjectProperty.homMk m.hom
      have hm' : cokernel.π fH ≫ mH = cokernel.π fH ≫ cokernel.desc fH π' hπ' := by
        apply ((t.heart).ι).map_injective
        change (cokernel.π fH).hom ≫ m.hom =
          (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom
        rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
          exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
        simpa [mH, p] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = cokernel.desc fH π' hπ' :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel fH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (cokernel.desc fH π' hπ').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : QI ≅ cokernel f := IsColimit.coconePointUniqueUpToIso hp_colim (colimit.isColimit _)
  let eH : FR.obj (cokernel f) ≅ FR.obj QI := FR.mapIso e.symm
  let j : FR.obj QI ≅ cokernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  have he :
      p ≫ e.hom = cokernel.π f := by
    simpa [e, CokernelCofork.ofπ] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hp_colim (colimit.isColimit _)
        Limits.WalkingParallelPair.one
  have hp_eq : FR.map p ≫ (FR.mapIso e).hom = FR.map (cokernel.π f) := by
    simpa [e] using congrArg FR.map he
  have hp_eq' : FR.map (cokernel.π f) ≫ eH.hom = FR.map p := by
    apply (cancel_mono (FR.mapIso e).hom).1
    simpa [eH] using hp_eq.symm
  have hj_map : FR.map p ≫ j.hom = cokernel.π fH := by
    apply ((t.heart).ι).map_injective
    change (FR.map p).hom ≫ (j.hom).hom = (cokernel.π fH).hom
    have hmap : (FR.map p).hom = (cokernel.π fH).hom := by
      change p.hom = (cokernel.π fH).hom
      rfl
    rw [hmap]
    simp [j]
  change FR.map (cokernel.π f) ≫ (eH.hom ≫ j.hom) = cokernel.π fH
  rw [← Category.assoc, hp_eq', hj_map]

/-- A strict epimorphism in `P((a, b))` becomes an epimorphism in the right heart
`P([b - 1, b))`. -/
theorem Slicing.IntervalCat.epi_toRightHeart_of_strictEpi (s : Slicing C)
    {X Y : s.IntervalCat C a b} (g : X ⟶ Y) (hg : IsStrictEpi g) :
    Epi ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map g) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FR.obj (kernel g)
  let YH : t.heart.FullSubcategory := FR.obj X
  let k : kernel g ⟶ X := kernel.ι g
  let kH : XH ⟶ YH := FR.map k
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) (cokernel.π kH)
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property |>.1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hQLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 (cokernel kH).obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1))
      (cokernel kH).obj).mp
      (cokernel kH).property |>.2
  have hQLt : s.ltProp C b (cokernel kH).obj := by
    simpa [show 1 + (b - 1) = b by grind] using
      (s.phaseShift_ltProp C (b - 1) 1 (cokernel kH).obj).mp hQLtShift
  have hT' : Pretriangulated.Triangle.mk i.hom (cokernel.π kH).hom δ ∈ distTriang C := by
    simpa using hT
  have hCoker_mem : s.intervalProp C a b (cokernel kH).obj :=
    s.third_intervalProp_of_triangle C hab' X.property hKGe hQLt hT'
  let QI : s.IntervalCat C a b := ⟨(cokernel kH).obj, hCoker_mem⟩
  let p : X ⟶ QI := ObjectProperty.homMk (cokernel.π kH).hom
  have hp_zero : k ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kH ≫ cokernel.π kH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition kH)
  have hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (cokernel.desc kH π' hπ').hom
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = g.hom
      rw [show (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc kH π' hπ')]
      rfl
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg
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
  let j : FR.obj QI ≅ cokernel kH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;> ext <;> simp
  have hj : FR.map p ≫ j.hom = cokernel.π kH := by
    apply ((t.heart).ι).map_injective
    change (FR.map p).hom ≫ (j.hom).hom = (cokernel.π kH).hom
    have hmap : (FR.map p).hom = (cokernel.π kH).hom := by
      change p.hom = (cokernel.π kH).hom
      rfl
    rw [hmap]
    simp [j]
  have hp_eq : FR.map p = cokernel.π kH ≫ j.inv := by
    letI : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
    letI : Mono j.hom := by infer_instance
    exact (cancel_mono j.hom).1 (by simpa [Category.assoc] using hj)
  have hp_epi : Epi (FR.map p) := by
    letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
    haveI : Epi (cokernel.π kH ≫ j.inv) := inferInstance
    simpa [hp_eq]
  let eH : FR.obj QI ≅ FR.obj Y := FR.mapIso e
  have hmapg : FR.map p ≫ eH.hom = FR.map g := by
    simpa [eH] using congrArg FR.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  haveI : Epi (FR.map p ≫ eH.hom) := inferInstance
  simpa [hmapg]

/-- A strict monomorphism in `P((a, b))` becomes a monomorphism in the left heart
`P((a, a + 1])`. -/
theorem Slicing.IntervalCat.mono_toLeftHeart_of_strictMono (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictMono f) :
    Mono ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let YH : t.heart.FullSubcategory := FL.obj Y
  let ZH : t.heart.FullSubcategory := FL.obj (cokernel f)
  let q : Y ⟶ cokernel f := cokernel.π f
  let qH : YH ⟶ ZH := FL.map q
  let π : YH ⟶ cokernel (kernel.ι qH) := cokernel.π (kernel.ι qH)
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) π
  have hKGtShift :
      (s.phaseShift C a).gtProp C 0 K.obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a) K.obj).mp
      K.property |>.1
  have hKGt : s.gtProp C a K.obj := (s.phaseShift_gtProp_zero C a K.obj).mp hKGtShift
  have hQLeShift :
      (s.phaseShift C a).leProp C 1 (cokernel (kernel.ι qH)).obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a)
      (cokernel (kernel.ι qH)).obj).mp
      (cokernel (kernel.ι qH)).property |>.2
  have hQLe : s.leProp C (a + 1) (cokernel (kernel.ι qH)).obj := by
    simpa [add_comm] using
      (s.phaseShift_leProp C a 1 (cokernel (kernel.ι qH)).obj).mp hQLeShift
  have hT' : Pretriangulated.Triangle.mk i.hom π.hom δ ∈ distTriang C := by
    simpa using hT
  have hK_mem_aux : s.intervalProp C a b K.obj :=
    s.first_intervalProp_of_triangle C hab' Y.property hQLe hKGt hT'
  have hKerπ : IsLimit (KernelFork.ofι (kernel.ι qH) (cokernel.condition _)) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  let eK : K ≅ kernel qH := IsLimit.conePointUniqueUpToIso
    (Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i π δ hT) hKerπ
  let eK0 : K.obj ≅ (kernel qH).obj :=
    ⟨eK.hom.hom, eK.inv.hom,
      by exact congrArg InducedCategory.Hom.hom eK.hom_inv_id,
      by exact congrArg InducedCategory.Hom.hom eK.inv_hom_id⟩
  have hKer_mem : s.intervalProp C a b (kernel qH).obj :=
    (s.intervalProp C a b).prop_of_iso eK0 hK_mem_aux
  let KI : s.IntervalCat C a b := ⟨(kernel qH).obj, hKer_mem⟩
  let k : KI ⟶ Y := ObjectProperty.homMk (kernel.ι qH).hom
  have hk_zero : k ≫ q = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι qH ≫ qH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition qH)
  let hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ YH := FL.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (kernel.lift qH ι' hι').hom
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ YH := FL.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = g.hom
      rw [show (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι qH ι' hι')]
      rfl
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ YH := FL.map g
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
  let j : kernel qH ≅ FL.obj KI := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;> ext <;> simp
  have hj : j.hom ≫ FL.map k = kernel.ι qH := by
    apply ((t.heart).ι).map_injective
    change (j.hom).hom ≫ (FL.map k).hom = (kernel.ι qH).hom
    have hmap : (FL.map k).hom = (kernel.ι qH).hom := by
      change k.hom = (kernel.ι qH).hom
      rfl
    rw [hmap]
    simp [j]
  have hk_eq : FL.map k = j.inv ≫ kernel.ι qH := by
    letI : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
    letI : Epi j.hom := by infer_instance
    exact (cancel_epi j.hom).1 (by simpa [Category.assoc] using hj)
  have hk_mono : Mono (FL.map k) := by
    letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
    haveI : Mono (j.inv ≫ kernel.ι qH) := inferInstance
    simpa [hk_eq]
  let eH : FL.obj X ≅ FL.obj KI := FL.mapIso e
  have hmapf : eH.hom ≫ FL.map k = FL.map f := by
    simpa [eH] using congrArg FL.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  haveI : Mono (eH.hom ≫ FL.map k) := inferInstance
  simpa [hmapf]

end Preabelian

end CategoryTheory.Triangulated
