/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.IntervalCategory.TwoHeartEmbedding

/-!
# Quasi-Abelian Structure of Interval Categories

Preabelian and quasi-abelian structure, strict morphisms, local finiteness,
skewed stability functions, and K₀ relations for interval subcategories.
-/

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

noncomputable def Slicing.intervalCat_hasKernel (s : Slicing C)
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

noncomputable def Slicing.intervalCat_hasCokernel (s : Slicing C)
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
    simpa [show 1 + (b - 1) = b by ring] using
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
    simpa [show 1 + (b - 1) = b by ring] using
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
    simpa [show 1 + (b - 1) = b by ring] using
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
    simpa [show 1 + (b - 1) = b by ring] using
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
      by simpa using congrArg InducedCategory.Hom.hom eK.hom_inv_id,
      by simpa using congrArg InducedCategory.Hom.hom eK.inv_hom_id⟩
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

/-- A strict monomorphism in `P((a, b))` becomes a monomorphism in the right heart
`P([b - 1, b))`. -/
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

instance Slicing.IntervalCat.toLeftHeart_additive (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Additive (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_add := by
    intro X Y f g
    rfl

instance Slicing.IntervalCat.toRightHeart_additive (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Additive (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_add := by
    intro X Y f g
    rfl

noncomputable instance Slicing.IntervalCat.toLeftHeart_preservesKernel (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0)
      (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  change IsLimit (FL.mapCone (KernelFork.ofι (kernel.ι f) (kernel.condition f)))
  exact (isLimitMapConeForkEquiv' FL (kernel.condition f)).symm <|
    IsLimit.ofIsoLimit (kernelIsKernel (FL.map f)) <|
      Fork.ext ((Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s)
        (a := a) (b := b) f).symm) <| by
          have hι :
              (Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s)
                (a := a) (b := b) f).hom ≫ kernel.ι (FL.map f) =
                FL.map (kernel.ι f) := by
            simpa [FL] using Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
              (C := C) (s := s) (a := a) (b := b) f
          change
            (Iso.symm (Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s)
              (a := a) (b := b) f)).hom ≫ FL.map (kernel.ι f) =
              kernel.ι (FL.map f)
          rw [← hι]
          simp [Category.assoc]

noncomputable instance Slicing.IntervalCat.toRightHeart_preservesCokernel (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0)
      (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  change IsColimit (FR.mapCocone (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)))
  exact (isColimitMapCoconeCoforkEquiv' FR (cokernel.condition f)).symm <|
    IsColimit.ofIsoColimit (cokernelIsCokernel (FR.map f)) <|
      Cofork.ext ((Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s)
        (a := a) (b := b) f).symm) <| by
          have hπ :
              FR.map (cokernel.π f) ≫
                (Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s)
                  (a := a) (b := b) f).hom =
                cokernel.π (FR.map f) := by
            simpa [FR] using Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
              (C := C) (s := s) (a := a) (b := b) f
          change
            cokernel.π (FR.map f) ≫
              (Iso.symm (Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s)
                (a := a) (b := b) f)).hom =
              FR.map (cokernel.π f)
          rw [← hπ]
          simp [Category.assoc]

noncomputable instance Slicing.intervalCat_hasBinaryBiproducts (s : Slicing C) :
    HasBinaryBiproducts (s.IntervalCat C a b) :=
  HasBinaryBiproducts.of_hasBinaryProducts

noncomputable instance Slicing.intervalCat_hasEqualizers (s : Slicing C) :
    HasEqualizers (s.IntervalCat C a b) :=
  Preadditive.hasEqualizers_of_hasKernels

noncomputable instance Slicing.intervalCat_hasCoequalizers (s : Slicing C) :
    HasCoequalizers (s.IntervalCat C a b) :=
  Preadditive.hasCoequalizers_of_hasCokernels

noncomputable instance Slicing.intervalCat_hasFiniteCoproducts (s : Slicing C) :
    HasFiniteCoproducts (s.IntervalCat C a b) :=
  hasFiniteCoproducts_of_has_binary_and_initial

noncomputable instance Slicing.intervalCat_hasPullbacks (s : Slicing C) :
    HasPullbacks (s.IntervalCat C a b) := by
  exact Limits.hasPullbacks_of_hasBinaryProducts_of_hasEqualizers _

noncomputable instance Slicing.intervalCat_hasPushouts (s : Slicing C) :
    HasPushouts (s.IntervalCat C a b) := by
  exact Limits.hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers _

noncomputable instance Slicing.IntervalCat.toLeftHeart_preservesFiniteLimits (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] :
    PreservesFiniteLimits
      (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  exact Functor.preservesFiniteLimits_of_preservesKernels FL

noncomputable instance Slicing.IntervalCat.toRightHeart_preservesFiniteColimits (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] :
    PreservesFiniteColimits
      (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  exact Functor.preservesFiniteColimits_of_preservesCokernels FR

/-- Finite subobjects in the left heart transfer to finite subobjects in `P((a,b))`
via the fully faithful left-heart embedding. -/
theorem Slicing.IntervalCat.finite_subobject_of_leftHeart (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b}
    (hX : Finite (Subobject ((Slicing.IntervalCat.toLeftHeart
      (C := C) (s := s) a b (Fact.out : b - a ≤ 1)).obj X))) :
    Finite (Subobject X) := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  exact Finite.subobject_of_faithful_preservesMono
    (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) hX

/-- Strict epimorphisms in `P((a,b))` are closed under composition. -/
theorem Slicing.IntervalCat.comp_strictEpi (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y Z : s.IntervalCat C a b} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsStrictEpi f) (hg : IsStrictEpi g) :
    IsStrictEpi (f ≫ g) := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  haveI : Epi (FL.map f) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
      (C := C) (s := s) (a := a) (b := b) f hf
  haveI : Epi (FL.map g) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
      (C := C) (s := s) (a := a) (b := b) g hg
  haveI : Epi (FL.map (f ≫ g)) := by
    simpa using (show Epi (FL.map f ≫ FL.map g) by infer_instance)
  exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) (f ≫ g)

/-- Strict monomorphisms in `P((a,b))` are closed under composition. -/
theorem Slicing.IntervalCat.comp_strictMono (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y Z : s.IntervalCat C a b} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsStrictMono f) (hg : IsStrictMono g) :
    IsStrictMono (f ≫ g) := by
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  haveI : Mono (FR.map f) :=
    Slicing.IntervalCat.mono_toRightHeart_of_strictMono
      (C := C) (s := s) (a := a) (b := b) f hf
  haveI : Mono (FR.map g) :=
    Slicing.IntervalCat.mono_toRightHeart_of_strictMono
      (C := C) (s := s) (a := a) (b := b) g hg
  haveI : Mono (FR.map (f ≫ g)) := by
    simpa using (show Mono (FR.map f ≫ FR.map g) by infer_instance)
  exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart
    (C := C) (s := s) (a := a) (b := b) (f ≫ g)

noncomputable instance Slicing.intervalCat_quasiAbelian (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] :
    QuasiAbelian (s.IntervalCat C a b) where
  pullback_strictEpi := by
    intro X Y Z f g hg
    let t := (s.phaseShift C a).toTStructure
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
    haveI : Epi (FL.map g) :=
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) g hg
    have hpb :
        IsLimit
          (PullbackCone.mk
            (FL.map (pullback.fst f g))
            (FL.map (pullback.snd f g))
            (by
              simpa using congrArg FL.map (pullback.condition (f := f) (g := g))) :
            PullbackCone (FL.map f) (FL.map g)) :=
      isLimitOfHasPullbackOfPreservesLimit FL f g
    haveI : Epi (FL.map (pullback.fst f g)) :=
      CategoryTheory.Abelian.epi_fst_of_isLimit (f := FL.map f) (g := FL.map g) hpb
    exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
      (C := C) (s := s) (a := a) (b := b) (pullback.fst f g)
  pushout_strictMono := by
    intro X Y Z f g hf
    let t := (s.phaseShift C (b - 1)).toTStructureGE
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
    haveI : Mono (FR.map f) :=
      Slicing.IntervalCat.mono_toRightHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) f hf
    have hpo :
        IsColimit
          (PushoutCocone.mk
            (FR.map (pushout.inl f g))
            (FR.map (pushout.inr f g))
            (by
              simpa using congrArg FR.map (pushout.condition (f := f) (g := g))) :
            PushoutCocone (FR.map f) (FR.map g)) :=
      isColimitOfHasPushoutOfPreservesColimit FR f g
    haveI : Mono (FR.map (pushout.inr f g)) :=
      CategoryTheory.Abelian.mono_inr_of_isColimit (f := FR.map f) (g := FR.map g) hpo
    exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) (pushout.inr f g)

/-! ### Local finiteness in thin interval categories -/

omit [IsTriangulated C] in
/-- A slicing is locally finite if there exists `η > 0` with `η < 1/2` such that every
object in each thin interval category `P((t-η, t+η))` has finite length in the
quasi-abelian sense, i.e. ACC/DCC on strict subobjects.

The extra bound `η < 1/2` is a harmless normalization: any Bridgeland witness may be
shrunk to such an `η`, and then the width `2η` is at most `1`, so the thin interval
category carries the exact / quasi-abelian structure proved above. -/
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  intervalFinite : ∃ η : ℝ, ∃ hη : 0 < η, ∃ hη' : η < 1 / 2, ∀ t : ℝ,
    let a := t - η
    let b := t + η
    letI : Fact (a < b) := ⟨by
      dsimp [a, b]
      linarith⟩
    letI : Fact (b - a ≤ 1) := ⟨by
      dsimp [a, b]
      linarith⟩
    ∀ (E : s.IntervalCat C a b),
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E

/-- If a short complex in `P((a,b))` is short exact after embedding into both hearts,
then its left map is a strict monomorphism and its right map is a strict epimorphism
in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictMono_strictEpi_of_shortExact_toLeftRightHearts (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hL :
      (S.map (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1))).ShortExact)
    (hR :
      (S.map (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1))).ShortExact) :
    IsStrictMono S.f ∧ IsStrictEpi S.g := by
  let tL := (s.phaseShift C a).toTStructure
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := tL.heartFullSubcategoryAbelian
  letI : CategoryWithHomology tL.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := tL.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  letI : CategoryWithHomology tR.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := tR.heart.FullSubcategory)
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  letI : Mono (FR.map S.f) := hR.mono_f
  letI : Epi (FL.map S.g) := hL.epi_g
  have hf : IsStrictMono S.f :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) S.f
  have hg : IsStrictEpi S.g :=
    Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
      (C := C) (s := s) (a := a) (b := b) S.g
  exact ⟨hf, hg⟩

/-- A distinguished triangle in `C` whose three vertices lie in `P((a,b))`
forces the first map to be a strict monomorphism and the second to be a strict epimorphism
in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictMono_strictEpi_of_distTriang (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    {δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C) :
    IsStrictMono S.f ∧ IsStrictEpi S.g := by
  let tL := (s.phaseShift C a).toTStructure
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := tL.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιL := tL.ιHeart (H := tL.heart.FullSubcategory)
  have hTL :
      Triangle.mk (ιL.map ((S.map FL).f)) (ιL.map ((S.map FL).g)) δ ∈ distTriang C := by
    simpa [FL] using hT
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := by
    simpa using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι tL) ((S.map FL).f) ((S.map FL).g) δ hTL
  have hCokL :
      IsColimit (CokernelCofork.ofπ ((S.map FL).g) (S.map FL).zero) := by
    simpa using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι tL) ((S.map FL).f) ((S.map FL).g) δ hTL
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExactL : (S.map FL).Exact := by
    exact ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKerL
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExactL (Fork.IsLimit.mono hKerL) (Cofork.IsColimit.epi hCokL)
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιR := tR.ιHeart (H := tR.heart.FullSubcategory)
  have hTR :
      Triangle.mk (ιR.map ((S.map FR).f)) (ιR.map ((S.map FR).g)) δ ∈ distTriang C := by
    simpa [FR] using hT
  have hKerR :
      IsLimit (KernelFork.ofι ((S.map FR).f) (S.map FR).zero) := by
    simpa using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι tR) ((S.map FR).f) ((S.map FR).g) δ hTR
  have hCokR :
      IsColimit (CokernelCofork.ofπ ((S.map FR).g) (S.map FR).zero) := by
    simpa using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι tR) ((S.map FR).f) ((S.map FR).g) δ hTR
  letI : (S.map FR).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FR))
  have hExactR : (S.map FR).Exact := by
    exact ShortComplex.exact_of_f_is_kernel (S := S.map FR) hKerR
  have hR : (S.map FR).ShortExact :=
    ShortComplex.ShortExact.mk' hExactR (Fork.IsLimit.mono hKerR) (Cofork.IsColimit.epi hCokR)
  exact Slicing.IntervalCat.strictMono_strictEpi_of_shortExact_toLeftRightHearts
    (C := C) (s := s) (a := a) (b := b) hL hR

/-- A short exact sequence in the left heart `P((a,a+1])` with vertices in `P((a,b))`
extends to a distinguished triangle in `C`. -/
theorem Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hL :
      (S.map (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1))).ShortExact) :
    ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧), Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : IsNormalMonoCategory t.heart.FullSubcategory := Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory t.heart.FullSubcategory := Abelian.toIsNormalEpiCategory
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  letI : Balanced t.heart.FullSubcategory := by infer_instance
  letI : Epi ((S.map FL).g) := hL.epi_g
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) ((S.map FL).g)
  have hKer :
      IsLimit (KernelFork.ofι i (show i ≫ (S.map FL).g = 0 by
        exact ι.map_injective (comp_distTriang_mor_zero₁₂ _ hT))) :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i ((S.map FL).g) δ hT
  have hLfIsKernel : IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := hL.fIsKernel
  let eKA : K ≅ FL.obj S.X₁ := IsLimit.conePointUniqueUpToIso hKer hLfIsKernel
  refine ⟨δ ≫ ((shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)), ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (ι.mapIso eKA.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · simp only [Iso.refl_hom, Functor.mapIso_hom, Iso.symm_hom, Triangle.mk_mor₁]
    have hcomp : ι.map eKA.inv ≫ ι.map i = S.f.hom := by
      simpa [Functor.map_comp] using
        congrArg (fun k => ι.map k)
        (IsLimit.conePointUniqueUpToIso_inv_comp hKer hLfIsKernel
          Limits.WalkingParallelPair.zero)
    change S.f.hom ≫ 𝟙 S.X₂.obj = ι.map eKA.inv ≫ t.ιHeart.map i
    simpa [FL] using hcomp.symm
  · have hmap : t.ιHeart.map ((S.map FL).g) = S.g.hom := rfl
    simp only [Iso.refl_hom, Triangle.mk_mor₂, Triangle.mk_obj₂, Triangle.mk_obj₃]
    rw [hmap]
    convert (rfl : S.g.hom = S.g.hom) using 1
    · exact Category.comp_id S.g.hom
    · exact Category.id_comp S.g.hom
  · simp only [Iso.refl_hom, Triangle.mk_mor₃, Functor.mapIso_hom, Iso.symm_hom]
    change (δ ≫ (shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)) ≫
        (shiftFunctor C (1 : ℤ)).map (ι.map eKA.inv) = 𝟙 _ ≫ δ
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp, ← ι.map_comp, eKA.hom_inv_id,
      ι.map_id, Functor.map_id]
    simp

/-- A strict short exact sequence in `P((a,b))` extends to a distinguished triangle in `C`. -/
theorem Slicing.IntervalCat.exists_distTriang_of_strictShortExact (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hS : StrictShortExact S) :
    ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧), Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := t.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have := hS.shortExact.mono_f
  have := hS.shortExact.epi_g
  let h := hS.shortExact.exact.condition.choose
  let eHi : kernel S.g ≅ h.left.K :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.left.hi
  have heHi : eHi.inv ≫ kernel.ι S.g = h.left.i := by
    simpa [KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) h.left.hi
        Limits.WalkingParallelPair.zero
  haveI : Epi h.left.f' := hS.shortExact.exact.epi_f' h.left
  have hFRMono : Mono (FR.map h.left.f') := by
    haveI : Mono (FR.map S.f) :=
      Slicing.IntervalCat.mono_toRightHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) S.f
        ⟨inferInstance, hS.strict_f⟩
    have hFRComp : FR.map h.left.f' ≫ FR.map h.left.i = FR.map S.f := by
      calc
        FR.map h.left.f' ≫ FR.map h.left.i = FR.map (h.left.f' ≫ h.left.i) := by
          rw [← FR.map_comp]
        _ = FR.map S.f := by
          simp [h.left.f'_i]
    haveI : Mono (FR.map h.left.f' ≫ FR.map h.left.i) := by
      rw [hFRComp]
      infer_instance
    exact mono_of_mono (FR.map h.left.f') (FR.map h.left.i)
  have hf'Strict : IsStrictMono h.left.f' :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) h.left.f'
  haveI : IsIso h.left.f' := hf'Strict.isIso
  let eK : S.X₁ ≅ kernel S.g := asIso h.left.f' ≪≫ eHi.symm
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    refine kernel.isoKernel S.g S.f eK ?_
    calc
      eK.hom ≫ kernel.ι S.g = h.left.f' ≫ h.left.i := by
          simp [eK, heHi, Category.assoc]
      _ = S.f := h.left.f'_i
  have hEpi : Epi (FL.map S.g) := by
    letI : Epi (FL.map S.g) :=
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) S.g
        ⟨inferInstance, hS.strict_g⟩
    infer_instance
  have hKer :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  have hExact : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKer
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
  exact Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) hL

/-- A distinguished triangle in `C` whose three vertices lie in `P((a,b))`
defines a strict short exact sequence in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictShortExact_of_distTriang (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    {δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C) :
    StrictShortExact S := by
  let tL := (s.phaseShift C a).toTStructure
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := tL.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιL := tL.ιHeart (H := tL.heart.FullSubcategory)
  have hTL :
      Triangle.mk (ιL.map ((S.map FL).f)) (ιL.map ((S.map FL).g)) δ ∈ distTriang C := by
    simpa [FL] using hT
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := by
    simpa using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι tL) ((S.map FL).f) ((S.map FL).g) δ hTL
  have hKerMap :
      IsLimit (FL.mapCone (KernelFork.ofι S.f S.zero)) :=
    (isLimitMapConeForkEquiv' FL S.zero).symm hKerL
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimitOfReflects FL hKerMap
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιR := tR.ιHeart (H := tR.heart.FullSubcategory)
  have hTR :
      Triangle.mk (ιR.map ((S.map FR).f)) (ιR.map ((S.map FR).g)) δ ∈ distTriang C := by
    simpa [FR] using hT
  have hCokR :
      IsColimit (CokernelCofork.ofπ ((S.map FR).g) (S.map FR).zero) := by
    simpa using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι tR) ((S.map FR).f) ((S.map FR).g) δ hTR
  have hCokMap :
      IsColimit (FR.mapCocone (CokernelCofork.ofπ S.g S.zero)) :=
    (isColimitMapCoconeCoforkEquiv' FR S.zero).symm hCokR
  have hCok : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    isColimitOfReflects FR hCokMap
  obtain ⟨hf, hg⟩ := Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
    (C := C) (s := s) (a := a) (b := b) hT
  let eK' : kernel S.g ≅ S.X₁ :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hKer
  let eK : S.X₁ ≅ kernel S.g := eK'.symm
  have heK : eK.hom ≫ kernel.ι S.g = S.f := by
    simpa [KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) hKer
        Limits.WalkingParallelPair.zero
  have hLift : kernel.lift S.g S.f S.zero = eK.hom := by
    apply (cancel_mono (kernel.ι S.g)).1
    simpa [heK] using kernel.lift_ι S.g S.f S.zero
  have hKernelComp : kernel.ι S.g ≫ cokernel.π S.f = 0 := by
    have hιEq : kernel.ι S.g = eK.inv ≫ S.f := by
      apply (cancel_epi eK.hom).1
      simp [Category.assoc, heK]
    rw [hιEq, Category.assoc, cokernel.condition]
    simp
  let eQ : cokernel S.f ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hCok
  have heQ : cokernel.π S.f ≫ eQ.hom = S.g := by
    simpa [CokernelCofork.ofπ] using
      IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel S.f) hCok
        Limits.WalkingParallelPair.one
  have hDesc : cokernel.desc S.f S.g S.zero = eQ.hom := by
    apply (cancel_epi (cokernel.π S.f)).1
    simpa [heQ] using cokernel.π_desc S.f S.g S.zero
  let hLeft : S.LeftHomologyData := ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S
  let hRight : S.RightHomologyData := ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel S
  have hLeftZero : IsZero hLeft.H := by
    haveI : IsIso (kernel.lift S.g S.f S.zero) := by rw [hLift]; infer_instance
    haveI : Epi (kernel.lift S.g S.f S.zero) := by infer_instance
    dsimp [hLeft]
    simpa [hLift] using isZero_cokernel_of_epi (kernel.lift S.g S.f S.zero)
  have hRightZero : IsZero hRight.H := by
    haveI : IsIso (cokernel.desc S.f S.g S.zero) := by rw [hDesc]; infer_instance
    haveI : Mono (cokernel.desc S.f S.g S.zero) := by infer_instance
    dsimp [hRight]
    simpa [hDesc] using isZero_kernel_of_mono (cokernel.desc S.f S.g S.zero)
  have hComp : hLeft.i ≫ hRight.p = 0 := by
    dsimp [hLeft, hRight]
    exact hKernelComp
  have hExact : S.Exact := by
    let hData : S.HomologyData :=
      { left := hLeft
        right := hRight
        iso := IsZero.iso hLeftZero hRightZero
        comm := by
          have hπZero : hLeft.π = 0 := hLeftZero.eq_of_tgt _ _
          simpa [hπZero, Category.assoc] using hComp.symm }
    exact ⟨⟨hData, hLeftZero⟩⟩
  have hShortExact : S.ShortExact :=
    ShortComplex.ShortExact.mk' hExact hf.mono hg.epi
  refine
    { shortExact := hShortExact
      strict_f := hf.strict
      strict_g := hg.strict }

/-- A strict short exact sequence in a smaller interval remains strict in any larger thin
interval containing it. This is the inclusion-case transport used in the deformation
theorem's interval-independence step. -/
theorem Slicing.IntervalCat.strictShortExact_inclusion (s : Slicing C)
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)] [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂)
    {S : ShortComplex (s.IntervalCat C a₁ b₁)} (hS : StrictShortExact S) :
    StrictShortExact (S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)) := by
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := s) (a := a₁) (b := b₁) hS
  have hT' :
      Triangle.mk ((S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)).f.hom)
        ((S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)).g.hom) δ ∈ distTriang C := by
    simpa [Slicing.IntervalCat.inclusion] using hT
  exact Slicing.IntervalCat.strictShortExact_of_distTriang
    (C := C) (s := s) (a := a₂) (b := b₂) hT'

/-- Strict short exact sequences in `P((a,b))` are exactly the distinguished triangles
in `C` whose three vertices lie in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictShortExact_iff_exists_distTriang (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)} :
    StrictShortExact S ↔
      ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧), Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  constructor
  · exact Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := s) (a := a) (b := b)
  · rintro ⟨δ, hT⟩
    exact Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := s) (a := a) (b := b) hT

/-- A strict short exact sequence in `P((a,b))` yields the expected `K₀` relation
in the ambient triangulated category. -/
theorem Slicing.IntervalCat.K0_of_strictShortExact (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hS : StrictShortExact S) :
    K₀.of C S.X₂.obj = K₀.of C S.X₁.obj + K₀.of C S.X₃.obj := by
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := s) (a := a) (b := b) hS
  simpa using K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT

/-- Append a semistable strict quotient in `P((a,b))` to an HN filtration of the
kernel. This packages `appendFactor` with the strict short exact sequence to triangle
bridge for interval categories. -/
noncomputable def HNFiltration.appendStrictFactor {P : ℝ → ObjectProperty C}
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {S : ShortComplex (s.IntervalCat C a b)}
    (G : HNFiltration C P S.X₁.obj)
    (hS : StrictShortExact S) (ψ : ℝ) (hψ : P ψ S.X₃.obj)
    (hψ_lt : ∀ j : Fin G.n, ψ < G.φ j) :
    HNFiltration C P S.X₂.obj := by
  let hδ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := s) (a := a) (b := b) hS
  let δ := Classical.choose hδ
  have hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := Classical.choose_spec hδ
  exact G.appendFactor C (Triangle.mk S.f.hom S.g.hom δ) hT
    (Iso.refl _) (Iso.refl _) ψ hψ hψ_lt

end Preabelian

/-! ### Skewed stability functions (Definition 4.4) -/

/-- A *skewed stability function* on a thin subcategory `P((a, b))` with `b - a ≤ 1`.
This is a group homomorphism `W : K₀ C →+ ℂ` together with a real parameter `α ∈ (a, b)`
such that for every nonzero semistable object `E` of phase `φ ∈ (a, b)`, `W([E]) ≠ 0`.

In the deformation theorem, `W` is a perturbation of the central charge `Z` of a
stability condition, and `α` is chosen so that `W`-phases are well-defined in
`(α - 1/2, α + 1/2)` for objects in `P((a, b))`. -/
structure SkewedStabilityFunction (s : Slicing C) (a b : ℝ) where
  /-- The group homomorphism (typically a perturbation of the central charge). -/
  W : K₀ C →+ ℂ
  /-- The skewing parameter, lying in the interval `(a, b)`. -/
  α : ℝ
  /-- The skewing parameter lies in the interval. -/
  hα_mem : a < α ∧ α < b
  /-- For every nonzero semistable object of phase `φ ∈ (a, b)`, the central charge
  `W([E])` is nonzero. -/
  nonzero : ∀ (E : C) (φ : ℝ), a < φ → φ < b →
    (s.P φ) E → ¬IsZero E → W (K₀.of C E) ≠ 0

variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The central charge of a `SkewedStabilityFunction` is additive on strict short exact
sequences in the thin interval category. -/
theorem SkewedStabilityFunction.strict_additive {s : Slicing C}
    (ssf : SkewedStabilityFunction C s a b)
    {S : ShortComplex (s.IntervalCat C a b)} (hS : StrictShortExact S) :
    ssf.W (K₀.of C S.X₂.obj) = ssf.W (K₀.of C S.X₁.obj) + ssf.W (K₀.of C S.X₃.obj) := by
  rw [Slicing.IntervalCat.K0_of_strictShortExact (C := C) (s := s) (a := a) (b := b) hS,
    map_add]

end CategoryTheory.Triangulated
