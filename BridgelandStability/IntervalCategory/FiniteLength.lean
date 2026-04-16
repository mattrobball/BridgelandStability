/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.IntervalCategory.Strictness

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

section Preabelian

variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

/-!
# Finite Length and Skewed Stability Functions

Additive/preserving instances, local finiteness in thin intervals,
strict short exact sequences, K₀ relations, skewed stability functions.
-/

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
          simp

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
    HasPullbacks (s.IntervalCat C a b) :=
  Limits.hasPullbacks_of_hasBinaryProducts_of_hasEqualizers _

noncomputable instance Slicing.intervalCat_hasPushouts (s : Slicing C) :
    HasPushouts (s.IntervalCat C a b) :=
  Limits.hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers _

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
@[informal "Definition 5.7" "per-object strict finite length is weaker than finite length of all chains (paper's assumption)" complete]
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
  have hExactL : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKerL
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
  have hExactR : (S.map FR).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FR) hKerR
  have hR : (S.map FR).ShortExact :=
    ShortComplex.ShortExact.mk' hExactR (Fork.IsLimit.mono hKerR) (Cofork.IsColimit.epi hCokR)
  exact Slicing.IntervalCat.strictMono_strictEpi_of_shortExact_toLeftRightHearts
    (C := C) (s := s) (a := a) (b := b) hL hR

section

variable {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

omit [Fact (a < b)]

/-- A short exact sequence in the left heart `P((a,a+1])` with vertices in `P((a,b))`
extends to a distinguished triangle in `C`. -/
theorem Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart (s : Slicing C)
    {S : ShortComplex (s.IntervalCat C a b)}
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

end

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
    rw [heK]
    exact kernel.lift_ι S.g S.f S.zero
  have hKernelComp : kernel.ι S.g ≫ cokernel.π S.f = 0 := by
    have hιEq : kernel.ι S.g = eK.inv ≫ S.f := by
      apply (cancel_epi eK.hom).1
      simp [heK]
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
    rw [heQ]
    exact cokernel.π_desc S.f S.g S.zero
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
        ((S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)).g.hom)
          δ ∈ distTriang C := by
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
This is a group homomorphism `W : Λ →+ ℂ` (the charge on the target lattice) together
with a class map `v : K₀ C →+ Λ` and a real parameter `α ∈ (a, b)`, such that for
every nonzero semistable object `E` of phase `φ ∈ (a, b)`, `W(v[E]) ≠ 0`.

In the deformation theorem, `W` is a perturbation of the central charge `Z : Λ → ℂ`
of a stability condition `(Z, P)` on `D` with respect to `Λ`, and `α` is chosen so
that `W`-phases are well-defined in `(α - 1/2, α + 1/2)` for objects in `P((a, b))`. -/
@[informal "Definition 4.4" "weaker: only σ-semistable nonvanishing, not all nonzero objects" complete]
structure SkewedStabilityFunction {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)
    (s : Slicing C) (a b : ℝ) where
  /-- The group homomorphism (typically a perturbation of the central charge). -/
  W : Λ →+ ℂ
  /-- The skewing parameter, lying in the interval `(a, b)`. -/
  α : ℝ
  /-- The skewing parameter lies in the interval. -/
  hα_mem : a < α ∧ α < b
  /-- For every nonzero semistable object of phase `φ ∈ (a, b)`, the central charge
  `W(v[E])` is nonzero. -/
  nonzero : ∀ (E : C) (φ : ℝ), a < φ → φ < b →
    (s.P φ) E → ¬IsZero E → W (cl C v E) ≠ 0

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}
variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The central charge of a `SkewedStabilityFunction` is additive on strict short exact
sequences in the thin interval category. -/
theorem SkewedStabilityFunction.strict_additive {s : Slicing C}
    (ssf : SkewedStabilityFunction C v s a b)
    {S : ShortComplex (s.IntervalCat C a b)} (hS : StrictShortExact S) :
    ssf.W (cl C v S.X₂.obj) = ssf.W (cl C v S.X₁.obj) + ssf.W (cl C v S.X₃.obj) := by
  simp only [cl, Slicing.IntervalCat.K0_of_strictShortExact (C := C) (s := s) (a := a) (b := b) hS,
    map_add]

end CategoryTheory.Triangulated
