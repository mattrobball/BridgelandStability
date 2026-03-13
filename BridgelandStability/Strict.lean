/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Strict Morphisms and Quasi-Abelian Categories

We define strict morphisms and quasi-abelian categories following
Bridgeland's "Stability conditions on triangulated categories" (2007), §4.

A morphism `f : X ⟶ Y` in a category with kernels and cokernels is *strict*
if the canonical comparison morphism from the coimage to the image is an isomorphism.
In an abelian category every morphism is strict, so strictness is a nontrivial condition
only in the pre-abelian setting.

A *quasi-abelian* category is a preadditive category with kernels, cokernels, pullbacks,
and pushouts in which pullbacks of strict epimorphisms are strict epimorphisms and
pushouts of strict monomorphisms are strict monomorphisms.

## Main definitions

* `CategoryTheory.IsStrict`: a morphism is strict if `coimageImageComparison` is an iso
* `CategoryTheory.IsStrictMono`: mono + strict
* `CategoryTheory.IsStrictEpi`: epi + strict
* `CategoryTheory.QuasiAbelian`: quasi-abelian category
* `CategoryTheory.StrictShortExact`: short exact with strict morphisms

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
* Schneiders, "Quasi-abelian categories and sheaves", Mém. Soc. Math. Fr. 1999
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

section Strict

variable {X Y : C} (f : X ⟶ Y)
  [HasKernel f] [HasCokernel f]
  [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- A morphism `f` is *strict* if the canonical comparison morphism from the
(abelian) coimage to the (abelian) image is an isomorphism. In an abelian category,
every morphism is strict.

This uses `Abelian.coimageImageComparison` from `Mathlib.CategoryTheory.Abelian.Images`,
which is defined without assuming the category is abelian. -/
def IsStrict : Prop :=
  IsIso (Abelian.coimageImageComparison f)

/-- A morphism is a *strict monomorphism* if it is both a monomorphism and strict. -/
structure IsStrictMono : Prop where
  mono : Mono f
  strict : IsStrict f

/-- A morphism is a *strict epimorphism* if it is both an epimorphism and strict. -/
structure IsStrictEpi : Prop where
  epi : Epi f
  strict : IsStrict f

end Strict

section StrictKernelCokernel

variable {X Y : C} {f : X ⟶ Y}
  [HasZeroObject C]
  [HasKernel f] [HasCokernel f]
  [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- A strict epimorphism is the cokernel of its kernel. -/
noncomputable def IsStrictEpi.isColimitCokernelCofork (hf : IsStrictEpi f) :
    IsColimit (CokernelCofork.ofπ f (kernel.condition f)) := by
  letI : Epi f := hf.epi
  letI : IsIso (Abelian.coimageImageComparison f) := hf.strict
  letI : IsIso (kernel.ι (cokernel.π f)) := kernel.of_cokernel_of_epi (f := f)
  let e : cokernel (kernel.ι f) ≅ Y :=
    asIso (Abelian.coimageImageComparison f ≫ kernel.ι (cokernel.π f))
  have hm : cokernel.π (kernel.ι f) ≫ e.hom = f := by
    simpa [e] using
      (Abelian.coimage_image_factorisation (f := f))
  exact cokernel.cokernelIso (kernel.ι f) f e hm

/-- A strict monomorphism is the kernel of its cokernel. -/
noncomputable def IsStrictMono.isLimitKernelFork (hf : IsStrictMono f) :
    IsLimit (KernelFork.ofι f (cokernel.condition f)) := by
  letI : Mono f := hf.mono
  letI : IsIso (Abelian.coimageImageComparison f) := hf.strict
  letI : IsIso (cokernel.π (kernel.ι f)) := cokernel.of_kernel_of_mono (f := f)
  let e : X ≅ kernel (cokernel.π f) :=
    asIso (cokernel.π (kernel.ι f) ≫ Abelian.coimageImageComparison f)
  have hm : e.hom ≫ kernel.ι (cokernel.π f) = f := by
    simpa [e] using (Abelian.coimage_image_factorisation (f := f))
  exact kernel.isoKernel (cokernel.π f) f e hm

/-- If `f` is the cokernel of its kernel, then `f` is a strict epimorphism. -/
theorem isStrictEpi_of_isColimitCokernelCofork
    (hf : IsColimit (CokernelCofork.ofπ f (kernel.condition f))) :
    IsStrictEpi f := by
  haveI : Epi f := Cofork.IsColimit.epi hf
  let e : Abelian.coimage f ≅ Y :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι f)) hf
  have he : Abelian.coimage.π f ≫ e.hom = f := by
    simpa [Abelian.coimage, e, CokernelCofork.ofπ] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel (kernel.ι f)) hf Limits.WalkingParallelPair.one
  have hcomp : Abelian.coimageImageComparison f ≫ Abelian.image.ι f = e.hom := by
    apply (cancel_epi (Abelian.coimage.π f)).1
    rw [he]
    exact Abelian.coimage_image_factorisation (f := f)
  refine ⟨inferInstance, ?_⟩
  letI : IsIso (Abelian.image.ι f) := kernel.of_cokernel_of_epi (f := f)
  letI : Mono (Abelian.image.ι f) := by infer_instance
  change IsIso (Abelian.coimageImageComparison f)
  rw [show Abelian.coimageImageComparison f = e.hom ≫ inv (Abelian.image.ι f) from by
    apply (cancel_mono (Abelian.image.ι f)).1
    simpa [Category.assoc] using hcomp]
  infer_instance

/-- If `f` is the kernel of its cokernel, then `f` is a strict monomorphism. -/
theorem isStrictMono_of_isLimitKernelFork
    (hf : IsLimit (KernelFork.ofι f (cokernel.condition f))) :
    IsStrictMono f := by
  haveI : Mono f := Fork.IsLimit.mono hf
  have hker : IsLimit (KernelFork.ofι (Abelian.image.ι f) (kernel.condition (cokernel.π f))) := by
    simpa [Abelian.image, KernelFork.ofι] using
      (kernelIsKernel (cokernel.π f))
  let u : X ⟶ Abelian.image f := hker.lift (KernelFork.ofι f (cokernel.condition f))
  have hu : u ≫ Abelian.image.ι f = f := by
    exact hker.fac (KernelFork.ofι f (cokernel.condition f)) Limits.WalkingParallelPair.zero
  let v : Abelian.image f ⟶ X :=
    hf.lift (KernelFork.ofι (Abelian.image.ι f) (kernel.condition (cokernel.π f)))
  have hv : v ≫ f = Abelian.image.ι f := by
    exact hf.fac
      (KernelFork.ofι (Abelian.image.ι f) (kernel.condition (cokernel.π f)))
      Limits.WalkingParallelPair.zero
  let e : X ≅ Abelian.image f :=
    ⟨u, v,
      by
        apply (cancel_mono f).1
        rw [Category.assoc, hv, hu]
        simp,
      by
        apply (cancel_mono (Abelian.image.ι f)).1
        rw [Category.assoc, hu, hv]
        simp⟩
  have he : e.hom ≫ Abelian.image.ι f = f := hu
  have hcomp : Abelian.coimage.π f ≫ Abelian.coimageImageComparison f = e.hom := by
    apply (cancel_mono (Abelian.image.ι f)).1
    rw [he]
    simpa [Category.assoc] using (Abelian.coimage_image_factorisation (f := f))
  refine ⟨inferInstance, ?_⟩
  letI : IsIso (Abelian.coimage.π f) := cokernel.of_kernel_of_mono (f := f)
  letI : Epi (Abelian.coimage.π f) := by infer_instance
  letI : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  change IsIso (Abelian.coimageImageComparison f)
  rw [show Abelian.coimageImageComparison f = inv (Abelian.coimage.π f) ≫ e.hom from by
    apply (cancel_epi (Abelian.coimage.π f)).1
    simpa [Category.assoc] using hcomp]
  infer_instance

/-- An isomorphism is a strict monomorphism. -/
theorem isStrictMono_of_isIso [IsIso f] : IsStrictMono f := by
  apply isStrictMono_of_isLimitKernelFork
  have hk : cokernel.π f = 0 := (isZero_cokernel_of_epi f).eq_of_tgt _ _
  refine KernelFork.IsLimit.ofι' f (by simpa [hk]) (fun {A} k hk' ↦ ?_)
  refine ⟨k ≫ inv f, by simp [Category.assoc]⟩

/-- An isomorphism is a strict epimorphism. -/
theorem isStrictEpi_of_isIso [IsIso f] : IsStrictEpi f := by
  apply isStrictEpi_of_isColimitCokernelCofork
  have hk : kernel.ι f = 0 := (isZero_kernel_of_mono f).eq_of_src _ _
  refine CokernelCofork.IsColimit.ofπ' f (by simpa [hk]) (fun {A} k hk' ↦ ?_)
  refine ⟨inv f ≫ k, by simp [Category.assoc]⟩

/-- A strict epimorphism that is also mono is an isomorphism. -/
theorem IsStrictEpi.isIso (hf : IsStrictEpi f) [Mono f] : IsIso f := by
  letI : Epi f := hf.epi
  have hk : kernel.ι f = 0 := (isZero_kernel_of_mono f).eq_of_src _ _
  let s : Y ⟶ X :=
    hf.isColimitCokernelCofork.desc (CokernelCofork.ofπ (𝟙 X) (by simpa [hk]))
  have hs : f ≫ s = 𝟙 X := by
    exact hf.isColimitCokernelCofork.fac
      (CokernelCofork.ofπ (𝟙 X) (by simpa [hk]))
      Limits.WalkingParallelPair.one
  letI : IsSplitMono f := IsSplitMono.mk' ⟨s, hs⟩
  exact isIso_of_epi_of_isSplitMono f

/-- A strict monomorphism that is also epi is an isomorphism. -/
theorem IsStrictMono.isIso (hf : IsStrictMono f) [Epi f] : IsIso f := by
  letI : Mono f := hf.mono
  have hk : cokernel.π f = 0 := (isZero_cokernel_of_epi f).eq_of_tgt _ _
  let s : Y ⟶ X :=
    hf.isLimitKernelFork.lift (KernelFork.ofι (𝟙 Y) (by simpa [hk]))
  have hs : s ≫ f = 𝟙 Y := by
    exact hf.isLimitKernelFork.fac
      (KernelFork.ofι (𝟙 Y) (by simpa [hk]))
      Limits.WalkingParallelPair.zero
  letI : IsSplitEpi f := IsSplitEpi.mk' ⟨s, hs⟩
  exact isIso_of_mono_of_isSplitEpi f

/-- A strict epimorphism is a normal epimorphism. -/
noncomputable def IsStrictEpi.normalEpi (hf : IsStrictEpi f) : NormalEpi f where
  W := kernel f
  g := kernel.ι f
  w := kernel.condition f
  isColimit := hf.isColimitCokernelCofork

/-- A strict epimorphism is a regular epimorphism. -/
noncomputable def IsStrictEpi.regularEpi (hf : IsStrictEpi f) : RegularEpi f :=
  (hf.normalEpi).regularEpi

/-- A strict epimorphism is a strong epimorphism. -/
theorem IsStrictEpi.strongEpi (hf : IsStrictEpi f) : StrongEpi f := by
  have := isRegularEpi_of_regularEpi hf.regularEpi
  infer_instance

/-- A normal epimorphism in a preadditive category with kernels and cokernels is strict. -/
theorem isStrictEpi_of_normalEpi [hf : NormalEpi f] : IsStrictEpi f := by
  let g' : hf.W ⟶ kernel f := kernel.lift f hf.g hf.w
  have hcolim : IsColimit (CokernelCofork.ofπ f (kernel.condition f)) :=
    isCokernelOfComp (f := kernel.ι f) g' hf.g hf.isColimit
      (kernel.condition f) (kernel.lift_ι f hf.g hf.w)
  exact isStrictEpi_of_isColimitCokernelCofork hcolim

/-- A strict monomorphism is a normal monomorphism. -/
noncomputable def IsStrictMono.normalMono (hf : IsStrictMono f) : NormalMono f where
  Z := cokernel f
  g := cokernel.π f
  w := cokernel.condition f
  isLimit := hf.isLimitKernelFork

/-- A normal monomorphism in a preadditive category with kernels and cokernels is strict. -/
theorem isStrictMono_of_normalMono [hf : NormalMono f] : IsStrictMono f := by
  let g' : cokernel f ⟶ hf.Z := cokernel.desc f hf.g hf.w
  have hlim : IsLimit (KernelFork.ofι f (cokernel.condition f)) :=
    isKernelOfComp (f := cokernel.π f) g' hf.g hf.isLimit
      (cokernel.condition f) (cokernel.π_desc f hf.g hf.w)
  exact isStrictMono_of_isLimitKernelFork hlim

end StrictKernelCokernel

section QuasiAbelian

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasKernels C] [HasCokernels C] [HasPullbacks C] [HasPushouts C]

/-- A preadditive category with kernels, cokernels, pullbacks, and pushouts is
*quasi-abelian* if pullbacks of strict epimorphisms are strict epimorphisms and
pushouts of strict monomorphisms are strict monomorphisms.

This follows the definition from Schneiders (1999). -/
class QuasiAbelian : Prop where
  /-- The pullback of a strict epimorphism along any morphism is a strict epimorphism. -/
  pullback_strictEpi : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    IsStrictEpi g → IsStrictEpi (pullback.fst f g)
  /-- The pushout of a strict monomorphism along any morphism is a strict monomorphism. -/
  pushout_strictMono : ∀ {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y),
    IsStrictMono f → IsStrictMono (pushout.inr f g)

end QuasiAbelian

section StrictShortExact

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasKernels C] [HasCokernels C]

/-- A *strict short exact sequence* is a `ShortComplex` that is short exact (mono left,
epi right, exact in the middle) and where both `f` and `g` are strict morphisms.

In a quasi-abelian category, the kernels of strict epimorphisms are strict monomorphisms,
and the cokernels of strict monomorphisms are strict epimorphisms. -/
structure StrictShortExact (S : ShortComplex C) : Prop where
  shortExact : S.ShortExact
  strict_f : IsStrict S.f
  strict_g : IsStrict S.g

end StrictShortExact

section KernelCokernelStrict

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]

/-- The kernel of any morphism is a strict monomorphism. The canonical comparison
`Coim(kernel.ι g) → Im(kernel.ι g)` is an isomorphism because `kernel.ι g` is mono
(so `Coim ≅ kernel g`), and the image `kernel(cokernel.π(kernel.ι g))` is isomorphic
to `kernel g` via an explicit inverse pair of `kernel.lift` morphisms. -/
theorem isStrictMono_kernel {X Y : C} (g : X ⟶ Y) : IsStrictMono (kernel.ι g) where
  mono := inferInstance
  strict := by
    -- kernel.ι g is mono, so kernel(kernel.ι g) is zero
    have hk0 : kernel.ι (kernel.ι g) = (0 : kernel (kernel.ι g) ⟶ kernel g) :=
      (isZero_kernel_of_mono (kernel.ι g)).eq_zero_of_src _
    -- Therefore coimage.π(kernel.ι g) = cokernel.π(kernel.ι(kernel.ι g)) is an iso
    haveI : IsIso (cokernel.π (kernel.ι (kernel.ι g))) := by rw [hk0]; infer_instance
    -- The image inclusion composed with g is zero (factors through cokernel)
    have h1 : kernel.ι (cokernel.π (kernel.ι g)) ≫ g = 0 := by
      have hf := cokernel.π_desc (kernel.ι g) g (kernel.condition g)
      conv_lhs => rhs; rw [← hf]
      rw [← Category.assoc, kernel.condition, zero_comp]
    -- kernel g ≅ Im(kernel.ι g) via inverse pair of kernel.lift morphisms
    have hℓj : kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g) (cokernel.condition _) ≫
        kernel.lift g (kernel.ι (cokernel.π (kernel.ι g))) h1 = 𝟙 _ := by ext; simp
    have hjℓ : kernel.lift g (kernel.ι (cokernel.π (kernel.ι g))) h1 ≫
        kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g) (cokernel.condition _) = 𝟙 _ := by
      ext; simp
    haveI : IsIso (kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g) (cokernel.condition _)) :=
      ⟨⟨_, hℓj, hjℓ⟩⟩
    -- coimageImageComparison = inv(coimage.π) ≫ ℓ, a composition of isos
    change IsIso (Abelian.coimageImageComparison (kernel.ι g))
    have hπ : cokernel.π (kernel.ι (kernel.ι g)) ≫
        Abelian.coimageImageComparison (kernel.ι g) =
        kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g) (cokernel.condition _) :=
      cokernel.π_desc _ _ _
    rw [show Abelian.coimageImageComparison (kernel.ι g) =
        inv (cokernel.π (kernel.ι (kernel.ι g))) ≫
        kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g) (cokernel.condition _) from
      by rw [← hπ, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]]
    infer_instance

/-- The cokernel of any morphism is a strict epimorphism. The canonical comparison
`Coim(cokernel.π g) → Im(cokernel.π g)` is an isomorphism because `cokernel.π g` is epi
(so `Im ≅ cokernel g`), and the coimage `cokernel(kernel.ι(cokernel.π g))` is isomorphic
to `cokernel g` via an explicit inverse pair of `cokernel.desc` morphisms. -/
theorem isStrictEpi_cokernel {X Y : C} (g : X ⟶ Y) : IsStrictEpi (cokernel.π g) where
  epi := inferInstance
  strict := by
    -- cokernel.π g is epi, so cokernel(cokernel.π g) is zero
    have hc0 : cokernel.π (cokernel.π g) = (0 : cokernel g ⟶ cokernel (cokernel.π g)) :=
      (isZero_cokernel_of_epi (cokernel.π g)).eq_zero_of_tgt _
    -- Therefore image.ι(cokernel.π g) = kernel.ι(cokernel.π(cokernel.π g)) is an iso
    haveI : IsIso (kernel.ι (cokernel.π (cokernel.π g))) := by rw [hc0]; infer_instance
    -- g ≫ coimage.π(cokernel.π g) = 0 (g factors through image.ι g)
    have h1 : g ≫ cokernel.π (kernel.ι (cokernel.π g)) = 0 := by
      rw [← Abelian.coimage_image_factorisation_assoc g]; simp
    -- cokernel g ≅ Coim(cokernel.π g) via inverse pair of cokernel.desc morphisms
    have hhk : cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g) (kernel.condition _) ≫
        cokernel.desc g (cokernel.π (kernel.ι (cokernel.π g))) h1 = 𝟙 _ := by
      apply (cancel_epi (cokernel.π (kernel.ι (cokernel.π g)))).mp; simp
    have hkh : cokernel.desc g (cokernel.π (kernel.ι (cokernel.π g))) h1 ≫
        cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g) (kernel.condition _) = 𝟙 _ := by
      apply (cancel_epi (cokernel.π g)).mp; simp
    haveI : IsIso (cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g) (kernel.condition _)) :=
      ⟨⟨_, hhk, hkh⟩⟩
    -- coimageImageComparison = h ≫ inv(image.ι), a composition of isos
    change IsIso (Abelian.coimageImageComparison (cokernel.π g))
    have key : Abelian.coimageImageComparison (cokernel.π g) ≫
        kernel.ι (cokernel.π (cokernel.π g)) =
        cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g) (kernel.condition _) := by
      apply (cancel_epi (cokernel.π (kernel.ι (cokernel.π g)))).mp; simp
    rw [show Abelian.coimageImageComparison (cokernel.π g) =
        cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g) (kernel.condition _) ≫
        inv (kernel.ι (cokernel.π (cokernel.π g))) from
      by rw [← key, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    infer_instance

end KernelCokernelStrict

section AbelianStrict

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category, every morphism is strict. -/
theorem isStrict_of_abelian {X Y : C} (f : X ⟶ Y) : IsStrict f :=
  show IsIso _ from inferInstance

/-- In an abelian category, every monomorphism is a strict monomorphism. -/
theorem isStrictMono_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : IsStrictMono f :=
  ⟨inferInstance, isStrict_of_abelian f⟩

/-- In an abelian category, every epimorphism is a strict epimorphism. -/
theorem isStrictEpi_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : IsStrictEpi f :=
  ⟨inferInstance, isStrict_of_abelian f⟩

/-- In an abelian category, every short exact sequence is a strict short exact sequence. -/
theorem strictShortExact_of_shortExact {S : ShortComplex C} (h : S.ShortExact) :
    StrictShortExact S :=
  ⟨h, isStrict_of_abelian S.f, isStrict_of_abelian S.g⟩

end AbelianStrict

section StrictSubobject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [Preadditive C]
  [HasKernels C] [HasCokernels C]

namespace Subobject

variable {X : C}

/-- A subobject is *strict* if its arrow is a strict monomorphism. This is the
quasi-abelian notion of admissible / exact subobject used in Bridgeland's finite-length
thin interval categories. -/
def IsStrict (P : Subobject X) : Prop :=
  IsStrictMono P.arrow

@[simp]
theorem isStrict_iff (P : Subobject X) : P.IsStrict ↔ IsStrictMono P.arrow :=
  Iff.rfl

end Subobject

/-- The ordered type of strict subobjects of `X`. -/
abbrev StrictSubobject (X : C) :=
  { P : Subobject X // P.IsStrict }

variable (X Y : C)

/-- An object is *strict-Artinian* if its strict subobjects satisfy the descending chain
condition. This is the exact finite-length notion relevant to quasi-abelian categories. -/
def isStrictArtinianObject : ObjectProperty C :=
  fun X ↦ WellFoundedLT (StrictSubobject X)

/-- An object is *strict-Artinian* if its strict subobjects satisfy the descending chain
condition. -/
abbrev IsStrictArtinianObject : Prop := isStrictArtinianObject.Is X

instance [IsStrictArtinianObject X] : WellFoundedLT (StrictSubobject X) :=
  isStrictArtinianObject.prop_of_is X

/-- An object is *strict-Noetherian* if its strict subobjects satisfy the ascending chain
condition. This is the exact finite-length notion relevant to quasi-abelian categories. -/
def isStrictNoetherianObject : ObjectProperty C :=
  fun X ↦ WellFoundedGT (StrictSubobject X)

/-- An object is *strict-Noetherian* if its strict subobjects satisfy the ascending chain
condition. -/
abbrev IsStrictNoetherianObject : Prop := isStrictNoetherianObject.Is X

instance [IsStrictNoetherianObject X] : WellFoundedGT (StrictSubobject X) :=
  isStrictNoetherianObject.prop_of_is X

/-- Ordinary Artinian objects are strict-Artinian, since strict subobjects form a subtype of
all subobjects. -/
theorem isStrictArtinianObject_of_isArtinianObject [IsArtinianObject X] :
    IsStrictArtinianObject X := by
  let f : StrictSubobject X → Subobject X := Subtype.val
  exact
    (show isStrictArtinianObject.Is X from
      ObjectProperty.is_of_prop _
        (show WellFoundedLT (StrictSubobject X) from
          ⟨InvImage.wf f
            (wellFounded_lt :
              WellFounded ((· < ·) : Subobject X → Subobject X → Prop))⟩))

/-- Ordinary Noetherian objects are strict-Noetherian, since strict subobjects form a subtype
of all subobjects. -/
theorem isStrictNoetherianObject_of_isNoetherianObject [IsNoetherianObject X] :
    IsStrictNoetherianObject X := by
  let f : StrictSubobject X → Subobject X := Subtype.val
  exact
    (show isStrictNoetherianObject.Is X from
      ObjectProperty.is_of_prop _
        (show WellFoundedGT (StrictSubobject X) from
          ⟨InvImage.wf f
            (wellFounded_gt :
              WellFounded ((· > ·) : Subobject X → Subobject X → Prop))⟩))

end StrictSubobject

section StrictSubobjectAbelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C}

/-- In an abelian category, strict-Artinian and Artinian coincide, because every mono is strict. -/
theorem isArtinianObject_of_isStrictArtinianObject [IsStrictArtinianObject X] :
    IsArtinianObject X := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  let g : ℕ →o (StrictSubobject X)ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual ⟨f n, by
        exact (Subobject.isStrict_iff _).2 (isStrictMono_of_mono (Subobject.arrow (f n)))⟩,
      fun i j hij ↦ f.2 hij⟩
  haveI : WellFoundedGT (StrictSubobject X)ᵒᵈ := by
    rw [wellFoundedGT_dual_iff]
    infer_instance
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
  exact ⟨n, fun m hm ↦ by
    simpa using congrArg Subtype.val (hn m hm)⟩

/-- In an abelian category, strict-Noetherian and Noetherian coincide, because every mono is
strict. -/
theorem isNoetherianObject_of_isStrictNoetherianObject [IsStrictNoetherianObject X] :
    IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let g : ℕ →o StrictSubobject X :=
    ⟨fun n ↦ ⟨f n, by
        exact (Subobject.isStrict_iff _).2 (isStrictMono_of_mono (Subobject.arrow (f n)))⟩,
      fun i j hij ↦ f.2 hij⟩
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
  exact ⟨n, fun m hm ↦ by
    simpa using congrArg Subtype.val (hn m hm)⟩

end StrictSubobjectAbelian

section SubobjectFiniteness

variable {A : Type u} [Category.{v} A] {C : Type u} [Category.{v} C]

private def subobjectImageOfFaithfulPreservesMono (F : A ⥤ C) [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] {E : A} :
    Subobject E → Subobject (F.obj E) :=
  Subobject.lift (fun {S} (f : S ⟶ E) [Mono f] ↦ Subobject.mk (F.map f))
    (fun {S₁ S₂} f g [Mono f] [Mono g] i w ↦
      Subobject.mk_eq_mk_of_comm _ _ (F.mapIso i) (by
        change F.map i.hom ≫ F.map g = F.map f
        rw [← F.map_comp, w]))

private theorem subobjectImageOfFaithfulPreservesMono_injective (F : A ⥤ C) [F.Full]
    [F.Faithful] [F.PreservesMonomorphisms] {E : A} :
    Function.Injective (subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E)) := by
  intro s₁ s₂ heq
  induction s₁ using Subobject.ind
  induction s₂ using Subobject.ind
  rename_i S₁ f₁ _ S₂ f₂ _
  change Subobject.mk (F.map f₁) = Subobject.mk (F.map f₂) at heq
  exact Subobject.mk_eq_mk_of_comm f₁ f₂
    (F.preimageIso (Subobject.isoOfMkEqMk _ _ heq))
    (F.map_injective (by
      simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
      exact Subobject.ofMkLEMk_comp heq.le))

private theorem subobjectImageOfFaithfulPreservesMono_monotone (F : A ⥤ C) [F.Full]
    [F.Faithful] [F.PreservesMonomorphisms] {E : A} :
    Monotone (subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E)) := by
  intro s₁ s₂ h
  induction s₁ using Subobject.ind
  induction s₂ using Subobject.ind
  rename_i S₁ f₁ _ S₂ f₂ _
  change Subobject.mk (F.map f₁) ≤ Subobject.mk (F.map f₂)
  exact Subobject.mk_le_mk_of_comm (F.map (Subobject.ofMkLEMk f₁ f₂ h)) (by
    change F.map (Subobject.ofMkLEMk f₁ f₂ h) ≫ F.map f₂ = F.map f₁
    rw [← F.map_comp]
    simpa using congrArg (F.map) (Subobject.ofMkLEMk_comp h))

/-- A faithful functor that preserves monomorphisms induces an injection on subobject
lattices. If `F : A ⥤ C` is faithful and preserves monomorphisms, subobjects of `E`
in `A` inject into subobjects of `F.obj E` in `C`. Together with `Finite.of_injective`,
this transfers finiteness of subobject lattices from `C` to `A`.

The key use case is the full subcategory inclusion `ι : P(φ) ⥤ C`, where local
finiteness of the slicing gives `Finite (Subobject (ι.obj E))` in `C`, and we
need `Finite (Subobject E)` in `P(φ)`.

Note: fullness is not required. The hypothesis `PreservesMonomorphisms F` is needed
because a faithful functor does not automatically preserve monomorphisms (the mono
test in `C` involves objects not in the image of `F`). -/
theorem Finite.subobject_of_faithful_preservesMono (F : A ⥤ C) [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms]
    {E : A} (h : Finite (Subobject (F.obj E))) : Finite (Subobject E) := by
  exact Finite.of_injective
    (subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F)
    (subobjectImageOfFaithfulPreservesMono_injective (A := A) (C := C) F)

/-- Artinian objects transfer across full faithful functors that preserve monomorphisms. -/
theorem isArtinianObject_of_faithful_preservesMono (F : A ⥤ C) [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] {E : A} [IsArtinianObject (F.obj E)] :
    IsArtinianObject E := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  let g : ℕ →o (Subobject (F.obj E))ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual <|
        subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E) (f n),
      fun i j hij ↦ by
        change
          subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E) (f j) ≤
            subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E) (f i)
        exact subobjectImageOfFaithfulPreservesMono_monotone (A := A) (C := C) F (E := E)
          (f.2 hij)⟩
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject g
  exact ⟨n, fun m hm ↦
    subobjectImageOfFaithfulPreservesMono_injective (A := A) (C := C) F (E := E)
      (by simpa using hn m hm)⟩

/-- Noetherian objects transfer across full faithful functors that preserve monomorphisms. -/
theorem isNoetherianObject_of_faithful_preservesMono (F : A ⥤ C) [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] {E : A} [IsNoetherianObject (F.obj E)] :
    IsNoetherianObject E := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let g : ℕ →o Subobject (F.obj E) :=
    ⟨fun n ↦ subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E) (f n),
      fun i j hij ↦
        subobjectImageOfFaithfulPreservesMono_monotone (A := A) (C := C) F (E := E)
          (f.2 hij)⟩
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject g
  exact ⟨n, fun m hm ↦
    subobjectImageOfFaithfulPreservesMono_injective (A := A) (C := C) F (E := E) (hn m hm)⟩

end SubobjectFiniteness

section StrictSubobjectTransfer

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [Preadditive A]
  [HasKernels A] [HasCokernels A]
  {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [Preadditive C]
  [HasKernels C] [HasCokernels C]

private noncomputable def strictSubobjectImageOfFaithful (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} :
    StrictSubobject E → Subobject (F.obj E) :=
  fun B ↦ by
    let hstrict : IsStrictMono (F.map B.1.arrow) := hF B.1.arrow B.2
    letI : Mono (F.map B.1.arrow) := hstrict.mono
    exact Subobject.mk (F.map B.1.arrow)

private theorem strictSubobjectImageOfFaithful_monotone (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} :
    Monotone (strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E)) := by
  intro B₁ B₂ hB
  let hstrict₁ : IsStrictMono (F.map B₁.1.arrow) := hF B₁.1.arrow B₁.2
  let hstrict₂ : IsStrictMono (F.map B₂.1.arrow) := hF B₂.1.arrow B₂.2
  letI : Mono (F.map B₁.1.arrow) := hstrict₁.mono
  letI : Mono (F.map B₂.1.arrow) := hstrict₂.mono
  have hB' : B₁.1 ≤ B₂.1 := hB
  have hmk : Subobject.mk B₁.1.arrow ≤ Subobject.mk B₂.1.arrow := by
    simpa [Subobject.mk_arrow] using hB'
  change
    Subobject.mk (F.map B₁.1.arrow) ≤ Subobject.mk (F.map B₂.1.arrow)
  exact Subobject.mk_le_mk_of_comm (F.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk)) (by
    change F.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk) ≫ F.map B₂.1.arrow =
      F.map B₁.1.arrow
    rw [← F.map_comp]
    simpa using congrArg F.map (Subobject.ofMkLEMk_comp hmk))

private theorem strictSubobjectImageOfFaithful_injective (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} :
    Function.Injective (strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E)) := by
  intro B₁ B₂ hEq
  let hstrict₁ : IsStrictMono (F.map B₁.1.arrow) := hF B₁.1.arrow B₁.2
  let hstrict₂ : IsStrictMono (F.map B₂.1.arrow) := hF B₂.1.arrow B₂.2
  letI : Mono (F.map B₁.1.arrow) := hstrict₁.mono
  letI : Mono (F.map B₂.1.arrow) := hstrict₂.mono
  apply Subtype.ext
  have hEq' : Subobject.mk (F.map B₁.1.arrow) = Subobject.mk (F.map B₂.1.arrow) := hEq
  simpa [Subobject.mk_arrow] using
    (Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
      (F.preimageIso (Subobject.isoOfMkEqMk _ _ hEq'))
      (F.map_injective (by
        simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
        exact Subobject.ofMkLEMk_comp hEq'.le)))

/-- Strict-Artinian objects transfer across full faithful functors that send strict
monomorphisms to strict monomorphisms. -/
theorem isStrictArtinianObject_of_faithful_map_strictMono (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} [IsArtinianObject (F.obj E)] :
    IsStrictArtinianObject E := by
  exact
    (show isStrictArtinianObject.Is E from
      ObjectProperty.is_of_prop _
        (show WellFoundedLT (StrictSubobject E) from by
          rw [← wellFoundedGT_dual_iff, wellFoundedGT_iff_monotone_chain_condition]
          intro f
          let g : ℕ →o (Subobject (F.obj E))ᵒᵈ :=
            ⟨fun n ↦ OrderDual.toDual <|
                strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E) (f n),
              fun i j hij ↦ by
                change
                  strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E) (f j) ≤
                    strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E) (f i)
                exact strictSubobjectImageOfFaithful_monotone (A := A) (C := C) F hF (E := E)
                  (f.2 hij)⟩
          obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject g
          exact ⟨n, fun m hm ↦
            strictSubobjectImageOfFaithful_injective (A := A) (C := C) F hF (E := E)
              (by simpa using hn m hm)⟩))

/-- Strict-Noetherian objects transfer across full faithful functors that send strict
monomorphisms to strict monomorphisms. -/
theorem isStrictNoetherianObject_of_faithful_map_strictMono (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} [IsNoetherianObject (F.obj E)] :
    IsStrictNoetherianObject E := by
  exact
    (show isStrictNoetherianObject.Is E from
      ObjectProperty.is_of_prop _
        (show WellFoundedGT (StrictSubobject E) from by
          rw [wellFoundedGT_iff_monotone_chain_condition]
          intro f
          let g : ℕ →o Subobject (F.obj E) :=
            ⟨fun n ↦ strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E) (f n),
              fun i j hij ↦
                strictSubobjectImageOfFaithful_monotone (A := A) (C := C) F hF (E := E)
                  (f.2 hij)⟩
          obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject g
          exact ⟨n, fun m hm ↦
            strictSubobjectImageOfFaithful_injective (A := A) (C := C) F hF (E := E)
              (hn m hm)⟩))

end StrictSubobjectTransfer

end CategoryTheory
