/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Subobject.Basic

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

/-- A strict epimorphism is a normal epimorphism. -/
noncomputable def IsStrictEpi.normalEpi (hf : IsStrictEpi f) : NormalEpi f where
  W := kernel f
  g := kernel.ι f
  w := kernel.condition f
  isColimit := hf.isColimitCokernelCofork

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

section SubobjectFiniteness

variable {A : Type u} [Category.{v} A] {C : Type u} [Category.{v} C]

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
  -- Build injection: Subobject E → Subobject (F.obj E)
  -- sending Subobject.mk (f : S ⟶ E) to Subobject.mk (F.map f : F.obj S ⟶ F.obj E)
  let φ : Subobject E → Subobject (F.obj E) :=
    Subobject.lift (fun {S} (f : S ⟶ E) [Mono f] ↦ Subobject.mk (F.map f))
      (fun {S₁ S₂} f g [Mono f] [Mono g] i w ↦
        Subobject.mk_eq_mk_of_comm _ _ (F.mapIso i) (by
          change F.map i.hom ≫ F.map g = F.map f; rw [← F.map_comp, w]))
  exact Finite.of_injective φ (fun s₁ s₂ heq ↦ by
    induction s₁ using Subobject.ind
    induction s₂ using Subobject.ind
    rename_i S₁ f₁ _ S₂ f₂ _
    change Subobject.mk (F.map f₁) = Subobject.mk (F.map f₂) at heq
    exact Subobject.mk_eq_mk_of_comm f₁ f₂
      (F.preimageIso (Subobject.isoOfMkEqMk _ _ heq))
      (F.map_injective (by
        simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
        exact Subobject.ofMkLEMk_comp heq.le)))

end SubobjectFiniteness

end CategoryTheory
