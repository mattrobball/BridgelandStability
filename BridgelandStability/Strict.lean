/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Abelian.Images
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

/-- A fully faithful functor induces an injection on subobject lattices.
If `F : A ⥤ C` is fully faithful and injective on objects, subobjects of `E` in `A`
inject into subobjects of `F.obj E` in `C`. Together with `Finite.of_injective`,
this transfers finiteness of subobject lattices from `C` to `A`.

The key use case is the full subcategory inclusion `ι : P(φ) ⥤ C`, where local
finiteness of the slicing gives `Finite (Subobject (ι.obj E))` in `C`, and we
need `Finite (Subobject E)` in `P(φ)`. -/
theorem Finite.subobject_of_fullyFaithful (F : A ⥤ C) [F.Full] [F.Faithful]
    {E : A} (h : Finite (Subobject (F.obj E))) : Finite (Subobject E) := by
  sorry

end SubobjectFiniteness

end CategoryTheory
