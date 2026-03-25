/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# FullSubcategory kernel/cokernel `.hom` simp lemmas

In a `FullSubcategory`, the simp lemma `comp_hom` normalizes `(f ≫ g).hom` to
`f.hom ≫ g.hom` (distributing `.hom` over composition). This means standard
limit lemmas like `kernel.condition` — which state `kernel.ι f ≫ f = 0` at the
subcategory level — cannot fire on goals in simp-normal form.

These lemmas restate kernel/cokernel facts in the distributed `.hom` form so
that `simp` can close them after `ext` reduces a subcategory morphism equality
to a base-category morphism equality.

The `_homMk` variants handle the common case where a functor between
FullSubcategories maps `f` to `ObjectProperty.homMk f.hom`, and simp has
already unfolded the functor map. Since `ObjectProperty.homMk` is not
`@[reducible]`, simp's pattern matcher cannot see through `(homMk g).hom = g`,
so these variants state the result with `homMk` explicit in the pattern.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty.FullSubcategory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {P : ObjectProperty C} {X Y W : P.FullSubcategory}

@[simp]
lemma homMk_eq_zero (f : X.obj ⟶ Y.obj) :
    (ObjectProperty.homMk f : X ⟶ Y) = 0 ↔ f = 0 :=
  ⟨fun h ↦ congr_arg InducedCategory.Hom.hom h, fun h ↦ by ext; exact h⟩

@[simp]
lemma kernel_condition_hom (f : X ⟶ Y) [HasKernel f] :
    (kernel.ι f).hom ≫ f.hom = 0 :=
  congr_arg (·.hom) (kernel.condition f)

@[simp]
lemma kernel_lift_ι_hom (f : X ⟶ Y) [HasKernel f]
    (g : W ⟶ X) (h : g ≫ f = 0) :
    (kernel.lift f g h).hom ≫ (kernel.ι f).hom = g.hom :=
  congr_arg (·.hom) (kernel.lift_ι f g h)

@[simp]
lemma cokernel_condition_hom (f : X ⟶ Y) [HasCokernel f] :
    f.hom ≫ (cokernel.π f).hom = 0 :=
  congr_arg (·.hom) (cokernel.condition f)

@[simp]
lemma cokernel_π_desc_hom (f : X ⟶ Y) [HasCokernel f]
    (g : Y ⟶ W) (h : f ≫ g = 0) :
    (cokernel.π f).hom ≫ (cokernel.desc f g h).hom = g.hom :=
  congr_arg (·.hom) (cokernel.π_desc f g h)

/-- Variant of `kernel_condition_hom` for the post-simp normal form where a functor
map has been unfolded to `ObjectProperty.homMk`. -/
@[simp]
lemma kernel_condition_homMk (g : X.obj ⟶ Y.obj)
    [HasKernel (ObjectProperty.homMk g : X ⟶ Y)] :
    (kernel.ι (ObjectProperty.homMk g : X ⟶ Y)).hom ≫ g = 0 :=
  kernel_condition_hom (ObjectProperty.homMk g)

@[simp]
lemma cokernel_condition_homMk (g : X.obj ⟶ Y.obj)
    [HasCokernel (ObjectProperty.homMk g : X ⟶ Y)] :
    g ≫ (cokernel.π (ObjectProperty.homMk g : X ⟶ Y)).hom = 0 :=
  cokernel_condition_hom (ObjectProperty.homMk g)

end CategoryTheory.ObjectProperty.FullSubcategory
