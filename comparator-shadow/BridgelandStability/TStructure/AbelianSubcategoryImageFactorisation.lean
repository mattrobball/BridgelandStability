/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory

/-!
# Abelian Subcategory Image Factorisation

This file contains a local extension of Mathlib's API for abelian subcategories of
triangulated categories. It isolates the image-factorisation triangle used in the
phase 4 heart-factorisation arguments.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated ZeroObject

namespace Triangulated

variable {C A : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category* A] {ι : A ⥤ C}

namespace AbelianSubcategory

variable (hι : ∀ ⦃X Y : A⦄ ⦃n : ℤ⦄ (f : ι.obj X ⟶ (ι.obj Y)⟦n⟧), n < 0 → f = 0)
variable [Preadditive A] [ι.Full] [ι.Faithful]

section

attribute [local instance] hasZeroObject_of_hasTerminal_object

variable [HasFiniteProducts A] [ι.Additive]
variable (hA : admissibleMorphism ι = ⊤)

set_option backward.isDefEq.respectTransparency false in
include hι hA in
omit [HasFiniteProducts A] in
variable [IsTriangulated C] in
lemma exists_distinguished_triangle_of_image_factorisation
    {X₁ X₂ : A} {f₁ : X₁ ⟶ X₂} {X₃ : C}
    (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ι.map f₁) f₂ f₃ ∈ distTriang C)
    {K Q : A} (α : (ι.obj K)⟦(1 : ℤ)⟧ ⟶ X₃) (β : X₃ ⟶ (ι.obj Q))
    {γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
    (hT' : Triangle.mk α β γ ∈ distTriang C) :
    ∃ (I : A) (i : I ⟶ X₂) (δ : ι.obj Q ⟶ (ι.obj I)⟦(1 : ℤ)⟧)
      (m₁ : X₁ ⟶ I) (m₃ : ι.obj I ⟶ (ι.obj K)⟦(1 : ℤ)⟧),
      Triangle.mk (ι.map i) (ι.map (πQ f₂ β)) δ ∈ distTriang C ∧
      Triangle.mk (ι.map (ιK f₃ α)) (ι.map m₁) (-m₃) ∈ distTriang C ∧
      m₁ ≫ i = f₁ := by
  have hEpi : Epi (πQ f₂ β) := epi_πQ hι hT hT'
  obtain ⟨I, i, δ, hI⟩ := exists_distinguished_triangle_of_epi hι hA (πQ f₂ β)
  have H := someOctahedron (show f₂ ≫ β = ι.map (πQ f₂ β) by simp)
    (rot_of_distTriang _ hT) (rot_of_distTriang _ hT')
    (rot_of_distTriang _ hI)
  obtain ⟨m₁, hm₁⟩ : ∃ (m₁ : X₁ ⟶ I), (shiftFunctor C (1 : ℤ)).map (ι.map m₁) = H.m₁ :=
    ⟨(ι ⋙ shiftFunctor C (1 : ℤ)).preimage H.m₁, Functor.map_preimage (ι ⋙ _) _⟩
  obtain ⟨m₃ : ι.obj I ⟶ (ι.obj K)⟦(1 : ℤ)⟧, hm₃⟩ :
      ∃ m₃, (shiftFunctor C (1 : ℤ)).map m₃ = H.m₃ :=
    ⟨(shiftFunctor C (1 : ℤ)).preimage H.m₃, Functor.map_preimage _ _⟩
  have Hmem : Triangle.mk (ι.map (ιK f₃ α)) (ι.map m₁) (-m₃) ∈ distTriang C := by
    rw [rotate_distinguished_triangle, ← Triangle.shift_distinguished_iff _ 1]
    refine isomorphic_distinguished _ H.mem _ ?_
    exact Triangle.isoMk _ _ (-(Iso.refl _)) (Iso.refl _) (Iso.refl _)
  refine ⟨I, i, δ, m₁, m₃, hI, Hmem, ?_⟩
  exact (ι ⋙ shiftFunctor C (1 : ℤ)).map_injective (by simpa [hm₁] using H.comm₂)

end
end AbelianSubcategory
end Triangulated
end CategoryTheory
