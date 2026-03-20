/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# The heart of a t-structure is abelian

We show that the heart of a t-structure on a triangulated category is abelian,
following [BBD, *Faisceaux pervers*, Théorème 1.3.6].

The proof uses the criterion `AbelianSubcategory.abelian`, which requires:
1. **No negative Hom spaces**: for heart objects `X, Y`, every morphism
  `ι X ⟶ (ι Y)⟦n⟧` is zero when `n < 0`.
2. **Admissibility**: every morphism in the heart is admissible. Given
  `f₁ : X₁ → X₂` in the heart, the cone `X₃` of `ι.map f₁` is `IsLE 0` and
  `IsGE (-1)`. The truncation functors decompose `X₃` as
  `τ<0(X₃) → X₃ → τ≥0(X₃)`, where both `τ≥0(X₃)` and `τ<0(X₃)⟦-1⟧` lie in
  the heart.

## Main results

* `CategoryTheory.Triangulated.TStructure.heartAbelian`: the heart of a t-structure
  on a triangulated category is abelian.

## References

* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*, 1.2][bbd-1982]
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Category
open scoped ZeroObject

universe v' u' v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)
  {H : Type u'} [Category.{v'} H] [Preadditive H] [t.Heart H]

/-- **No negative Hom spaces in the heart.** For heart objects `X` and `Y`, every morphism
`ι X ⟶ (ι Y)⟦n⟧` is zero when `n < 0`. -/
theorem heart_hι :
    ∀ ⦃X Y : H⦄ ⦃n : ℤ⦄ (f : (t.ιHeart).obj X ⟶ ((t.ιHeart).obj Y)⟦n⟧),
      n < 0 → f = 0 := by
  intro X Y n f hn
  haveI : t.IsGE ((t.ιHeart.obj Y)⟦n⟧) (-n) := t.isGE_shift _ 0 n (-n)
  exact t.zero f 0 (-n) (by lia)

/-- **Admissibility of heart morphisms.** Every morphism in the heart is admissible: for
`f₁ : X₁ → X₂` in the heart, the cone `X₃` of `ι.map f₁` decomposes as
`(ι K)⟦1⟧ → X₃ → ι Q` via the truncation triangle, with `K, Q` in the heart. -/
theorem heart_admissible :
    AbelianSubcategory.admissibleMorphism (t.ιHeart (H := H)) = ⊤ := by
  ext X₁ X₂ f₁
  simp only [MorphismProperty.top_apply, iff_true]
  intro X₃ f₂ f₃ hT
  set T := Triangle.mk (t.ιHeart.map f₁) f₂ f₃
  -- Step 1: X₃ is IsLE 0 (rotation of original triangle + isLE₂)
  haveI hX₃_le : t.IsLE X₃ 0 := by
    have hrot := rot_of_distTriang _ hT
    apply t.isLE₂ _ hrot 0
    · -- rotate.obj₁ = (t.ιHeart).obj X₂, which is IsLE 0
      change t.IsLE ((t.ιHeart).obj X₂) 0; infer_instance
    · -- rotate.obj₃ = ((t.ιHeart).obj X₁)⟦1⟧, IsLE(-1) hence IsLE 0
      change t.IsLE (((t.ιHeart).obj X₁)⟦(1 : ℤ)⟧) 0
      haveI := t.isLE_shift ((t.ιHeart).obj X₁) 0 1 (-1)
      exact t.isLE_of_le _ (-1) 0
  -- Step 2: X₃ is IsGE(-1) (rotation of original triangle + isGE₂)
  haveI hX₃_ge : t.IsGE X₃ (-1) := by
    have hrot := rot_of_distTriang _ hT
    apply t.isGE₂ _ hrot (-1)
    · -- rotate.obj₁ = (t.ιHeart).obj X₂, IsGE 0 hence IsGE(-1)
      change t.IsGE ((t.ιHeart).obj X₂) (-1)
      exact t.isGE_of_ge _ (-1) 0
    · -- rotate.obj₃ = ((t.ιHeart).obj X₁)⟦1⟧, IsGE(-1)
      change t.IsGE (((t.ιHeart).obj X₁)⟦(1 : ℤ)⟧) (-1)
      exact t.isGE_shift _ 0 1 (-1)
  -- Step 3: τ≥0(X₃) is in the heart (IsGE 0 by truncation, IsLE 0 by isLE₂)
  have hQ_le : t.IsLE ((t.truncGE 0).obj X₃) 0 := by
    have hrot_trunc := rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X₃)
    apply t.isLE₂ _ hrot_trunc 0
    · -- rotate.obj₁ = X₃, IsLE 0
      change t.IsLE X₃ 0; exact hX₃_le
    · -- rotate.obj₃ = ((truncLT 0).obj X₃)⟦1⟧
      change t.IsLE (((t.truncLT 0).obj X₃)⟦(1 : ℤ)⟧) 0
      haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
      haveI := t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
      exact t.isLE_of_le _ (-2) 0
  have hQ_heart : t.heart ((t.truncGE 0).obj X₃) :=
    (t.mem_heart_iff _).mpr ⟨hQ_le, inferInstance⟩
  -- Step 4: τ<0(X₃) is IsGE(-1) (inverse rotation of truncation triangle + isGE₂)
  have hK_ge : t.IsGE ((t.truncLT 0).obj X₃) (-1) := by
    have hinv := inv_rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X₃)
    apply t.isGE₂ _ hinv (-1)
    · -- invRotate.obj₁ = ((truncGE 0).obj X₃)⟦-1⟧
      change t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) (-1)
      haveI : t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) 1 := t.isGE_shift _ 0 (-1) 1
      exact t.isGE_of_ge _ (-1) 1
    · -- invRotate.obj₃ = X₃
      change t.IsGE X₃ (-1)
      exact hX₃_ge
  -- τ<0(X₃)⟦-1⟧ is in the heart
  haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
  have hK_heart : t.heart (((t.truncLT 0).obj X₃)⟦(-1 : ℤ)⟧) :=
    (t.mem_heart_iff _).mpr ⟨t.isLE_shift _ (-1) (-1) 0, t.isGE_shift _ (-1) (-1) 0⟩
  -- Step 5: Extract K, Q from the essential image of ι
  rw [← t.essImage_ιHeart H] at hQ_heart hK_heart
  obtain ⟨Q, ⟨eQ⟩⟩ := hQ_heart
  obtain ⟨K, ⟨eK⟩⟩ := hK_heart
  -- eK : t.ιHeart.obj K ≅ ((t.truncLT 0).obj X₃)⟦(-1 : ℤ)⟧
  -- eQ : t.ιHeart.obj Q ≅ (t.truncGE 0).obj X₃
  -- Step 6: Build the admissible triangle isomorphic to the truncation triangle
  let e₁ : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLT 0).obj X₃ :=
    (shiftFunctor C (1 : ℤ)).mapIso eK ≪≫
      (shiftEquiv C (1 : ℤ)).counitIso.app ((t.truncLT 0).obj X₃)
  let α : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ⟶ X₃ := e₁.hom ≫ (t.truncLTι 0).app X₃
  let β : X₃ ⟶ t.ιHeart.obj Q := (t.truncGEπ 0).app X₃ ≫ eQ.inv
  let γ : t.ιHeart.obj Q ⟶ (t.ιHeart.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    eQ.hom ≫ (t.truncGEδLT 0).app X₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv
  exact ⟨K, Q, α, β, γ, isomorphic_distinguished _
    (t.triangleLTGE_distinguished 0 X₃) _
    (Triangle.isoMk _ _ e₁ (Iso.refl _) eQ
      (by dsimp [α, triangleLTGE]; simp)
      (by dsimp [β, triangleLTGE]; simp)
      (by dsimp [γ]; simp))⟩

variable [IsTriangulated C] [HasFiniteProducts H] in
/-- **Heart abelianity.** The heart of a t-structure on a triangulated category is abelian,
assuming the heart has finite products. -/
noncomputable def heartAbelian : Abelian H :=
  AbelianSubcategory.abelian (t.ιHeart (H := H)) (heart_hι t) (heart_admissible t)

/-! ### The heart contains zero and is closed under binary products -/

/-- The zero object lies in the heart of any t-structure. -/
instance heart_containsZero : t.heart.ContainsZero where
  exists_zero := ⟨0, isZero_zero C, (t.mem_heart_iff _).mpr ⟨inferInstance, inferInstance⟩⟩

/-- The biproduct of two heart objects lies in the heart. -/
lemma heart_biprod (X Y : C) (hX : t.heart X) (hY : t.heart Y) :
    t.heart (X ⊞ Y) := by
  rw [t.mem_heart_iff] at hX hY ⊢
  have hT := binaryBiproductTriangle_distinguished X Y
  exact ⟨t.isLE₂ _ hT 0 hX.1 hY.1, t.isGE₂ _ hT 0 hX.2 hY.2⟩

/-- The heart of a t-structure is closed under binary products. -/
instance heart_closedUnderBinaryProducts :
    t.heart.IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    set A := F.obj ⟨WalkingPair.left⟩
    set B := F.obj ⟨WalkingPair.right⟩
    -- F ≅ pair A B as functors from Discrete WalkingPair
    have e_diag : F ≅ pair A B :=
      Discrete.natIso (fun ⟨j⟩ ↦ match j with
        | WalkingPair.left => Iso.refl _
        | WalkingPair.right => Iso.refl _)
    -- limit F ≅ A ⨯ B ≅ A ⊞ B
    have e : A ⊞ B ≅ limit F :=
      (biprod.isoProd A B) ≪≫ (HasLimit.isoOfNatIso e_diag).symm
    exact t.heart.prop_of_iso e
      (t.heart_biprod A B (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))

/-- The heart of a t-structure is closed under finite products. -/
instance heart_closedUnderFiniteProducts : t.heart.IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The full subcategory defined by the heart has finite products. -/
noncomputable instance heart_hasFiniteProducts :
    HasFiniteProducts t.heart.FullSubcategory :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- **Heart abelianity (canonical form).** The full subcategory of heart objects of a
t-structure on a triangulated category is abelian. -/
noncomputable def heartFullSubcategoryAbelian [IsTriangulated C] :
    Abelian t.heart.FullSubcategory :=
  haveI := t.hasHeartFullSubcategory
  heartAbelian t (H := t.heart.FullSubcategory)

end CategoryTheory.Triangulated.TStructure
