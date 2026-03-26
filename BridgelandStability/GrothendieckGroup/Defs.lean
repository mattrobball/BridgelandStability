/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.GrothendieckGroup.Presentation
public import BridgelandStability.PostnikovTower.Defs
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Grothendieck Group of a Triangulated Category

We define the Grothendieck group `K₀ C` of a pretriangulated category `C` as the free abelian
group on objects of `C` modulo the distinguished triangle relations:
`[B] = [A] + [C]` for each distinguished triangle `A → B → C → A⟦1⟧`.

The isomorphism relation `[X] = [Y]` for `X ≅ Y` is derivable from the triangle relations
(via the distinguished triangle `X → Y → 0 → X⟦1⟧`), so we do not include it as a separate
generator.

## Main definitions

* `CategoryTheory.Triangulated.trianglePresentation`: the `K0Presentation` for triangles
* `CategoryTheory.Triangulated.K₀`: the Grothendieck group via `K0Presentation`
* `CategoryTheory.Triangulated.K₀.of`: the class map `C → K₀ C`
* `CategoryTheory.Triangulated.K₀.of_triangle`: additivity on distinguished triangles
* `CategoryTheory.Triangulated.IsTriangleAdditive`: typeclass for functions `C → A` that
  respect distinguished triangle relations
* `CategoryTheory.Triangulated.K₀.lift`: the universal property of `K₀`
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The `K0Presentation` for distinguished triangles in a pretriangulated category:
generators are objects of `C`, relations are distinguished triangles. -/
abbrev trianglePresentation :
    K0Presentation C {T : Pretriangulated.Triangle C // T ∈ distTriang C} where
  obj₁ := fun r => r.1.obj₁
  obj₂ := fun r => r.1.obj₂
  obj₃ := fun r => r.1.obj₃

/-- The Grothendieck group of a pretriangulated category `C`, defined as the quotient of
`FreeAbelianGroup C` by the distinguished triangle relations. -/
def K₀ : Type _ := (trianglePresentation C).K0

instance K₀.instAddCommGroup : AddCommGroup (K₀ C) :=
  inferInstanceAs (AddCommGroup (trianglePresentation C).K0)

/-- The class map sending an object `X` of `C` to its class `[X]` in `K₀ C`. -/
def K₀.of (X : C) : K₀ C :=
  QuotientAddGroup.mk (FreeAbelianGroup.of X)

@[simp]
theorem trianglePresentation_of (X : C) :
    (trianglePresentation C).of X = K₀.of C X := rfl

/-- For a distinguished triangle `T`, the class of `T.obj₂` equals the sum of the classes of
`T.obj₁` and `T.obj₃` in `K₀ C`. -/
lemma K₀.of_triangle (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) :
    K₀.of C T.obj₂ = K₀.of C T.obj₁ + K₀.of C T.obj₃ :=
  (trianglePresentation C).of_rel ⟨T, hT⟩

/-- The class of the explicit zero object vanishes in K₀. -/
lemma K₀.of_zero : K₀.of C (0 : C) = 0 := by
  have h := K₀.of_triangle C (Pretriangulated.contractibleTriangle (0 : C))
    (Pretriangulated.contractible_distinguished (0 : C))
  -- h : K₀.of C (contractibleTriangle 0).obj₂ = ... + K₀.of C (contractibleTriangle 0).obj₃
  -- contractibleTriangle 0 = Triangle.mk (𝟙 0) (0 : 0 ⟶ 0) 0
  -- obj₁ = obj₂ = 0, obj₃ = 0
  simp only [Pretriangulated.contractibleTriangle] at h
  -- h : K₀.of C 0 = K₀.of C 0 + K₀.of C 0
  have : K₀.of C (0 : C) + 0 = K₀.of C (0 : C) + K₀.of C (0 : C) := by
    rw [add_zero]; exact h
  exact (add_left_cancel this).symm

/-- Isomorphic objects have the same class in K₀. -/
lemma K₀.of_iso {X Y : C} (e : X ≅ Y) : K₀.of C X = K₀.of C Y := by
  have hdist := Pretriangulated.isomorphic_distinguished _
    (Pretriangulated.contractible_distinguished X)
    (Pretriangulated.Triangle.mk e.hom (0 : Y ⟶ (0 : C)) 0)
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk e.hom (0 : Y ⟶ (0 : C)) 0)
      (Pretriangulated.contractibleTriangle X)
      (Iso.refl _) e.symm (Iso.refl _)
      (by simp [Pretriangulated.contractibleTriangle])
      (by simp [Pretriangulated.contractibleTriangle])
      (by simp [Pretriangulated.contractibleTriangle]))
  have h := K₀.of_triangle C _ hdist
  simp only [Pretriangulated.Triangle.mk] at h
  rw [K₀.of_zero, add_zero] at h
  exact h.symm

/-- The class of a zero object vanishes in K₀. -/
lemma K₀.of_isZero {X : C} (hX : IsZero X) : K₀.of C X = 0 := by
  rw [K₀.of_iso C (hX.iso (isZero_zero C)), K₀.of_zero]

/-- Shifting by `[1]` negates the class in K₀: `[X⟦1⟧] = -[X]`. This follows from the
rotation of the contractible triangle, which gives `0 = [X] + [X⟦1⟧]`. -/
@[simp]
lemma K₀.of_shift_one (X : C) : K₀.of C (X⟦(1 : ℤ)⟧) = -K₀.of C X := by
  -- Rotation of the contractible triangle gives a triangle with
  -- obj₁ = X, obj₂ = 0, obj₃ = X⟦1⟧
  have hc := Pretriangulated.contractible_distinguished X
  have hrot := Pretriangulated.rot_of_distTriang _ hc
  have h := K₀.of_triangle C _ hrot
  -- After K₀: [0] = [X] + [X⟦1⟧]
  have h₂ : K₀.of C (Pretriangulated.contractibleTriangle X).rotate.obj₂ =
      0 := K₀.of_isZero C (isZero_zero C)
  rw [h₂] at h
  -- After rw [h₂]: h : 0 = K₀.of C X + K₀.of C (_.rotate.obj₃)
  -- The obj₃ of the rotated contractible triangle is X⟦1⟧
  have h₃ : (Pretriangulated.contractibleTriangle X).rotate.obj₃ = X⟦(1 : ℤ)⟧ := rfl
  rw [h₃] at h
  -- h : 0 = K₀.of C X + K₀.of C (X⟦1⟧)
  have := h.symm
  -- this : K₀.of C X + K₀.of C (X⟦1⟧) = 0
  rwa [add_comm, add_eq_zero_iff_eq_neg] at this

/-- Shifting by `[-1]` negates the class in K₀: `[X⟦-1⟧] = -[X]`. -/
@[simp]
lemma K₀.of_shift_neg_one (X : C) : K₀.of C (X⟦(-1 : ℤ)⟧) = -K₀.of C X := by
  have h1 := K₀.of_shift_one C (X⟦(-1 : ℤ)⟧)
  have h2 := K₀.of_iso C ((shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by lia)).app X)
  simp only [Functor.comp_obj] at h2
  rw [h2] at h1
  exact (neg_eq_iff_eq_neg.mpr h1).symm

variable {C} in
/-- A function `f : C → A` to an additive group is triangle-additive if
`f(B) = f(A) + f(C)` for every distinguished triangle `A → B → C → A⟦1⟧`. -/
class IsTriangleAdditive {A : Type*} [AddCommGroup A] (f : C → A) : Prop where
  additive : ∀ (T : Pretriangulated.Triangle C),
    T ∈ (distTriang C) → f T.obj₂ = f T.obj₁ + f T.obj₃

variable {C} in
instance {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] :
    (trianglePresentation C).IsAdditive f where
  additive := fun ⟨T, hT⟩ => IsTriangleAdditive.additive T hT

/-- The universal property of K₀: any triangle-additive function lifts
to an additive group homomorphism from K₀. -/
def K₀.lift {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] : K₀ C →+ A :=
  (trianglePresentation C).lift f

/-- The lift of a triangle-additive function agrees with the original function on generators. -/
@[simp]
lemma K₀.lift_of {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] (X : C) :
    K₀.lift C f (K₀.of C X) = f X :=
  (trianglePresentation C).lift_of f X

/-- Two homomorphisms from `K₀ C` that agree on all object classes are equal. -/
@[ext 1100]
theorem K₀.hom_ext {A : Type*} [AddCommGroup A] {f g : K₀ C →+ A}
    (h : ∀ X : C, f (K₀.of C X) = g (K₀.of C X)) : f = g :=
  (trianglePresentation C).hom_ext h

/-! ### K₀ additivity for Postnikov towers -/

/-- The K₀ class of the `(i+1)`-th chain object equals the class of the `i`-th plus
the class of the `i`-th factor, using the `i`-th distinguished triangle. -/
private lemma K₀.of_chain_succ {E : C} (P : PostnikovTower C E) (i : Fin P.n) :
    K₀.of C (P.chain.obj' (i.val + 1) (by lia)) =
    K₀.of C (P.chain.obj' i.val (by lia)) + K₀.of C (P.factor i) := by
  have h := K₀.of_triangle C (P.triangle i) (P.triangle_dist i)
  have h₂ := K₀.of_iso C (Classical.choice (P.triangle_obj₂ i))
  have h₁ := K₀.of_iso C (Classical.choice (P.triangle_obj₁ i))
  rwa [h₂, h₁] at h

/-- Auxiliary telescoping: the K₀ class of the `k`-th chain object is the partial sum
of K₀ classes of the first `k` factors. -/
private lemma K₀.of_chain_eq_partial_sum {E : C} (P : PostnikovTower C E)
    (k : ℕ) (hk : k ≤ P.n) :
    K₀.of C (P.chain.obj' k (by lia)) =
    ∑ i : Fin k, K₀.of C (P.factor ⟨i.val, by lia⟩) := by
  induction k with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [show P.chain.obj' 0 (by lia) = P.chain.left from rfl]
    exact K₀.of_isZero C P.base_isZero
  | succ k ih =>
    rw [K₀.of_chain_succ C P ⟨k, by lia⟩, ih (by lia)]
    rw [Fin.sum_univ_castSucc]; congr 1

/-- **K₀ additivity for Postnikov towers**. The K₀ class of `E` equals the sum of
the K₀ classes of the factors: `[E] = ∑ᵢ [Fᵢ]` in K₀. This is the key algebraic
identity used in the sector bound (**Lemma 6.2**). -/
theorem K₀.of_postnikovTower_eq_sum {E : C} (P : PostnikovTower C E) :
    K₀.of C E = ∑ i : Fin P.n, K₀.of C (P.factor i) := by
  rw [show K₀.of C E = K₀.of C (P.chain.obj' P.n (by lia)) from by
    rw [show P.chain.obj' P.n (by lia) = P.chain.right from rfl]
    exact (K₀.of_iso C (Classical.choice P.top_iso)).symm]
  exact K₀.of_chain_eq_partial_sum C P P.n le_rfl

end CategoryTheory.Triangulated
