/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Data.Real.Basic

/-!
# Bridgeland Slicings on Triangulated Categories

We define slicings, Harder-Narasimhan filtrations, and local finiteness conditions
following Bridgeland's "Stability conditions on triangulated categories" (2007).

## Main definitions

* `CategoryTheory.Triangulated.IsStrictMono`: a morphism that is the kernel of some morphism
* `CategoryTheory.Triangulated.IsStrictEpi`: a morphism that is the cokernel of some morphism
* `CategoryTheory.Triangulated.QuasiAbelian`: a quasi-abelian category
* `CategoryTheory.Triangulated.HNFiltration`: Harder-Narasimhan filtration data
* `CategoryTheory.Triangulated.Slicing`: a slicing of a triangulated category
* `CategoryTheory.Triangulated.Slicing.intervalProp`: the interval subcategory predicate
* `CategoryTheory.Triangulated.Slicing.IsLocallyFinite`: the local finiteness condition
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v v' u u'

namespace CategoryTheory.Triangulated

/-! ### Strict morphisms -/

section StrictMorphisms

variable {A : Type u'} [Category.{v'} A] [HasZeroMorphisms A]

/-- A morphism `f` is a strict monomorphism if it is the kernel of some morphism. -/
def IsStrictMono {X Y : A} (f : X ⟶ Y) : Prop :=
  ∃ (Z : A) (g : Y ⟶ Z) (w : f ≫ g = 0), Nonempty (IsLimit (KernelFork.ofι f w))

/-- A morphism `f` is a strict epimorphism if it is the cokernel of some morphism. -/
def IsStrictEpi {X Y : A} (f : X ⟶ Y) : Prop :=
  ∃ (Z : A) (g : Z ⟶ X) (w : g ≫ f = 0), Nonempty (IsColimit (CokernelCofork.ofπ f w))

end StrictMorphisms

/-! ### Quasi-abelian categories -/

/-- A preadditive category with kernels, cokernels, pullbacks, and pushouts is
quasi-abelian if pullbacks of strict epimorphisms are strict epimorphisms and
pushouts of strict monomorphisms are strict monomorphisms. -/
class QuasiAbelian (A : Type u') [Category.{v'} A] [Preadditive A]
    [HasKernels A] [HasCokernels A] [HasPullbacks A] [HasPushouts A] : Prop where
  /-- The pullback of a strict epimorphism along any morphism is a strict epimorphism. -/
  pullback_strictEpi : ∀ {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z),
    IsStrictEpi g → IsStrictEpi (pullback.fst f g)
  /-- The pushout of a strict monomorphism along any morphism is a strict monomorphism. -/
  pushout_strictMono : ∀ {X Y Z : A} (f : Z ⟶ X) (g : Z ⟶ Y),
    IsStrictMono f → IsStrictMono (pushout.inr f g)

/-! ### HN filtrations and slicings -/

section Slicing

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A Harder-Narasimhan (HN) filtration of an object `E` with respect to a phase function `P`.
This consists of a chain of distinguished triangles whose third vertices
are semistable objects with strictly decreasing phases. -/
structure HNFiltration (P : ℝ → C → Prop) (E : C) where
  /-- The number of semistable factors. -/
  n : ℕ
  /-- The distinguished triangles in the filtration. -/
  T : Fin n → Pretriangulated.Triangle C
  /-- The phases of the semistable factors, in strictly decreasing order. -/
  φ : Fin n → ℝ
  /-- Each triangle is distinguished. -/
  distinguished : ∀ j, (T j ∈ distTriang C)
  /-- The phases are strictly decreasing. -/
  hφ : StrictAnti φ
  /-- The third object of each triangle is semistable of the given phase. -/
  semistable : ∀ j, P (φ j) (T j).obj₃
  /-- When `n > 0`, the first object of the first triangle is zero. -/
  bot_zero : (h : 0 < n) → IsZero (T ⟨0, h⟩).obj₁
  /-- When `n > 0`, the second object of the last triangle is isomorphic to `E`. -/
  top_iso : (h : 0 < n) → Nonempty ((T ⟨n - 1, by omega⟩).obj₂ ≅ E)
  /-- Consecutive triangles chain: the second object of `T j` is isomorphic to
  the first object of `T (j+1)`. -/
  chain_iso : ∀ (j : Fin n) (hj : j.val + 1 < n),
    Nonempty ((T j).obj₂ ≅ (T ⟨j.val + 1, hj⟩).obj₁)
  /-- When `n = 0`, the object `E` must be zero. -/
  zero_isZero : n = 0 → IsZero E

/-- A slicing of a pretriangulated category `C`, as defined in
Bridgeland (2007), Definition 5.1. A slicing assigns to each real number `φ`
a class of semistable objects `P(φ)`, subject to shift, Hom-vanishing,
and Harder-Narasimhan existence axioms. -/
structure Slicing where
  /-- For each phase `φ ∈ ℝ`, the predicate of semistable objects of phase `φ`. -/
  P : ℝ → C → Prop
  /-- The semistable predicate is closed under isomorphism. -/
  closedUnderIso : ∀ (φ : ℝ) {X Y : C}, P φ X → (X ≅ Y) → P φ Y
  /-- Shifting by `[1]` increases the phase by 1. -/
  shift : ∀ (φ : ℝ) (X : C), P φ X → P (φ + 1) (X⟦(1 : ℤ)⟧)
  /-- Inverse of the shift axiom. -/
  shift_inv : ∀ (φ : ℝ) (X : C), P (φ + 1) (X⟦(1 : ℤ)⟧) → P φ X
  /-- Morphisms from higher-phase to lower-phase semistable objects vanish. -/
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C), φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ (f : A ⟶ B), f = 0
  /-- Every object has a Harder-Narasimhan filtration. -/
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)

/-! ### Interval subcategories and local finiteness -/

/-- The interval subcategory predicate `P((a,b))`: an object `E` belongs to the
interval subcategory if it is zero or all phases in its HN filtration lie in `(a,b)`. -/
def Slicing.intervalProp (s : Slicing C) (a b : ℝ) : C → Prop :=
  fun E => IsZero E ∨ ∃ (F : HNFiltration C s.P E), ∀ i, a < F.φ i ∧ F.φ i < b

/-- A slicing is locally finite if there exists `η > 0` such that for every `t`, the interval
subcategory `P((t-η, t+η))` satisfies both the descending and ascending chain conditions
for strict subobjects. This captures the requirement that the interval subcategories
be quasi-abelian categories of finite length (Bridgeland, Appendix A). -/
def Slicing.IsLocallyFinite (s : Slicing C) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ,
    -- Every object in the interval satisfies the descending chain condition
    (∀ (E : C), s.intervalProp C (t - η) (t + η) E →
      ∀ (f : ℕ → C) (ι : ∀ n, f n ⟶ E),
        (∀ n, s.intervalProp C (t - η) (t + η) (f n)) →
        (∀ n, IsStrictMono (ι n)) →
        (∀ n, ∃ g : f (n + 1) ⟶ f n, g ≫ ι n = ι (n + 1)) →
        ∃ N, ∀ n ≥ N, ∀ g : f (n + 1) ⟶ f n, g ≫ ι n = ι (n + 1) → IsIso g) ∧
    -- Every object in the interval satisfies the ascending chain condition
    (∀ (E : C), s.intervalProp C (t - η) (t + η) E →
      ∀ (f : ℕ → C) (ι : ∀ n, f n ⟶ E),
        (∀ n, s.intervalProp C (t - η) (t + η) (f n)) →
        (∀ n, IsStrictMono (ι n)) →
        (∀ n, ∃ g : f n ⟶ f (n + 1), g ≫ ι (n + 1) = ι n) →
        ∃ N, ∀ n ≥ N, ∀ g : f n ⟶ f (n + 1), g ≫ ι (n + 1) = ι n → IsIso g)

end Slicing

end CategoryTheory.Triangulated
