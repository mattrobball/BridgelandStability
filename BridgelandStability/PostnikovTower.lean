/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.ComposableArrows

/-!
# Postnikov Towers in Triangulated Categories

A Postnikov tower of an object `E` in a pretriangulated category is a finite chain of
distinguished triangles that filter `E`. This structure separates the tower/filtration
data from any phase or semistability data that may be layered on top (e.g., for
Harder-Narasimhan filtrations).

## Main definitions

* `CategoryTheory.Triangulated.PostnikovTower`: a finite chain of distinguished triangles
  filtering an object `E`, with a zero base and `E` at the top.
* `CategoryTheory.Triangulated.PostnikovTower.length`: the number of factors.

## Implementation notes

The chain of objects uses `ComposableArrows C n` (i.e., `Fin (n+1) ⥤ C`), ensuring
good categorical packaging. Each consecutive pair of objects is completed to a
distinguished triangle with a factor object as the third vertex. The isomorphisms
between chain objects and triangle vertices are wrapped in `Nonempty` to stay in `Prop`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A Postnikov tower of an object `E` in a pretriangulated category. This consists of
a chain of `n+1` objects connected by `n` distinguished triangles:
```
0 = A₀ → A₁ → ⋯ → Aₙ ≅ E
```
where each step `Aᵢ → Aᵢ₊₁` completes to a distinguished triangle
`Aᵢ → Aᵢ₊₁ → Fᵢ → Aᵢ⟦1⟧` with factor `Fᵢ`. -/
structure PostnikovTower (E : C) where
  /-- The number of factors (equivalently, the number of distinguished triangles). -/
  n : ℕ
  /-- The chain of objects: `A₀ → A₁ → ⋯ → Aₙ`. -/
  chain : ComposableArrows C n
  /-- The factors (third vertices of the triangles). -/
  factor : Fin n → C
  /-- Each consecutive arrow completes to a distinguished triangle
  `Aᵢ → Aᵢ₊₁ → Fᵢ → Aᵢ⟦1⟧`. -/
  triangle : Fin n → Pretriangulated.Triangle C
  /-- Each triangle is distinguished. -/
  triangle_dist : ∀ i, triangle i ∈ distTriang C
  /-- The triangle's first object is isomorphic to the i-th chain object. -/
  triangle_obj₁ : ∀ i, Nonempty ((triangle i).obj₁ ≅ chain.obj' i.val (by omega))
  /-- The triangle's second object is isomorphic to the (i+1)-th chain object. -/
  triangle_obj₂ : ∀ i, Nonempty ((triangle i).obj₂ ≅ chain.obj' (i.val + 1) (by omega))
  /-- The triangle's third object is isomorphic to the factor. -/
  triangle_obj₃ : ∀ i, Nonempty ((triangle i).obj₃ ≅ factor i)
  /-- The leftmost object is zero. -/
  base_isZero : IsZero (chain.left)
  /-- The rightmost object is isomorphic to `E`. -/
  top_iso : Nonempty (chain.right ≅ E)
  /-- When `n = 0`, the object `E` is zero. -/
  zero_isZero : n = 0 → IsZero E

/-- The number of factors in a Postnikov tower. -/
def PostnikovTower.length {E : C} (P : PostnikovTower C E) : ℕ := P.n

/-- The sequence of factor objects in a Postnikov tower. -/
def PostnikovTower.factors {E : C} (P : PostnikovTower C E) : Fin P.n → C := P.factor

end CategoryTheory.Triangulated
