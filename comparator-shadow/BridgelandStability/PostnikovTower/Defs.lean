/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.ComposableArrows.Basic

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
* `CategoryTheory.Triangulated.PostnikovTower.factor`: the `i`-th factor object, derived
  as `(triangle i).obj₃` (no separate data field).

## Implementation notes

The chain of objects uses `ComposableArrows C n` (i.e., `Fin (n+1) ⥤ C`), ensuring
good categorical packaging. Each consecutive pair of objects is completed to a
distinguished triangle with a factor object as the third vertex. The factor is
derived directly as `obj₃` of the triangle — no separate `factor` field or
`triangle_obj₃` isomorphism is needed.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

-- ANCHOR: CategoryTheory.Triangulated.PostnikovTower
/-- A Postnikov tower of an object `E` in a pretriangulated category. This consists of
a chain of `n+1` objects connected by `n` distinguished triangles:
```
0 = A₀ → A₁ → ⋯ → Aₙ ≅ E
```
where each step `Aᵢ → Aᵢ₊₁` completes to a distinguished triangle
`Aᵢ → Aᵢ₊₁ → Fᵢ → Aᵢ⟦1⟧` with factor `Fᵢ = (triangle i).obj₃`.

The factor objects are derived from the triangles (as `obj₃`) rather than stored
as a separate data field. -/
structure PostnikovTower (E : C) where
  /-- The number of factors (equivalently, the number of distinguished triangles). -/
  n : ℕ
  /-- The chain of objects: `A₀ → A₁ → ⋯ → Aₙ`. -/
  chain : ComposableArrows C n
  /-- Each consecutive pair of objects completes to a distinguished triangle. -/
  triangle : Fin n → Pretriangulated.Triangle C
  /-- Each triangle is distinguished. -/
  triangle_dist : ∀ i, triangle i ∈ distTriang C
  /-- The triangle's first object is isomorphic to the i-th chain object. -/
  triangle_obj₁ : ∀ i, Nonempty ((triangle i).obj₁ ≅ chain.obj' i.val (by lia))
  /-- The triangle's second object is isomorphic to the (i+1)-th chain object. -/
  triangle_obj₂ : ∀ i, Nonempty ((triangle i).obj₂ ≅ chain.obj' (i.val + 1) (by lia))
  /-- The leftmost object is zero. -/
  base_isZero : IsZero (chain.left)
  /-- The rightmost object is isomorphic to `E`. -/
  top_iso : Nonempty (chain.right ≅ E)
  /-- When `n = 0`, the object `E` is zero. -/
  zero_isZero : n = 0 → IsZero E
-- ANCHOR_END: CategoryTheory.Triangulated.PostnikovTower

/-- The number of factors in a Postnikov tower. -/
def PostnikovTower.length {E : C} (P : PostnikovTower C E) : ℕ := P.n

variable {C} in
-- ANCHOR: CategoryTheory.Triangulated.PostnikovTower.factor
/-- The `i`-th factor of a Postnikov tower, derived as `obj₃` of the `i`-th
distinguished triangle. -/
def PostnikovTower.factor {E : C} (P : PostnikovTower C E) (i : Fin P.n) : C :=
  (P.triangle i).obj₃
-- ANCHOR_END: CategoryTheory.Triangulated.PostnikovTower.factor

variable {C} in
/-- The sequence of factor objects in a Postnikov tower. -/
def PostnikovTower.factors {E : C} (P : PostnikovTower C E) : Fin P.n → C := P.factor

end CategoryTheory.Triangulated
