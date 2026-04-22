/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses

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
open scoped ZeroObject

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

/-- The number of factors in a Postnikov tower. -/
def PostnikovTower.length {E : C} (P : PostnikovTower C E) : ℕ := P.n

variable {C} in
/-- The `i`-th factor of a Postnikov tower, derived as `obj₃` of the `i`-th
distinguished triangle. -/
def PostnikovTower.factor {E : C} (P : PostnikovTower C E) (i : Fin P.n) : C :=
  (P.triangle i).obj₃

variable {C} in
/-- The sequence of factor objects in a Postnikov tower. -/
def PostnikovTower.factors {E : C} (P : PostnikovTower C E) : Fin P.n → C := P.factor

/-! ### `IsPostnikovTower` predicate

A principled replacement for the bundled `PostnikovTower` structure. Given a
family `Q : Fin n → ObjectProperty C`, the predicate `IsPostnikovTower Q chain`
asserts that `chain : ComposableArrows C n` is a Postnikov tower whose `i`-th
cone lies in `Q i`. The cone of the `i`-th consecutive morphism is existentially
bundled via `ObjectProperty.trW`, so there is no separate triangle data. -/

variable {C}

/-- `chain : ComposableArrows C n` is a Postnikov tower with cone conditions
`Q : Fin n → ObjectProperty C`: the chain starts at zero, and the cone of
each consecutive morphism lies in the prescribed `ObjectProperty`. -/
structure IsPostnikovTower {n : ℕ} (Q : Fin n → ObjectProperty C)
    (chain : ComposableArrows C n) : Prop where
  /-- The chain starts at the zero object. -/
  base_isZero : IsZero chain.left
  /-- The cone of the `i`-th consecutive morphism lies in `Q i`. -/
  cone_mem (i : Fin n) : (Q i).trW (chain.map' i.val (i.val + 1))

namespace IsPostnikovTower

variable {n : ℕ} {Q : Fin n → ObjectProperty C} {chain : ComposableArrows C n}

/-- The `i`-th cone of a Postnikov tower, chosen classically from the
`ObjectProperty.trW` witness. -/
noncomputable def cone (h : IsPostnikovTower Q chain) (i : Fin n) : C :=
  (h.cone_mem i).choose

/-- The `i`-th distinguished triangle of a Postnikov tower, built from the
chain's `i`-th consecutive morphism and the classical cone witness. -/
noncomputable def triangle (h : IsPostnikovTower Q chain) (i : Fin n) :
    Pretriangulated.Triangle C :=
  Pretriangulated.Triangle.mk (chain.map' i.val (i.val + 1))
    (h.cone_mem i).choose_spec.choose
    (h.cone_mem i).choose_spec.choose_spec.choose

lemma triangle_mem_distTriang (h : IsPostnikovTower Q chain) (i : Fin n) :
    h.triangle i ∈ distTriang C :=
  (h.cone_mem i).choose_spec.choose_spec.choose_spec.choose

lemma cone_mem_prop (h : IsPostnikovTower Q chain) (i : Fin n) : (Q i) (h.cone i) :=
  (h.cone_mem i).choose_spec.choose_spec.choose_spec.choose_spec

@[simp] lemma triangle_obj₁ (h : IsPostnikovTower Q chain) (i : Fin n) :
    (h.triangle i).obj₁ = chain.obj' i.val (by lia) := rfl

@[simp] lemma triangle_obj₂ (h : IsPostnikovTower Q chain) (i : Fin n) :
    (h.triangle i).obj₂ = chain.obj' (i.val + 1) (by lia) := rfl

@[simp] lemma triangle_obj₃ (h : IsPostnikovTower Q chain) (i : Fin n) :
    (h.triangle i).obj₃ = h.cone i := rfl

@[simp] lemma triangle_mor₁ (h : IsPostnikovTower Q chain) (i : Fin n) :
    (h.triangle i).mor₁ = chain.map' i.val (i.val + 1) := rfl

end IsPostnikovTower

/-- `IsPostnikovTower Q` is closed under isomorphisms of composable arrows:
if two chains are naturally isomorphic, being a Postnikov tower transports across. -/
instance IsPostnikovTower.isClosedUnderIsomorphisms {n : ℕ}
    (Q : Fin n → ObjectProperty C) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsPostnikovTower (C := C) Q : ObjectProperty (ComposableArrows C n)) where
  of_iso {chain₁ chain₂} e h :=
    { base_isZero := h.base_isZero.of_iso (e.app (⟨0, by lia⟩ : Fin (n + 1))).symm
      cone_mem i :=
        ((Q i).trW.arrow_mk_iso_iff
          (Arrow.isoMk (e.app ⟨i.val, by lia⟩) (e.app ⟨i.val + 1, by lia⟩)
            (e.hom.naturality _).symm)).mp (h.cone_mem i) }

/-! ### Tower-level algebra

Operations that construct new `IsPostnikovTower` witnesses from old ones, without
reference to any phase data. These are the reusable building blocks for HN
filtration operations. -/

namespace IsPostnikovTower

variable {n : ℕ} {Q : Fin n → ObjectProperty C} {chain : ComposableArrows C n}

/-- Prefix of length `k` of a Postnikov tower. -/
lemma «prefix» (h : IsPostnikovTower Q chain) (k : ℕ) (hk : k ≤ n) :
    IsPostnikovTower (fun i : Fin k ↦ Q ⟨i.val, by lia⟩)
      (ComposableArrows.mkOfObjOfMapSucc
        (fun i : Fin (k + 1) ↦ chain.obj ⟨i.val, by lia⟩)
        (fun i : Fin k ↦ chain.map' i.val (i.val + 1) (by lia) (by lia))) where
  base_isZero := by
    change IsZero (chain.obj ⟨0, by lia⟩)
    exact h.base_isZero
  cone_mem i := by
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i.val i.isLt]
    exact h.cone_mem ⟨i.val, by lia⟩

/-- Drop the last step of a Postnikov tower. -/
lemma dropLast (h : IsPostnikovTower Q chain) (hn : 1 ≤ n) :
    IsPostnikovTower (fun i : Fin (n - 1) ↦ Q ⟨i.val, by lia⟩)
      (ComposableArrows.mkOfObjOfMapSucc
        (fun i : Fin (n - 1 + 1) ↦ chain.obj ⟨i.val, by lia⟩)
        (fun i : Fin (n - 1) ↦ chain.map' i.val (i.val + 1) (by lia) (by lia))) :=
  h.«prefix» (n - 1) (by lia)

/-- Drop the first step of a Postnikov tower when its cone is zero. -/
lemma dropFirst (h : IsPostnikovTower Q chain) (hn : 1 ≤ n)
    (hzero : IsZero (h.cone ⟨0, by lia⟩)) :
    IsPostnikovTower (fun i : Fin (n - 1) ↦ Q ⟨i.val + 1, by lia⟩)
      (ComposableArrows.mkOfObjOfMapSucc
        (fun i : Fin (n - 1 + 1) ↦ chain.obj ⟨i.val + 1, by lia⟩)
        (fun i : Fin (n - 1) ↦ chain.map' (i.val + 1) (i.val + 2) (by lia) (by lia))) where
  base_isZero := by
    set T := h.triangle ⟨0, by lia⟩ with hT_def
    haveI hiso : IsIso T.mor₁ :=
      (Pretriangulated.Triangle.isZero₃_iff_isIso₁ T
        (h.triangle_mem_distTriang ⟨0, by lia⟩)).mp hzero
    exact h.base_isZero.of_iso (asIso T.mor₁).symm
  cone_mem i := by
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i.val i.isLt]
    exact h.cone_mem ⟨i.val + 1, by lia⟩

/-- Shifting a Postnikov tower by `a : ℤ`: the cone at index `i` is `(Q i).trW`'s
cone shifted by `a`, which the caller must witness via `hQ'`. -/
lemma shiftByFunctor {Q' : Fin n → ObjectProperty C}
    (h : IsPostnikovTower Q chain) (a : ℤ)
    (hQ' : ∀ (i : Fin n) (X : C), Q i X → Q' i (X⟦a⟧)) :
    IsPostnikovTower Q' (chain ⋙ shiftFunctor C a) where
  base_isZero := (shiftFunctor C a).map_isZero h.base_isZero
  cone_mem i := by
    obtain ⟨Z, g, k, hT, hZ⟩ := h.cone_mem i
    show (Q' i).trW ((chain.map' i.val (i.val + 1))⟦a⟧')
    rw [← (Q' i).smul_mem_trW_iff _ a.negOnePow]
    exact ⟨_, _, _,
      Pretriangulated.Triangle.shift_distinguished
        (Pretriangulated.Triangle.mk (chain.map' i.val (i.val + 1)) g k) hT a,
      hQ' i _ hZ⟩

/-- The trivial empty Postnikov tower over a zero object. -/
lemma zero {X : C} (hX : IsZero X) :
    IsPostnikovTower (n := 0) (fun _ ↦ ⊤) (ComposableArrows.mk₀ X) where
  base_isZero := hX
  cone_mem i := i.elim0

/-- A one-step Postnikov tower from zero to a single object with given property. -/
lemma single {X : C} (Q₀ : ObjectProperty C) (hX : Q₀ X) :
    IsPostnikovTower (n := 1) (fun _ ↦ Q₀)
      (ComposableArrows.mk₁ (0 : (0 : C) ⟶ X)) where
  base_isZero := by
    change IsZero (0 : C)
    exact isZero_zero C
  cone_mem j := by
    obtain rfl : j = ⟨0, by lia⟩ := Fin.ext (by lia)
    exact ⟨X, 𝟙 X, 0, Pretriangulated.contractible_distinguished₁ X, hX⟩

end IsPostnikovTower

end CategoryTheory.Triangulated
