/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Tactic

/-!
# K₀ Presentation

A lightweight algebraic abstraction for Grothendieck group quotients. A
`K0Presentation` specifies a type of objects, a type of relations, and
three projections extracting the "middle = first + third" pattern. The
quotient `P.K0 = FreeAbelianGroup P.Obj ⧸ {obj₂(r) - obj₁(r) - obj₃(r)}` is
the associated Grothendieck group.

This factors out the identical quotient plumbing shared by:
- The triangulated K₀ (relations from distinguished triangles)
- The heart K₀ (relations from short exact sequences)

The abstraction lives below category theory — it is purely algebraic.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

universe v u

/-- A presentation of a Grothendieck-style group: objects, relations, and
the three-term decomposition `obj₂(r) = obj₁(r) + obj₃(r)`. -/
structure K0Presentation where
  /-- The type of objects (generators). -/
  Obj : Type u
  /-- The type of relations (e.g., distinguished triangles, short exact sequences). -/
  Rel : Type v
  /-- The first term of the relation (e.g., `T.obj₁` or `S.X₁`). -/
  obj₁ : Rel → Obj
  /-- The middle term (the one that equals the sum of the other two). -/
  obj₂ : Rel → Obj
  /-- The third term. -/
  obj₃ : Rel → Obj

namespace K0Presentation

variable (P : K0Presentation.{u, v})

/-- The subgroup of relations: `{obj₂(r) - obj₁(r) - obj₃(r) | r : Rel}`. -/
def subgroup : AddSubgroup (FreeAbelianGroup P.Obj) :=
  AddSubgroup.closure
    {x | ∃ r : P.Rel,
      x = FreeAbelianGroup.of (P.obj₂ r) - FreeAbelianGroup.of (P.obj₁ r) -
          FreeAbelianGroup.of (P.obj₃ r)}

/-- The Grothendieck group: free abelian group on objects modulo the relations. -/
abbrev K0 : Type _ := FreeAbelianGroup P.Obj ⧸ P.subgroup

instance : AddCommGroup P.K0 :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup P.Obj ⧸ P.subgroup))

/-- The class map: sends an object to its equivalence class. -/
def of (X : P.Obj) : P.K0 :=
  QuotientAddGroup.mk (FreeAbelianGroup.of X)

/-- The fundamental relation: `[obj₂(r)] = [obj₁(r)] + [obj₃(r)]`. -/
theorem of_rel (r : P.Rel) :
    P.of (P.obj₂ r) = P.of (P.obj₁ r) + P.of (P.obj₃ r) := by
  simp only [of, K0]
  apply Quotient.sound
  change QuotientAddGroup.leftRel _ _ _
  rw [QuotientAddGroup.leftRel_apply]
  have h : FreeAbelianGroup.of (P.obj₂ r) - FreeAbelianGroup.of (P.obj₁ r) -
    FreeAbelianGroup.of (P.obj₃ r) ∈ P.subgroup :=
    AddSubgroup.subset_closure ⟨r, rfl⟩
  convert P.subgroup.neg_mem h using 1
  abel

/-- A function on objects is *additive* for a presentation if it respects the relations. -/
class IsAdditive {A : Type*} [AddCommGroup A] (f : P.Obj → A) : Prop where
  additive : ∀ r : P.Rel, f (P.obj₂ r) = f (P.obj₁ r) + f (P.obj₃ r)

/-- The universal property: an additive function lifts uniquely to a group homomorphism. -/
def lift {A : Type*} [AddCommGroup A] (f : P.Obj → A) [P.IsAdditive f] : P.K0 →+ A :=
  QuotientAddGroup.lift P.subgroup (FreeAbelianGroup.lift f)
    ((AddSubgroup.closure_le _).mpr fun x ⟨r, hx⟩ ↦ by
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hx, map_sub,
        FreeAbelianGroup.lift_apply_of]
      have h := IsAdditive.additive (P := P) (f := f) r
      rw [h]; abel)

@[simp]
theorem lift_of {A : Type*} [AddCommGroup A] (f : P.Obj → A) [P.IsAdditive f] (X : P.Obj) :
    P.lift f (P.of X) = f X :=
  FreeAbelianGroup.lift_apply_of f X

end K0Presentation
