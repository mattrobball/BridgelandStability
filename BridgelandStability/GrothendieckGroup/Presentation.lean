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

/-! ### Extensionality and induction -/

/-- Two homomorphisms from `P.K0` that agree on generators are equal. -/
theorem hom_ext {A : Type*} [AddCommGroup A] {f g : P.K0 →+ A}
    (h : ∀ X : P.Obj, f (P.of X) = g (P.of X)) : f = g :=
  AddMonoidHom.ext fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      induction x using FreeAbelianGroup.induction_on with
      | zero => simp [map_zero]
      | of X => exact h X
      | neg x ih => simp [map_neg, ih]
      | add x y ihx ihy => simp [map_add, ihx, ihy]

/-- Induction principle for `P.K0`: it suffices to check generators, zero, negation, and
addition. -/
@[elab_as_elim]
theorem induction_on {motive : P.K0 → Prop} (x : P.K0)
    (of : ∀ X : P.Obj, motive (P.of X))
    (zero : motive 0)
    (neg : ∀ a, motive a → motive (-a))
    (add : ∀ a b, motive a → motive b → motive (a + b)) : motive x := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    induction x using FreeAbelianGroup.induction_on with
    | zero => simpa [QuotientAddGroup.mk_zero] using zero
    | of X => exact of X
    | neg x ih => simpa [map_neg] using neg _ ih
    | add x y ihx ihy => simpa [map_add] using add _ _ ihx ihy

/-! ### Functorial maps -/

/-- The class map is additive for its own presentation. -/
instance isAdditive_of : P.IsAdditive P.of where
  additive := P.of_rel

/-- The induced map on Grothendieck groups from a function on objects that respects
relations. The additivity proof is an explicit argument since composed functions
`Q.of ∘ f` are not suited to typeclass inference. -/
def map {Q : K0Presentation} (f : P.Obj → Q.Obj)
    (hf : P.IsAdditive (Q.of ∘ f)) : P.K0 →+ Q.K0 :=
  @P.lift _ _ (Q.of ∘ f) hf

@[simp]
theorem map_of {Q : K0Presentation} (f : P.Obj → Q.Obj)
    (hf : P.IsAdditive (Q.of ∘ f)) (X : P.Obj) :
    P.map f hf (P.of X) = Q.of (f X) :=
  @P.lift_of _ _ (Q.of ∘ f) hf X

/-- A compatible map on relations implies additivity of the induced object map. -/
theorem IsAdditive.of_relMap {Q : K0Presentation} (fObj : P.Obj → Q.Obj)
    (fRel : P.Rel → Q.Rel)
    (h₁ : ∀ r, fObj (P.obj₁ r) = Q.obj₁ (fRel r))
    (h₂ : ∀ r, fObj (P.obj₂ r) = Q.obj₂ (fRel r))
    (h₃ : ∀ r, fObj (P.obj₃ r) = Q.obj₃ (fRel r)) :
    P.IsAdditive (Q.of ∘ fObj) where
  additive r := by simp only [Function.comp]; rw [h₂, h₁, h₃]; exact Q.of_rel (fRel r)

theorem map_id : P.map id ⟨P.of_rel⟩ = AddMonoidHom.id P.K0 := by
  apply P.hom_ext; intro X; simp [map]

variable {P} in
theorem map_comp {Q R : K0Presentation} (f : P.Obj → Q.Obj) (g : Q.Obj → R.Obj)
    (hf : P.IsAdditive (Q.of ∘ f))
    (hg : Q.IsAdditive (R.of ∘ g))
    (hgf : P.IsAdditive (R.of ∘ g ∘ f)) :
    P.map (g ∘ f) hgf = (Q.map g hg).comp (P.map f hf) := by
  apply P.hom_ext; intro X; simp [map]

end K0Presentation
