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
quotient `P.K0 = FreeAbelianGroup Obj ⧸ {obj₂(r) - obj₁(r) - obj₃(r)}` is
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

universe u v u' v' u'' v''

-- ANCHOR: K0Presentation
/-- A presentation of a Grothendieck-style group: objects, relations, and
the three-term decomposition `obj₂(r) = obj₁(r) + obj₃(r)`. -/
@[nolint checkUnivs]
structure K0Presentation (Obj : Type u) (Rel : Type v) where
  /-- The first term of the relation (e.g., `T.obj₁` or `S.X₁`). -/
  obj₁ : Rel → Obj
  /-- The middle term (the one that equals the sum of the other two). -/
  obj₂ : Rel → Obj
  /-- The third term. -/
  obj₃ : Rel → Obj
-- ANCHOR_END: K0Presentation

namespace K0Presentation

variable {Obj : Type u} {Rel : Type v} (P : K0Presentation Obj Rel)

-- ANCHOR: K0Presentation.subgroup
/-- The subgroup of relations: `{obj₂(r) - obj₁(r) - obj₃(r) | r : Rel}`. -/
def subgroup : AddSubgroup (FreeAbelianGroup Obj) :=
  AddSubgroup.closure
    {x | ∃ r : Rel,
      x = FreeAbelianGroup.of (P.obj₂ r) - FreeAbelianGroup.of (P.obj₁ r) -
          FreeAbelianGroup.of (P.obj₃ r)}
-- ANCHOR_END: K0Presentation.subgroup

-- ANCHOR: K0Presentation.K0
/-- The Grothendieck group: free abelian group on objects modulo the relations. -/
abbrev K0 : Type _ := FreeAbelianGroup Obj ⧸ P.subgroup
-- ANCHOR_END: K0Presentation.K0

-- ANCHOR: K0Presentation.instAddCommGroupK0
instance : AddCommGroup P.K0 :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup Obj ⧸ P.subgroup))
-- ANCHOR_END: K0Presentation.instAddCommGroupK0

/-- The class map: sends an object to its equivalence class. -/
def of (X : Obj) : P.K0 :=
  QuotientAddGroup.mk (FreeAbelianGroup.of X)

/-- The fundamental relation: `[obj₂(r)] = [obj₁(r)] + [obj₃(r)]`. -/
theorem of_rel (r : Rel) :
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

-- ANCHOR: K0Presentation.IsAdditive
/-- A function on objects is *additive* for a presentation if it respects the relations. -/
class IsAdditive {A : Type*} [AddCommGroup A] (f : Obj → A) : Prop where
  additive : ∀ r : Rel, f (P.obj₂ r) = f (P.obj₁ r) + f (P.obj₃ r)
-- ANCHOR_END: K0Presentation.IsAdditive

-- ANCHOR: K0Presentation.lift
/-- The universal property: an additive function lifts uniquely to a group homomorphism. -/
def lift {A : Type*} [AddCommGroup A] (f : Obj → A) [P.IsAdditive f] : P.K0 →+ A :=
  QuotientAddGroup.lift P.subgroup (FreeAbelianGroup.lift f)
    ((AddSubgroup.closure_le _).mpr fun x ⟨r, hx⟩ ↦ by
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hx, map_sub,
        FreeAbelianGroup.lift_apply_of]
      have h := IsAdditive.additive (P := P) (f := f) r
      rw [h]; abel)
-- ANCHOR_END: K0Presentation.lift

@[simp]
theorem lift_of {A : Type*} [AddCommGroup A] (f : Obj → A) [P.IsAdditive f] (X : Obj) :
    P.lift f (P.of X) = f X :=
  FreeAbelianGroup.lift_apply_of f X

/-! ### Extensionality and induction -/

/-- Two homomorphisms from `P.K0` that agree on generators are equal. -/
theorem hom_ext {A : Type*} [AddCommGroup A] {f g : P.K0 →+ A}
    (h : ∀ X : Obj, f (P.of X) = g (P.of X)) : f = g :=
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
    (of : ∀ X : Obj, motive (P.of X))
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
def map {QObj : Type u'} {QRel : Type v'} {Q : K0Presentation QObj QRel} (f : Obj → QObj)
    (hf : P.IsAdditive (Q.of ∘ f)) : P.K0 →+ Q.K0 :=
  P.lift (f := Q.of ∘ f)

@[simp]
theorem map_of {QObj : Type u'} {QRel : Type v'} {Q : K0Presentation QObj QRel} (f : Obj → QObj)
    (hf : P.IsAdditive (Q.of ∘ f)) (X : Obj) :
    P.map f hf (P.of X) = Q.of (f X) :=
  P.lift_of (f := Q.of ∘ f) X

/-- A compatible map on relations implies additivity of the induced object map. -/
theorem IsAdditive.of_relMap {QObj : Type u'} {QRel : Type v'} {Q : K0Presentation QObj QRel}
    (fObj : Obj → QObj) (fRel : Rel → QRel)
    (h₁ : ∀ r, fObj (P.obj₁ r) = Q.obj₁ (fRel r))
    (h₂ : ∀ r, fObj (P.obj₂ r) = Q.obj₂ (fRel r))
    (h₃ : ∀ r, fObj (P.obj₃ r) = Q.obj₃ (fRel r)) :
    P.IsAdditive (Q.of ∘ fObj) where
  additive r := by simp only [Function.comp]; rw [h₂, h₁, h₃]; exact Q.of_rel (fRel r)

theorem map_id : P.map (Q := P) id ⟨P.of_rel⟩ = AddMonoidHom.id P.K0 := by
  apply P.hom_ext; intro X; simp [map]

variable {Obj : Type u} {Rel : Type v} {P : K0Presentation Obj Rel} in
theorem map_comp
    {QObj : Type u'} {QRel : Type v'} {Q : K0Presentation QObj QRel}
    {RObj : Type u''} {RRel : Type v''} {R : K0Presentation RObj RRel}
    (f : Obj → QObj) (g : QObj → RObj)
    (hf : P.IsAdditive (Q.of ∘ f))
    (hg : Q.IsAdditive (R.of ∘ g))
    (hgf : P.IsAdditive (R.of ∘ g ∘ f)) :
    P.map (g ∘ f) hgf = (Q.map g hg).comp (P.map f hf) := by
  apply P.hom_ext; intro X; simp [map]

end K0Presentation
