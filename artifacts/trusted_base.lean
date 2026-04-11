import Mathlib

/-! # Trusted Formalization Base
BridgelandStability — `CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent`
Auto-generated — all proofs replaced with `sorry`.
57 declarations in dependency order.
-/

set_option maxHeartbeats 400000
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option backward.privateInPublic.warn false

universe v u u' v' u'' v'' w

-- ═══ PostnikovTower.Defs ═══

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
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
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
variable {C} in
/-- The `i`-th factor of a Postnikov tower, derived as `obj₃` of the `i`-th
distinguished triangle. -/
def PostnikovTower.factor {E : C} (P : PostnikovTower C E) (i : Fin P.n) : C :=
  (P.triangle i).obj₃
variable {C} in
/-- The sequence of factor objects in a Postnikov tower. -/
def PostnikovTower.factors {E : C} (P : PostnikovTower C E) : Fin P.n → C := P.factor
end CategoryTheory.Triangulated


-- ═══ Slicing.Defs ═══

/-!
# Slicing Definitions

Core data-carrying declarations for Bridgeland slicings: the `HNFiltration` and `Slicing`
structures, the intrinsic phase functions `φ⁺`/`φ⁻`, and supporting HN filtration operations
(prefix, shift, transport, drop, existence of nonzero factors).

These definitions are separated from the full proof files so that downstream modules
(stability conditions, topology, Euler form) can import lightweight type-level dependencies
without pulling in hom-vanishing proofs and interval subcategory theory.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
/-! ### Grind annotations for arithmetic automation -/
attribute [grind →] StrictAnti.imp
attribute [grind →] StrictMono.imp
attribute [grind →] Antitone.imp
attribute [grind →] Monotone.imp
namespace CategoryTheory.Triangulated
section Slicing
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
/-! ### Core structures -/
/-- A Harder-Narasimhan (HN) filtration of an object `E` with respect to a phase
predicate `P`. This extends a `PostnikovTower` with phase data: each factor is
semistable with a given phase, and the phases are strictly decreasing. -/
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C) extends PostnikovTower C E where
  /-- The phases of the semistable factors, in strictly decreasing order. -/
  φ : Fin n → ℝ
  /-- The phases are strictly decreasing (higher phase factors appear first). -/
  hφ : StrictAnti φ
  /-- Each factor is semistable of the given phase. -/
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j)
/-- A slicing of a pretriangulated category `C`, as defined in
Bridgeland (2007), Definition 5.1. A slicing assigns to each real number `φ`
a full subcategory of semistable objects `P(φ)` (as an `ObjectProperty`),
subject to shift, Hom-vanishing, and Harder-Narasimhan existence axioms.

Each `P(φ)` is an `ObjectProperty C`, enabling use of the `ObjectProperty` API
(e.g. `FullSubcategory`, shift stability, closure properties). -/
structure Slicing where
  /-- For each phase `φ ∈ ℝ`, the property of semistable objects of phase `φ`. -/
  P : ℝ → ObjectProperty C
  /-- Each phase slice is closed under isomorphisms. -/
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  /-- The zero object satisfies every phase predicate. -/
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)
  /-- Shifting by `[1]` increases the phase by 1, and conversely. -/
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  /-- Morphisms from higher-phase to lower-phase nonzero semistable objects vanish. -/
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0
  /-- Every object has a Harder-Narasimhan filtration. -/
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)
/-- The interval subcategory predicate `P((a,b))`: an object `E` belongs to the
interval subcategory if it is zero or all phases in its HN filtration lie in `(a,b)`. -/
def Slicing.intervalProp (s : Slicing C) (a b : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E), ∀ i, a < F.φ i ∧ F.φ i < b
/-- For any nonzero object, there exists an HN filtration with nonzero first factor.
Proved by repeatedly dropping zero first factors; terminates since `n` decreases
and some factor must be nonzero (by `exists_nonzero_factor`). -/
lemma HNFiltration.exists_nonzero_first (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n), ¬IsZero (F.triangle ⟨0, hn⟩).obj₃  := sorry
/-- For any nonzero object, there exists an HN filtration with nonzero last factor.
Proved by repeatedly dropping zero last factors. -/
lemma HNFiltration.exists_nonzero_last (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.triangle ⟨F.n - 1, by lia⟩).obj₃  := sorry
/-- The intrinsic highest phase of a nonzero object with respect to a slicing.
This is the phase of the first factor in any HN filtration with nonzero first factor.
Well-defined by `phiPlus_eq_of_nonzero_factors`. -/
noncomputable def Slicing.phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hn := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  F.φ ⟨0, hn⟩
/-- The intrinsic lowest phase of a nonzero object with respect to a slicing.
This is the phase of the last factor in any HN filtration with nonzero last factor.
Well-defined by `phiMinus_eq_of_nonzero_last_factors`. -/
noncomputable def Slicing.phiMinus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_last C s hE).choose
  let hn : 0 < F.n := (HNFiltration.exists_nonzero_last C s hE).choose_spec.choose
  F.φ ⟨F.n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩
end Slicing
end CategoryTheory.Triangulated


-- ═══ GrothendieckGroup.Defs ═══

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
namespace K0Presentation
variable {Obj : Type u} {Rel : Type v} (P : K0Presentation Obj Rel)
/-- The subgroup of relations: `{obj₂(r) - obj₁(r) - obj₃(r) | r : Rel}`. -/
def subgroup : AddSubgroup (FreeAbelianGroup Obj) :=
  AddSubgroup.closure
    {x | ∃ r : Rel,
      x = FreeAbelianGroup.of (P.obj₂ r) - FreeAbelianGroup.of (P.obj₁ r) -
          FreeAbelianGroup.of (P.obj₃ r)}
/-- The Grothendieck group: free abelian group on objects modulo the relations. -/
abbrev K0 : Type _ := FreeAbelianGroup Obj ⧸ P.subgroup
instance : AddCommGroup P.K0 :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup Obj ⧸ P.subgroup))
/-- A function on objects is *additive* for a presentation if it respects the relations. -/
class IsAdditive {A : Type*} [AddCommGroup A] (f : Obj → A) : Prop where
  additive : ∀ r : Rel, f (P.obj₂ r) = f (P.obj₁ r) + f (P.obj₃ r)
/-- The universal property: an additive function lifts uniquely to a group homomorphism. -/
def lift {A : Type*} [AddCommGroup A] (f : Obj → A) [P.IsAdditive f] : P.K0 →+ A :=
  QuotientAddGroup.lift P.subgroup (FreeAbelianGroup.lift f)
    ((AddSubgroup.closure_le _).mpr fun x ⟨r, hx⟩ ↦ by
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hx, map_sub,
        FreeAbelianGroup.lift_apply_of]
      have h := IsAdditive.additive (P := P) (f := f) r
      rw [h]; abel)
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


-- ═══ GrothendieckGroup.Basic ═══

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
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
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
variable {C} in
/-- A function `f : C → A` to an additive group is triangle-additive if
`f(B) = f(A) + f(C)` for every distinguished triangle `A → B → C → A⟦1⟧`. -/
class IsTriangleAdditive {A : Type*} [AddCommGroup A] (f : C → A) : Prop where
  additive : ∀ (T : Pretriangulated.Triangle C),
    T ∈ (distTriang C) → f T.obj₂ = f T.obj₁ + f T.obj₃
variable {C} in
instance {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] :
    (trianglePresentation C).IsAdditive f  := sorry
/-- The universal property of K₀: any triangle-additive function lifts
to an additive group homomorphism from K₀. -/
def K₀.lift {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] : K₀ C →+ A :=
  (trianglePresentation C).lift f
section ClassMap
variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)
/-- The class of an object `E` in the target lattice `Λ`, via the class map
`v : K₀(C) → Λ`. This is `v([E])` in the notation of Bridgeland, BMS16, etc.

At `v = id`: `cl v E = K₀.of C E` definitionally. -/
abbrev cl (E : C) : Λ := v (K₀.of C E)
@[simp] lemma cl_id (E : C) : cl C (AddMonoidHom.id (K₀ C)) E = K₀.of C E := rfl
@[simp] lemma cl_isZero {E : C} (hE : IsZero E) : cl C v E = 0 := by
  simp [cl, K₀.of_isZero C hE, map_zero]
lemma cl_triangle (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) :
    cl C v T.obj₂ = cl C v T.obj₁ + cl C v T.obj₃ := by
  simp [cl, K₀.of_triangle C T hT, map_add]
lemma cl_iso {X Y : C} (e : X ≅ Y) : cl C v X = cl C v Y := by
  simp [cl, K₀.of_iso C e]
@[simp] lemma cl_shift_one (E : C) : cl C v (E⟦(1 : ℤ)⟧) = -cl C v E := by
  simp [cl]
@[simp] lemma cl_shift_neg_one (E : C) : cl C v (E⟦(-1 : ℤ)⟧) = -cl C v E := by
  simp [cl]
theorem cl_postnikovTower_eq_sum {E : C} (P : PostnikovTower C E) :
    cl C v E = ∑ i : Fin P.n, cl C v (P.factor i) := by
  simp [cl, K₀.of_postnikovTower_eq_sum C P, map_sum]
end ClassMap
end CategoryTheory.Triangulated


-- ═══ QuasiAbelian.Basic ═══

/-!
# Strict Morphisms and Quasi-Abelian Categories

We define strict morphisms and quasi-abelian categories following
Bridgeland's "Stability conditions on triangulated categories" (2007), §4.

A morphism `f : X ⟶ Y` in a category with kernels and cokernels is *strict*
if the canonical comparison morphism from the coimage to the image is an isomorphism.
In an abelian category every morphism is strict, so strictness is a nontrivial condition
only in the pre-abelian setting.

A *quasi-abelian* category is a preadditive category with kernels, cokernels, pullbacks,
and pushouts in which pullbacks of strict epimorphisms are strict epimorphisms and
pushouts of strict monomorphisms are strict monomorphisms.

## Main definitions

* `CategoryTheory.IsStrict`: a morphism is strict if `coimageImageComparison` is an iso
* `CategoryTheory.IsStrictMono`: mono + strict
* `CategoryTheory.IsStrictEpi`: epi + strict
* `CategoryTheory.QuasiAbelian`: quasi-abelian category
* `CategoryTheory.StrictShortExact`: short exact with strict morphisms

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
* Schneiders, "Quasi-abelian categories and sheaves", Mém. Soc. Math. Fr. 1999
-/
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
section Strict
variable {X Y : C} (f : X ⟶ Y)
  [HasKernel f] [HasCokernel f]
  [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]
/-- A morphism `f` is *strict* if the canonical comparison morphism from the
(abelian) coimage to the (abelian) image is an isomorphism. In an abelian category,
every morphism is strict.

This uses `Abelian.coimageImageComparison` from `Mathlib.CategoryTheory.Abelian.Images`,
which is defined without assuming the category is abelian. -/
def IsStrict : Prop :=
  IsIso (Abelian.coimageImageComparison f)
/-- A morphism is a *strict monomorphism* if it is both a monomorphism and strict. -/
structure IsStrictMono : Prop where
  mono : Mono f
  strict : IsStrict f
end Strict
section StrictKernelCokernel
variable {X Y : C} {f : X ⟶ Y}
  [HasZeroObject C]
  [HasKernel f] [HasCokernel f]
  [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]
end StrictKernelCokernel
section QuasiAbelian
variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasKernels C] [HasCokernels C] [HasPullbacks C] [HasPushouts C]
end QuasiAbelian
section StrictShortExact
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasKernels C] [HasCokernels C]
end StrictShortExact
section KernelCokernelStrict
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]
end KernelCokernelStrict
section AbelianStrict
variable {C : Type u} [Category.{v} C] [Abelian C]
end AbelianStrict
section StrictSubobject
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [Preadditive C]
  [HasKernels C] [HasCokernels C]
namespace Subobject
variable {X : C}
/-- A subobject is *strict* if its arrow is a strict monomorphism. This is the
quasi-abelian notion of admissible / exact subobject used in Bridgeland's finite-length
thin interval categories. -/
def IsStrict (P : Subobject X) : Prop :=
  IsStrictMono P.arrow
section
end
end Subobject
/-- The ordered type of strict subobjects of `X`. -/
abbrev StrictSubobject (X : C) :=
  { P : Subobject X // P.IsStrict }
variable (X Y : C)
/-- An object is *strict-Artinian* if its strict subobjects satisfy the descending chain
condition. This is the exact finite-length notion relevant to quasi-abelian categories. -/
def isStrictArtinianObject : ObjectProperty C :=
  fun X ↦ WellFoundedLT (StrictSubobject X)
/-- An object is *strict-Artinian* if its strict subobjects satisfy the descending chain
condition. -/
abbrev IsStrictArtinianObject : Prop := isStrictArtinianObject.Is X
/-- An object is *strict-Noetherian* if its strict subobjects satisfy the ascending chain
condition. This is the exact finite-length notion relevant to quasi-abelian categories. -/
def isStrictNoetherianObject : ObjectProperty C :=
  fun X ↦ WellFoundedGT (StrictSubobject X)
/-- An object is *strict-Noetherian* if its strict subobjects satisfy the ascending chain
condition. -/
abbrev IsStrictNoetherianObject : Prop := isStrictNoetherianObject.Is X
instance [IsStrictNoetherianObject X] : WellFoundedGT (StrictSubobject X) :=
  isStrictNoetherianObject.prop_of_is X
section
omit [Preadditive C]
/-- Ordinary Artinian objects are strict-Artinian, since strict subobjects form a subtype of
all subobjects. -/
theorem isStrictArtinianObject_of_isArtinianObject [IsArtinianObject X] :
    IsStrictArtinianObject X := by
  let f : StrictSubobject X → Subobject X := Subtype.val
  exact
    (show isStrictArtinianObject.Is X from
      ObjectProperty.is_of_prop _
        (show WellFoundedLT (StrictSubobject X) from
          ⟨InvImage.wf f
            (wellFounded_lt :
              WellFounded ((· < ·) : Subobject X → Subobject X → Prop))⟩))
/-- Ordinary Noetherian objects are strict-Noetherian, since strict subobjects form a subtype
of all subobjects. -/
theorem isStrictNoetherianObject_of_isNoetherianObject [IsNoetherianObject X] :
    IsStrictNoetherianObject X := by
  let f : StrictSubobject X → Subobject X := Subtype.val
  exact
    (show isStrictNoetherianObject.Is X from
      ObjectProperty.is_of_prop _
        (show WellFoundedGT (StrictSubobject X) from
          ⟨InvImage.wf f
            (wellFounded_gt :
              WellFounded ((· > ·) : Subobject X → Subobject X → Prop))⟩))
end
end StrictSubobject
section StrictSubobjectAbelian
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C}
/-- In an abelian category, strict-Artinian and Artinian coincide, because every mono is strict. -/
theorem isArtinianObject_of_isStrictArtinianObject [IsStrictArtinianObject X] :
    IsArtinianObject X := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  let g : ℕ →o (StrictSubobject X)ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual ⟨f n, by
        exact (Subobject.isStrict_iff _).2 (isStrictMono_of_mono (Subobject.arrow (f n)))⟩,
      fun i j hij ↦ f.2 hij⟩
  haveI : WellFoundedGT (StrictSubobject X)ᵒᵈ := by
    rw [wellFoundedGT_dual_iff]
    infer_instance
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
  exact ⟨n, fun m hm ↦ by
    simpa using congrArg Subtype.val (hn m hm)⟩
/-- In an abelian category, strict-Noetherian and Noetherian coincide, because every mono is
strict. -/
theorem isNoetherianObject_of_isStrictNoetherianObject [IsStrictNoetherianObject X] :
    IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let g : ℕ →o StrictSubobject X :=
    ⟨fun n ↦ ⟨f n, by
        exact (Subobject.isStrict_iff _).2 (isStrictMono_of_mono (Subobject.arrow (f n)))⟩,
      fun i j hij ↦ f.2 hij⟩
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
  exact ⟨n, fun m hm ↦ by
    simpa using congrArg Subtype.val (hn m hm)⟩
end StrictSubobjectAbelian
section SubobjectFiniteness
variable {A : Type u} [Category.{v} A] {C : Type u} [Category.{v} C]
private def subobjectImageOfFaithfulPreservesMono (F : A ⥤ C) [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] {E : A} :
    Subobject E → Subobject (F.obj E) :=
  Subobject.lift (fun {S} (f : S ⟶ E) [Mono f] ↦ Subobject.mk (F.map f))
    (fun {S₁ S₂} f g [Mono f] [Mono g] i w ↦
      Subobject.mk_eq_mk_of_comm _ _ (F.mapIso i) (by
        change F.map i.hom ≫ F.map g = F.map f
        rw [← F.map_comp, w]))
private theorem subobjectImageOfFaithfulPreservesMono_injective (F : A ⥤ C) [F.Full]
    [F.Faithful] [F.PreservesMonomorphisms] {E : A} :
    Function.Injective (subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E)) := by
  intro s₁ s₂ heq
  induction s₁ using Subobject.ind
  induction s₂ using Subobject.ind
  rename_i S₁ f₁ _ S₂ f₂ _
  change Subobject.mk (F.map f₁) = Subobject.mk (F.map f₂) at heq
  exact Subobject.mk_eq_mk_of_comm f₁ f₂
    (F.preimageIso (Subobject.isoOfMkEqMk _ _ heq))
    (F.map_injective (by
      simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
      exact Subobject.ofMkLEMk_comp heq.le))
private theorem subobjectImageOfFaithfulPreservesMono_monotone (F : A ⥤ C) [F.Full]
    [F.Faithful] [F.PreservesMonomorphisms] {E : A} :
    Monotone (subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E)) := by
  intro s₁ s₂ h
  induction s₁ using Subobject.ind
  induction s₂ using Subobject.ind
  rename_i S₁ f₁ _ S₂ f₂ _
  change Subobject.mk (F.map f₁) ≤ Subobject.mk (F.map f₂)
  exact Subobject.mk_le_mk_of_comm (F.map (Subobject.ofMkLEMk f₁ f₂ h)) (by
    rw [← F.map_comp]
    exact congrArg (F.map) (Subobject.ofMkLEMk_comp h))
/-- A faithful functor that preserves monomorphisms induces an injection on subobject
lattices. If `F : A ⥤ C` is faithful and preserves monomorphisms, subobjects of `E`
in `A` inject into subobjects of `F.obj E` in `C`. Together with `Finite.of_injective`,
this transfers finiteness of subobject lattices from `C` to `A`.

The key use case is the full subcategory inclusion `ι : P(φ) ⥤ C`, where local
finiteness of the slicing gives `Finite (Subobject (ι.obj E))` in `C`, and we
need `Finite (Subobject E)` in `P(φ)`.

Note: fullness is not required. The hypothesis `PreservesMonomorphisms F` is needed
because a faithful functor does not automatically preserve monomorphisms (the mono
test in `C` involves objects not in the image of `F`). -/
theorem Finite.subobject_of_faithful_preservesMono (F : A ⥤ C) [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms]
    {E : A} (h : Finite (Subobject (F.obj E))) : Finite (Subobject E) :=
  Finite.of_injective
    (subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F)
    (subobjectImageOfFaithfulPreservesMono_injective (A := A) (C := C) F)
/-- Artinian objects transfer across full faithful functors that preserve monomorphisms. -/
theorem isArtinianObject_of_faithful_preservesMono (F : A ⥤ C) [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] {E : A} [IsArtinianObject (F.obj E)] :
    IsArtinianObject E := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  let g : ℕ →o (Subobject (F.obj E))ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual <|
        subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E) (f n),
      fun i j hij ↦ by
        change
          subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E) (f j) ≤
            subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E) (f i)
        exact subobjectImageOfFaithfulPreservesMono_monotone (A := A) (C := C) F (E := E)
          (f.2 hij)⟩
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject g
  exact ⟨n, fun m hm ↦
    subobjectImageOfFaithfulPreservesMono_injective (A := A) (C := C) F (E := E)
      (by simpa using hn m hm)⟩
/-- Noetherian objects transfer across full faithful functors that preserve monomorphisms. -/
theorem isNoetherianObject_of_faithful_preservesMono (F : A ⥤ C) [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] {E : A} [IsNoetherianObject (F.obj E)] :
    IsNoetherianObject E := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let g : ℕ →o Subobject (F.obj E) :=
    ⟨fun n ↦ subobjectImageOfFaithfulPreservesMono (A := A) (C := C) F (E := E) (f n),
      fun i j hij ↦
        subobjectImageOfFaithfulPreservesMono_monotone (A := A) (C := C) F (E := E)
          (f.2 hij)⟩
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject g
  exact ⟨n, fun m hm ↦
    subobjectImageOfFaithfulPreservesMono_injective (A := A) (C := C) F (E := E) (hn m hm)⟩
end SubobjectFiniteness
section StrictSubobjectTransfer
variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [Preadditive A]
  [HasKernels A] [HasCokernels A]
  {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [Preadditive C]
  [HasKernels C] [HasCokernels C]
private noncomputable def strictSubobjectImageOfFaithful (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} :
    StrictSubobject E → Subobject (F.obj E) :=
  fun B ↦ by
    let hstrict : IsStrictMono (F.map B.1.arrow) := hF B.1.arrow B.2
    letI : Mono (F.map B.1.arrow) := hstrict.mono
    exact Subobject.mk (F.map B.1.arrow)
omit [Preadditive A] [Preadditive C] in
private theorem strictSubobjectImageOfFaithful_monotone (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} :
    Monotone (strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E)) := by
  intro B₁ B₂ hB
  let hstrict₁ : IsStrictMono (F.map B₁.1.arrow) := hF B₁.1.arrow B₁.2
  let hstrict₂ : IsStrictMono (F.map B₂.1.arrow) := hF B₂.1.arrow B₂.2
  letI : Mono (F.map B₁.1.arrow) := hstrict₁.mono
  letI : Mono (F.map B₂.1.arrow) := hstrict₂.mono
  have hB' : B₁.1 ≤ B₂.1 := by simpa using hB
  have hmk : Subobject.mk B₁.1.arrow ≤ Subobject.mk B₂.1.arrow := by
    simpa [Subobject.mk_arrow] using hB'
  change
    Subobject.mk (F.map B₁.1.arrow) ≤ Subobject.mk (F.map B₂.1.arrow)
  exact Subobject.mk_le_mk_of_comm (F.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk)) (by
    rw [← F.map_comp]
    exact congrArg F.map (Subobject.ofMkLEMk_comp hmk))
omit [Preadditive A] [Preadditive C] in
private theorem strictSubobjectImageOfFaithful_injective (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} :
    Function.Injective (strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E)) := by
  intro B₁ B₂ hEq
  let hstrict₁ : IsStrictMono (F.map B₁.1.arrow) := hF B₁.1.arrow B₁.2
  let hstrict₂ : IsStrictMono (F.map B₂.1.arrow) := hF B₂.1.arrow B₂.2
  letI : Mono (F.map B₁.1.arrow) := hstrict₁.mono
  letI : Mono (F.map B₂.1.arrow) := hstrict₂.mono
  apply Subtype.ext
  have hEq' : Subobject.mk (F.map B₁.1.arrow) = Subobject.mk (F.map B₂.1.arrow) := hEq
  simpa [Subobject.mk_arrow] using
    (Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
      (F.preimageIso (Subobject.isoOfMkEqMk _ _ hEq'))
      (F.map_injective (by
        simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
        exact Subobject.ofMkLEMk_comp hEq'.le)))
section
omit [Preadditive A] [Preadditive C]
/-- Strict-Artinian objects transfer across full faithful functors that send strict
monomorphisms to strict monomorphisms. -/
theorem isStrictArtinianObject_of_faithful_map_strictMono (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} [IsArtinianObject (F.obj E)] :
    IsStrictArtinianObject E :=
    (show isStrictArtinianObject.Is E from
      ObjectProperty.is_of_prop _
        (show WellFoundedLT (StrictSubobject E) from by
          rw [← wellFoundedGT_dual_iff, wellFoundedGT_iff_monotone_chain_condition]
          intro f
          let g : ℕ →o (Subobject (F.obj E))ᵒᵈ :=
            ⟨fun n ↦ OrderDual.toDual <|
                strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E) (f n),
              fun i j hij ↦ by
                change
                  strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E) (f j) ≤
                    strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E) (f i)
                exact strictSubobjectImageOfFaithful_monotone (A := A) (C := C) F hF (E := E)
                  (f.2 hij)⟩
          obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject g
          exact ⟨n, fun m hm ↦
            strictSubobjectImageOfFaithful_injective (A := A) (C := C) F hF (E := E)
              (by simpa using hn m hm)⟩))
/-- Strict-Noetherian objects transfer across full faithful functors that send strict
monomorphisms to strict monomorphisms. -/
theorem isStrictNoetherianObject_of_faithful_map_strictMono (F : A ⥤ C) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
    {E : A} [IsNoetherianObject (F.obj E)] :
    IsStrictNoetherianObject E :=
    (show isStrictNoetherianObject.Is E from
      ObjectProperty.is_of_prop _
        (show WellFoundedGT (StrictSubobject E) from by
          rw [wellFoundedGT_iff_monotone_chain_condition]
          intro f
          let g : ℕ →o Subobject (F.obj E) :=
            ⟨fun n ↦ strictSubobjectImageOfFaithful (A := A) (C := C) F hF (E := E) (f n),
              fun i j hij ↦
                strictSubobjectImageOfFaithful_monotone (A := A) (C := C) F hF (E := E)
                  (f.2 hij)⟩
          obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject g
          exact ⟨n, fun m hm ↦
            strictSubobjectImageOfFaithful_injective (A := A) (C := C) F hF (E := E)
              (hn m hm)⟩))
end
end StrictSubobjectTransfer
end CategoryTheory


-- ═══ IntervalCategory.Basic ═══

/-!
# Interval Subcategories of Slicings

Given a slicing `s` on a pretriangulated category `C` and an open interval `(a, b) ⊂ ℝ`,
we define the interval subcategory `P((a, b))` as the full subcategory of `C` on objects
whose HN phases all lie in `(a, b)`.

These interval subcategories play a central role in Bridgeland's deformation theorem (§7):
when `b - a` is small enough (relative to the local finiteness parameter), objects in
`P((a,b))` have finite length in the quasi-abelian sense, i.e. well-founded chains of
strict subobjects and strict quotients, enabling HN filtration arguments within thin
subcategories.

## Main definitions

* `CategoryTheory.Triangulated.Slicing.IntervalCat`: the full subcategory `P((a, b))`
* `CategoryTheory.Triangulated.Slicing.intervalFiniteLength`: objects in thin intervals
  have well-founded subobject lattices

## Main results

* `CategoryTheory.Triangulated.Slicing.intervalHom_eq_zero`: hom-vanishing between
  objects in disjoint intervals
* `CategoryTheory.Triangulated.Slicing.intervalProp_of_semistable`: semistable objects
  with phase in `(a, b)` lie in `P((a, b))`

## References

* Bridgeland, "Stability conditions on triangulated categories", §4, §7
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace CategoryTheory.Triangulated
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
/-! ### Interval subcategory -/
/-- The interval subcategory `P((a, b))` of a slicing, defined as the full subcategory
on objects whose HN phases all lie in `(a, b)`. An object `E` belongs to `P((a, b))` if
it is zero or admits an HN filtration with all phases in `(a, b)`.

This is **Bridgeland's Definition 4.1** specialized to open intervals. -/
abbrev Slicing.IntervalCat (s : Slicing C) (a b : ℝ) :=
  (s.intervalProp C a b).FullSubcategory

-- ─── IntervalCategory.QuasiAbelian ───

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
noncomputable instance Slicing.intervalCat_hasKernels (s : Slicing C) :
    HasKernels (s.IntervalCat C a b)  := sorry
noncomputable instance Slicing.intervalCat_hasCokernels (s : Slicing C) :
    HasCokernels (s.IntervalCat C a b)  := sorry

-- ─── IntervalCategory.FiniteLength ───

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
omit [IsTriangulated C] in
/-- A slicing is locally finite if there exists `η > 0` with `η < 1/2` such that every
object in each thin interval category `P((t-η, t+η))` has finite length in the
quasi-abelian sense, i.e. ACC/DCC on strict subobjects.

The extra bound `η < 1/2` is a harmless normalization: any Bridgeland witness may be
shrunk to such an `η`, and then the width `2η` is at most `1`, so the thin interval
category carries the exact / quasi-abelian structure proved above. -/
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  intervalFinite : ∃ η : ℝ, ∃ hη : 0 < η, ∃ hη' : η < 1 / 2, ∀ t : ℝ,
    let a := t - η
    let b := t + η
    letI : Fact (a < b) := ⟨by
      dsimp [a, b]
      linarith⟩
    letI : Fact (b - a ≤ 1) := ⟨by
      dsimp [a, b]
      linarith⟩
    ∀ (E : s.IntervalCat C a b),
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E
/-- If a short complex in `P((a,b))` is short exact after embedding into both hearts,
then its left map is a strict monomorphism and its right map is a strict epimorphism
in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictMono_strictEpi_of_shortExact_toLeftRightHearts (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hL :
      (S.map (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1))).ShortExact)
    (hR :
      (S.map (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1))).ShortExact) :
    IsStrictMono S.f ∧ IsStrictEpi S.g := by
  let tL := (s.phaseShift C a).toTStructure
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := tL.heartFullSubcategoryAbelian
  letI : CategoryWithHomology tL.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := tL.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  letI : CategoryWithHomology tR.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := tR.heart.FullSubcategory)
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  letI : Mono (FR.map S.f) := hR.mono_f
  letI : Epi (FL.map S.g) := hL.epi_g
  have hf : IsStrictMono S.f :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) S.f
  have hg : IsStrictEpi S.g :=
    Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
      (C := C) (s := s) (a := a) (b := b) S.g
  exact ⟨hf, hg⟩
/-- A distinguished triangle in `C` whose three vertices lie in `P((a,b))`
forces the first map to be a strict monomorphism and the second to be a strict epimorphism
in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictMono_strictEpi_of_distTriang (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    {δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C) :
    IsStrictMono S.f ∧ IsStrictEpi S.g := by
  let tL := (s.phaseShift C a).toTStructure
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := tL.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιL := tL.ιHeart (H := tL.heart.FullSubcategory)
  have hTL :
      Triangle.mk (ιL.map ((S.map FL).f)) (ιL.map ((S.map FL).g)) δ ∈ distTriang C := by
    simpa [FL] using hT
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := by
    simpa using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι tL) ((S.map FL).f) ((S.map FL).g) δ hTL
  have hCokL :
      IsColimit (CokernelCofork.ofπ ((S.map FL).g) (S.map FL).zero) := by
    simpa using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι tL) ((S.map FL).f) ((S.map FL).g) δ hTL
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExactL : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKerL
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExactL (Fork.IsLimit.mono hKerL) (Cofork.IsColimit.epi hCokL)
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιR := tR.ιHeart (H := tR.heart.FullSubcategory)
  have hTR :
      Triangle.mk (ιR.map ((S.map FR).f)) (ιR.map ((S.map FR).g)) δ ∈ distTriang C := by
    simpa [FR] using hT
  have hKerR :
      IsLimit (KernelFork.ofι ((S.map FR).f) (S.map FR).zero) := by
    simpa using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι tR) ((S.map FR).f) ((S.map FR).g) δ hTR
  have hCokR :
      IsColimit (CokernelCofork.ofπ ((S.map FR).g) (S.map FR).zero) := by
    simpa using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι tR) ((S.map FR).f) ((S.map FR).g) δ hTR
  letI : (S.map FR).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FR))
  have hExactR : (S.map FR).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FR) hKerR
  have hR : (S.map FR).ShortExact :=
    ShortComplex.ShortExact.mk' hExactR (Fork.IsLimit.mono hKerR) (Cofork.IsColimit.epi hCokR)
  exact Slicing.IntervalCat.strictMono_strictEpi_of_shortExact_toLeftRightHearts
    (C := C) (s := s) (a := a) (b := b) hL hR
section
variable {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
omit [Fact (a < b)]
/-- A short exact sequence in the left heart `P((a,a+1])` with vertices in `P((a,b))`
extends to a distinguished triangle in `C`. -/
theorem Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart (s : Slicing C)
    {S : ShortComplex (s.IntervalCat C a b)}
    (hL :
      (S.map (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1))).ShortExact) :
    ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧), Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : IsNormalMonoCategory t.heart.FullSubcategory := Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory t.heart.FullSubcategory := Abelian.toIsNormalEpiCategory
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  letI : Balanced t.heart.FullSubcategory := by infer_instance
  letI : Epi ((S.map FL).g) := hL.epi_g
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) ((S.map FL).g)
  have hKer :
      IsLimit (KernelFork.ofι i (show i ≫ (S.map FL).g = 0 by
        exact ι.map_injective (comp_distTriang_mor_zero₁₂ _ hT))) :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i ((S.map FL).g) δ hT
  have hLfIsKernel : IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := hL.fIsKernel
  let eKA : K ≅ FL.obj S.X₁ := IsLimit.conePointUniqueUpToIso hKer hLfIsKernel
  refine ⟨δ ≫ ((shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)), ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (ι.mapIso eKA.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · simp only [Iso.refl_hom, Functor.mapIso_hom, Iso.symm_hom, Triangle.mk_mor₁]
    have hcomp : ι.map eKA.inv ≫ ι.map i = S.f.hom := by
      simpa [Functor.map_comp] using
        congrArg (fun k => ι.map k)
        (IsLimit.conePointUniqueUpToIso_inv_comp hKer hLfIsKernel
          Limits.WalkingParallelPair.zero)
    change S.f.hom ≫ 𝟙 S.X₂.obj = ι.map eKA.inv ≫ t.ιHeart.map i
    simpa [FL] using hcomp.symm
  · have hmap : t.ιHeart.map ((S.map FL).g) = S.g.hom := rfl
    simp only [Iso.refl_hom, Triangle.mk_mor₂, Triangle.mk_obj₂, Triangle.mk_obj₃]
    rw [hmap]
    convert (rfl : S.g.hom = S.g.hom) using 1
    · exact Category.comp_id S.g.hom
    · exact Category.id_comp S.g.hom
  · simp only [Iso.refl_hom, Triangle.mk_mor₃, Functor.mapIso_hom, Iso.symm_hom]
    change (δ ≫ (shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)) ≫
        (shiftFunctor C (1 : ℤ)).map (ι.map eKA.inv) = 𝟙 _ ≫ δ
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp, ← ι.map_comp, eKA.hom_inv_id,
      ι.map_id, Functor.map_id]
    simp
end
/-- A strict short exact sequence in `P((a,b))` extends to a distinguished triangle in `C`. -/
theorem Slicing.IntervalCat.exists_distTriang_of_strictShortExact (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hS : StrictShortExact S) :
    ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧), Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := t.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have := hS.shortExact.mono_f
  have := hS.shortExact.epi_g
  let h := hS.shortExact.exact.condition.choose
  let eHi : kernel S.g ≅ h.left.K :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.left.hi
  have heHi : eHi.inv ≫ kernel.ι S.g = h.left.i := by
    simpa [KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) h.left.hi
        Limits.WalkingParallelPair.zero
  haveI : Epi h.left.f' := hS.shortExact.exact.epi_f' h.left
  have hFRMono : Mono (FR.map h.left.f') := by
    haveI : Mono (FR.map S.f) :=
      Slicing.IntervalCat.mono_toRightHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) S.f
        ⟨inferInstance, hS.strict_f⟩
    have hFRComp : FR.map h.left.f' ≫ FR.map h.left.i = FR.map S.f := by
      calc
        FR.map h.left.f' ≫ FR.map h.left.i = FR.map (h.left.f' ≫ h.left.i) := by
          rw [← FR.map_comp]
        _ = FR.map S.f := by
          simp [h.left.f'_i]
    haveI : Mono (FR.map h.left.f' ≫ FR.map h.left.i) := by
      rw [hFRComp]
      infer_instance
    exact mono_of_mono (FR.map h.left.f') (FR.map h.left.i)
  have hf'Strict : IsStrictMono h.left.f' :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) h.left.f'
  haveI : IsIso h.left.f' := hf'Strict.isIso
  let eK : S.X₁ ≅ kernel S.g := asIso h.left.f' ≪≫ eHi.symm
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    refine kernel.isoKernel S.g S.f eK ?_
    calc
      eK.hom ≫ kernel.ι S.g = h.left.f' ≫ h.left.i := by
          simp [eK, heHi, Category.assoc]
      _ = S.f := h.left.f'_i
  have hEpi : Epi (FL.map S.g) := by
    letI : Epi (FL.map S.g) :=
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) S.g
        ⟨inferInstance, hS.strict_g⟩
    infer_instance
  have hKer :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  have hExact : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKer
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
  exact Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) hL
/-- A distinguished triangle in `C` whose three vertices lie in `P((a,b))`
defines a strict short exact sequence in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictShortExact_of_distTriang (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    {δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C) :
    StrictShortExact S := by
  let tL := (s.phaseShift C a).toTStructure
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := tL.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιL := tL.ιHeart (H := tL.heart.FullSubcategory)
  have hTL :
      Triangle.mk (ιL.map ((S.map FL).f)) (ιL.map ((S.map FL).g)) δ ∈ distTriang C := by
    simpa [FL] using hT
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := by
    simpa using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι tL) ((S.map FL).f) ((S.map FL).g) δ hTL
  have hKerMap :
      IsLimit (FL.mapCone (KernelFork.ofι S.f S.zero)) :=
    (isLimitMapConeForkEquiv' FL S.zero).symm hKerL
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimitOfReflects FL hKerMap
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιR := tR.ιHeart (H := tR.heart.FullSubcategory)
  have hTR :
      Triangle.mk (ιR.map ((S.map FR).f)) (ιR.map ((S.map FR).g)) δ ∈ distTriang C := by
    simpa [FR] using hT
  have hCokR :
      IsColimit (CokernelCofork.ofπ ((S.map FR).g) (S.map FR).zero) := by
    simpa using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι tR) ((S.map FR).f) ((S.map FR).g) δ hTR
  have hCokMap :
      IsColimit (FR.mapCocone (CokernelCofork.ofπ S.g S.zero)) :=
    (isColimitMapCoconeCoforkEquiv' FR S.zero).symm hCokR
  have hCok : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    isColimitOfReflects FR hCokMap
  obtain ⟨hf, hg⟩ := Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
    (C := C) (s := s) (a := a) (b := b) hT
  let eK' : kernel S.g ≅ S.X₁ :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hKer
  let eK : S.X₁ ≅ kernel S.g := eK'.symm
  have heK : eK.hom ≫ kernel.ι S.g = S.f := by
    simpa [KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) hKer
        Limits.WalkingParallelPair.zero
  have hLift : kernel.lift S.g S.f S.zero = eK.hom := by
    apply (cancel_mono (kernel.ι S.g)).1
    rw [heK]
    exact kernel.lift_ι S.g S.f S.zero
  have hKernelComp : kernel.ι S.g ≫ cokernel.π S.f = 0 := by
    have hιEq : kernel.ι S.g = eK.inv ≫ S.f := by
      apply (cancel_epi eK.hom).1
      simp [heK]
    rw [hιEq, Category.assoc, cokernel.condition]
    simp
  let eQ : cokernel S.f ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hCok
  have heQ : cokernel.π S.f ≫ eQ.hom = S.g := by
    simpa [CokernelCofork.ofπ] using
      IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel S.f) hCok
        Limits.WalkingParallelPair.one
  have hDesc : cokernel.desc S.f S.g S.zero = eQ.hom := by
    apply (cancel_epi (cokernel.π S.f)).1
    rw [heQ]
    exact cokernel.π_desc S.f S.g S.zero
  let hLeft : S.LeftHomologyData := ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S
  let hRight : S.RightHomologyData := ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel S
  have hLeftZero : IsZero hLeft.H := by
    haveI : IsIso (kernel.lift S.g S.f S.zero) := by rw [hLift]; infer_instance
    haveI : Epi (kernel.lift S.g S.f S.zero) := by infer_instance
    dsimp [hLeft]
    simpa [hLift] using isZero_cokernel_of_epi (kernel.lift S.g S.f S.zero)
  have hRightZero : IsZero hRight.H := by
    haveI : IsIso (cokernel.desc S.f S.g S.zero) := by rw [hDesc]; infer_instance
    haveI : Mono (cokernel.desc S.f S.g S.zero) := by infer_instance
    dsimp [hRight]
    simpa [hDesc] using isZero_kernel_of_mono (cokernel.desc S.f S.g S.zero)
  have hComp : hLeft.i ≫ hRight.p = 0 := by
    dsimp [hLeft, hRight]
    exact hKernelComp
  have hExact : S.Exact := by
    let hData : S.HomologyData :=
      { left := hLeft
        right := hRight
        iso := IsZero.iso hLeftZero hRightZero
        comm := by
          have hπZero : hLeft.π = 0 := hLeftZero.eq_of_tgt _ _
          simpa [hπZero, Category.assoc] using hComp.symm }
    exact ⟨⟨hData, hLeftZero⟩⟩
  have hShortExact : S.ShortExact :=
    ShortComplex.ShortExact.mk' hExact hf.mono hg.epi
  refine
    { shortExact := hShortExact
      strict_f := hf.strict
      strict_g := hg.strict }
/-- A strict short exact sequence in a smaller interval remains strict in any larger thin
interval containing it. This is the inclusion-case transport used in the deformation
theorem's interval-independence step. -/
theorem Slicing.IntervalCat.strictShortExact_inclusion (s : Slicing C)
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)] [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂)
    {S : ShortComplex (s.IntervalCat C a₁ b₁)} (hS : StrictShortExact S) :
    StrictShortExact (S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)) := by
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := s) (a := a₁) (b := b₁) hS
  have hT' :
      Triangle.mk ((S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)).f.hom)
        ((S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)).g.hom)
          δ ∈ distTriang C := by
    simpa [Slicing.IntervalCat.inclusion] using hT
  exact Slicing.IntervalCat.strictShortExact_of_distTriang
    (C := C) (s := s) (a := a₂) (b := b₂) hT'
/-- Strict short exact sequences in `P((a,b))` are exactly the distinguished triangles
in `C` whose three vertices lie in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictShortExact_iff_exists_distTriang (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)} :
    StrictShortExact S ↔
      ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧), Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  constructor
  · exact Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := s) (a := a) (b := b)
  · rintro ⟨δ, hT⟩
    exact Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := s) (a := a) (b := b) hT
/-- A strict short exact sequence in `P((a,b))` yields the expected `K₀` relation
in the ambient triangulated category. -/
theorem Slicing.IntervalCat.K0_of_strictShortExact (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hS : StrictShortExact S) :
    K₀.of C S.X₂.obj = K₀.of C S.X₁.obj + K₀.of C S.X₃.obj := by
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := s) (a := a) (b := b) hS
  simpa using K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT
/-- Append a semistable strict quotient in `P((a,b))` to an HN filtration of the
kernel. This packages `appendFactor` with the strict short exact sequence to triangle
bridge for interval categories. -/
noncomputable def HNFiltration.appendStrictFactor {P : ℝ → ObjectProperty C}
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {S : ShortComplex (s.IntervalCat C a b)}
    (G : HNFiltration C P S.X₁.obj)
    (hS : StrictShortExact S) (ψ : ℝ) (hψ : P ψ S.X₃.obj)
    (hψ_lt : ∀ j : Fin G.n, ψ < G.φ j) :
    HNFiltration C P S.X₂.obj := by
  let hδ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := s) (a := a) (b := b) hS
  let δ := Classical.choose hδ
  have hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := Classical.choose_spec hδ
  exact G.appendFactor C (Triangle.mk S.f.hom S.g.hom δ) hT
    (Iso.refl _) (Iso.refl _) ψ hψ hψ_lt
end Preabelian
/-! ### Skewed stability functions (Definition 4.4) -/
/-- A *skewed stability function* on a thin subcategory `P((a, b))` with `b - a ≤ 1`.
This is a group homomorphism `W : Λ →+ ℂ` (the charge on the target lattice) together
with a class map `v : K₀ C →+ Λ` and a real parameter `α ∈ (a, b)`, such that for
every nonzero semistable object `E` of phase `φ ∈ (a, b)`, `W(v[E]) ≠ 0`.

In the deformation theorem, `W` is a perturbation of the central charge `Z : Λ → ℂ`
of a stability condition `(Z, P)` on `D` with respect to `Λ`, and `α` is chosen so
that `W`-phases are well-defined in `(α - 1/2, α + 1/2)` for objects in `P((a, b))`. -/
structure SkewedStabilityFunction {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)
    (s : Slicing C) (a b : ℝ) where
  /-- The group homomorphism (typically a perturbation of the central charge). -/
  W : Λ →+ ℂ
  /-- The skewing parameter, lying in the interval `(a, b)`. -/
  α : ℝ
  /-- The skewing parameter lies in the interval. -/
  hα_mem : a < α ∧ α < b
  /-- For every nonzero semistable object of phase `φ ∈ (a, b)`, the central charge
  `W(v[E])` is nonzero. -/
  nonzero : ∀ (E : C) (φ : ℝ), a < φ → φ < b →
    (s.P φ) E → ¬IsZero E → W (cl C v E) ≠ 0
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}
variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
/-- The central charge of a `SkewedStabilityFunction` is additive on strict short exact
sequences in the thin interval category. -/
theorem SkewedStabilityFunction.strict_additive {s : Slicing C}
    (ssf : SkewedStabilityFunction C v s a b)
    {S : ShortComplex (s.IntervalCat C a b)} (hS : StrictShortExact S) :
    ssf.W (cl C v S.X₂.obj) = ssf.W (cl C v S.X₁.obj) + ssf.W (cl C v S.X₃.obj) := by
  simp only [cl, Slicing.IntervalCat.K0_of_strictShortExact (C := C) (s := s) (a := a) (b := b) hS,
    map_add]
end CategoryTheory.Triangulated


-- ═══ StabilityCondition.Defs ═══

/-!
# Stability Condition Definitions

Core data-carrying declarations for Bridgeland stability conditions: the
`PreStabilityCondition.WithClassMap` and `StabilityCondition.WithClassMap` structures,
the generalized metric `slicingDist`, the seminorm `stabSeminorm`, basis neighborhoods,
the Bridgeland topology, and connected-component types.

These definitions are separated from the proof files so that downstream modules
(Euler form, numerical stability, manifold structure) can import type-level dependencies
without pulling in phase rigidity proofs and sector-bound lemmas.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ENNReal
namespace CategoryTheory.Triangulated
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]
/-! ### Prestability and stability conditions -/
namespace PreStabilityCondition
/-- A Bridgeland prestability condition with respect to a class map
`v : K₀(C) → Λ`. The central charge lives on `Λ`, and the ordinary ambient
charge is recovered by precomposition with `v`. -/
structure WithClassMap (v : K₀ C →+ Λ) where
  /-- The underlying slicing. -/
  slicing : Slicing C
  /-- The central charge on the class lattice `Λ`. -/
  Z : Λ →+ ℂ
  /-- Compatibility (raw). Use `σ.compat` instead. -/
  compat' : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)
omit [IsTriangulated C] in
variable {C} in
/-- The central charge evaluated at the class of `E`. This is `Z(v[E])`. -/
noncomputable abbrev WithClassMap.charge {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) (E : C) : ℂ :=
  σ.Z (cl C v E)
end PreStabilityCondition
namespace StabilityCondition
/-- A Bridgeland stability condition with respect to a class map `v : K₀(C) → Λ`.
This is the locally-finite refinement of `PreStabilityCondition.WithClassMap`. -/
structure WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  /-- The slicing is locally finite. -/
  locallyFinite : slicing.IsLocallyFinite C
end StabilityCondition
open Real in
/-- The Bridgeland generalized metric on slicings. For slicings `s₁` and `s₂`,
this is the supremum over all nonzero objects `E` of
`max(|φ₁⁺(E) - φ₂⁺(E)|, |φ₁⁻(E) - φ₂⁻(E)|)`. -/
def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)
/-- The Bridgeland seminorm `‖U‖_σ` on `Hom(Λ, ℂ)`. For a class-map stability
condition `σ = (Z, P)` with class map `v : K₀(D) → Λ` and a group homomorphism
`U : Λ → ℂ`, this is `sup { |U(v[E])| / |Z(v[E])| : E is σ-semistable and nonzero }`.

When `v = id` (i.e., `Λ = K₀(D)`), this recovers Bridgeland's original seminorm. -/
def stabSeminorm {v : K₀ C →+ Λ} (σ : StabilityCondition.WithClassMap C v)
    (U : Λ →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (cl C v E)‖ / ‖σ.charge E‖)
/-- The basis neighborhood `B_ε(σ)` for the Bridgeland topology on `Stab_v(D)`. -/
def basisNhd {v : K₀ C →+ Λ} (σ : StabilityCondition.WithClassMap C v) (ε : ℝ) :
    Set (StabilityCondition.WithClassMap C v) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}
/-- The Bridgeland topology on `Stab_v(D)`, generated by the basis neighborhoods
`B_ε(σ)` for all stability conditions `σ` and all `ε ∈ (0, 1/8)`.

This is the BLMNPS topology: the coarsest making both the charge map `σ ↦ σ.Z`
and the slicing map continuous. When `v = id`, this recovers Bridgeland's original
topology on `Stab(D)`. -/
instance StabilityCondition.WithClassMap.topologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  TopologicalSpace.generateFrom
    {U | ∃ (σ : StabilityCondition.WithClassMap C v) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧
      U = basisNhd C σ ε}
namespace StabilityCondition.WithClassMap
/-- The connected-component index set for `Stab_v(D)`. -/
abbrev ComponentIndex (v : K₀ C →+ Λ) :=
  _root_.ConnectedComponents (StabilityCondition.WithClassMap C v)
/-- The type of `v`-relative stability conditions in a fixed connected component. -/
abbrev Component (v : K₀ C →+ Λ) (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :=
  {σ : StabilityCondition.WithClassMap C v // _root_.ConnectedComponents.mk σ = cc}
/-- The local-homeomorphism package for connected components of `Stab_v(D)`, stated directly in
terms of the class-map charge `Z : Λ →+ ℂ`. Specializing to `v = id` recovers Bridgeland's
Theorem 1.2 proposition-object; specializing to the numerical quotient recovers Corollary 1.3. -/
def CentralChargeIsLocalHomeomorphOnConnectedComponents {v : K₀ C →+ Λ} : Prop :=
  ∀ (cc : StabilityCondition.WithClassMap.ComponentIndex C v),
    ∃ (V : Submodule ℂ (Λ →+ ℂ))
      (_ : NormedAddCommGroup V)
      (_ : NormedSpace ℂ V)
      (hZ : ∀ σ : StabilityCondition.WithClassMap C v,
        ConnectedComponents.mk σ = cc → σ.Z ∈ V),
      @IsLocalHomeomorph
        (StabilityCondition.WithClassMap.Component C v cc)
        V inferInstance inferInstance
        (fun ⟨σ, hσ⟩ ↦ ⟨σ.Z, hZ σ hσ⟩)
end StabilityCondition.WithClassMap
end CategoryTheory.Triangulated


-- ═══ NumericalStability.Defs ═══

/-!
# Finite Type and Object-Level Euler Form

The `IsFiniteType` class and `eulerFormObj` definition, separated from the
comparison tools so that downstream Defs modules can import lightweight
type-level dependencies without pulling in continuity and equivalence proofs.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory.Triangulated
variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
/-! ### Finite type -/
/-- A `k`-linear pretriangulated category is of finite type if all Hom spaces are
finite-dimensional over `k` and for each pair of objects, only finitely many shifted
Hom spaces are nonzero. -/
class IsFiniteType [Linear k C] : Prop where
  /-- Each Hom space `Hom(E, F)` is finite-dimensional over `k`. -/
  finite_dim : ∀ (E F : C), Module.Finite k (E ⟶ F)
  /-- For each pair of objects, only finitely many shifted Hom spaces are nontrivial. -/
  finite_support : ∀ (E F : C), Set.Finite {n : ℤ | Nontrivial (E ⟶ (shiftFunctor C n).obj F)}
/-- The Euler form on objects: `χ(E,F) = Σₙ (-1)ⁿ dim_k Hom(E, F[n])`.
This is defined as a finitely-supported sum using `finsum`. -/
def eulerFormObj [Linear k C] (E F : C) : ℤ :=
  ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ (shiftFunctor C n).obj F) : ℤ)
end CategoryTheory.Triangulated


-- ═══ EulerForm.Basic ═══

/-!
# Euler form on `K₀`

We prove that the Euler form `χ(E,F) = Σₙ (-1)ⁿ dim_k Hom(E, F[n])` is
triangle-additive in both arguments, then lift it to a bilinear form on `K₀`.

The proof uses the long exact Hom sequence from the homological Yoneda functor
and the rank-nullity theorem for finite-dimensional vector spaces.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite
namespace CategoryTheory.Triangulated
variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [Linear k C] [IsFiniteType k C]
lemma finrank_mid_of_exact {K M N : Type v} [AddCommGroup K] [Module k K]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [Module.Finite k M]
    (f : K →ₗ[k] M) (g : M →ₗ[k] N) (hfg : LinearMap.range f = LinearMap.ker g) :
    (Module.finrank k M : ℤ) = Module.finrank k (LinearMap.range f) +
      Module.finrank k (LinearMap.range g) := by
  have h := g.finrank_range_add_finrank_ker
  rw [← hfg] at h
  lia
lemma finsum_alternating_shift_cancel {r : ℤ → ℤ} :
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * r (n - 1) +
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * r n = 0 := by
  -- Shift the first sum: n ↦ n-1 becomes m ↦ m+1
  have h_shift : ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * r (n - 1) =
      ∑ᶠ m : ℤ, ((m + 1).negOnePow : ℤ) * r m := by
    show ∑ᶠ n : ℤ, (((n : ℤ).negOnePow : ℤ) * r (n - 1)) =
        ∑ᶠ m : ℤ, (((m + 1 : ℤ).negOnePow : ℤ) * r m)
    have : (fun n : ℤ ↦ ((n : ℤ).negOnePow : ℤ) * r (n - 1)) =
        fun n : ℤ ↦ (((Equiv.subRight (1 : ℤ) n + 1 : ℤ).negOnePow : ℤ) *
          r (Equiv.subRight (1 : ℤ) n)) := by
      ext n; simp [Equiv.subRight, sub_add_cancel]
    rw [this]
    exact @finsum_comp_equiv ℤ ℤ ℤ _ (Equiv.subRight 1)
      (f := fun m ↦ ((m + 1 : ℤ).negOnePow : ℤ) * r m)
  rw [h_shift]
  -- (-1)^(m+1) = -(-1)^m
  simp_rw [Int.negOnePow_succ, Units.val_neg, neg_mul]
  -- Now: Σ -(-1)^m r(m) + Σ (-1)^n r(n) = 0
  rw [finsum_neg_distrib]
  linarith
omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsFiniteType k C] in
lemma eulerSum_of_rank_identity
    (E : C) {a b c : ℤ → C} {r : ℤ → ℤ}
    (hrank : ∀ n : ℤ, (Module.finrank k (E ⟶ b n) : ℤ) =
      Module.finrank k (E ⟶ a n) + Module.finrank k (E ⟶ c n) - r (n - 1) - r n)
    (hfin_a : Set.Finite {n : ℤ | Nontrivial (E ⟶ a n)})
    (hfin_b : Set.Finite {n : ℤ | Nontrivial (E ⟶ b n)})
    (hfin_c : Set.Finite {n : ℤ | Nontrivial (E ⟶ c n)})
    (hr : (Function.support r).Finite) :
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * Module.finrank k (E ⟶ b n)) =
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * Module.finrank k (E ⟶ a n)) +
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * Module.finrank k (E ⟶ c n)) := by
  let fa : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * Module.finrank k (E ⟶ a n)
  let fb : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * Module.finrank k (E ⟶ b n)
  let fc : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * Module.finrank k (E ⟶ c n)
  let fr : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * (-r (n - 1) - r n)
  have hfa : (Function.support fa).Finite := by
    refine Set.Finite.subset hfin_a ?_
    intro n hn
    have hfinrank_ne : (Module.finrank k (E ⟶ a n) : ℤ) ≠ 0 := by
      intro h0
      apply hn
      simp [fa, h0]
    letI : Nontrivial (E ⟶ a n) :=
      Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero (by exact_mod_cast hfinrank_ne))
    show Nontrivial (E ⟶ a n)
    infer_instance
  have hfb : (Function.support fb).Finite := by
    refine Set.Finite.subset hfin_b ?_
    intro n hn
    have hfinrank_ne : (Module.finrank k (E ⟶ b n) : ℤ) ≠ 0 := by
      intro h0
      apply hn
      simp [fb, h0]
    letI : Nontrivial (E ⟶ b n) :=
      Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero (by exact_mod_cast hfinrank_ne))
    show Nontrivial (E ⟶ b n)
    infer_instance
  have hfc : (Function.support fc).Finite := by
    refine Set.Finite.subset hfin_c ?_
    intro n hn
    have hfinrank_ne : (Module.finrank k (E ⟶ c n) : ℤ) ≠ 0 := by
      intro h0
      apply hn
      simp [fc, h0]
    letI : Nontrivial (E ⟶ c n) :=
      Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero (by exact_mod_cast hfinrank_ne))
    show Nontrivial (E ⟶ c n)
    infer_instance
  -- Rewrite b(n) using hrank: b(n) = a(n) + c(n) - r(n-1) - r(n)
  have key : ∀ n, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ b n) : ℤ) =
      (n.negOnePow : ℤ) * Module.finrank k (E ⟶ a n) +
      (n.negOnePow : ℤ) * Module.finrank k (E ⟶ c n) +
      (n.negOnePow : ℤ) * (-r (n - 1) - r n) := fun n ↦ by rw [hrank]; ring
  simp_rw [key]
  -- Goal: Σ (x + y + z) = Σ x + Σ y where z cancels
  -- Suffices: Σ z = 0
  suffices hz : ∑ᶠ n : ℤ, fr n = 0 by
    have hfac : (Function.support (fun n : ℤ ↦ fa n + fc n)).Finite :=
      Set.Finite.subset (hfa.union hfc) (Function.support_add _ _)
    have hr_shift : (Function.support fun n : ℤ ↦ r (n - 1)).Finite := by
      refine Set.Finite.subset (hr.image fun m : ℤ ↦ m + 1) ?_
      intro n hn
      refine ⟨n - 1, hn, by simp⟩
    have hfr : (Function.support fr).Finite := by
      refine Set.Finite.subset (hr_shift.union hr) ?_
      intro n hn
      by_cases h1 : r (n - 1) = 0
      · by_cases h2 : r n = 0
        · exfalso
          apply hn
          simp [fr, h1, h2]
        · exact Or.inr h2
      · exact Or.inl h1
    let lhs : ℤ := finsum (fun n : ℤ ↦ (fa n + fc n) + fr n)
    let rhs : ℤ := finsum fa + finsum fc
    have hsum := by
      show lhs = rhs
      dsimp [lhs, rhs]
      rw [finsum_add_distrib hfac]
      · rw [finsum_add_distrib hfa hfc, hz]
        simp
      · exact hfr
    simpa [fa, fc, fr, lhs, rhs]
  -- Expand: (-1)^n * (-r(n-1) - r(n)) = -((-1)^n * r(n-1)) - ((-1)^n * r(n))
  change ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (-r (n - 1) - r n) = 0
  simp_rw [show ∀ n : ℤ, (n.negOnePow : ℤ) * (-r (n - 1) - r n) =
      -(((n : ℤ).negOnePow : ℤ) * r (n - 1)) - ((n : ℤ).negOnePow : ℤ) * r n from
    fun n ↦ by ring]
  -- = -Σ (-1)^n r(n-1) - Σ (-1)^n r(n) by finsum_neg + finsum_sub
  rw [show (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r (n - 1)) -
      ((n : ℤ).negOnePow : ℤ) * r n) =
    fun n : ℤ ↦ (-(((n : ℤ).negOnePow : ℤ) * r (n - 1)) +
      (-(((n : ℤ).negOnePow : ℤ) * r n))) from by ext; ring]
  have hr_shift : (Function.support (fun n : ℤ ↦ r (n - 1))).Finite := by
    refine Set.Finite.subset (hr.image fun m : ℤ ↦ m + 1) ?_
    intro n hn
    refine ⟨n - 1, hn, by simp⟩
  have hfs1 : (Function.support (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r (n - 1)))).Finite := by
    apply hr_shift.subset; intro n hn
    simp only [Function.mem_support, neg_ne_zero, mul_ne_zero_iff] at hn
    exact hn.2
  have hfs2 : (Function.support (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r n))).Finite := by
    apply hr.subset; intro n hn
    simp only [Function.mem_support, neg_ne_zero, mul_ne_zero_iff] at hn
    exact hn.2
  rw [finsum_add_distrib hfs1 hfs2]
  simp only [finsum_neg_distrib]
  linarith [finsum_alternating_shift_cancel (r := r)]
lemma eulerSum_of_rank_identity_int {a b c r : ℤ → ℤ}
    (hrank : ∀ n : ℤ, b n = a n + c n - r (n - 1) - r n)
    (hfa : (Function.support a).Finite)
    (hfc : (Function.support c).Finite)
    (hr : (Function.support r).Finite) :
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * b n) =
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * a n) +
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * c n) := by
  let fa : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * a n
  let fc : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * c n
  let fr : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * (-r (n - 1) - r n)
  have hfa' : (Function.support fa).Finite := by
    refine Set.Finite.subset hfa ?_
    intro n hn
    simp [Function.mem_support, fa] at hn ⊢
    intro ha
    exact hn (by simp [ha])
  have hfc' : (Function.support fc).Finite := by
    refine Set.Finite.subset hfc ?_
    intro n hn
    simp [Function.mem_support, fc] at hn ⊢
    intro hc
    exact hn (by simp [hc])
  have key : ∀ n, (n.negOnePow : ℤ) * b n =
      (n.negOnePow : ℤ) * a n +
      (n.negOnePow : ℤ) * c n +
      (n.negOnePow : ℤ) * (-r (n - 1) - r n) := fun n ↦ by
    rw [hrank]
    ring
  simp_rw [key]
  suffices hz : ∑ᶠ n : ℤ, fr n = 0 by
    have hfac : (Function.support (fun n : ℤ ↦ fa n + fc n)).Finite :=
      Set.Finite.subset (hfa'.union hfc') (Function.support_add _ _)
    have hr_shift : (Function.support fun n : ℤ ↦ r (n - 1)).Finite := by
      refine Set.Finite.subset (hr.image fun m : ℤ ↦ m + 1) ?_
      intro n hn
      refine ⟨n - 1, hn, by simp⟩
    have hfr : (Function.support fr).Finite := by
      refine Set.Finite.subset (hr_shift.union hr) ?_
      intro n hn
      by_cases h1 : r (n - 1) = 0
      · by_cases h2 : r n = 0
        · exfalso
          apply hn
          simp [fr, h1, h2]
        · exact Or.inr h2
      · exact Or.inl h1
    let lhs : ℤ := finsum (fun n : ℤ ↦ (fa n + fc n) + fr n)
    let rhs : ℤ := finsum fa + finsum fc
    have hsum : lhs = rhs := by
      dsimp [lhs, rhs]
      rw [finsum_add_distrib hfac]
      · rw [finsum_add_distrib hfa' hfc', hz]
        simp
      · exact hfr
    simpa [fa, fc, fr, lhs, rhs]
  change ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (-r (n - 1) - r n) = 0
  simp_rw [show ∀ n : ℤ, (n.negOnePow : ℤ) * (-r (n - 1) - r n) =
      -(((n : ℤ).negOnePow : ℤ) * r (n - 1)) - ((n : ℤ).negOnePow : ℤ) * r n from
    fun n ↦ by ring]
  have hr_shift : (Function.support (fun n : ℤ ↦ r (n - 1))).Finite := by
    refine Set.Finite.subset (hr.image fun m : ℤ ↦ m + 1) ?_
    intro n hn
    refine ⟨n - 1, hn, by simp⟩
  have hfs1 : (Function.support (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r (n - 1)))).Finite := by
    apply hr_shift.subset
    intro n hn
    simp only [Function.mem_support, neg_ne_zero, mul_ne_zero_iff] at hn
    exact hn.2
  have hfs2 : (Function.support (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r n))).Finite := by
    apply hr.subset
    intro n hn
    simp only [Function.mem_support, neg_ne_zero, mul_ne_zero_iff] at hn
    exact hn.2
  rw [show (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r (n - 1)) -
      ((n : ℤ).negOnePow : ℤ) * r n) =
    fun n : ℤ ↦ (-(((n : ℤ).negOnePow : ℤ) * r (n - 1)) +
      (-(((n : ℤ).negOnePow : ℤ) * r n))) from by
    ext
    ring]
  rw [finsum_add_distrib hfs1 hfs2]
  simp only [finsum_neg_distrib]
  linarith [finsum_alternating_shift_cancel (r := r)]
omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsFiniteType k C] in
lemma linearRange_eq_linearKer_of_ab_exact {A B C' : C} (E : C)
    (f : A ⟶ B) (g : B ⟶ C') (hfg : f ≫ g = 0)
    (hexact : ∀ (x : E ⟶ B), x ≫ g = 0 → ∃ y : E ⟶ A, y ≫ f = x) :
    LinearMap.range (Linear.rightComp k E f) = LinearMap.ker (Linear.rightComp k E g) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Linear.rightComp_apply]
  constructor
  · rintro ⟨y, rfl⟩; rw [Category.assoc, hfg, comp_zero]
  · intro hx; exact hexact x hx
lemma linearMap_range_eq_ker_of_addMonoidHom {V W X : Type v}
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    [AddCommGroup X] [Module k X]
    (f : V →ₗ[k] W) (g : W →ₗ[k] X)
    (h : f.toAddMonoidHom.range = g.toAddMonoidHom.ker) :
    LinearMap.range f = LinearMap.ker g := by
  ext x
  change x ∈ f.toAddMonoidHom.range ↔ x ∈ g.toAddMonoidHom.ker
  rw [h]
noncomputable instance linearCoyonedaObjIsHomological (E : C) :
    (((linearCoyoneda k C).obj (Opposite.op E)) : C ⥤ ModuleCat k).IsHomological where
  exact T hT := by
    rw [ShortComplex.exact_iff_exact_map_forget₂]
    simpa using ((preadditiveCoyoneda.obj (Opposite.op E)).map_distinguished_exact T hT)
section EulerTriangleAdditivity
omit [IsTriangulated C]
theorem eulerFormObj_contravariant_triangleAdditive (E : C) :
    IsTriangleAdditive (fun F ↦ eulerFormObj k C E F)  := sorry
end EulerTriangleAdditivity
/-- For fixed `E`, lift `F ↦ χ(E, F)` to a group homomorphism `K₀ C →+ ℤ`
using the universal property of `K₀`. -/
def eulerFormInner (E : C) : K₀ C →+ ℤ := by
  letI := eulerFormObj_contravariant_triangleAdditive (k := k) (C := C) E
  exact K₀.lift C (fun F ↦ eulerFormObj k C E F)
/-- The outer function `E ↦ eulerFormInner E` is triangle-additive, so the Euler
form descends to a bilinear form on `K₀`. -/
instance eulerFormInner_isTriangleAdditive
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    IsTriangleAdditive (eulerFormInner k C)  := sorry
/-- The Euler form on `K₀`, obtained by applying the universal property of `K₀`
twice to `eulerFormObj`. -/
def eulerForm [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ K₀ C →+ ℤ :=
  K₀.lift C (eulerFormInner k C)
/-- The left radical of the Euler form on `K₀ C`. -/
def eulerFormRad [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddSubgroup (K₀ C) :=
  (eulerForm k C).ker
/-- The numerical Grothendieck group attached to the Euler form on `K₀`. -/
def NumericalK₀ [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k] :
    Type _ :=
  K₀ C ⧸ eulerFormRad k C
/-- The `AddCommGroup` instance on `NumericalK₀ k C`. -/
instance NumericalK₀.instAddCommGroup [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddCommGroup (NumericalK₀ k C) :=
  inferInstanceAs (AddCommGroup (K₀ C ⧸ eulerFormRad k C))
/-- The quotient map `K₀(C) → N(C)`. -/
abbrev numericalQuotientMap [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ NumericalK₀ k C :=
  QuotientAddGroup.mk' (eulerFormRad k C)
/-- The category `C` is numerically finite if the numerical Grothendieck group attached to the
Euler form is finitely generated as an abelian group. -/
class NumericallyFinite [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] : Prop where
  /-- The Euler-form numerical Grothendieck group is finitely generated. -/
  fg : AddGroup.FG (NumericalK₀ k C)
/-- A connected component of numerical stability conditions. -/
abbrev NumericalComponent [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :=
  StabilityCondition.WithClassMap.Component C (numericalQuotientMap k C) cc
end CategoryTheory.Triangulated


-- ═══ NumericalStabilityManifold ═══

/-!
# Numerical Stability Manifolds

Bridgeland's Corollary 1.3: each connected component of `Stab_Λ(D)` is a
complex manifold of dimension `rk(Λ)`.

The proof is direct assembly from the generalized `ComponentTopologicalLinearLocalModel`:
1. `V(Σ) ⊆ Hom(Λ, ℂ)` is finite-dimensional (because `Λ` has finite rank).
2. The charge map `σ ↦ σ.Z` is a local homeomorphism into `V(Σ)`.
3. Apply the generic manifold construction.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped Manifold Topology
namespace CategoryTheory.Triangulated
/-! ### Finite-dimensionality of `Hom(Λ, ℂ)` -/
section
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
/-- A finite-rank class lattice has finite-dimensional complex charge space. -/
theorem classMapChargeSpace_finiteDimensional (Λ : Type u') [AddCommGroup Λ] [AddGroup.FG Λ] :
    FiniteDimensional ℂ (Λ →+ ℂ) := by
  let A := Λ
  have hfg : AddGroup.FG A := inferInstance
  have htopfg : (⊤ : AddSubgroup A).FG := (AddGroup.fg_def).mp hfg
  rcases (AddSubgroup.fg_iff_exists_fin_addMonoidHom (H := (⊤ : AddSubgroup A))).mp htopfg with
    ⟨n, g, hg_range⟩
  have hg : Function.Surjective g := by
    intro x
    have hx : x ∈ AddMonoidHom.range g := by
      rw [hg_range]
      simp
    rcases hx with ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  let precomp : (Λ →+ ℂ) →ₗ[ℂ] ((Fin n → ℤ) →+ ℂ) := {
    toFun := fun Z => Z.comp g
    map_add' := by
      intro Z₁ Z₂
      ext x
      rfl
    map_smul' := by
      intro a Z
      ext x
      rfl }
  have hprecomp : Function.Injective precomp := by
    intro Z₁ Z₂ hZ
    ext x
    obtain ⟨y, rfl⟩ := hg x
    exact DFunLike.congr_fun hZ y
  let eval : ((Fin n → ℤ) →+ ℂ) →ₗ[ℂ] (Fin n → ℂ) := {
    toFun := fun Z i => Z (Pi.single i 1)
    map_add' := by
      intro Z₁ Z₂
      ext i
      rfl
    map_smul' := by
      intro a Z
      ext i
      rfl }
  have heval : Function.Injective eval := by
    intro Z₁ Z₂ hZ
    apply AddMonoidHom.toIntLinearMap_injective
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro i
    simpa [eval, Pi.basisFun_apply] using congr_fun hZ i
  exact FiniteDimensional.of_injective (eval ∘ₗ precomp) (heval.comp hprecomp)
end
/-! ### Generic manifold construction -/
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
/-- A generic manifold-construction theorem for complex local homeomorphisms into a normed model
space. The genuinely nontrivial step is to build a charted space whose transition maps are
restrictions of the identity. -/
theorem exists_chartedSpace_and_hasGroupoid_idRestr_of_isLocalHomeomorph_to_complex_model
    {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    (f : M → E) (hf : IsLocalHomeomorph f) :
    ∃ _ : ChartedSpace E M, HasGroupoid M (@idRestrGroupoid E _) := by
  classical
  let chartAt : M → OpenPartialHomeomorph M E := fun x => Classical.choose (hf x)
  have mem_chart_source : ∀ x : M, x ∈ (chartAt x).source := fun x =>
    (Classical.choose_spec (hf x)).1
  have chartAt_eq : ∀ x : M, f = chartAt x := fun x =>
    (Classical.choose_spec (hf x)).2
  let charted : ChartedSpace E M := {
    atlas := Set.range chartAt
    chartAt := chartAt
    mem_chart_source := mem_chart_source
    chart_mem_atlas x := ⟨x, rfl⟩ }
  letI : ChartedSpace E M := charted
  refine ⟨charted, ?_⟩
  constructor
  intro e e' he he'
  rcases he with ⟨x, rfl⟩
  rcases he' with ⟨y, rfl⟩
  let g : OpenPartialHomeomorph E E := (chartAt x).symm ≫ₕ chartAt y
  have hchart_eq : (chartAt y : M → E) = chartAt x :=
    (chartAt_eq y).symm.trans (chartAt_eq x)
  have hg :
      g ≈ OpenPartialHomeomorph.ofSet g.source g.open_source := by
    constructor
    · rfl
    · intro z hz
      change chartAt y ((chartAt x).symm z) = z
      rw [hchart_eq]
      exact (chartAt x).right_inv hz.1
  exact (@idRestrGroupoid E _).mem_of_eqOnSource (idRestrGroupoid_mem g.open_source) hg
/-- Once a charted space has transition maps in the restriction groupoid, it is automatically a
complex manifold. This is the fully generic part of the manifold assembly. -/
theorem isManifold_of_hasGroupoid_idRestr
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
    [ChartedSpace E M] [HasGroupoid M (@idRestrGroupoid E _)] :
    IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞) M := by
  have hle : @idRestrGroupoid E _ ≤ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓘(ℂ, E)) :=
    (closedUnderRestriction_iff_id_le _).mp inferInstance
  letI : HasGroupoid M (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓘(ℂ, E))) :=
    hasGroupoid_of_le (M := M) (G₁ := @idRestrGroupoid E _)
      (G₂ := contDiffGroupoid _ (𝓘(ℂ, E)))
      inferInstance hle
  exact IsManifold.mk' (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞) M
/-- A generic manifold-construction theorem for complex local homeomorphisms into a normed model
space. This is the abstract topological-to-manifold bridge needed to keep Corollary 1.3 small. -/
theorem exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
    (f : M → E) (hf : IsLocalHomeomorph f) :
    ∃ _ : ChartedSpace E M, IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞) M := by
  rcases
      exists_chartedSpace_and_hasGroupoid_idRestr_of_isLocalHomeomorph_to_complex_model
        (E := E) (M := M) f hf with
    ⟨_instChartedSpace, _instHasGroupoid⟩
  exact ⟨_instChartedSpace, isManifold_of_hasGroupoid_idRestr (E := E) (M := M)⟩
/-! ### Corollary 1.3: Complex manifold structure -/
/-- **Bridgeland's Corollary 1.3** for `Stab_Λ(D)`. Each connected component of the
stability space `Stab_Λ(D)` is a complex manifold.

The proof is direct: `ComponentTopologicalLinearLocalModel` gives a local homeomorphism
`σ ↦ σ.Z` into `V(Σ) ⊆ Hom(Λ, ℂ)`. Since `Λ` has finite rank, `Hom(Λ, ℂ)` is
finite-dimensional, hence so is `V(Σ)`. The generic manifold construction applies. -/
theorem StabilityCondition.WithClassMap.existsComplexManifoldOnConnectedComponent
    {Λ : Type u'} [AddCommGroup Λ] [AddGroup.FG Λ]
    {v : K₀ C →+ Λ} [Fact (Function.Surjective v)]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :
    ∃ (E : Type u') (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (StabilityCondition.WithClassMap.Component C v cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (StabilityCondition.WithClassMap.Component C v cc) := by
  -- The local model from Theorem 1.2
  let M := componentTopologicalLinearLocalModel C cc
  -- V(Σ) is finite-dimensional: it's a submodule of Hom(Λ, ℂ) which has finite rank
  haveI : FiniteDimensional ℂ (Λ →+ ℂ) := classMapChargeSpace_finiteDimensional Λ
  haveI : FiniteDimensional ℂ M.V := FiniteDimensional.finiteDimensional_submodule M.V
  -- Apply generic manifold construction to the charge map
  rcases exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model
      (E := M.V) (ComponentTopologicalLinearLocalModel.chargeMap (C := C) M)
      M.isLocalHomeomorph_chargeMap with ⟨inst, hmanifold⟩
  exact ⟨M.V, M.instNormedAddCommGroup, M.instNormedSpace, this, inst, hmanifold⟩
/-- **Bridgeland's Corollary 1.3** for numerical stability conditions. Each connected
component of `Stab_N(D)` is a complex manifold of dimension `rk(N(D))`.

This is a specialization of the generic class-map theorem to
`v = numericalQuotientMap k C`, which is surjective by definition. -/
theorem NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent
    (k : Type w) [Field k]
    [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    [NumericallyFinite k C]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (NumericalComponent (k := k) C cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (NumericalComponent (k := k) C cc)  := sorry
end CategoryTheory.Triangulated

