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
end CategoryTheory.Triangulated

-- ═══ Slicing.Defs ═══
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace CategoryTheory.Triangulated
section Slicing
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
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
end K0Presentation

-- ═══ GrothendieckGroup.Basic ═══
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
end ClassMap
end CategoryTheory.Triangulated

-- ═══ QuasiAbelian.Basic ═══
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
end StrictSubobject
section StrictSubobjectTransfer
variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [Preadditive A]
  [HasKernels A] [HasCokernels A]
  {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [Preadditive C]
  [HasKernels C] [HasCokernels C]
end StrictSubobjectTransfer
end CategoryTheory

-- ═══ IntervalCategory.Basic ═══
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace CategoryTheory.Triangulated
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
/-- The interval subcategory `P((a, b))` of a slicing, defined as the full subcategory
on objects whose HN phases all lie in `(a, b)`. An object `E` belongs to `P((a, b))` if
it is zero or admits an HN filtration with all phases in `(a, b)`.

This is **Bridgeland's Definition 4.1** specialized to open intervals. -/
abbrev Slicing.IntervalCat (s : Slicing C) (a b : ℝ) :=
  (s.intervalProp C a b).FullSubcategory
end CategoryTheory.Triangulated

-- ═══ IntervalCategory.QuasiAbelian ═══
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace CategoryTheory.Triangulated
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
section Preabelian
variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
noncomputable instance Slicing.intervalCat_hasKernels (s : Slicing C) :
    HasKernels (s.IntervalCat C a b)  := sorry
noncomputable instance Slicing.intervalCat_hasCokernels (s : Slicing C) :
    HasCokernels (s.IntervalCat C a b)  := sorry
end Preabelian
end CategoryTheory.Triangulated

-- ═══ IntervalCategory.FiniteLength ═══
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace CategoryTheory.Triangulated
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
section Preabelian
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
end Preabelian
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}
variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
end CategoryTheory.Triangulated

-- ═══ StabilityCondition.Defs ═══
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ENNReal
namespace CategoryTheory.Triangulated
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]
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
end StabilityCondition.WithClassMap
end CategoryTheory.Triangulated

-- ═══ NumericalStability.Defs ═══
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory.Triangulated
variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
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
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite
namespace CategoryTheory.Triangulated
variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [Linear k C] [IsFiniteType k C]
section EulerTriangleAdditivity
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
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped Manifold Topology
namespace CategoryTheory.Triangulated
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
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

