/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.Topology
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.GroupTheory.Finiteness

/-!
# Class-Map Stability Conditions

We define the generic package attached to a class map `v : K₀(C) → Λ`. The actual
numerical quotient `K₀(C) / K₀(C)ᵖᵉʳᵖ` attached to the Euler form is proved
downstream in `BridgelandStability.EulerForm`.

## Main definitions

* `CategoryTheory.Triangulated.IsFiniteType`: a `k`-linear triangulated category of
  finite type (finite-dimensional Hom spaces, finitely many nonzero shifted Hom spaces)
* `CategoryTheory.Triangulated.eulerFormObj`: the Euler form on objects
  `χ(E,F) = Σᵢ (-1)ⁱ dim_k Hom(E, F[i])`
* `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap`: a prestability condition
  with central charge `Z : Λ →+ ℂ`
* `CategoryTheory.Triangulated.StabilityCondition.WithClassMap`: the locally-finite version
* `CategoryTheory.Triangulated.StabilityCondition.FactorsThrough`: the derived comparison
  predicate on ordinary stability conditions

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u u'

namespace CategoryTheory.Triangulated

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]

/-! ### Finite type -/

/-- A `k`-linear pretriangulated category is of finite type if all Hom spaces are
finite-dimensional over `k` and for each pair of objects, only finitely many shifted
Hom spaces are nonzero (blueprint B0). -/
class IsFiniteType [Linear k C] : Prop where
  /-- Each Hom space `Hom(E, F)` is finite-dimensional over `k`. -/
  finite_dim : ∀ (E F : C), Module.Finite k (E ⟶ F)
  /-- For each pair of objects, only finitely many shifted Hom spaces are nontrivial. -/
  finite_support : ∀ (E F : C), Set.Finite {n : ℤ | Nontrivial (E ⟶ (shiftFunctor C n).obj F)}

/-! ### Object-level Euler form -/

/-- The Euler form on objects (blueprint B1): `χ(E,F) = Σₙ (-1)ⁿ dim_k Hom(E, F[n])`.
This is defined as a finitely-supported sum using `finsum`. -/
def eulerFormObj [Linear k C] (E F : C) : ℤ :=
  ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ (shiftFunctor C n).obj F) : ℤ)

/-! ### Comparison tools for class-map stability conditions -/

@[simp] theorem StabilityCondition.WithClassMap.toStabilityCondition_slicing
    {v : K₀ C →+ Λ} (σ : StabilityCondition.WithClassMap C v) :
    σ.toStabilityCondition.slicing = σ.slicing := rfl

@[simp] theorem StabilityCondition.WithClassMap.toStabilityCondition_Z
    {v : K₀ C →+ Λ} (σ : StabilityCondition.WithClassMap C v) :
    σ.toStabilityCondition.Z = σ.Z.comp v := rfl

/-- The ambient central charge of `σ` factors through the chosen class map `v`. -/
def StabilityCondition.FactorsThrough (v : K₀ C →+ Λ) (σ : StabilityCondition C) : Prop :=
  ∃ Z' : Λ →+ ℂ, σ.Z = Z'.comp v

/-- The factorization subtype, kept as a comparison object for the topology and
surjective-recovery theorems. -/
abbrev ClassMapStabilityCondition (v : K₀ C →+ Λ) : Type _ :=
  {σ : StabilityCondition C // σ.FactorsThrough (C := C) v}

/-- A bundled class-map stability condition determines an ordinary stability
condition whose charge factors through `v`. -/
def StabilityCondition.WithClassMap.toClassMapStabilityCondition {v : K₀ C →+ Λ}
    (σ : StabilityCondition.WithClassMap C v) : ClassMapStabilityCondition C v :=
  ⟨σ.toStabilityCondition, ⟨σ.Z, rfl⟩⟩

namespace StabilityCondition.WithClassMap

@[continuity]
theorem continuous_toClassMapStabilityCondition {v : K₀ C →+ Λ} :
    Continuous (StabilityCondition.WithClassMap.toClassMapStabilityCondition (C := C) (v := v)) :=
  Continuous.subtype_mk
    (StabilityCondition.WithClassMap.continuous_toStabilityCondition (C := C) (v := v))
    (fun _ => ⟨_, rfl⟩)

end StabilityCondition.WithClassMap

/-- The factorization property for a class-map stability condition. -/
theorem ClassMapStabilityCondition.factors {v : K₀ C →+ Λ}
    (σ : ClassMapStabilityCondition C v) :
    ∃ Z' : Λ →+ ℂ, (σ : StabilityCondition C).Z = Z'.comp v :=
  σ.2

/-- The chosen factored central charge for a factorization-subtype point. -/
noncomputable def ClassMapStabilityCondition.factorMap {v : K₀ C →+ Λ}
    (σ : ClassMapStabilityCondition C v) : Λ →+ ℂ :=
  Classical.choose σ.factors

@[simp]
theorem ClassMapStabilityCondition.factorMap_comp {v : K₀ C →+ Λ}
    (σ : ClassMapStabilityCondition C v) :
    (σ : StabilityCondition C).Z = σ.factorMap.comp v :=
  Classical.choose_spec σ.factors

omit [IsTriangulated C] in
/-- Two class-lattice charges agreeing after precomposition with a surjective
class map are equal. -/
theorem classMapCharge_ext_of_surjective {v : K₀ C →+ Λ}
    (hv : Function.Surjective v) {Z₁ Z₂ : Λ →+ ℂ}
    (hcomp : Z₁.comp v = Z₂.comp v) : Z₁ = Z₂ := by
  ext x
  obtain ⟨y, rfl⟩ := hv x
  exact congrArg (fun f : K₀ C →+ ℂ => f y) hcomp

/-- Recover a bundled class-map stability condition from the factorization
subtype once the class map is surjective. -/
noncomputable def StabilityCondition.WithClassMap.ofClassMapStabilityCondition
    {v : K₀ C →+ Λ} (σ : ClassMapStabilityCondition C v) :
    StabilityCondition.WithClassMap C v where
  slicing := σ.1.slicing
  Z := σ.factorMap
  compat := by
    intro φ E hE hNZ
    rcases stabilityCondition_compat_apply (C := C) σ.1 φ E hE hNZ with ⟨m, hm, hχ⟩
    refine ⟨m, hm, ?_⟩
    have hfac :=
      congrArg (fun f : K₀ C →+ ℂ => f (K₀.of C E))
        (ClassMapStabilityCondition.factorMap_comp (C := C) (v := v) σ)
    exact hfac.symm.trans hχ
  locallyFinite := σ.1.locallyFinite

/-- Under surjectivity of `v`, the bundled and factorization-subtype
presentations of `Stab_v(D)` are equivalent. -/
noncomputable def StabilityCondition.WithClassMap.equivClassMapStabilityCondition
    {v : K₀ C →+ Λ} (hv : Function.Surjective v) :
    StabilityCondition.WithClassMap C v ≃ ClassMapStabilityCondition C v where
  toFun := fun σ => σ.toClassMapStabilityCondition
  invFun := StabilityCondition.WithClassMap.ofClassMapStabilityCondition (C := C)
  left_inv σ := by
    apply StabilityCondition.WithClassMap.ext
    · rfl
    · apply classMapCharge_ext_of_surjective (C := C) (v := v) hv
      simpa [StabilityCondition.WithClassMap.toClassMapStabilityCondition,
        StabilityCondition.WithClassMap.toStabilityCondition_Z] using
        (ClassMapStabilityCondition.factorMap_comp
          (C := C) (v := v) (σ := σ.toClassMapStabilityCondition)).symm
  right_inv σ := by
    apply Subtype.ext
    apply StabilityCondition.WithClassMap.ext
    · rfl
    · change σ.factorMap.comp v = (σ : StabilityCondition C).Z
      exact (ClassMapStabilityCondition.factorMap_comp (C := C) (v := v) σ).symm

/-- Specializing a class-map stability condition to the identity class map
recovers the usual ambient stability condition. -/
def StabilityCondition.WithClassMap.idEquiv :
    StabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C)) ≃ StabilityCondition C where
  toFun := fun σ => σ
  invFun := fun σ => σ
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end CategoryTheory.Triangulated
