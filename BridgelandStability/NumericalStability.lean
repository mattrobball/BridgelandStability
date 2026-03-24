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
# Numerical Stability Conditions

We define the generic numerical quotient package attached to a bilinear form on `K₀`.
The actual descent of the Euler form to `K₀` is proved downstream in
`BridgelandStability.EulerForm`.

## Main definitions

* `CategoryTheory.Triangulated.IsFiniteType`: a `k`-linear triangulated category of
  finite type (finite-dimensional Hom spaces, finitely many nonzero shifted Hom spaces)
* `CategoryTheory.Triangulated.eulerFormObj`: the Euler form on objects
  `χ(E,F) = Σᵢ (-1)ⁱ dim_k Hom(E, F[i])`
* `CategoryTheory.Triangulated.NumericalK₀`: the numerical Grothendieck group
  `N(D) = K₀(D) / ker(χ)`
* `CategoryTheory.Triangulated.NumericallyFinite`: `N(D)` is finitely generated
* `CategoryTheory.Triangulated.NumericalStabilityCondition`: a stability condition
  whose central charge factors through `N(D)`

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CategoryTheory.Triangulated

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

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

/-! ### Numerical Grothendieck group -/

/-- The left radical of a bilinear form `χ` on `K₀ C`: the subgroup of elements
`x ∈ K₀ C` such that `χ(x, y) = 0` for all `y` (i.e., the kernel of the curried
map `χ : K₀ C →+ (K₀ C →+ ℤ)`). When `χ` is the Euler form lifted to K₀, this
gives the numerical equivalence relation (blueprint B2). -/
def eulerFormRad (χ : K₀ C →+ K₀ C →+ ℤ) : AddSubgroup (K₀ C) := χ.ker

/-- The numerical Grothendieck group `N(D) = K₀(D) / ker(χ)` (blueprint B2). -/
def NumericalK₀ (χ : K₀ C →+ K₀ C →+ ℤ) : Type _ := K₀ C ⧸ eulerFormRad C χ

/-- The `AddCommGroup` instance on `NumericalK₀ C χ`. -/
instance NumericalK₀.instAddCommGroup (χ : K₀ C →+ K₀ C →+ ℤ) :
    AddCommGroup (NumericalK₀ C χ) :=
  inferInstanceAs (AddCommGroup (K₀ C ⧸ eulerFormRad C χ))

/-- The category `C` is numerically finite (blueprint B3) if the numerical Grothendieck
group `N(D) = K₀(D)/ker(χ)` is finitely generated as an abelian group. -/
class NumericallyFinite (χ : K₀ C →+ K₀ C →+ ℤ) : Prop where
  /-- The numerical Grothendieck group is finitely generated. -/
  fg : AddGroup.FG (NumericalK₀ C χ)

/-! ### Numerical stability conditions -/

/-- A numerical stability condition is a stability condition whose central charge
factors through the numerical Grothendieck group `N(D) = K₀(D)/ker(χ)` (blueprint B4). -/
structure NumericalStabilityCondition (χ : K₀ C →+ K₀ C →+ ℤ) where
  /-- The underlying stability condition. -/
  toStabilityCondition : StabilityCondition C
  /-- The central charge factors through `NumericalK₀`. -/
  factors : ∃ Z' : NumericalK₀ C χ →+ ℂ,
    toStabilityCondition.Z = Z'.comp (QuotientAddGroup.mk' (eulerFormRad C χ))

/-- The topology on numerical stability conditions, induced from the Bridgeland topology
on `StabilityCondition C` via the inclusion map. -/
instance NumericalStabilityCondition.topologicalSpace (χ : K₀ C →+ K₀ C →+ ℤ) :
    TopologicalSpace (NumericalStabilityCondition C χ) :=
  TopologicalSpace.induced
    NumericalStabilityCondition.toStabilityCondition
    (StabilityCondition.topologicalSpace C)

/-- The numerical local-homeomorphism package for connected components of numerical stability
conditions. This is the proposition-object behind Bridgeland's Corollary 1.3 once the relevant
bilinear form `χ` on `K₀` has been fixed. -/
def NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents
    (χ : K₀ C →+ K₀ C →+ ℤ) : Prop :=
  NumericallyFinite C χ →
    ∀ (cc : ConnectedComponents (NumericalStabilityCondition C χ)),
      ∃ (V : Submodule ℂ (NumericalK₀ C χ →+ ℂ))
        (_ : NormedAddCommGroup V)
        (_ : NormedSpace ℂ V)
        (hZ : ∀ σ : NumericalStabilityCondition C χ,
          ConnectedComponents.mk σ = cc →
            σ.factors.choose ∈ V),
        @IsLocalHomeomorph
          {σ : NumericalStabilityCondition C χ //
            ConnectedComponents.mk σ = cc}
          V inferInstance inferInstance
          (fun ⟨σ, hσ⟩ ↦ ⟨σ.factors.choose, hZ σ hσ⟩)

end CategoryTheory.Triangulated
