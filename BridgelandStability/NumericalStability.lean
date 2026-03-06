/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.StabilityCondition
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Numerical Stability Conditions

We define numerical K-theory and state Bridgeland's Corollary 1.3 for numerically
finite triangulated categories.

## Main definitions

* `CategoryTheory.Triangulated.IsFiniteType`: a `k`-linear triangulated category of
  finite type (finite-dimensional Hom spaces, finitely many nonzero shifted Hom spaces)
* `CategoryTheory.Triangulated.eulerFormObj`: the Euler form on objects
  `χ(E,F) = Σᵢ (-1)ⁱ dim_k Hom(E, F[i])`
* `CategoryTheory.Triangulated.eulerFormDescends`: the descent property asserting that
  the Euler form respects distinguished triangle relations
* `CategoryTheory.Triangulated.NumericalK₀`: the numerical Grothendieck group
  `N(D) = K₀(D) / ker(χ)`
* `CategoryTheory.Triangulated.NumericallyFinite`: `N(D)` is finitely generated
* `CategoryTheory.Triangulated.NumericalStabilityCondition`: a stability condition
  whose central charge factors through `N(D)`
* `CategoryTheory.Triangulated.bridgelandCorollary_1_3`: **Corollary 1.3** as a `Prop`

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CategoryTheory.Triangulated

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Finite type -/

/-- A `k`-linear pretriangulated category is of finite type if all Hom spaces are
finite-dimensional over `k` and for each pair of objects, only finitely many shifted
Hom spaces are nonzero (blueprint B0). -/
class IsFiniteType [Linear k C] : Prop where
  /-- Each Hom space `Hom(E, F)` is finite-dimensional over `k`. -/
  finite_dim : ∀ (E F : C), Module.Finite k (E ⟶ F)
  /-- For each pair of objects, only finitely many shifted Hom spaces are nontrivial. -/
  finite_support : ∀ (E F : C), Set.Finite {n : ℤ | Nontrivial (E ⟶ (shiftFunctor C n).obj F)}

/-! ### Euler form -/

/-- The Euler form on objects (blueprint B1): `χ(E,F) = Σₙ (-1)ⁿ dim_k Hom(E, F[n])`.
This is defined as a finitely-supported sum using `finsum`. -/
def eulerFormObj [Linear k C] (E F : C) : ℤ :=
  ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ (shiftFunctor C n).obj F) : ℤ)

/-- The descent property for the Euler form: for every distinguished triangle
`A → B → C → A[1]`, the Euler form satisfies `χ(B, F) = χ(A, F) + χ(C, F)` and
`χ(F, B) = χ(F, A) + χ(F, C)` for all `F`.

This is a consequence of the long exact sequence on shifted Hom spaces and
the rank-nullity theorem. -/
def eulerFormDescends [Linear k C] : Prop :=
  (∀ (T : Pretriangulated.Triangle C) (_ : T ∈ distTriang C) (F : C),
    eulerFormObj k C T.obj₂ F = eulerFormObj k C T.obj₁ F + eulerFormObj k C T.obj₃ F) ∧
  (∀ (T : Pretriangulated.Triangle C) (_ : T ∈ distTriang C) (F : C),
    eulerFormObj k C F T.obj₂ = eulerFormObj k C F T.obj₁ + eulerFormObj k C F T.obj₃)

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

/-! ### Corollary 1.3 -/

/-- **Bridgeland's Corollary 1.3** (corrected statement). Assume `C` is numerically
finite. Then for each connected component of `Stab_N(D)` (the space of numerical
stability conditions), there exists a linear subspace `V ⊆ Hom_ℤ(N(D), ℂ)` with
a topology, and a local homeomorphism from `Stab_N(D)` to `V`, such that every
numerical stability condition in that component lies in the source.

Since `N(D)` is finitely generated, `V` is finite-dimensional, making each
connected component a finite-dimensional complex manifold (blueprint B5). -/
def bridgelandCorollary_1_3 (χ : K₀ C →+ K₀ C →+ ℤ) : Prop :=
  NumericallyFinite C χ →
    ∀ (cc : ConnectedComponents (NumericalStabilityCondition C χ)),
      ∃ (V : AddSubgroup (NumericalK₀ C χ →+ ℂ))
        (τ_V : TopologicalSpace V),
        ∃ (e : @PartialHomeomorph (NumericalStabilityCondition C χ) V
          (NumericalStabilityCondition.topologicalSpace C χ) τ_V),
          ∀ σ : NumericalStabilityCondition C χ,
            ConnectedComponents.mk σ = cc → σ ∈ e.source

end CategoryTheory.Triangulated
