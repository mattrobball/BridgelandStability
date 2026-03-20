/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.StabilityCondition.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.GroupTheory.Finiteness

/-!
# Numerical Stability Conditions

We define numerical K-theory and state Bridgeland's Corollary 1.3 for numerically
finite triangulated categories.

## Main definitions

* `CategoryTheory.Triangulated.IsFiniteType`: a `k`-linear triangulated category of
  finite type (finite-dimensional Hom spaces, finitely many nonzero shifted Hom spaces)
* `CategoryTheory.Triangulated.eulerFormObj`: the Euler form on objects
  `χ(E,F) = Σᵢ (-1)ⁱ dim_k Hom(E, F[i])`
* `CategoryTheory.Triangulated.EulerFormDescends`: typeclass asserting that the Euler
  form descends to K₀ (triangle-additive in both arguments)
* `CategoryTheory.Triangulated.eulerForm`: the Euler form lifted to K₀, constructed
  via the universal property under `[EulerFormDescends k C]`
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

/-! ### Euler form -/

/-- The Euler form on objects (blueprint B1): `χ(E,F) = Σₙ (-1)ⁿ dim_k Hom(E, F[n])`.
This is defined as a finitely-supported sum using `finsum`. -/
def eulerFormObj [Linear k C] (E F : C) : ℤ :=
  ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ (shiftFunctor C n).obj F) : ℤ)

/-- The Euler form descends to K₀ if it is triangle-additive in both arguments.
This is a consequence of the long exact sequence on shifted Hom spaces and
the rank-nullity theorem. We state it as a typeclass to be instantiated when
the full proof is available. -/
class EulerFormDescends [Linear k C] [IsFiniteType k C] : Prop where
  /-- For fixed `F`, the function `E ↦ χ(E, F)` is triangle-additive. -/
  covariant (F : C) : IsTriangleAdditive (fun E ↦ eulerFormObj k C E F)
  /-- For fixed `E`, the function `F ↦ χ(E, F)` is triangle-additive. -/
  contravariant (E : C) : IsTriangleAdditive (fun F ↦ eulerFormObj k C E F)

/-! ### Euler form on K₀ -/

section EulerForm

variable [Linear k C] [IsFiniteType k C] [EulerFormDescends k C]

/-- The inner lift: for fixed `E`, lift `F ↦ χ(E, F)` to a group homomorphism
`K₀ C →+ ℤ` via the universal property. -/
private def eulerFormInner (E : C) : K₀ C →+ ℤ :=
  letI := (EulerFormDescends.contravariant (k := k) (C := C) E)
  K₀.lift C (fun F ↦ eulerFormObj k C E F)

/-- The outer function `E ↦ eulerFormInner E` is triangle-additive: for a
distinguished triangle `T`, the lifted functions agree additively. -/
private instance eulerFormInner_isTriangleAdditive :
    IsTriangleAdditive (eulerFormInner k C) where
  additive T hT := by
    -- Goal: eulerFormInner k C T.obj₂ = eulerFormInner k C T.obj₁ + eulerFormInner k C T.obj₃
    -- Both sides are AddMonoidHoms from K₀ C = FreeAbelianGroup C ⧸ K₀Subgroup C.
    -- By addMonoidHom_ext, suffices to check compositions with mk' are equal.
    -- Those are AddMonoidHoms from FreeAbelianGroup C, so use lift_ext.
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro F
    -- Now the goal involves compositions with mk' and FreeAbelianGroup.of F
    simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
    change (eulerFormInner k C T.obj₂) (K₀.of C F) =
      (eulerFormInner k C T.obj₁) (K₀.of C F) +
      (eulerFormInner k C T.obj₃) (K₀.of C F)
    simp only [eulerFormInner, K₀.lift_of]
    exact (EulerFormDescends.covariant (k := k) F).additive T hT

/-- The Euler form on K₀, a bilinear form `K₀ C →+ K₀ C →+ ℤ` constructed from
`eulerFormObj` via the universal property of K₀ applied twice. -/
def eulerForm : K₀ C →+ K₀ C →+ ℤ :=
  K₀.lift C (eulerFormInner k C)

end EulerForm

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
finite with respect to the Euler form. Then for each connected component of
`Stab_N(D)` (the space of numerical stability conditions), the factored central
charge map is a local homeomorphism into a subspace of `Hom_ℤ(N(D), ℂ)`.

Since `N(D)` is finitely generated, the target is finite-dimensional, making each
connected component a finite-dimensional complex manifold (blueprint B5).

This uses `IsLocalHomeomorph` from `Mathlib.Topology.IsLocalHomeomorph` and
replaces the abstract `χ` parameter with the concrete `eulerForm k C` under
`[EulerFormDescends k C]`. -/
def bridgelandCorollary_1_3 [Linear k C] [IsFiniteType k C] [EulerFormDescends k C] : Prop :=
  let χ := eulerForm k C
  NumericallyFinite C χ →
    ∀ (cc : ConnectedComponents (NumericalStabilityCondition C χ)),
      ∃ (V : AddSubgroup (NumericalK₀ C χ →+ ℂ))
        (τ_V : TopologicalSpace V)
        (hZ : ∀ σ : NumericalStabilityCondition C χ,
          ConnectedComponents.mk σ = cc → σ.factors.choose ∈ V),
        @IsLocalHomeomorph
          {σ : NumericalStabilityCondition C χ // ConnectedComponents.mk σ = cc}
          V inferInstance τ_V
          (fun ⟨σ, hσ⟩ ↦ ⟨σ.factors.choose, hZ σ hσ⟩)

end CategoryTheory.Triangulated
