/- 
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/

import Mathlib.CategoryTheory.Triangulated.NumericalStability
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Topology.IsLocalHomeomorph

/-!
# Numerical Stability Manifolds

This file isolates the manifold-level packaging behind Bridgeland's Corollary 1.3.

The current statement of `bridgelandCorollary_1_3` only exports a local homeomorphism into an
additive subgroup with a bare topology. For the actual complex-manifold corollary, we want to
separate the work into the following stages:

1. Produce a topological complex-linear local model for each connected component of numerical
   stability conditions.
2. Replace that topological model by a finite-dimensional normed complex model space.
3. Build the `ChartedSpace` and `IsManifold` structures from the resulting local homeomorphism.

The declarations in this file are the intended interfaces for those steps. Once they are proved,
Corollary 1.3 should be mechanical assembly.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped Manifold Topology

universe w v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- The type of numerical stability conditions in a fixed connected component. -/
abbrev NumericalComponent (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (NumericalStabilityCondition C χ)) :=
  {σ : NumericalStabilityCondition C χ // ConnectedComponents.mk σ = cc}

/-- The ambient complex charge space for numerical stability conditions. -/
abbrev NumericalChargeSpace (χ : K₀ C →+ K₀ C →+ ℤ) :=
  NumericalK₀ C χ →+ ℂ

/-- A topological complex-linear local model for a connected component of numerical stability
conditions. This is the strengthened codomain package that Corollary 1.3 should ultimately
export before any manifold-level assembly. -/
structure NumericalComponentTopologicalLinearModel (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (NumericalStabilityCondition C χ)) where
  /-- Bridgeland's `V(Σ)`, formalized as a complex-linear subspace of numerical charges. -/
  V : Submodule ℂ (NumericalChargeSpace C χ)
  instTopologicalSpace : TopologicalSpace V
  instIsTopologicalAddGroup : IsTopologicalAddGroup V
  instContinuousSMul : ContinuousSMul ℂ V
  instPolynormableSpace : PolynormableSpace ℂ V
  instFiniteDimensional : FiniteDimensional ℂ V
  /-- The factored central charge lands in `V`. -/
  mem_charge : ∀ σ : NumericalStabilityCondition C χ,
    ConnectedComponents.mk σ = cc → σ.factors.choose ∈ V
  /-- The factored central charge map is a local homeomorphism into `V`. -/
  isLocalHomeomorph :
    @IsLocalHomeomorph (NumericalComponent C χ cc) V inferInstance instTopologicalSpace
      (fun ⟨σ, hσ⟩ ↦ ⟨σ.factors.choose, mem_charge σ hσ⟩)

attribute [instance] NumericalComponentTopologicalLinearModel.instTopologicalSpace
attribute [instance] NumericalComponentTopologicalLinearModel.instIsTopologicalAddGroup
attribute [instance] NumericalComponentTopologicalLinearModel.instContinuousSMul
attribute [instance] NumericalComponentTopologicalLinearModel.instPolynormableSpace
attribute [instance] NumericalComponentTopologicalLinearModel.instFiniteDimensional

namespace NumericalComponentTopologicalLinearModel

variable {C} {χ : K₀ C →+ K₀ C →+ ℤ}
variable {cc : ConnectedComponents (NumericalStabilityCondition C χ)}

/-- The local-homeomorphism chart map associated to a topological linear local model. -/
def chargeMap (M : NumericalComponentTopologicalLinearModel C χ cc) :
    NumericalComponent C χ cc → M.V :=
  fun ⟨σ, hσ⟩ ↦ ⟨σ.factors.choose, M.mem_charge σ hσ⟩

/-- Replace the abstract topological complex vector space `V` by a chosen finite-dimensional
normed complex model space. Proving this should make the manifold step for Corollary 1.3
purely formal. -/
theorem exists_normedComplexModel (M : NumericalComponentTopologicalLinearModel C χ cc) :
    ∃ (E : Type*) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E) (f : NumericalComponent C χ cc → E),
      IsLocalHomeomorph f := by
  sorry

end NumericalComponentTopologicalLinearModel

variable (k : Type w) [Field k]

/-- A strengthened, theorem-shaped version of Corollary 1.3. This is the numerical analogue of
the stronger form Theorem 1.2 should eventually export. -/
noncomputable def bridgelandCorollary_1_3_topologicalLinearModel [Linear k C] [IsFiniteType k C]
    [EulerFormDescends k C] (hnum : NumericallyFinite C (eulerForm k C))
    (cc : ConnectedComponents (NumericalStabilityCondition C (eulerForm k C))) :
    NumericalComponentTopologicalLinearModel C (eulerForm k C) cc := by
  sorry

/-- A generic manifold-construction theorem for complex local homeomorphisms into a normed model
space. This is the abstract topological-to-manifold bridge needed to keep Corollary 1.3 small. -/
theorem exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
    (f : M → E) (hf : IsLocalHomeomorph f) :
    ∃ _ : ChartedSpace E M, IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞) M := by
  sorry

/-- A mechanical-assembly version of Bridgeland's Corollary 1.3: once the topological linear local
model and the generic manifold bridge are available, the complex-manifold conclusion should follow
without a large bespoke proof. -/
theorem bridgelandCorollary_1_3_complexManifold [Linear k C] [IsFiniteType k C]
    [EulerFormDescends k C] (hnum : NumericallyFinite C (eulerForm k C))
    (cc : ConnectedComponents (NumericalStabilityCondition C (eulerForm k C))) :
    ∃ (E : Type*) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (NumericalComponent C (eulerForm k C) cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (NumericalComponent C (eulerForm k C) cc) := by
  sorry

end CategoryTheory.Triangulated
