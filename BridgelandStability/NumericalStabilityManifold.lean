/- 
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/

import Mathlib.CategoryTheory.Triangulated.NumericalStability
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.LocalAtTarget

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

/-- The ambient Bridgeland charge space `Hom_ℤ(K₀(D), ℂ)` before passing to numerical charges. -/
abbrev AmbientChargeSpace :=
  K₀ C →+ ℂ

/-- The quotient map `K₀(D) → N(D)`. -/
abbrev numericalQuotientMap (χ : K₀ C →+ K₀ C →+ ℤ) :
    K₀ C →+ NumericalK₀ C χ :=
  QuotientAddGroup.mk' (eulerFormRad C χ)

/-- Precomposition with the quotient map `K₀(D) → N(D)`. -/
def precomposeNumericalQuotient (χ : K₀ C →+ K₀ C →+ ℤ) :
    NumericalChargeSpace C χ →ₗ[ℂ] AmbientChargeSpace C where
  toFun := fun Z' => Z'.comp (numericalQuotientMap C χ)
  map_add' Z₁ Z₂ := by
    ext x
    rfl
  map_smul' a Z := by
    ext x
    rfl

/-- The subspace of ambient charges that factor through `N(D)`. -/
def numericalFactorSubmodule (χ : K₀ C →+ K₀ C →+ ℤ) :
    Submodule ℂ (AmbientChargeSpace C) :=
  LinearMap.range (precomposeNumericalQuotient C χ)

theorem mem_numericalFactorSubmodule_iff {χ : K₀ C →+ K₀ C →+ ℤ} {Z : AmbientChargeSpace C} :
    Z ∈ numericalFactorSubmodule C χ ↔
      ∃ Z' : NumericalChargeSpace C χ, Z = Z'.comp (numericalQuotientMap C χ) := by
  rw [numericalFactorSubmodule, LinearMap.mem_range]
  constructor
  · rintro ⟨Z', rfl⟩
    exact ⟨Z', rfl⟩
  · rintro ⟨Z', rfl⟩
    exact ⟨Z', rfl⟩

/-- `Hom_ℤ(N(D), ℂ)` identifies with the subspace of ambient charges factoring through `N(D)`. -/
noncomputable def numericalChargeSpaceEquivFactorSubmodule (χ : K₀ C →+ K₀ C →+ ℤ) :
    NumericalChargeSpace C χ ≃ₗ[ℂ] numericalFactorSubmodule C χ :=
  LinearEquiv.ofInjective (precomposeNumericalQuotient C χ) <| by
    intro Z₁ Z₂ h
    ext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (eulerFormRad C χ) x
    exact congrArg (fun f : AmbientChargeSpace C => f y) h

/-- A numerical stability condition has ambient central charge in the numerical factor subspace. -/
theorem NumericalStabilityCondition.charge_mem_numericalFactorSubmodule
    {χ : K₀ C →+ K₀ C →+ ℤ} (σ : NumericalStabilityCondition C χ) :
    σ.toStabilityCondition.Z ∈ numericalFactorSubmodule C χ := by
  rcases σ.factors with ⟨Z', hZ'⟩
  rw [mem_numericalFactorSubmodule_iff]
  exact ⟨Z', hZ'⟩

/-- The inclusion of numerical stability conditions into ordinary stability conditions is continuous
for the induced topology. -/
theorem NumericalStabilityCondition.continuous_toStabilityCondition
    (χ : K₀ C →+ K₀ C →+ ℤ) :
    Continuous
      (NumericalStabilityCondition.toStabilityCondition :
        NumericalStabilityCondition C χ → StabilityCondition C) :=
  continuous_induced_dom

/-- The map on connected components induced by the inclusion
`Stab_N(D) ⟶ Stab(D)`. -/
noncomputable def NumericalStabilityCondition.ambientComponentMap
    (χ : K₀ C →+ K₀ C →+ ℤ) :
    ConnectedComponents (NumericalStabilityCondition C χ) →
      ConnectedComponents (StabilityCondition C) :=
  (NumericalStabilityCondition.continuous_toStabilityCondition (C := C) χ).connectedComponentsMap

@[simp]
theorem NumericalStabilityCondition.ambientComponentMap_apply
    (χ : K₀ C →+ K₀ C →+ ℤ) (σ : NumericalStabilityCondition C χ) :
    NumericalStabilityCondition.ambientComponentMap (C := C) χ (ConnectedComponents.mk σ) =
      ConnectedComponents.mk σ.toStabilityCondition := by
  simp [NumericalStabilityCondition.ambientComponentMap, Continuous.connectedComponentsMap]

/-- Restricting a local homeomorphism to the preimage of an arbitrary subset of the codomain.

This is the general topological ingredient behind the restriction step from Bridgeland's Theorem
1.2 to Corollary 1.3. -/
theorem IsLocalHomeomorph.codRestrict_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) (s : Set Y) :
    @IsLocalHomeomorph {x : X // f x ∈ s} s inferInstance inferInstance
      (fun x => ⟨f x.1, x.2⟩) := by
  sorry

/-- A topological complex-linear local model for a connected component of numerical stability
conditions. This packages the local-homeomorphism part of Corollary 1.3, before using numerical
finiteness to prove finite-dimensionality. -/
structure NumericalComponentTopologicalLinearLocalModel (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (NumericalStabilityCondition C χ)) where
  /-- Bridgeland's `V(Σ)`, formalized as a complex-linear subspace of numerical charges. -/
  V : Submodule ℂ (NumericalChargeSpace C χ)
  instTopologicalSpace : TopologicalSpace V
  instIsTopologicalAddGroup : IsTopologicalAddGroup V
  instContinuousSMul : ContinuousSMul ℂ V
  instT2Space : T2Space V
  instPolynormableSpace : PolynormableSpace ℂ V
  /-- The factored central charge lands in `V`. -/
  mem_charge : ∀ σ : NumericalStabilityCondition C χ,
    ConnectedComponents.mk σ = cc → σ.factors.choose ∈ V
  /-- The factored central charge map is a local homeomorphism into `V`. -/
  isLocalHomeomorph :
    @IsLocalHomeomorph (NumericalComponent C χ cc) V inferInstance instTopologicalSpace
      (fun ⟨σ, hσ⟩ ↦ ⟨σ.factors.choose, mem_charge σ hσ⟩)

attribute [instance] NumericalComponentTopologicalLinearLocalModel.instTopologicalSpace
attribute [instance] NumericalComponentTopologicalLinearLocalModel.instIsTopologicalAddGroup
attribute [instance] NumericalComponentTopologicalLinearLocalModel.instContinuousSMul
attribute [instance] NumericalComponentTopologicalLinearLocalModel.instT2Space
attribute [instance] NumericalComponentTopologicalLinearLocalModel.instPolynormableSpace

/-- The full strengthened Corollary 1.3 package: local-homeomorphism data plus finite
dimensionality. -/
structure NumericalComponentTopologicalLinearModel (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (NumericalStabilityCondition C χ))
    extends NumericalComponentTopologicalLinearLocalModel C χ cc where
  instFiniteDimensional : FiniteDimensional ℂ V

attribute [instance] NumericalComponentTopologicalLinearModel.instFiniteDimensional

namespace NumericalComponentTopologicalLinearLocalModel

variable {C} {χ : K₀ C →+ K₀ C →+ ℤ}
variable {cc : ConnectedComponents (NumericalStabilityCondition C χ)}

/-- The local-homeomorphism chart map associated to a topological linear local model. -/
def chargeMap (M : NumericalComponentTopologicalLinearLocalModel C χ cc) :
    NumericalComponent C χ cc → M.V :=
  fun ⟨σ, hσ⟩ ↦ ⟨σ.factors.choose, M.mem_charge σ hσ⟩

/-- Numerical finiteness should imply that the numerical charge space is finite-dimensional over
`ℂ`. This is the algebraic input needed to upgrade a local linear model to the full
Corollary 1.3 package. -/
theorem numericalChargeSpace_finiteDimensional (χ : K₀ C →+ K₀ C →+ ℤ)
    [NumericallyFinite C χ] :
    FiniteDimensional ℂ (NumericalChargeSpace C χ) := by
  sorry

/-- Upgrade a local linear model to a full topological linear model once the ambient numerical
charge space is known to be finite-dimensional. -/
noncomputable def toTopologicalLinearModel (M : NumericalComponentTopologicalLinearLocalModel C χ cc)
    [FiniteDimensional ℂ (NumericalChargeSpace C χ)] :
    NumericalComponentTopologicalLinearModel C χ cc where
  toNumericalComponentTopologicalLinearLocalModel := M
  instFiniteDimensional := inferInstance

end NumericalComponentTopologicalLinearLocalModel

namespace NumericalComponentTopologicalLinearModel

variable {C} {χ : K₀ C →+ K₀ C →+ ℤ}
variable {cc : ConnectedComponents (NumericalStabilityCondition C χ)}

/-- The local-homeomorphism chart map associated to a topological linear model. -/
def chargeMap (M : NumericalComponentTopologicalLinearModel C χ cc) :
    NumericalComponent C χ cc → M.V :=
  M.toNumericalComponentTopologicalLinearLocalModel.chargeMap

/-- Replace the abstract topological complex vector space `V` by a chosen finite-dimensional
normed complex model space. Proving this should make the manifold step for Corollary 1.3
purely formal. -/
theorem exists_normedComplexModel (M : NumericalComponentTopologicalLinearModel C χ cc) :
    ∃ n : ℕ, ∃ f : NumericalComponent C χ cc → Fin n → ℂ,
      IsLocalHomeomorph f := by
  let e : M.V ≃L[ℂ] (Fin (Module.finrank ℂ M.V) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨Module.finrank ℂ M.V, fun x => e (M.chargeMap x), ?_⟩
  simpa [chargeMap, NumericalComponentTopologicalLinearLocalModel.chargeMap] using
    e.toHomeomorph.isLocalHomeomorph.comp M.isLocalHomeomorph

end NumericalComponentTopologicalLinearModel

variable (k : Type w) [Field k]

/-- The local-homeomorphism part of Corollary 1.3, before using numerical finiteness to promote
the target to a finite-dimensional complex vector space. -/
noncomputable def bridgelandCorollary_1_3_localLinearModel [Linear k C] [IsFiniteType k C]
    [EulerFormDescends k C] (hnum : NumericallyFinite C (eulerForm k C))
    (cc : ConnectedComponents (NumericalStabilityCondition C (eulerForm k C))) :
    NumericalComponentTopologicalLinearLocalModel C (eulerForm k C) cc := by
  sorry

/-- A strengthened, theorem-shaped version of Corollary 1.3. This is the numerical analogue of
the stronger form Theorem 1.2 should eventually export. -/
noncomputable def bridgelandCorollary_1_3_topologicalLinearModel [Linear k C] [IsFiniteType k C]
    [EulerFormDescends k C] (hnum : NumericallyFinite C (eulerForm k C))
    (cc : ConnectedComponents (NumericalStabilityCondition C (eulerForm k C))) :
    NumericalComponentTopologicalLinearModel C (eulerForm k C) cc := by
  letI : FiniteDimensional ℂ (NumericalChargeSpace C (eulerForm k C)) :=
    NumericalComponentTopologicalLinearLocalModel.numericalChargeSpace_finiteDimensional
      (C := C) (χ := eulerForm k C)
  exact
    (bridgelandCorollary_1_3_localLinearModel (C := C) (k := k) hnum cc).toTopologicalLinearModel

/-- A generic manifold-construction theorem for complex local homeomorphisms into a normed model
space. The genuinely nontrivial step is to build a charted space whose transition maps are
restrictions of the identity. -/
theorem exists_chartedSpace_and_hasGroupoid_idRestr_of_isLocalHomeomorph_to_complex_model
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
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
  have hchart_eq : (chartAt y : M → E) = chartAt x := by
    exact (chartAt_eq y).symm.trans (chartAt_eq x)
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

/-- A mechanical-assembly version of Bridgeland's Corollary 1.3: once the topological linear local
model and the generic manifold bridge are available, the complex-manifold conclusion should follow
without a large bespoke proof. -/
theorem bridgelandCorollary_1_3_complexManifold [Linear k C] [IsFiniteType k C]
    [EulerFormDescends k C] (hnum : NumericallyFinite C (eulerForm k C))
    (cc : ConnectedComponents (NumericalStabilityCondition C (eulerForm k C))) :
    ∃ n : ℕ,
      ∃ _ : ChartedSpace (Fin n → ℂ) (NumericalComponent C (eulerForm k C) cc),
      IsManifold (𝓘(ℂ, Fin n → ℂ)) (⊤ : WithTop ℕ∞)
        (NumericalComponent C (eulerForm k C) cc) := by
  let M := bridgelandCorollary_1_3_topologicalLinearModel (C := C) (k := k) hnum cc
  rcases M.exists_normedComplexModel with ⟨n, f, hf⟩
  rcases exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model f hf with
    ⟨_inst4, hmanifold⟩
  exact ⟨n, _inst4, hmanifold⟩

end CategoryTheory.Triangulated
