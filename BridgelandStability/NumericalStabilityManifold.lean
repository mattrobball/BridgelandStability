/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.LocalHomeomorphism
public import BridgelandStability.NumericalStability.Basic
public import BridgelandStability.EulerForm.Basic
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Numerical Stability Manifolds

Bridgeland's Corollary 1.3: each connected component of `Stab_Λ(D)` is a
complex manifold of dimension `rk(Λ)`.

The proof is direct assembly from the generalized `ComponentTopologicalLinearLocalModel`:
1. `V(Σ) ⊆ Hom(Λ, ℂ)` is finite-dimensional (because `Λ` has finite rank).
2. The charge map `σ ↦ σ.Z` is a local homeomorphism into `V(Σ)`.
3. Apply the generic manifold construction.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped Manifold Topology

universe w v u u'

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
@[informal "Corollary 1.3" "class-map generalization; manifold consequence only" complete]
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
@[informal "Corollary 1.3" "complex manifold conclusion only; local homeomorphism is in componentTopologicalLinearLocalModel" complete]
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
        (NumericalComponent (k := k) C cc) := by
  haveI : Fact (Function.Surjective (numericalQuotientMap k C)) :=
    ⟨QuotientAddGroup.mk'_surjective (eulerFormRad k C)⟩
  simpa [NumericalComponent] using
    StabilityCondition.WithClassMap.existsComplexManifoldOnConnectedComponent C cc

end CategoryTheory.Triangulated
