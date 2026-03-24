module

import Architect
import BridgelandStability.Deformation.Theorem
import BridgelandStability.EulerForm.Basic
import BridgelandStability.NumericalStabilityManifold
import BridgelandStability.StabilityCondition.LocalHomeomorphism
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Blueprint-facing statements for BridgelandStability

This module provides a small curated collection of theorem wrappers for the
blueprint and project page. The goal is to expose the main mathematical results
without annotating the entire implementation tree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped Manifold

universe w v u u'

namespace CategoryTheory.Triangulated.BridgelandBlueprint

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- The public theorem package for Bridgeland's Theorem 1.2. -/
@[blueprint "thm:bridgeland-1-2"
  (statement := /-- **Bridgeland's Theorem 1.2.** For each connected component
  `Σ ⊂ Stab(D)` there is a linear subspace `V(Σ) ⊂ Hom_ℤ(K_0(D), ℂ)` and a local
  homeomorphism `Z : Σ → V(Σ)` sending a stability condition to its central
  charge. -/)
  (proof := /-- This is the assembled formal proof of the ordinary `v = id`
  case in the library. -/)]
theorem ordinary_central_charge_is_local_homeomorph_on_connected_components :
    StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents C := by
  simpa using
    (StabilityCondition.centralChargeIsLocalHomeomorphOnConnectedComponents (C := C))

/-- The generic class-map manifold theorem used for the numerical specialization. -/
@[blueprint "thm:class-map-manifold"
  (statement := /-- For a surjective class map `v : K_0(D) → \Lambda` to a finitely
  generated abelian group, each connected component of the corresponding space of
  stability conditions carries the structure of a finite-dimensional complex
  manifold. -/)
  (proof := /-- This is the public class-map-first manifold theorem exposed by the
  library. -/)]
theorem class_map_component_exists_complex_manifold
    {Λ : Type u'} [AddCommGroup Λ] [AddGroup.FG Λ]
    (v₀ : K₀ C →+ Λ) (hv₀ : Function.Surjective v₀)
    (cc : StabilityCondition.WithClassMap.ComponentIndex C v₀) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (StabilityCondition.WithClassMap.Component C v₀ cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (StabilityCondition.WithClassMap.Component C v₀ cc) := by
  simpa using
    (StabilityCondition.WithClassMap.existsComplexManifoldOnConnectedComponent
      (C := C) (v := v₀) hv₀ cc)

/-- The complex-manifold conclusion of Bridgeland's Corollary 1.3. -/
@[blueprint "thm:bridgeland-1-3"
  (statement := /-- **Bridgeland's Corollary 1.3.** Suppose `D` is numerically
  finite. Then each connected component `Σ ⊂ Stab_N(D)` is a finite-dimensional
  complex manifold. -/)
  (proof := /-- This is the canonical numerical specialization of the generic
  class-map manifold theorem. -/)
  (proofUses := [class_map_component_exists_complex_manifold])]
theorem numerical_component_exists_complex_manifold
    [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    [NumericallyFinite k C]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (NumericalComponent (k := k) C cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (NumericalComponent (k := k) C cc) := by
  let hsurj : Function.Surjective (numericalQuotientMap k C) :=
    QuotientAddGroup.mk'_surjective (eulerFormRad k C)
  simpa [NumericalComponent] using
    (class_map_component_exists_complex_manifold (C := C)
      (v₀ := numericalQuotientMap k C) hsurj cc)

/-- The deformation theorem that drives the local-homeomorphism argument. -/
@[blueprint "thm:bridgeland-7-1"
  (statement := /-- **Bridgeland's Theorem 7.1.** If `‖W - Z‖_σ < \sin(\pi ε)`,
  then there exists a locally finite stability condition `τ = (W, Q)` with
  `d(P, Q) < ε`. -/)
  (proof := /-- The library proves this by constructing the canonical deformed
  slicing and shrinking `ε` slightly to fit the strict sine bound. -/)]
theorem deformation_exists_eq_Z_and_slicingDist_lt_of_stabSeminorm_lt_sin
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by grind))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    ∃ (τ : StabilityCondition C), τ.Z = W ∧
      slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε := by
  simpa using
    (StabilityCondition.exists_eq_Z_and_slicingDist_lt_of_stabSeminorm_lt_sin
      (C := C) σ W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin)

end CategoryTheory.Triangulated.BridgelandBlueprint
