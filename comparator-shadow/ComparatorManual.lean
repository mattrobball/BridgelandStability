import VersoManual
import BridgelandStability.NumericalStabilityManifold
import ComparatorManualSupport

open Verso.Genre Manual
open Verso.Code.External
open ComparatorManualSupport

set_option pp.rawOnError true
set_option maxHeartbeats 2000000
set_option verso.exampleProject "."

#doc (Manual) "BridgelandStability Comparator Manual" =>
%%%
htmlSplit := .never
%%%

# Overview

![comparator](badge/comparator.svg)

Repository: [https://github.com/mattrobball/BridgelandStability](https://github.com/mattrobball/BridgelandStability)

This manual presents the comparator view of the formalization.
It was generated mechanically from the trusted formalization base walk rooted at the comparator target theorem in `BridgelandStability.NumericalStabilityManifold`.
The formalization covers *57* declarations across *11* modules.

## `CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent`
%%%
tag := "shadow-entry-bridgelandstability-numericalstabilitymanifold-categorytheory-triangulated-numericalstabilitycondition-existscomplexmanifoldonconnectedcomponent-198-218"
%%%

`Theorem` | `BridgelandStability.NumericalStabilityManifold` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/NumericalStabilityManifold.lean#L198) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: existsComplexManifoldOnConnectedComponent&body=**Declaration:** `CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent`%0A**Module:** `BridgelandStability.NumericalStabilityManifold`%0A**Source:** BridgelandStability/NumericalStabilityManifold.lean:198%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent
```

```collapsibleModule (module := BridgelandStability.NumericalStabilityManifold) (anchor := CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent)
/-- **Bridgeland's Corollary 1.3** for numerical stability conditions. Each connected
component of `Stab_N(D)` is a complex manifold of dimension `rk(N(D))`.

This is a specialization of the generic class-map theorem to
`v = numericalQuotientMap k C`, which is surjective by definition. -/
@[informal "Corollary 1.3" "complex manifold conclusion only; local homeomorphism is in componentTopologicalLinearLocalModel"]
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
```

## Declaration census

Every constant in the transitive closure of the target theorem's type.
Auxiliary declarations are resolved to their user-facing parent.

*126* raw constants: *55* user-facing, *71* auxiliary.

 * `K0Presentation` — user
 * `CategoryTheory.IsStrict` — user
 * `CategoryTheory.IsStrictArtinianObject` — user
 * `CategoryTheory.IsStrictMono` — user
 * `CategoryTheory.IsStrictNoetherianObject` — user
 * `CategoryTheory.StrictSubobject` — user
 * `CategoryTheory.isStrictArtinianObject` — user
 * `CategoryTheory.isStrictNoetherianObject` — user
 * `K0Presentation.IsAdditive` — user
 * `K0Presentation.K0` — user
 * `K0Presentation.lift` — user
 * `K0Presentation.mk` — constructor → `K0Presentation`
 * `K0Presentation.obj₁` — projection → `K0Presentation`
 * `K0Presentation.obj₂` — projection → `K0Presentation`
 * `K0Presentation.obj₃` — projection → `K0Presentation`
 * `K0Presentation.subgroup` — user
 * `CategoryTheory.IsStrictMono.mk` — constructor → `CategoryTheory.IsStrictMono`
 * `CategoryTheory.Subobject.IsStrict` — user
 * `CategoryTheory.Triangulated.HNFiltration` — user
 * `CategoryTheory.Triangulated.IsFiniteType` — user
 * `CategoryTheory.Triangulated.IsTriangleAdditive` — user
 * `CategoryTheory.Triangulated.K₀` — user
 * `CategoryTheory.Triangulated.NumericalComponent` — user
 * `CategoryTheory.Triangulated.NumericalK₀` — user
 * `CategoryTheory.Triangulated.NumericallyFinite` — user
 * `CategoryTheory.Triangulated.PostnikovTower` — user
 * `CategoryTheory.Triangulated.Slicing` — user
 * `CategoryTheory.Triangulated.basisNhd` — user
 * `CategoryTheory.Triangulated.cl` — user
 * `CategoryTheory.Triangulated.eulerForm` — user
 * `CategoryTheory.Triangulated.eulerFormInner` — user
 * `CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive` — user
 * `CategoryTheory.Triangulated.eulerFormObj` — user
 * `CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive` — user
 * `CategoryTheory.Triangulated.eulerFormRad` — user
 * `CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive` — user
 * `CategoryTheory.Triangulated.numericalQuotientMap` — user
 * `CategoryTheory.Triangulated.slicingDist` — user
 * `CategoryTheory.Triangulated.stabSeminorm` — user
 * `CategoryTheory.Triangulated.trianglePresentation` — user
 * `K0Presentation.IsAdditive.mk` — constructor → `K0Presentation.IsAdditive`
 * `K0Presentation.instAddCommGroupK0._proof_1` — internal → `K0Presentation.instAddCommGroupK0`
 * `K0Presentation.lift._proof_1` — internal → `K0Presentation.lift`
 * `CategoryTheory.Subobject.IsStrict._proof_1` — internal → `CategoryTheory.Subobject.IsStrict`
 * `CategoryTheory.Subobject.IsStrict._proof_2` — internal → `CategoryTheory.Subobject.IsStrict`
 * `CategoryTheory.Subobject.IsStrict._proof_3` — internal → `CategoryTheory.Subobject.IsStrict`
 * `CategoryTheory.Subobject.IsStrict._proof_4` — internal → `CategoryTheory.Subobject.IsStrict`
 * `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first` — user
 * `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last` — user
 * `CategoryTheory.Triangulated.HNFiltration.mk` — constructor → `CategoryTheory.Triangulated.HNFiltration`
 * `CategoryTheory.Triangulated.HNFiltration.toPostnikovTower` — projection → `CategoryTheory.Triangulated.HNFiltration`
 * `CategoryTheory.Triangulated.HNFiltration.φ` — projection → `CategoryTheory.Triangulated.HNFiltration`
 * `CategoryTheory.Triangulated.IsFiniteType.mk` — constructor → `CategoryTheory.Triangulated.IsFiniteType`
 * `CategoryTheory.Triangulated.IsTriangleAdditive.mk` — constructor → `CategoryTheory.Triangulated.IsTriangleAdditive`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup` — user
 * `CategoryTheory.Triangulated.K₀.lift` — user
 * `CategoryTheory.Triangulated.K₀.of` — user
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup` — user
 * `CategoryTheory.Triangulated.NumericallyFinite.mk` — constructor → `CategoryTheory.Triangulated.NumericallyFinite`
 * `CategoryTheory.Triangulated.PostnikovTower._proof_1` — internal → `CategoryTheory.Triangulated.PostnikovTower`
 * `CategoryTheory.Triangulated.PostnikovTower._proof_3` — internal → `CategoryTheory.Triangulated.PostnikovTower`
 * `CategoryTheory.Triangulated.PostnikovTower.factor` — user
 * `CategoryTheory.Triangulated.PostnikovTower.mk` — constructor → `CategoryTheory.Triangulated.PostnikovTower`
 * `CategoryTheory.Triangulated.PostnikovTower.n` — projection → `CategoryTheory.Triangulated.PostnikovTower`
 * `CategoryTheory.Triangulated.PostnikovTower.triangle` — projection → `CategoryTheory.Triangulated.PostnikovTower`
 * `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap` — user
 * `CategoryTheory.Triangulated.Slicing.IntervalCat` — user
 * `CategoryTheory.Triangulated.Slicing.IsLocallyFinite` — user
 * `CategoryTheory.Triangulated.Slicing.P` — projection → `CategoryTheory.Triangulated.Slicing`
 * `CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels` — user
 * `CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels` — user
 * `CategoryTheory.Triangulated.Slicing.intervalProp` — user
 * `CategoryTheory.Triangulated.Slicing.mk` — constructor → `CategoryTheory.Triangulated.Slicing`
 * `CategoryTheory.Triangulated.Slicing.phiMinus` — user
 * `CategoryTheory.Triangulated.Slicing.phiPlus` — user
 * `CategoryTheory.Triangulated.StabilityCondition.WithClassMap` — user
 * `CategoryTheory.Triangulated.numericalQuotientMap._proof_1` — internal → `CategoryTheory.Triangulated.numericalQuotientMap`
 * `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last._proof_1` — internal → `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._aux_1` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._aux_12` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._aux_14` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._aux_17` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._aux_4` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._aux_8` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_10` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_11` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_16` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_19` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_20` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_21` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_22` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_23` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_3` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_6` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.K₀.instAddCommGroup._proof_7` — internal → `CategoryTheory.Triangulated.K₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._aux_1` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._aux_12` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._aux_14` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._aux_17` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._aux_4` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._aux_8` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_10` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_11` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_16` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_19` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_20` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_21` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_22` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_23` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_3` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_6` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup._proof_7` — internal → `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
 * `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.Z` — projection → `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap`
 * `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge` — user
 * `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.mk` — constructor → `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap`
 * `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.slicing` — projection → `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap`
 * `CategoryTheory.Triangulated.Slicing.IsLocallyFinite.mk` — constructor → `CategoryTheory.Triangulated.Slicing.IsLocallyFinite`
 * `CategoryTheory.Triangulated.Slicing.phiMinus._proof_1` — internal → `CategoryTheory.Triangulated.Slicing.phiMinus`
 * `CategoryTheory.Triangulated.Slicing.phiMinus._proof_2` — internal → `CategoryTheory.Triangulated.Slicing.phiMinus`
 * `CategoryTheory.Triangulated.Slicing.phiPlus._proof_1` — internal → `CategoryTheory.Triangulated.Slicing.phiPlus`
 * `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component` — user
 * `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex` — user
 * `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.mk` — constructor → `CategoryTheory.Triangulated.StabilityCondition.WithClassMap`
 * `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.toWithClassMap` — projection → `CategoryTheory.Triangulated.StabilityCondition.WithClassMap`
 * `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace` — user
 * `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace._proof_1` — internal → `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace`

## Dependency graph

Click a node to navigate to its declaration.

```graphEmbed
{"edges":[{"source":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","target":"CategoryTheory.Triangulated.NumericalComponent"},{"source":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","target":"CategoryTheory.Triangulated.NumericalK₀"},{"source":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","target":"CategoryTheory.Triangulated.NumericallyFinite"},{"source":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","target":"CategoryTheory.Triangulated.numericalQuotientMap"},{"source":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","target":"CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap"},{"source":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex"},{"source":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace"},{"source":"CategoryTheory.Triangulated.PostnikovTower.factor","target":"CategoryTheory.Triangulated.PostnikovTower"},{"source":"CategoryTheory.Triangulated.trianglePresentation","target":"K0Presentation"},{"source":"K0Presentation.subgroup","target":"K0Presentation"},{"source":"K0Presentation.IsAdditive","target":"K0Presentation"},{"source":"CategoryTheory.IsStrictMono","target":"CategoryTheory.IsStrict"},{"source":"CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive","target":"CategoryTheory.Triangulated.IsTriangleAdditive"},{"source":"CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive","target":"CategoryTheory.Triangulated.eulerFormObj"},{"source":"CategoryTheory.Triangulated.HNFiltration","target":"CategoryTheory.Triangulated.PostnikovTower"},{"source":"CategoryTheory.Triangulated.HNFiltration","target":"CategoryTheory.Triangulated.PostnikovTower.factor"},{"source":"CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive","target":"K0Presentation.IsAdditive"},{"source":"CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive","target":"CategoryTheory.Triangulated.IsTriangleAdditive"},{"source":"CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive","target":"CategoryTheory.Triangulated.trianglePresentation"},{"source":"K0Presentation.K0","target":"K0Presentation"},{"source":"K0Presentation.K0","target":"K0Presentation.subgroup"},{"source":"CategoryTheory.Subobject.IsStrict","target":"CategoryTheory.IsStrictMono"},{"source":"CategoryTheory.Triangulated.Slicing","target":"CategoryTheory.Triangulated.HNFiltration"},{"source":"CategoryTheory.Triangulated.K₀","target":"K0Presentation.K0"},{"source":"CategoryTheory.Triangulated.K₀","target":"CategoryTheory.Triangulated.trianglePresentation"},{"source":"K0Presentation.instAddCommGroupK0","target":"K0Presentation"},{"source":"K0Presentation.instAddCommGroupK0","target":"K0Presentation.K0"},{"source":"K0Presentation.instAddCommGroupK0","target":"K0Presentation.subgroup"},{"source":"K0Presentation.lift","target":"K0Presentation"},{"source":"K0Presentation.lift","target":"K0Presentation.IsAdditive"},{"source":"K0Presentation.lift","target":"K0Presentation.K0"},{"source":"K0Presentation.lift","target":"K0Presentation.subgroup"},{"source":"CategoryTheory.StrictSubobject","target":"CategoryTheory.Subobject.IsStrict"},{"source":"CategoryTheory.Triangulated.Slicing.intervalProp","target":"CategoryTheory.Triangulated.HNFiltration"},{"source":"CategoryTheory.Triangulated.Slicing.intervalProp","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first","target":"CategoryTheory.Triangulated.HNFiltration"},{"source":"CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last","target":"CategoryTheory.Triangulated.HNFiltration"},{"source":"CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.K₀.instAddCommGroup","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.K₀.of","target":"K0Presentation.subgroup"},{"source":"CategoryTheory.Triangulated.K₀.of","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.K₀.of","target":"CategoryTheory.Triangulated.trianglePresentation"},{"source":"CategoryTheory.isStrictArtinianObject","target":"CategoryTheory.StrictSubobject"},{"source":"CategoryTheory.isStrictArtinianObject","target":"CategoryTheory.Subobject.IsStrict"},{"source":"CategoryTheory.isStrictNoetherianObject","target":"CategoryTheory.StrictSubobject"},{"source":"CategoryTheory.isStrictNoetherianObject","target":"CategoryTheory.Subobject.IsStrict"},{"source":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap","target":"CategoryTheory.Triangulated.K₀.of"},{"source":"CategoryTheory.Triangulated.Slicing.phiPlus","target":"CategoryTheory.Triangulated.HNFiltration"},{"source":"CategoryTheory.Triangulated.Slicing.phiPlus","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.Slicing.phiPlus","target":"CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first"},{"source":"CategoryTheory.Triangulated.Slicing.phiMinus","target":"CategoryTheory.Triangulated.HNFiltration"},{"source":"CategoryTheory.Triangulated.Slicing.phiMinus","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.Slicing.phiMinus","target":"CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last"},{"source":"CategoryTheory.Triangulated.K₀.lift","target":"K0Presentation.lift"},{"source":"CategoryTheory.Triangulated.K₀.lift","target":"CategoryTheory.Triangulated.IsTriangleAdditive"},{"source":"CategoryTheory.Triangulated.K₀.lift","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.K₀.lift","target":"CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive"},{"source":"CategoryTheory.Triangulated.K₀.lift","target":"CategoryTheory.Triangulated.trianglePresentation"},{"source":"CategoryTheory.Triangulated.K₀.lift","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.cl","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.cl","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.cl","target":"CategoryTheory.Triangulated.K₀.of"},{"source":"CategoryTheory.Triangulated.Slicing.IntervalCat","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.Slicing.IntervalCat","target":"CategoryTheory.Triangulated.Slicing.intervalProp"},{"source":"CategoryTheory.IsStrictArtinianObject","target":"CategoryTheory.isStrictArtinianObject"},{"source":"CategoryTheory.IsStrictNoetherianObject","target":"CategoryTheory.isStrictNoetherianObject"},{"source":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge","target":"CategoryTheory.Triangulated.cl"},{"source":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge","target":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap"},{"source":"CategoryTheory.Triangulated.slicingDist","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.slicingDist","target":"CategoryTheory.Triangulated.Slicing.phiMinus"},{"source":"CategoryTheory.Triangulated.slicingDist","target":"CategoryTheory.Triangulated.Slicing.phiPlus"},{"source":"CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels","target":"CategoryTheory.Triangulated.Slicing.IntervalCat"},{"source":"CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels","target":"CategoryTheory.Triangulated.Slicing.intervalProp"},{"source":"CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels","target":"CategoryTheory.Triangulated.Slicing.IntervalCat"},{"source":"CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels","target":"CategoryTheory.Triangulated.Slicing.intervalProp"},{"source":"CategoryTheory.Triangulated.eulerFormInner","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.eulerFormInner","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.eulerFormInner","target":"CategoryTheory.Triangulated.eulerFormObj"},{"source":"CategoryTheory.Triangulated.eulerFormInner","target":"CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive"},{"source":"CategoryTheory.Triangulated.eulerFormInner","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.eulerFormInner","target":"CategoryTheory.Triangulated.K₀.lift"},{"source":"CategoryTheory.Triangulated.Slicing.IsLocallyFinite","target":"CategoryTheory.IsStrictArtinianObject"},{"source":"CategoryTheory.Triangulated.Slicing.IsLocallyFinite","target":"CategoryTheory.IsStrictNoetherianObject"},{"source":"CategoryTheory.Triangulated.Slicing.IsLocallyFinite","target":"CategoryTheory.Triangulated.Slicing"},{"source":"CategoryTheory.Triangulated.Slicing.IsLocallyFinite","target":"CategoryTheory.Triangulated.Slicing.IntervalCat"},{"source":"CategoryTheory.Triangulated.Slicing.IsLocallyFinite","target":"CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels"},{"source":"CategoryTheory.Triangulated.Slicing.IsLocallyFinite","target":"CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels"},{"source":"CategoryTheory.Triangulated.Slicing.IsLocallyFinite","target":"CategoryTheory.Triangulated.Slicing.intervalProp"},{"source":"CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive","target":"CategoryTheory.Triangulated.IsTriangleAdditive"},{"source":"CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive","target":"CategoryTheory.Triangulated.eulerFormInner"},{"source":"CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap","target":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap","target":"CategoryTheory.Triangulated.Slicing.IsLocallyFinite"},{"source":"CategoryTheory.Triangulated.eulerForm","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.eulerForm","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.eulerForm","target":"CategoryTheory.Triangulated.eulerFormInner"},{"source":"CategoryTheory.Triangulated.eulerForm","target":"CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive"},{"source":"CategoryTheory.Triangulated.eulerForm","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.eulerForm","target":"CategoryTheory.Triangulated.K₀.lift"},{"source":"CategoryTheory.Triangulated.stabSeminorm","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.stabSeminorm","target":"CategoryTheory.Triangulated.cl"},{"source":"CategoryTheory.Triangulated.stabSeminorm","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.stabSeminorm","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap"},{"source":"CategoryTheory.Triangulated.stabSeminorm","target":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge"},{"source":"CategoryTheory.Triangulated.eulerFormRad","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.eulerFormRad","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.eulerFormRad","target":"CategoryTheory.Triangulated.eulerForm"},{"source":"CategoryTheory.Triangulated.eulerFormRad","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.basisNhd","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.basisNhd","target":"CategoryTheory.Triangulated.slicingDist"},{"source":"CategoryTheory.Triangulated.basisNhd","target":"CategoryTheory.Triangulated.stabSeminorm"},{"source":"CategoryTheory.Triangulated.basisNhd","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.basisNhd","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap"},{"source":"CategoryTheory.Triangulated.NumericalK₀","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.NumericalK₀","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.NumericalK₀","target":"CategoryTheory.Triangulated.eulerFormRad"},{"source":"CategoryTheory.Triangulated.NumericalK₀","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace","target":"CategoryTheory.Triangulated.basisNhd"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap"},{"source":"CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup","target":"CategoryTheory.Triangulated.NumericalK₀"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace"},{"source":"CategoryTheory.Triangulated.numericalQuotientMap","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.numericalQuotientMap","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.numericalQuotientMap","target":"CategoryTheory.Triangulated.NumericalK₀"},{"source":"CategoryTheory.Triangulated.numericalQuotientMap","target":"CategoryTheory.Triangulated.eulerFormRad"},{"source":"CategoryTheory.Triangulated.numericalQuotientMap","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.numericalQuotientMap","target":"CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.NumericallyFinite","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.NumericallyFinite","target":"CategoryTheory.Triangulated.NumericalK₀"},{"source":"CategoryTheory.Triangulated.NumericallyFinite","target":"CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component","target":"CategoryTheory.Triangulated.K₀"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component","target":"CategoryTheory.Triangulated.K₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex"},{"source":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace"},{"source":"CategoryTheory.Triangulated.NumericalComponent","target":"CategoryTheory.Triangulated.IsFiniteType"},{"source":"CategoryTheory.Triangulated.NumericalComponent","target":"CategoryTheory.Triangulated.NumericalK₀"},{"source":"CategoryTheory.Triangulated.NumericalComponent","target":"CategoryTheory.Triangulated.numericalQuotientMap"},{"source":"CategoryTheory.Triangulated.NumericalComponent","target":"CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup"},{"source":"CategoryTheory.Triangulated.NumericalComponent","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component"},{"source":"CategoryTheory.Triangulated.NumericalComponent","target":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex"}],"nodes":[{"groupKey":"BridgelandStability.NumericalStabilityManifold","href":"numericalstabilitymanifold/","id":"CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent","kind":"Theorem","label":"existsComplexManifoldOnConnectedComponent","moduleName":"BridgelandStability.NumericalStabilityManifold","status":"clean"},{"groupKey":"BridgelandStability.PostnikovTower.Defs","href":"postnikovtower-defs/","id":"CategoryTheory.Triangulated.PostnikovTower","kind":"Structure","label":"PostnikovTower","moduleName":"BridgelandStability.PostnikovTower.Defs","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Basic","href":"grothendieckgroup-basic/","id":"CategoryTheory.Triangulated.IsTriangleAdditive","kind":"Structure","label":"IsTriangleAdditive","moduleName":"BridgelandStability.GrothendieckGroup.Basic","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Defs","href":"grothendieckgroup-defs/","id":"K0Presentation","kind":"Structure","label":"K0Presentation","moduleName":"BridgelandStability.GrothendieckGroup.Defs","status":"clean"},{"groupKey":"BridgelandStability.QuasiAbelian.Basic","href":"quasiabelian-basic/","id":"CategoryTheory.IsStrict","kind":"Definition","label":"IsStrict","moduleName":"BridgelandStability.QuasiAbelian.Basic","status":"clean"},{"groupKey":"BridgelandStability.NumericalStability.Defs","href":"numericalstability-defs/","id":"CategoryTheory.Triangulated.IsFiniteType","kind":"Structure","label":"IsFiniteType","moduleName":"BridgelandStability.NumericalStability.Defs","status":"clean"},{"groupKey":"BridgelandStability.NumericalStability.Defs","href":"numericalstability-defs/","id":"CategoryTheory.Triangulated.eulerFormObj","kind":"Definition","label":"eulerFormObj","moduleName":"BridgelandStability.NumericalStability.Defs","status":"clean"},{"groupKey":"BridgelandStability.PostnikovTower.Defs","href":"postnikovtower-defs/","id":"CategoryTheory.Triangulated.PostnikovTower.factor","kind":"Definition","label":"factor","moduleName":"BridgelandStability.PostnikovTower.Defs","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Basic","href":"grothendieckgroup-basic/","id":"CategoryTheory.Triangulated.trianglePresentation","kind":"Definition","label":"trianglePresentation","moduleName":"BridgelandStability.GrothendieckGroup.Basic","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Defs","href":"grothendieckgroup-defs/","id":"K0Presentation.subgroup","kind":"Definition","label":"subgroup","moduleName":"BridgelandStability.GrothendieckGroup.Defs","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Defs","href":"grothendieckgroup-defs/","id":"K0Presentation.IsAdditive","kind":"Structure","label":"IsAdditive","moduleName":"BridgelandStability.GrothendieckGroup.Defs","status":"clean"},{"groupKey":"BridgelandStability.QuasiAbelian.Basic","href":"quasiabelian-basic/","id":"CategoryTheory.IsStrictMono","kind":"Structure","label":"IsStrictMono","moduleName":"BridgelandStability.QuasiAbelian.Basic","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive","kind":"Theorem","label":"eulerFormObj_contravariant_triangleAdditive","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"},{"groupKey":"BridgelandStability.Slicing.Defs","href":"slicing-defs/","id":"CategoryTheory.Triangulated.HNFiltration","kind":"Structure","label":"HNFiltration","moduleName":"BridgelandStability.Slicing.Defs","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Basic","href":"grothendieckgroup-basic/","id":"CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive","kind":"Theorem","label":"instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive","moduleName":"BridgelandStability.GrothendieckGroup.Basic","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Defs","href":"grothendieckgroup-defs/","id":"K0Presentation.K0","kind":"Definition","label":"K0","moduleName":"BridgelandStability.GrothendieckGroup.Defs","status":"clean"},{"groupKey":"BridgelandStability.QuasiAbelian.Basic","href":"quasiabelian-basic/","id":"CategoryTheory.Subobject.IsStrict","kind":"Definition","label":"IsStrict","moduleName":"BridgelandStability.QuasiAbelian.Basic","status":"clean"},{"groupKey":"BridgelandStability.Slicing.Defs","href":"slicing-defs/","id":"CategoryTheory.Triangulated.Slicing","kind":"Structure","label":"Slicing","moduleName":"BridgelandStability.Slicing.Defs","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Basic","href":"grothendieckgroup-basic/","id":"CategoryTheory.Triangulated.K₀","kind":"Definition","label":"K₀","moduleName":"BridgelandStability.GrothendieckGroup.Basic","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Defs","href":"grothendieckgroup-defs/","id":"K0Presentation.instAddCommGroupK0","kind":"Definition","label":"instAddCommGroupK0","moduleName":"BridgelandStability.GrothendieckGroup.Defs","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Defs","href":"grothendieckgroup-defs/","id":"K0Presentation.lift","kind":"Definition","label":"lift","moduleName":"BridgelandStability.GrothendieckGroup.Defs","status":"clean"},{"groupKey":"BridgelandStability.QuasiAbelian.Basic","href":"quasiabelian-basic/","id":"CategoryTheory.StrictSubobject","kind":"Definition","label":"StrictSubobject","moduleName":"BridgelandStability.QuasiAbelian.Basic","status":"clean"},{"groupKey":"BridgelandStability.Slicing.Defs","href":"slicing-defs/","id":"CategoryTheory.Triangulated.Slicing.intervalProp","kind":"Definition","label":"intervalProp","moduleName":"BridgelandStability.Slicing.Defs","status":"clean"},{"groupKey":"BridgelandStability.Slicing.Defs","href":"slicing-defs/","id":"CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first","kind":"Theorem","label":"exists_nonzero_first","moduleName":"BridgelandStability.Slicing.Defs","status":"clean"},{"groupKey":"BridgelandStability.Slicing.Defs","href":"slicing-defs/","id":"CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last","kind":"Theorem","label":"exists_nonzero_last","moduleName":"BridgelandStability.Slicing.Defs","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Basic","href":"grothendieckgroup-basic/","id":"CategoryTheory.Triangulated.K₀.instAddCommGroup","kind":"Definition","label":"instAddCommGroup","moduleName":"BridgelandStability.GrothendieckGroup.Basic","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Basic","href":"grothendieckgroup-basic/","id":"CategoryTheory.Triangulated.K₀.of","kind":"Definition","label":"of","moduleName":"BridgelandStability.GrothendieckGroup.Basic","status":"clean"},{"groupKey":"BridgelandStability.QuasiAbelian.Basic","href":"quasiabelian-basic/","id":"CategoryTheory.isStrictArtinianObject","kind":"Definition","label":"isStrictArtinianObject","moduleName":"BridgelandStability.QuasiAbelian.Basic","status":"clean"},{"groupKey":"BridgelandStability.QuasiAbelian.Basic","href":"quasiabelian-basic/","id":"CategoryTheory.isStrictNoetherianObject","kind":"Definition","label":"isStrictNoetherianObject","moduleName":"BridgelandStability.QuasiAbelian.Basic","status":"clean"},{"groupKey":"BridgelandStability.StabilityCondition.Defs","href":"stabilitycondition-defs/","id":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap","kind":"Structure","label":"WithClassMap","moduleName":"BridgelandStability.StabilityCondition.Defs","status":"clean"},{"groupKey":"BridgelandStability.Slicing.Defs","href":"slicing-defs/","id":"CategoryTheory.Triangulated.Slicing.phiPlus","kind":"Definition","label":"phiPlus","moduleName":"BridgelandStability.Slicing.Defs","status":"clean"},{"groupKey":"BridgelandStability.Slicing.Defs","href":"slicing-defs/","id":"CategoryTheory.Triangulated.Slicing.phiMinus","kind":"Definition","label":"phiMinus","moduleName":"BridgelandStability.Slicing.Defs","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Basic","href":"grothendieckgroup-basic/","id":"CategoryTheory.Triangulated.K₀.lift","kind":"Definition","label":"lift","moduleName":"BridgelandStability.GrothendieckGroup.Basic","status":"clean"},{"groupKey":"BridgelandStability.GrothendieckGroup.Basic","href":"grothendieckgroup-basic/","id":"CategoryTheory.Triangulated.cl","kind":"Definition","label":"cl","moduleName":"BridgelandStability.GrothendieckGroup.Basic","status":"clean"},{"groupKey":"BridgelandStability.IntervalCategory.Basic","href":"intervalcategory-basic/","id":"CategoryTheory.Triangulated.Slicing.IntervalCat","kind":"Definition","label":"IntervalCat","moduleName":"BridgelandStability.IntervalCategory.Basic","status":"clean"},{"groupKey":"BridgelandStability.QuasiAbelian.Basic","href":"quasiabelian-basic/","id":"CategoryTheory.IsStrictArtinianObject","kind":"Definition","label":"IsStrictArtinianObject","moduleName":"BridgelandStability.QuasiAbelian.Basic","status":"clean"},{"groupKey":"BridgelandStability.QuasiAbelian.Basic","href":"quasiabelian-basic/","id":"CategoryTheory.IsStrictNoetherianObject","kind":"Definition","label":"IsStrictNoetherianObject","moduleName":"BridgelandStability.QuasiAbelian.Basic","status":"clean"},{"groupKey":"BridgelandStability.StabilityCondition.Defs","href":"stabilitycondition-defs/","id":"CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge","kind":"Definition","label":"charge","moduleName":"BridgelandStability.StabilityCondition.Defs","status":"clean"},{"groupKey":"BridgelandStability.StabilityCondition.Defs","href":"stabilitycondition-defs/","id":"CategoryTheory.Triangulated.slicingDist","kind":"Definition","label":"slicingDist","moduleName":"BridgelandStability.StabilityCondition.Defs","status":"clean"},{"groupKey":"BridgelandStability.IntervalCategory.QuasiAbelian","href":"intervalcategory-quasiabelian/","id":"CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels","kind":"Theorem","label":"intervalCat_hasKernels","moduleName":"BridgelandStability.IntervalCategory.QuasiAbelian","status":"clean"},{"groupKey":"BridgelandStability.IntervalCategory.QuasiAbelian","href":"intervalcategory-quasiabelian/","id":"CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels","kind":"Theorem","label":"intervalCat_hasCokernels","moduleName":"BridgelandStability.IntervalCategory.QuasiAbelian","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.eulerFormInner","kind":"Definition","label":"eulerFormInner","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"},{"groupKey":"BridgelandStability.IntervalCategory.FiniteLength","href":"intervalcategory-finitelength/","id":"CategoryTheory.Triangulated.Slicing.IsLocallyFinite","kind":"Structure","label":"IsLocallyFinite","moduleName":"BridgelandStability.IntervalCategory.FiniteLength","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive","kind":"Theorem","label":"eulerFormInner_isTriangleAdditive","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"},{"groupKey":"BridgelandStability.StabilityCondition.Defs","href":"stabilitycondition-defs/","id":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap","kind":"Structure","label":"WithClassMap","moduleName":"BridgelandStability.StabilityCondition.Defs","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.eulerForm","kind":"Definition","label":"eulerForm","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"},{"groupKey":"BridgelandStability.StabilityCondition.Defs","href":"stabilitycondition-defs/","id":"CategoryTheory.Triangulated.stabSeminorm","kind":"Definition","label":"stabSeminorm","moduleName":"BridgelandStability.StabilityCondition.Defs","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.eulerFormRad","kind":"Definition","label":"eulerFormRad","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"},{"groupKey":"BridgelandStability.StabilityCondition.Defs","href":"stabilitycondition-defs/","id":"CategoryTheory.Triangulated.basisNhd","kind":"Definition","label":"basisNhd","moduleName":"BridgelandStability.StabilityCondition.Defs","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.NumericalK₀","kind":"Definition","label":"NumericalK₀","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"},{"groupKey":"BridgelandStability.StabilityCondition.Defs","href":"stabilitycondition-defs/","id":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace","kind":"Definition","label":"topologicalSpace","moduleName":"BridgelandStability.StabilityCondition.Defs","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup","kind":"Definition","label":"instAddCommGroup","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"},{"groupKey":"BridgelandStability.StabilityCondition.Defs","href":"stabilitycondition-defs/","id":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex","kind":"Definition","label":"ComponentIndex","moduleName":"BridgelandStability.StabilityCondition.Defs","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.numericalQuotientMap","kind":"Definition","label":"numericalQuotientMap","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.NumericallyFinite","kind":"Structure","label":"NumericallyFinite","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"},{"groupKey":"BridgelandStability.StabilityCondition.Defs","href":"stabilitycondition-defs/","id":"CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component","kind":"Definition","label":"Component","moduleName":"BridgelandStability.StabilityCondition.Defs","status":"clean"},{"groupKey":"BridgelandStability.EulerForm.Basic","href":"eulerform-basic/","id":"CategoryTheory.Triangulated.NumericalComponent","kind":"Definition","label":"NumericalComponent","moduleName":"BridgelandStability.EulerForm.Basic","status":"clean"}]}
```

# GrothendieckGroup.Basic

Module `BridgelandStability.GrothendieckGroup.Basic` — *8* declarations (Structure, Definition, Theorem)

## `CategoryTheory.Triangulated.IsTriangleAdditive`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-basic-categorytheory-triangulated-istriangleadditive-149-153"
%%%

`Structure` | `BridgelandStability.GrothendieckGroup.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Basic.lean#L149) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IsTriangleAdditive&body=**Declaration:** `CategoryTheory.Triangulated.IsTriangleAdditive`%0A**Module:** `BridgelandStability.GrothendieckGroup.Basic`%0A**Source:** BridgelandStability/GrothendieckGroup/Basic.lean:149%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.IsTriangleAdditive
```

```module (module := BridgelandStability.GrothendieckGroup.Basic) (anchor := CategoryTheory.Triangulated.IsTriangleAdditive) -defSite
/-- A function `f : C → A` to an additive group is triangle-additive if
`f(B) = f(A) + f(C)` for every distinguished triangle `A → B → C → A⟦1⟧`. -/
class IsTriangleAdditive {A : Type*} [AddCommGroup A] (f : C → A) : Prop where
  additive : ∀ (T : Pretriangulated.Triangle C),
    T ∈ (distTriang C) → f T.obj₂ = f T.obj₁ + f T.obj₃
```

## `CategoryTheory.Triangulated.trianglePresentation`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-basic-categorytheory-triangulated-trianglepresentation-54-60"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Basic.lean#L54) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: trianglePresentation&body=**Declaration:** `CategoryTheory.Triangulated.trianglePresentation`%0A**Module:** `BridgelandStability.GrothendieckGroup.Basic`%0A**Source:** BridgelandStability/GrothendieckGroup/Basic.lean:54%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.trianglePresentation
```

```module (module := BridgelandStability.GrothendieckGroup.Basic) (anchor := CategoryTheory.Triangulated.trianglePresentation) -defSite
/-- The `K0Presentation` for distinguished triangles in a pretriangulated category:
generators are objects of `C`, relations are distinguished triangles. -/
abbrev trianglePresentation :
    K0Presentation C {T : Pretriangulated.Triangle C // T ∈ distTriang C} where
  obj₁ := fun r => r.1.obj₁
  obj₂ := fun r => r.1.obj₂
  obj₃ := fun r => r.1.obj₃
```

## `CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-basic-categorytheory-triangulated-instisadditivesubtypetrianglememsetdistinguishedtrianglestrianglepresentationofistriangleadditive-156-158"
%%%

`Theorem` | `BridgelandStability.GrothendieckGroup.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Basic.lean#L156) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive&body=**Declaration:** `CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive`%0A**Module:** `BridgelandStability.GrothendieckGroup.Basic`%0A**Source:** BridgelandStability/GrothendieckGroup/Basic.lean:156%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive
```

```collapsibleModule (module := BridgelandStability.GrothendieckGroup.Basic) (anchor := CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive) -defSite
instance {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] :
    (trianglePresentation C).IsAdditive f where
  additive := fun ⟨T, hT⟩ => IsTriangleAdditive.additive T hT
```

## `CategoryTheory.Triangulated.K₀`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-basic-categorytheory-triangulated-k--62-64"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Basic.lean#L62) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: K₀&body=**Declaration:** `CategoryTheory.Triangulated.K₀`%0A**Module:** `BridgelandStability.GrothendieckGroup.Basic`%0A**Source:** BridgelandStability/GrothendieckGroup/Basic.lean:62%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.K₀
```

```module (module := BridgelandStability.GrothendieckGroup.Basic) (anchor := CategoryTheory.Triangulated.K₀) -defSite
/-- The Grothendieck group of a pretriangulated category `C`, defined as the quotient of
`FreeAbelianGroup C` by the distinguished triangle relations. -/
def K₀ : Type _ := (trianglePresentation C).K0
```

## `CategoryTheory.Triangulated.K₀.instAddCommGroup`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-basic-categorytheory-triangulated-k-instaddcommgroup-66-67"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Basic.lean#L66) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: instAddCommGroup&body=**Declaration:** `CategoryTheory.Triangulated.K₀.instAddCommGroup`%0A**Module:** `BridgelandStability.GrothendieckGroup.Basic`%0A**Source:** BridgelandStability/GrothendieckGroup/Basic.lean:66%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.K₀.instAddCommGroup
```

```module (module := BridgelandStability.GrothendieckGroup.Basic) (anchor := CategoryTheory.Triangulated.K₀.instAddCommGroup) -defSite
instance K₀.instAddCommGroup : AddCommGroup (K₀ C) :=
  inferInstanceAs (AddCommGroup (trianglePresentation C).K0)
```

## `CategoryTheory.Triangulated.K₀.of`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-basic-categorytheory-triangulated-k-of-69-71"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Basic.lean#L69) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: of&body=**Declaration:** `CategoryTheory.Triangulated.K₀.of`%0A**Module:** `BridgelandStability.GrothendieckGroup.Basic`%0A**Source:** BridgelandStability/GrothendieckGroup/Basic.lean:69%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.K₀.of
```

```module (module := BridgelandStability.GrothendieckGroup.Basic) (anchor := CategoryTheory.Triangulated.K₀.of) -defSite
/-- The class map sending an object `X` of `C` to its class `[X]` in `K₀ C`. -/
def K₀.of (X : C) : K₀ C :=
  QuotientAddGroup.mk (FreeAbelianGroup.of X)
```

## `CategoryTheory.Triangulated.K₀.lift`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-basic-categorytheory-triangulated-k-lift-160-163"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Basic.lean#L160) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: lift&body=**Declaration:** `CategoryTheory.Triangulated.K₀.lift`%0A**Module:** `BridgelandStability.GrothendieckGroup.Basic`%0A**Source:** BridgelandStability/GrothendieckGroup/Basic.lean:160%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.K₀.lift
```

```module (module := BridgelandStability.GrothendieckGroup.Basic) (anchor := CategoryTheory.Triangulated.K₀.lift) -defSite
/-- The universal property of K₀: any triangle-additive function lifts
to an additive group homomorphism from K₀. -/
def K₀.lift {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] : K₀ C →+ A :=
  (trianglePresentation C).lift f
```

## `CategoryTheory.Triangulated.cl`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-basic-categorytheory-triangulated-cl-220-224"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Basic.lean#L220) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: cl&body=**Declaration:** `CategoryTheory.Triangulated.cl`%0A**Module:** `BridgelandStability.GrothendieckGroup.Basic`%0A**Source:** BridgelandStability/GrothendieckGroup/Basic.lean:220%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.cl
```

```module (module := BridgelandStability.GrothendieckGroup.Basic) (anchor := CategoryTheory.Triangulated.cl) -defSite
/-- The class of an object `E` in the target lattice `Λ`, via the class map
`v : K₀(C) → Λ`. This is `v([E])` in the notation of Bridgeland, BMS16, etc.

At `v = id`: `cl v E = K₀.of C E` definitionally. -/
abbrev cl (E : C) : Λ := v (K₀.of C E)
```

# GrothendieckGroup.Defs

Module `BridgelandStability.GrothendieckGroup.Defs` — *6* declarations (Structure, Definition)

## `K0Presentation`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-defs-k0presentation-36-45"
%%%

`Structure` | `BridgelandStability.GrothendieckGroup.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Defs.lean#L36) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: K0Presentation&body=**Declaration:** `K0Presentation`%0A**Module:** `BridgelandStability.GrothendieckGroup.Defs`%0A**Source:** BridgelandStability/GrothendieckGroup/Defs.lean:36%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
K0Presentation
```

```module (module := BridgelandStability.GrothendieckGroup.Defs) (anchor := K0Presentation) -defSite
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
```

## `K0Presentation.subgroup`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-defs-k0presentation-subgroup-51-56"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Defs.lean#L51) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: subgroup&body=**Declaration:** `K0Presentation.subgroup`%0A**Module:** `BridgelandStability.GrothendieckGroup.Defs`%0A**Source:** BridgelandStability/GrothendieckGroup/Defs.lean:51%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
K0Presentation.subgroup
```

```module (module := BridgelandStability.GrothendieckGroup.Defs) (anchor := K0Presentation.subgroup) -defSite
/-- The subgroup of relations: `{obj₂(r) - obj₁(r) - obj₃(r) | r : Rel}`. -/
def subgroup : AddSubgroup (FreeAbelianGroup Obj) :=
  AddSubgroup.closure
    {x | ∃ r : Rel,
      x = FreeAbelianGroup.of (P.obj₂ r) - FreeAbelianGroup.of (P.obj₁ r) -
          FreeAbelianGroup.of (P.obj₃ r)}
```

## `K0Presentation.IsAdditive`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-defs-k0presentation-isadditive-81-83"
%%%

`Structure` | `BridgelandStability.GrothendieckGroup.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Defs.lean#L81) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IsAdditive&body=**Declaration:** `K0Presentation.IsAdditive`%0A**Module:** `BridgelandStability.GrothendieckGroup.Defs`%0A**Source:** BridgelandStability/GrothendieckGroup/Defs.lean:81%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
K0Presentation.IsAdditive
```

```module (module := BridgelandStability.GrothendieckGroup.Defs) (anchor := K0Presentation.IsAdditive) -defSite
/-- A function on objects is *additive* for a presentation if it respects the relations. -/
class IsAdditive {A : Type*} [AddCommGroup A] (f : Obj → A) : Prop where
  additive : ∀ r : Rel, f (P.obj₂ r) = f (P.obj₁ r) + f (P.obj₃ r)
```

## `K0Presentation.K0`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-defs-k0presentation-k0-58-59"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Defs.lean#L58) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: K0&body=**Declaration:** `K0Presentation.K0`%0A**Module:** `BridgelandStability.GrothendieckGroup.Defs`%0A**Source:** BridgelandStability/GrothendieckGroup/Defs.lean:58%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
K0Presentation.K0
```

```module (module := BridgelandStability.GrothendieckGroup.Defs) (anchor := K0Presentation.K0) -defSite
/-- The Grothendieck group: free abelian group on objects modulo the relations. -/
abbrev K0 : Type _ := FreeAbelianGroup Obj ⧸ P.subgroup
```

## `K0Presentation.instAddCommGroupK0`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-defs-k0presentation-instaddcommgroupk0-61-62"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Defs.lean#L61) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: instAddCommGroupK0&body=**Declaration:** `K0Presentation.instAddCommGroupK0`%0A**Module:** `BridgelandStability.GrothendieckGroup.Defs`%0A**Source:** BridgelandStability/GrothendieckGroup/Defs.lean:61%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
K0Presentation.instAddCommGroupK0
```

```module (module := BridgelandStability.GrothendieckGroup.Defs) (anchor := K0Presentation.instAddCommGroupK0) -defSite
instance : AddCommGroup P.K0 :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup Obj ⧸ P.subgroup))
```

## `K0Presentation.lift`
%%%
tag := "shadow-entry-bridgelandstability-grothendieckgroup-defs-k0presentation-lift-85-92"
%%%

`Definition` | `BridgelandStability.GrothendieckGroup.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/GrothendieckGroup/Defs.lean#L85) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: lift&body=**Declaration:** `K0Presentation.lift`%0A**Module:** `BridgelandStability.GrothendieckGroup.Defs`%0A**Source:** BridgelandStability/GrothendieckGroup/Defs.lean:85%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
K0Presentation.lift
```

```module (module := BridgelandStability.GrothendieckGroup.Defs) (anchor := K0Presentation.lift) -defSite
/-- The universal property: an additive function lifts uniquely to a group homomorphism. -/
def lift {A : Type*} [AddCommGroup A] (f : Obj → A) [P.IsAdditive f] : P.K0 →+ A :=
  QuotientAddGroup.lift P.subgroup (FreeAbelianGroup.lift f)
    ((AddSubgroup.closure_le _).mpr fun x ⟨r, hx⟩ ↦ by
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hx, map_sub,
        FreeAbelianGroup.lift_apply_of]
      have h := IsAdditive.additive (P := P) (f := f) r
      rw [h]; abel)
```

# NumericalStability.Defs

Module `BridgelandStability.NumericalStability.Defs` — *2* declarations (Structure, Definition)

## `CategoryTheory.Triangulated.IsFiniteType`
%%%
tag := "shadow-entry-bridgelandstability-numericalstability-defs-categorytheory-triangulated-isfinitetype-45-52"
%%%

`Structure` | `BridgelandStability.NumericalStability.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/NumericalStability/Defs.lean#L45) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IsFiniteType&body=**Declaration:** `CategoryTheory.Triangulated.IsFiniteType`%0A**Module:** `BridgelandStability.NumericalStability.Defs`%0A**Source:** BridgelandStability/NumericalStability/Defs.lean:45%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.IsFiniteType
```

```module (module := BridgelandStability.NumericalStability.Defs) (anchor := CategoryTheory.Triangulated.IsFiniteType) -defSite
/-- A `k`-linear pretriangulated category is of finite type if all Hom spaces are
finite-dimensional over `k` and for each pair of objects, only finitely many shifted
Hom spaces are nonzero. -/
class IsFiniteType [Linear k C] : Prop where
  /-- Each Hom space `Hom(E, F)` is finite-dimensional over `k`. -/
  finite_dim : ∀ (E F : C), Module.Finite k (E ⟶ F)
  /-- For each pair of objects, only finitely many shifted Hom spaces are nontrivial. -/
  finite_support : ∀ (E F : C), Set.Finite {n : ℤ | Nontrivial (E ⟶ (shiftFunctor C n).obj F)}
```

## `CategoryTheory.Triangulated.eulerFormObj`
%%%
tag := "shadow-entry-bridgelandstability-numericalstability-defs-categorytheory-triangulated-eulerformobj-56-59"
%%%

`Definition` | `BridgelandStability.NumericalStability.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/NumericalStability/Defs.lean#L56) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: eulerFormObj&body=**Declaration:** `CategoryTheory.Triangulated.eulerFormObj`%0A**Module:** `BridgelandStability.NumericalStability.Defs`%0A**Source:** BridgelandStability/NumericalStability/Defs.lean:56%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.eulerFormObj
```

```module (module := BridgelandStability.NumericalStability.Defs) (anchor := CategoryTheory.Triangulated.eulerFormObj) -defSite
/-- The Euler form on objects: `χ(E,F) = Σₙ (-1)ⁿ dim_k Hom(E, F[n])`.
This is defined as a finitely-supported sum using `finsum`. -/
def eulerFormObj [Linear k C] (E F : C) : ℤ :=
  ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ (shiftFunctor C n).obj F) : ℤ)
```

# PostnikovTower.Defs

Module `BridgelandStability.PostnikovTower.Defs` — *2* declarations (Structure, Definition)

## `CategoryTheory.Triangulated.PostnikovTower`
%%%
tag := "shadow-entry-bridgelandstability-postnikovtower-defs-categorytheory-triangulated-postnikovtower-53-81"
%%%

`Structure` | `BridgelandStability.PostnikovTower.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/PostnikovTower/Defs.lean#L53) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: PostnikovTower&body=**Declaration:** `CategoryTheory.Triangulated.PostnikovTower`%0A**Module:** `BridgelandStability.PostnikovTower.Defs`%0A**Source:** BridgelandStability/PostnikovTower/Defs.lean:53%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.PostnikovTower
```

````module (module := BridgelandStability.PostnikovTower.Defs) (anchor := CategoryTheory.Triangulated.PostnikovTower) -defSite
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
````

## `CategoryTheory.Triangulated.PostnikovTower.factor`
%%%
tag := "shadow-entry-bridgelandstability-postnikovtower-defs-categorytheory-triangulated-postnikovtower-factor-87-90"
%%%

`Definition` | `BridgelandStability.PostnikovTower.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/PostnikovTower/Defs.lean#L87) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: factor&body=**Declaration:** `CategoryTheory.Triangulated.PostnikovTower.factor`%0A**Module:** `BridgelandStability.PostnikovTower.Defs`%0A**Source:** BridgelandStability/PostnikovTower/Defs.lean:87%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.PostnikovTower.factor
```

```module (module := BridgelandStability.PostnikovTower.Defs) (anchor := CategoryTheory.Triangulated.PostnikovTower.factor) -defSite
/-- The `i`-th factor of a Postnikov tower, derived as `obj₃` of the `i`-th
distinguished triangle. -/
def PostnikovTower.factor {E : C} (P : PostnikovTower C E) (i : Fin P.n) : C :=
  (P.triangle i).obj₃
```

# QuasiAbelian.Basic

Module `BridgelandStability.QuasiAbelian.Basic` — *8* declarations (Definition, Structure)

## `CategoryTheory.IsStrict`
%%%
tag := "shadow-entry-bridgelandstability-quasiabelian-basic-categorytheory-isstrict-65-72"
%%%

`Definition` | `BridgelandStability.QuasiAbelian.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/QuasiAbelian/Basic.lean#L65) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IsStrict&body=**Declaration:** `CategoryTheory.IsStrict`%0A**Module:** `BridgelandStability.QuasiAbelian.Basic`%0A**Source:** BridgelandStability/QuasiAbelian/Basic.lean:65%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.IsStrict
```

```module (module := BridgelandStability.QuasiAbelian.Basic) (anchor := CategoryTheory.IsStrict) -defSite
/-- A morphism `f` is *strict* if the canonical comparison morphism from the
(abelian) coimage to the (abelian) image is an isomorphism. In an abelian category,
every morphism is strict.

This uses `Abelian.coimageImageComparison` from `Mathlib.CategoryTheory.Abelian.Images`,
which is defined without assuming the category is abelian. -/
def IsStrict : Prop :=
  IsIso (Abelian.coimageImageComparison f)
```

## `CategoryTheory.IsStrictMono`
%%%
tag := "shadow-entry-bridgelandstability-quasiabelian-basic-categorytheory-isstrictmono-74-77"
%%%

`Structure` | `BridgelandStability.QuasiAbelian.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/QuasiAbelian/Basic.lean#L74) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IsStrictMono&body=**Declaration:** `CategoryTheory.IsStrictMono`%0A**Module:** `BridgelandStability.QuasiAbelian.Basic`%0A**Source:** BridgelandStability/QuasiAbelian/Basic.lean:74%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.IsStrictMono
```

```module (module := BridgelandStability.QuasiAbelian.Basic) (anchor := CategoryTheory.IsStrictMono) -defSite
/-- A morphism is a *strict monomorphism* if it is both a monomorphism and strict. -/
structure IsStrictMono : Prop where
  mono : Mono f
  strict : IsStrict f
```

## `CategoryTheory.Subobject.IsStrict`
%%%
tag := "shadow-entry-bridgelandstability-quasiabelian-basic-categorytheory-subobject-isstrict-417-421"
%%%

`Definition` | `BridgelandStability.QuasiAbelian.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/QuasiAbelian/Basic.lean#L417) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IsStrict&body=**Declaration:** `CategoryTheory.Subobject.IsStrict`%0A**Module:** `BridgelandStability.QuasiAbelian.Basic`%0A**Source:** BridgelandStability/QuasiAbelian/Basic.lean:417%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Subobject.IsStrict
```

```module (module := BridgelandStability.QuasiAbelian.Basic) (anchor := CategoryTheory.Subobject.IsStrict) -defSite
/-- A subobject is *strict* if its arrow is a strict monomorphism. This is the
quasi-abelian notion of admissible / exact subobject used in Bridgeland's finite-length
thin interval categories. -/
def IsStrict (P : Subobject X) : Prop :=
  IsStrictMono P.arrow
```

## `CategoryTheory.StrictSubobject`
%%%
tag := "shadow-entry-bridgelandstability-quasiabelian-basic-categorytheory-strictsubobject-435-437"
%%%

`Definition` | `BridgelandStability.QuasiAbelian.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/QuasiAbelian/Basic.lean#L435) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: StrictSubobject&body=**Declaration:** `CategoryTheory.StrictSubobject`%0A**Module:** `BridgelandStability.QuasiAbelian.Basic`%0A**Source:** BridgelandStability/QuasiAbelian/Basic.lean:435%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.StrictSubobject
```

```module (module := BridgelandStability.QuasiAbelian.Basic) (anchor := CategoryTheory.StrictSubobject) -defSite
/-- The ordered type of strict subobjects of `X`. -/
abbrev StrictSubobject (X : C) :=
  { P : Subobject X // P.IsStrict }
```

## `CategoryTheory.isStrictArtinianObject`
%%%
tag := "shadow-entry-bridgelandstability-quasiabelian-basic-categorytheory-isstrictartinianobject-441-444"
%%%

`Definition` | `BridgelandStability.QuasiAbelian.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/QuasiAbelian/Basic.lean#L441) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: isStrictArtinianObject&body=**Declaration:** `CategoryTheory.isStrictArtinianObject`%0A**Module:** `BridgelandStability.QuasiAbelian.Basic`%0A**Source:** BridgelandStability/QuasiAbelian/Basic.lean:441%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.isStrictArtinianObject
```

```module (module := BridgelandStability.QuasiAbelian.Basic) (anchor := CategoryTheory.isStrictArtinianObject) -defSite
/-- An object is *strict-Artinian* if its strict subobjects satisfy the descending chain
condition. This is the exact finite-length notion relevant to quasi-abelian categories. -/
def isStrictArtinianObject : ObjectProperty C :=
  fun X ↦ WellFoundedLT (StrictSubobject X)
```

## `CategoryTheory.isStrictNoetherianObject`
%%%
tag := "shadow-entry-bridgelandstability-quasiabelian-basic-categorytheory-isstrictnoetherianobject-453-456"
%%%

`Definition` | `BridgelandStability.QuasiAbelian.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/QuasiAbelian/Basic.lean#L453) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: isStrictNoetherianObject&body=**Declaration:** `CategoryTheory.isStrictNoetherianObject`%0A**Module:** `BridgelandStability.QuasiAbelian.Basic`%0A**Source:** BridgelandStability/QuasiAbelian/Basic.lean:453%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.isStrictNoetherianObject
```

```module (module := BridgelandStability.QuasiAbelian.Basic) (anchor := CategoryTheory.isStrictNoetherianObject) -defSite
/-- An object is *strict-Noetherian* if its strict subobjects satisfy the ascending chain
condition. This is the exact finite-length notion relevant to quasi-abelian categories. -/
def isStrictNoetherianObject : ObjectProperty C :=
  fun X ↦ WellFoundedGT (StrictSubobject X)
```

## `CategoryTheory.IsStrictArtinianObject`
%%%
tag := "shadow-entry-bridgelandstability-quasiabelian-basic-categorytheory-isstrictartinianobject-446-448"
%%%

`Definition` | `BridgelandStability.QuasiAbelian.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/QuasiAbelian/Basic.lean#L446) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IsStrictArtinianObject&body=**Declaration:** `CategoryTheory.IsStrictArtinianObject`%0A**Module:** `BridgelandStability.QuasiAbelian.Basic`%0A**Source:** BridgelandStability/QuasiAbelian/Basic.lean:446%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.IsStrictArtinianObject
```

```module (module := BridgelandStability.QuasiAbelian.Basic) (anchor := CategoryTheory.IsStrictArtinianObject) -defSite
/-- An object is *strict-Artinian* if its strict subobjects satisfy the descending chain
condition. -/
abbrev IsStrictArtinianObject : Prop := isStrictArtinianObject.Is X
```

## `CategoryTheory.IsStrictNoetherianObject`
%%%
tag := "shadow-entry-bridgelandstability-quasiabelian-basic-categorytheory-isstrictnoetherianobject-458-460"
%%%

`Definition` | `BridgelandStability.QuasiAbelian.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/QuasiAbelian/Basic.lean#L458) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IsStrictNoetherianObject&body=**Declaration:** `CategoryTheory.IsStrictNoetherianObject`%0A**Module:** `BridgelandStability.QuasiAbelian.Basic`%0A**Source:** BridgelandStability/QuasiAbelian/Basic.lean:458%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.IsStrictNoetherianObject
```

```module (module := BridgelandStability.QuasiAbelian.Basic) (anchor := CategoryTheory.IsStrictNoetherianObject) -defSite
/-- An object is *strict-Noetherian* if its strict subobjects satisfy the ascending chain
condition. -/
abbrev IsStrictNoetherianObject : Prop := isStrictNoetherianObject.Is X
```

# EulerForm.Basic

Module `BridgelandStability.EulerForm.Basic` — *10* declarations (Theorem, Definition, Structure)

## `CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-eulerformobj-contravariant-triangleadditive-324-414"
%%%

`Theorem` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L324) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: eulerFormObj_contravariant_triangleAdditive&body=**Declaration:** `CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:324%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive
```

```collapsibleModule (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive) -defSite
theorem eulerFormObj_contravariant_triangleAdditive (E : C) :
    IsTriangleAdditive (fun F ↦ eulerFormObj k C E F) where
  additive := fun T hT ↦ by
    simp only [eulerFormObj]
    let F : C ⥤ ModuleCat k := (linearCoyoneda k C).obj (Opposite.op E)
    letI : F.ShiftSequence ℤ := Functor.ShiftSequence.tautological F ℤ
    letI : F.IsHomological := linearCoyonedaObjIsHomological (k := k) (C := C) E
    let δ_lin : (n : ℤ) → ((E ⟶ T.obj₃⟦n⟧) →ₗ[k] (E ⟶ T.obj₁⟦(n + 1)⟧)) := fun n ↦
      Linear.rightComp k E (T.mor₃⟦n⟧' ≫
        (shiftFunctorAdd' C 1 n (n + 1) (by lia)).inv.app T.obj₁)
    let r : ℤ → ℤ := fun n ↦ Module.finrank k (LinearMap.range (δ_lin n))
    have hδ_eq : ∀ n : ℤ, ((F.homologySequenceδ T n (n + 1) rfl).hom) = δ_lin n := by
      intro n
      ext x
      simpa [F, δ_lin] using
        (CategoryTheory.Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply
          (C := C) (T := T) (n₀ := n) (n₁ := n + 1) (h := rfl) (A := Opposite.op E) x)
    have h_ker_f_aux : ∀ m : ℤ,
        Module.finrank k (LinearMap.ker (((F.shift (m + 1)).map T.mor₁).hom)) = r m := by
      intro m
      let f_succ : (E ⟶ T.obj₁⟦m + 1⟧) →ₗ[k] (E ⟶ T.obj₂⟦m + 1⟧) :=
        ((F.shift (m + 1)).map T.mor₁).hom
      have h_exact₁ : LinearMap.range (δ_lin m) = LinearMap.ker f_succ := by
        simpa [f_succ, hδ_eq m] using
          (ShortComplex.Exact.moduleCat_range_eq_ker
            (F.homologySequence_exact₁ T hT m (m + 1) rfl))
      simpa [r] using
        congrArg (fun V : Submodule k (E ⟶ T.obj₁⟦m + 1⟧) => Module.finrank k V) h_exact₁.symm
    have hrank : ∀ n : ℤ,
        (Module.finrank k (E ⟶ T.obj₂⟦n⟧) : ℤ) =
        Module.finrank k (E ⟶ T.obj₁⟦n⟧) + Module.finrank k (E ⟶ T.obj₃⟦n⟧) -
          r (n - 1) - r n := by
      intro n
      let f_n : (E ⟶ T.obj₁⟦n⟧) →ₗ[k] (E ⟶ T.obj₂⟦n⟧) := ((F.shift n).map T.mor₁).hom
      let g_n : (E ⟶ T.obj₂⟦n⟧) →ₗ[k] (E ⟶ T.obj₃⟦n⟧) := ((F.shift n).map T.mor₂).hom
      have hexact_B : LinearMap.range f_n = LinearMap.ker g_n := by
        simpa [f_n, g_n, F] using
          (ShortComplex.Exact.moduleCat_range_eq_ker
            (F.homologySequence_exact₂ T hT n))
      haveI : Module.Finite k (E ⟶ T.obj₂⟦n⟧) := IsFiniteType.finite_dim (k := k) E (T.obj₂⟦n⟧)
      have h_mid := finrank_mid_of_exact k f_n g_n hexact_B
      haveI : Module.Finite k (E ⟶ T.obj₁⟦n⟧) := IsFiniteType.finite_dim (k := k) E (T.obj₁⟦n⟧)
      haveI : Module.Finite k (E ⟶ T.obj₃⟦n⟧) := IsFiniteType.finite_dim (k := k) E (T.obj₃⟦n⟧)
      have h_ker_f : Module.finrank k (LinearMap.ker f_n) = r (n - 1) := by
        change Module.finrank k (LinearMap.ker (((F.shift n).map T.mor₁).hom)) = r (n - 1)
        have hn : n = (n - 1) + 1 := by lia
        rw [hn]
        simpa using h_ker_f_aux (n - 1)
      have h_ker_δ : Module.finrank k (LinearMap.ker (δ_lin n)) =
          Module.finrank k (LinearMap.range g_n) := by
        have h_exact₃ : LinearMap.range g_n = LinearMap.ker (δ_lin n) := by
          simpa [g_n, hδ_eq n] using
            (ShortComplex.Exact.moduleCat_range_eq_ker
              (F.homologySequence_exact₃ T hT n (n + 1) rfl))
        simpa using
          congrArg (fun V : Submodule k (E ⟶ T.obj₃⟦n⟧) => Module.finrank k V) h_exact₃.symm
      have h_f : (Module.finrank k (LinearMap.range f_n) : ℤ) =
          Module.finrank k (E ⟶ T.obj₁⟦n⟧) - r (n - 1) := by
        have := f_n.finrank_range_add_finrank_ker
        lia
      have h_g : (Module.finrank k (LinearMap.range g_n) : ℤ) =
          Module.finrank k (E ⟶ T.obj₃⟦n⟧) - r n := by
        have h1 := (δ_lin n).finrank_range_add_finrank_ker
        have h2 := h_ker_δ
        simp only [r] at h2 ⊢
        lia
      linarith
    have hr : (Function.support r).Finite := by
      refine Set.Finite.subset
        ((IsFiniteType.finite_support (k := k) E T.obj₁).image fun m : ℤ ↦ m - 1) ?_
      intro n hn
      have hnonzero : (r n : ℤ) ≠ 0 := hn
      have hnontrivial : Nontrivial (E ⟶ T.obj₁⟦n + 1⟧) := by
        by_contra htriv
        haveI : Subsingleton (E ⟶ T.obj₁⟦n + 1⟧) := not_nontrivial_iff_subsingleton.mp htriv
        have hδ : δ_lin n = 0 := by
          ext x
          exact Subsingleton.elim _ _
        apply hnonzero
        simp [r]
      exact ⟨n + 1, hnontrivial, by simp⟩
    exact eulerSum_of_rank_identity (k := k) (C := C) E
      (a := fun n ↦ T.obj₁⟦n⟧)
      (b := fun n ↦ T.obj₂⟦n⟧)
      (c := fun n ↦ T.obj₃⟦n⟧)
      (r := r)
      hrank
      (by simpa using IsFiniteType.finite_support (k := k) E T.obj₁)
      (by simpa using IsFiniteType.finite_support (k := k) E T.obj₂)
      (by simpa using IsFiniteType.finite_support (k := k) E T.obj₃)
      hr
```

## `CategoryTheory.Triangulated.eulerFormInner`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-eulerforminner-567-571"
%%%

`Definition` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L567) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: eulerFormInner&body=**Declaration:** `CategoryTheory.Triangulated.eulerFormInner`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:567%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.eulerFormInner
```

```module (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.eulerFormInner) -defSite
/-- For fixed `E`, lift `F ↦ χ(E, F)` to a group homomorphism `K₀ C →+ ℤ`
using the universal property of `K₀`. -/
def eulerFormInner (E : C) : K₀ C →+ ℤ := by
  letI := eulerFormObj_contravariant_triangleAdditive (k := k) (C := C) E
  exact K₀.lift C (fun F ↦ eulerFormObj k C E F)
```

## `CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-eulerforminner-istriangleadditive-573-582"
%%%

`Theorem` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L573) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: eulerFormInner_isTriangleAdditive&body=**Declaration:** `CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:573%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive
```

```collapsibleModule (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive) -defSite
/-- The outer function `E ↦ eulerFormInner E` is triangle-additive, so the Euler
form descends to a bilinear form on `K₀`. -/
instance eulerFormInner_isTriangleAdditive
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    IsTriangleAdditive (eulerFormInner k C) where
  additive T hT := by
    apply K₀.hom_ext; intro F
    simp only [AddMonoidHom.add_apply, eulerFormInner, K₀.lift_of]
    letI := eulerFormObj_covariant_triangleAdditive (k := k) (C := C) F
    exact IsTriangleAdditive.additive (f := fun E ↦ eulerFormObj k C E F) T hT
```

## `CategoryTheory.Triangulated.eulerForm`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-eulerform-584-588"
%%%

`Definition` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L584) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: eulerForm&body=**Declaration:** `CategoryTheory.Triangulated.eulerForm`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:584%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.eulerForm
```

```module (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.eulerForm) -defSite
/-- The Euler form on `K₀`, obtained by applying the universal property of `K₀`
twice to `eulerFormObj`. -/
def eulerForm [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ K₀ C →+ ℤ :=
  K₀.lift C (eulerFormInner k C)
```

## `CategoryTheory.Triangulated.eulerFormRad`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-eulerformrad-590-593"
%%%

`Definition` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L590) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: eulerFormRad&body=**Declaration:** `CategoryTheory.Triangulated.eulerFormRad`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:590%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.eulerFormRad
```

```module (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.eulerFormRad) -defSite
/-- The left radical of the Euler form on `K₀ C`. -/
def eulerFormRad [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddSubgroup (K₀ C) :=
  (eulerForm k C).ker
```

## `CategoryTheory.Triangulated.NumericalK₀`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-numericalk--595-598"
%%%

`Definition` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L595) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: NumericalK₀&body=**Declaration:** `CategoryTheory.Triangulated.NumericalK₀`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:595%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.NumericalK₀
```

```module (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.NumericalK₀) -defSite
/-- The numerical Grothendieck group attached to the Euler form on `K₀`. -/
def NumericalK₀ [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k] :
    Type _ :=
  K₀ C ⧸ eulerFormRad k C
```

## `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-numericalk-instaddcommgroup-600-604"
%%%

`Definition` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L600) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: instAddCommGroup&body=**Declaration:** `CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:600%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup
```

```module (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup) -defSite
/-- The `AddCommGroup` instance on `NumericalK₀ k C`. -/
instance NumericalK₀.instAddCommGroup [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddCommGroup (NumericalK₀ k C) :=
  inferInstanceAs (AddCommGroup (K₀ C ⧸ eulerFormRad k C))
```

## `CategoryTheory.Triangulated.numericalQuotientMap`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-numericalquotientmap-606-610"
%%%

`Definition` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L606) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: numericalQuotientMap&body=**Declaration:** `CategoryTheory.Triangulated.numericalQuotientMap`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:606%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.numericalQuotientMap
```

```module (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.numericalQuotientMap) -defSite
/-- The quotient map `K₀(C) → N(C)`. -/
abbrev numericalQuotientMap [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ NumericalK₀ k C :=
  QuotientAddGroup.mk' (eulerFormRad k C)
```

## `CategoryTheory.Triangulated.NumericallyFinite`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-numericallyfinite-612-617"
%%%

`Structure` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L612) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: NumericallyFinite&body=**Declaration:** `CategoryTheory.Triangulated.NumericallyFinite`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:612%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.NumericallyFinite
```

```module (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.NumericallyFinite) -defSite
/-- The category `C` is numerically finite if the numerical Grothendieck group attached to the
Euler form is finitely generated as an abelian group. -/
class NumericallyFinite [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] : Prop where
  /-- The Euler-form numerical Grothendieck group is finitely generated. -/
  fg : AddGroup.FG (NumericalK₀ k C)
```

## `CategoryTheory.Triangulated.NumericalComponent`
%%%
tag := "shadow-entry-bridgelandstability-eulerform-basic-categorytheory-triangulated-numericalcomponent-639-643"
%%%

`Definition` | `BridgelandStability.EulerForm.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/EulerForm/Basic.lean#L639) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: NumericalComponent&body=**Declaration:** `CategoryTheory.Triangulated.NumericalComponent`%0A**Module:** `BridgelandStability.EulerForm.Basic`%0A**Source:** BridgelandStability/EulerForm/Basic.lean:639%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.NumericalComponent
```

```module (module := BridgelandStability.EulerForm.Basic) (anchor := CategoryTheory.Triangulated.NumericalComponent) -defSite
/-- A connected component of numerical stability conditions. -/
abbrev NumericalComponent [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :=
  StabilityCondition.WithClassMap.Component C (numericalQuotientMap k C) cc
```

# Slicing.Defs

Module `BridgelandStability.Slicing.Defs` — *7* declarations (Structure, Definition, Theorem)

## `CategoryTheory.Triangulated.HNFiltration`
%%%
tag := "shadow-entry-bridgelandstability-slicing-defs-categorytheory-triangulated-hnfiltration-62-72"
%%%

`Structure` | `BridgelandStability.Slicing.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/Slicing/Defs.lean#L62) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: HNFiltration&body=**Declaration:** `CategoryTheory.Triangulated.HNFiltration`%0A**Module:** `BridgelandStability.Slicing.Defs`%0A**Source:** BridgelandStability/Slicing/Defs.lean:62%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.HNFiltration
```

```module (module := BridgelandStability.Slicing.Defs) (anchor := CategoryTheory.Triangulated.HNFiltration) -defSite
/-- A Harder-Narasimhan (HN) filtration of an object `E` with respect to a phase
predicate `P`. This extends a `PostnikovTower` with phase data: each factor is
semistable with a given phase, and the phases are strictly decreasing. -/
@[informal "Definition 3.3" "axiom (c): HN decomposition data for triangulated categories"]
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C) extends PostnikovTower C E where
  /-- The phases of the semistable factors, in strictly decreasing order. -/
  φ : Fin n → ℝ
  /-- The phases are strictly decreasing (higher phase factors appear first). -/
  hφ : StrictAnti φ
  /-- Each factor is semistable of the given phase. -/
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j)
```

## `CategoryTheory.Triangulated.Slicing`
%%%
tag := "shadow-entry-bridgelandstability-slicing-defs-categorytheory-triangulated-slicing-74-95"
%%%

`Structure` | `BridgelandStability.Slicing.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/Slicing/Defs.lean#L74) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: Slicing&body=**Declaration:** `CategoryTheory.Triangulated.Slicing`%0A**Module:** `BridgelandStability.Slicing.Defs`%0A**Source:** BridgelandStability/Slicing/Defs.lean:74%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.Slicing
```

```module (module := BridgelandStability.Slicing.Defs) (anchor := CategoryTheory.Triangulated.Slicing) -defSite
/-- A slicing of a pretriangulated category `C`, as defined in
Bridgeland (2007), Definition 5.1. A slicing assigns to each real number `φ`
a full subcategory of semistable objects `P(φ)` (as an `ObjectProperty`),
subject to shift, Hom-vanishing, and Harder-Narasimhan existence axioms.

Each `P(φ)` is an `ObjectProperty C`, enabling use of the `ObjectProperty` API
(e.g. `FullSubcategory`, shift stability, closure properties). -/
@[informal "Definition 3.3"]
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
```

## `CategoryTheory.Triangulated.Slicing.intervalProp`
%%%
tag := "shadow-entry-bridgelandstability-slicing-defs-categorytheory-triangulated-slicing-intervalprop-201-204"
%%%

`Definition` | `BridgelandStability.Slicing.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/Slicing/Defs.lean#L201) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: intervalProp&body=**Declaration:** `CategoryTheory.Triangulated.Slicing.intervalProp`%0A**Module:** `BridgelandStability.Slicing.Defs`%0A**Source:** BridgelandStability/Slicing/Defs.lean:201%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.Slicing.intervalProp
```

```module (module := BridgelandStability.Slicing.Defs) (anchor := CategoryTheory.Triangulated.Slicing.intervalProp) -defSite
/-- The interval subcategory predicate `P((a,b))`: an object `E` belongs to the
interval subcategory if it is zero or all phases in its HN filtration lie in `(a,b)`. -/
def Slicing.intervalProp (s : Slicing C) (a b : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E), ∀ i, a < F.φ i ∧ F.φ i < b
```

## `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first`
%%%
tag := "shadow-entry-bridgelandstability-slicing-defs-categorytheory-triangulated-hnfiltration-exists-nonzero-first-374-403"
%%%

`Theorem` | `BridgelandStability.Slicing.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/Slicing/Defs.lean#L374) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: exists_nonzero_first&body=**Declaration:** `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first`%0A**Module:** `BridgelandStability.Slicing.Defs`%0A**Source:** BridgelandStability/Slicing/Defs.lean:374%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first
```

```collapsibleModule (module := BridgelandStability.Slicing.Defs) (anchor := CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first) -defSite
/-- For any nonzero object, there exists an HN filtration with nonzero first factor.
Proved by repeatedly dropping zero first factors; terminates since `n` decreases
and some factor must be nonzero (by `exists_nonzero_factor`). -/
lemma HNFiltration.exists_nonzero_first (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n), ¬IsZero (F.triangle ⟨0, hn⟩).obj₃ := by
  obtain ⟨F⟩ := s.hn_exists E
  suffices hmain : ∀ (m : ℕ) (G : HNFiltration C s.P E), G.n ≤ m →
      ∃ (H : HNFiltration C s.P E) (hn : 0 < H.n),
        ¬IsZero (H.triangle ⟨0, hn⟩).obj₃ from
    hmain F.n F le_rfl
  intro m
  induction m with
  | zero =>
    intro G hGn
    exact absurd (G.zero_isZero (by lia)) hE
  | succ m ih =>
    intro G hGn
    have hGn0 : 0 < G.n := G.n_pos C hE
    by_cases hfirst : IsZero (G.triangle ⟨0, hGn0⟩).obj₃
    · -- First factor is zero; drop it and recurse
      have hn1 : 1 < G.n := by
        by_contra h; push Not at h
        have : ∀ (i : Fin G.n), IsZero (G.triangle i).obj₃ := fun i ↦ by
          have : i = ⟨0, hGn0⟩ := Fin.ext (by lia)
          subst this; exact hfirst
        exact absurd ((G.exists_nonzero_factor C hE).elim fun i hi ↦ absurd (this i) hi) id
      have hdrop : (G.dropFirst C hn1 hfirst).n ≤ m := by
        change G.n - 1 ≤ m; lia
      exact ih (G.dropFirst C hn1 hfirst) hdrop
    · exact ⟨G, hGn0, hfirst⟩
```

## `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last`
%%%
tag := "shadow-entry-bridgelandstability-slicing-defs-categorytheory-triangulated-hnfiltration-exists-nonzero-last-440-468"
%%%

`Theorem` | `BridgelandStability.Slicing.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/Slicing/Defs.lean#L440) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: exists_nonzero_last&body=**Declaration:** `CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last`%0A**Module:** `BridgelandStability.Slicing.Defs`%0A**Source:** BridgelandStability/Slicing/Defs.lean:440%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last
```

```collapsibleModule (module := BridgelandStability.Slicing.Defs) (anchor := CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last) -defSite
/-- For any nonzero object, there exists an HN filtration with nonzero last factor.
Proved by repeatedly dropping zero last factors. -/
lemma HNFiltration.exists_nonzero_last (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.triangle ⟨F.n - 1, by lia⟩).obj₃ := by
  obtain ⟨F⟩ := s.hn_exists E
  suffices hmain : ∀ (m : ℕ) (G : HNFiltration C s.P E), G.n ≤ m →
      ∃ (H : HNFiltration C s.P E) (hn : 0 < H.n),
        ¬IsZero (H.triangle ⟨H.n - 1, by lia⟩).obj₃ from
    hmain F.n F le_rfl
  intro m
  induction m with
  | zero =>
    intro G hGn
    exact absurd (G.zero_isZero (by lia)) hE
  | succ m ih =>
    intro G hGn
    have hGn0 : 0 < G.n := G.n_pos C hE
    by_cases hlast : IsZero (G.triangle ⟨G.n - 1, by lia⟩).obj₃
    · have hn1 : 1 < G.n := by
        by_contra h; push Not at h
        have : ∀ (i : Fin G.n), IsZero (G.triangle i).obj₃ := fun i ↦ by
          have : i = ⟨G.n - 1, by lia⟩ := Fin.ext (by lia)
          subst this; exact hlast
        exact absurd ((G.exists_nonzero_factor C hE).elim fun i hi ↦ absurd (this i) hi) id
      have hdrop : (G.dropLast C hn1 hlast).n ≤ m := by
        change G.n - 1 ≤ m; lia
      exact ih (G.dropLast C hn1 hlast) hdrop
    · exact ⟨G, hGn0, hlast⟩
```

## `CategoryTheory.Triangulated.Slicing.phiPlus`
%%%
tag := "shadow-entry-bridgelandstability-slicing-defs-categorytheory-triangulated-slicing-phiplus-472-478"
%%%

`Definition` | `BridgelandStability.Slicing.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/Slicing/Defs.lean#L472) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: phiPlus&body=**Declaration:** `CategoryTheory.Triangulated.Slicing.phiPlus`%0A**Module:** `BridgelandStability.Slicing.Defs`%0A**Source:** BridgelandStability/Slicing/Defs.lean:472%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.Slicing.phiPlus
```

```module (module := BridgelandStability.Slicing.Defs) (anchor := CategoryTheory.Triangulated.Slicing.phiPlus) -defSite
/-- The intrinsic highest phase of a nonzero object with respect to a slicing.
This is the phase of the first factor in any HN filtration with nonzero first factor.
Well-defined by `phiPlus_eq_of_nonzero_factors`. -/
noncomputable def Slicing.phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hn := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  F.φ ⟨0, hn⟩
```

## `CategoryTheory.Triangulated.Slicing.phiMinus`
%%%
tag := "shadow-entry-bridgelandstability-slicing-defs-categorytheory-triangulated-slicing-phiminus-480-486"
%%%

`Definition` | `BridgelandStability.Slicing.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/Slicing/Defs.lean#L480) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: phiMinus&body=**Declaration:** `CategoryTheory.Triangulated.Slicing.phiMinus`%0A**Module:** `BridgelandStability.Slicing.Defs`%0A**Source:** BridgelandStability/Slicing/Defs.lean:480%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.Slicing.phiMinus
```

```module (module := BridgelandStability.Slicing.Defs) (anchor := CategoryTheory.Triangulated.Slicing.phiMinus) -defSite
/-- The intrinsic lowest phase of a nonzero object with respect to a slicing.
This is the phase of the last factor in any HN filtration with nonzero last factor.
Well-defined by `phiMinus_eq_of_nonzero_last_factors`. -/
noncomputable def Slicing.phiMinus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_last C s hE).choose
  let hn : 0 < F.n := (HNFiltration.exists_nonzero_last C s hE).choose_spec.choose
  F.φ ⟨F.n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩
```

# IntervalCategory.Basic

Module `BridgelandStability.IntervalCategory.Basic` — *1* declarations (Definition)

## `CategoryTheory.Triangulated.Slicing.IntervalCat`
%%%
tag := "shadow-entry-bridgelandstability-intervalcategory-basic-categorytheory-triangulated-slicing-intervalcat-72-78"
%%%

`Definition` | `BridgelandStability.IntervalCategory.Basic` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/IntervalCategory/Basic.lean#L72) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IntervalCat&body=**Declaration:** `CategoryTheory.Triangulated.Slicing.IntervalCat`%0A**Module:** `BridgelandStability.IntervalCategory.Basic`%0A**Source:** BridgelandStability/IntervalCategory/Basic.lean:72%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.Slicing.IntervalCat
```

```module (module := BridgelandStability.IntervalCategory.Basic) (anchor := CategoryTheory.Triangulated.Slicing.IntervalCat) -defSite
/-- The interval subcategory `P((a, b))` of a slicing, defined as the full subcategory
on objects whose HN phases all lie in `(a, b)`. An object `E` belongs to `P((a, b))` if
it is zero or admits an HN filtration with all phases in `(a, b)`.

This is **Bridgeland's Definition 4.1** specialized to open intervals. -/
abbrev Slicing.IntervalCat (s : Slicing C) (a b : ℝ) :=
  (s.intervalProp C a b).FullSubcategory
```

# StabilityCondition.Defs

Module `BridgelandStability.StabilityCondition.Defs` — *9* declarations (Structure, Definition)

## `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap`
%%%
tag := "shadow-entry-bridgelandstability-stabilitycondition-defs-categorytheory-triangulated-prestabilitycondition-withclassmap-56-68"
%%%

`Structure` | `BridgelandStability.StabilityCondition.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/StabilityCondition/Defs.lean#L56) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: WithClassMap&body=**Declaration:** `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap`%0A**Module:** `BridgelandStability.StabilityCondition.Defs`%0A**Source:** BridgelandStability/StabilityCondition/Defs.lean:56%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap
```

```module (module := BridgelandStability.StabilityCondition.Defs) (anchor := CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap) -defSite
/-- A Bridgeland prestability condition with respect to a class map
`v : K₀(C) → Λ`. The central charge lives on `Λ`, and the ordinary ambient
charge is recovered by precomposition with `v`. -/
@[informal "Definition 5.1"]
structure WithClassMap (v : K₀ C →+ Λ) where
  /-- The underlying slicing. -/
  slicing : Slicing C
  /-- The central charge on the class lattice `Λ`. -/
  Z : Λ →+ ℂ
  /-- Compatibility (raw). Use `σ.compat` instead. -/
  compat' : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)
```

## `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge`
%%%
tag := "shadow-entry-bridgelandstability-stabilitycondition-defs-categorytheory-triangulated-prestabilitycondition-withclassmap-charge-72-75"
%%%

`Definition` | `BridgelandStability.StabilityCondition.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/StabilityCondition/Defs.lean#L72) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: charge&body=**Declaration:** `CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge`%0A**Module:** `BridgelandStability.StabilityCondition.Defs`%0A**Source:** BridgelandStability/StabilityCondition/Defs.lean:72%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge
```

```module (module := BridgelandStability.StabilityCondition.Defs) (anchor := CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge) -defSite
/-- The central charge evaluated at the class of `E`. This is `Z(v[E])`. -/
noncomputable abbrev WithClassMap.charge {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) (E : C) : ℂ :=
  σ.Z (cl C v E)
```

## `CategoryTheory.Triangulated.slicingDist`
%%%
tag := "shadow-entry-bridgelandstability-stabilitycondition-defs-categorytheory-triangulated-slicingdist-165-171"
%%%

`Definition` | `BridgelandStability.StabilityCondition.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/StabilityCondition/Defs.lean#L165) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: slicingDist&body=**Declaration:** `CategoryTheory.Triangulated.slicingDist`%0A**Module:** `BridgelandStability.StabilityCondition.Defs`%0A**Source:** BridgelandStability/StabilityCondition/Defs.lean:165%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.slicingDist
```

```module (module := BridgelandStability.StabilityCondition.Defs) (anchor := CategoryTheory.Triangulated.slicingDist) -defSite
/-- The Bridgeland generalized metric on slicings. For slicings `s₁` and `s₂`,
this is the supremum over all nonzero objects `E` of
`max(|φ₁⁺(E) - φ₂⁺(E)|, |φ₁⁻(E) - φ₂⁻(E)|)`. -/
def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)
```

## `CategoryTheory.Triangulated.StabilityCondition.WithClassMap`
%%%
tag := "shadow-entry-bridgelandstability-stabilitycondition-defs-categorytheory-triangulated-stabilitycondition-withclassmap-123-129"
%%%

`Structure` | `BridgelandStability.StabilityCondition.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/StabilityCondition/Defs.lean#L123) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: WithClassMap&body=**Declaration:** `CategoryTheory.Triangulated.StabilityCondition.WithClassMap`%0A**Module:** `BridgelandStability.StabilityCondition.Defs`%0A**Source:** BridgelandStability/StabilityCondition/Defs.lean:123%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.StabilityCondition.WithClassMap
```

```module (module := BridgelandStability.StabilityCondition.Defs) (anchor := CategoryTheory.Triangulated.StabilityCondition.WithClassMap) -defSite
/-- A Bridgeland stability condition with respect to a class map `v : K₀(C) → Λ`.
This is the locally-finite refinement of `PreStabilityCondition.WithClassMap`. -/
@[informal "Definition 5.7"]
structure WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  /-- The slicing is locally finite. -/
  locallyFinite : slicing.IsLocallyFinite C
```

## `CategoryTheory.Triangulated.stabSeminorm`
%%%
tag := "shadow-entry-bridgelandstability-stabilitycondition-defs-categorytheory-triangulated-stabseminorm-173-181"
%%%

`Definition` | `BridgelandStability.StabilityCondition.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/StabilityCondition/Defs.lean#L173) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: stabSeminorm&body=**Declaration:** `CategoryTheory.Triangulated.stabSeminorm`%0A**Module:** `BridgelandStability.StabilityCondition.Defs`%0A**Source:** BridgelandStability/StabilityCondition/Defs.lean:173%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.stabSeminorm
```

```module (module := BridgelandStability.StabilityCondition.Defs) (anchor := CategoryTheory.Triangulated.stabSeminorm) -defSite
/-- The Bridgeland seminorm `‖U‖_σ` on `Hom(Λ, ℂ)`. For a class-map stability
condition `σ = (Z, P)` with class map `v : K₀(D) → Λ` and a group homomorphism
`U : Λ → ℂ`, this is `sup { |U(v[E])| / |Z(v[E])| : E is σ-semistable and nonzero }`.

When `v = id` (i.e., `Λ = K₀(D)`), this recovers Bridgeland's original seminorm. -/
def stabSeminorm {v : K₀ C →+ Λ} (σ : StabilityCondition.WithClassMap C v)
    (U : Λ →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (cl C v E)‖ / ‖σ.charge E‖)
```

## `CategoryTheory.Triangulated.basisNhd`
%%%
tag := "shadow-entry-bridgelandstability-stabilitycondition-defs-categorytheory-triangulated-basisnhd-185-189"
%%%

`Definition` | `BridgelandStability.StabilityCondition.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/StabilityCondition/Defs.lean#L185) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: basisNhd&body=**Declaration:** `CategoryTheory.Triangulated.basisNhd`%0A**Module:** `BridgelandStability.StabilityCondition.Defs`%0A**Source:** BridgelandStability/StabilityCondition/Defs.lean:185%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.basisNhd
```

```module (module := BridgelandStability.StabilityCondition.Defs) (anchor := CategoryTheory.Triangulated.basisNhd) -defSite
/-- The basis neighborhood `B_ε(σ)` for the Bridgeland topology on `Stab_v(D)`. -/
def basisNhd {v : K₀ C →+ Λ} (σ : StabilityCondition.WithClassMap C v) (ε : ℝ) :
    Set (StabilityCondition.WithClassMap C v) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}
```

## `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace`
%%%
tag := "shadow-entry-bridgelandstability-stabilitycondition-defs-categorytheory-triangulated-stabilitycondition-withclassmap-topologicalspace-191-201"
%%%

`Definition` | `BridgelandStability.StabilityCondition.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/StabilityCondition/Defs.lean#L191) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: topologicalSpace&body=**Declaration:** `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace`%0A**Module:** `BridgelandStability.StabilityCondition.Defs`%0A**Source:** BridgelandStability/StabilityCondition/Defs.lean:191%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace
```

```module (module := BridgelandStability.StabilityCondition.Defs) (anchor := CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace) -defSite
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
```

## `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex`
%%%
tag := "shadow-entry-bridgelandstability-stabilitycondition-defs-categorytheory-triangulated-stabilitycondition-withclassmap-componentindex-205-207"
%%%

`Definition` | `BridgelandStability.StabilityCondition.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/StabilityCondition/Defs.lean#L205) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: ComponentIndex&body=**Declaration:** `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex`%0A**Module:** `BridgelandStability.StabilityCondition.Defs`%0A**Source:** BridgelandStability/StabilityCondition/Defs.lean:205%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex
```

```module (module := BridgelandStability.StabilityCondition.Defs) (anchor := CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex) -defSite
/-- The connected-component index set for `Stab_v(D)`. -/
abbrev ComponentIndex (v : K₀ C →+ Λ) :=
  _root_.ConnectedComponents (StabilityCondition.WithClassMap C v)
```

## `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component`
%%%
tag := "shadow-entry-bridgelandstability-stabilitycondition-defs-categorytheory-triangulated-stabilitycondition-withclassmap-component-209-211"
%%%

`Definition` | `BridgelandStability.StabilityCondition.Defs` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/StabilityCondition/Defs.lean#L209) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: Component&body=**Declaration:** `CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component`%0A**Module:** `BridgelandStability.StabilityCondition.Defs`%0A**Source:** BridgelandStability/StabilityCondition/Defs.lean:209%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component
```

```module (module := BridgelandStability.StabilityCondition.Defs) (anchor := CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component) -defSite
/-- The type of `v`-relative stability conditions in a fixed connected component. -/
abbrev Component (v : K₀ C →+ Λ) (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :=
  {σ : StabilityCondition.WithClassMap C v // _root_.ConnectedComponents.mk σ = cc}
```

# IntervalCategory.QuasiAbelian

Module `BridgelandStability.IntervalCategory.QuasiAbelian` — *2* declarations (Theorem)

## `CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels`
%%%
tag := "shadow-entry-bridgelandstability-intervalcategory-quasiabelian-categorytheory-triangulated-slicing-intervalcat-haskernels-118-121"
%%%

`Theorem` | `BridgelandStability.IntervalCategory.QuasiAbelian` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/IntervalCategory/QuasiAbelian.lean#L118) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: intervalCat_hasKernels&body=**Declaration:** `CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels`%0A**Module:** `BridgelandStability.IntervalCategory.QuasiAbelian`%0A**Source:** BridgelandStability/IntervalCategory/QuasiAbelian.lean:118%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels
```

```collapsibleModule (module := BridgelandStability.IntervalCategory.QuasiAbelian) (anchor := CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels) -defSite
noncomputable instance Slicing.intervalCat_hasKernels (s : Slicing C) :
    HasKernels (s.IntervalCat C a b) :=
  ⟨fun {X Y} f ↦ Slicing.intervalCat_hasKernel (C := C) (s := s)
    (a := a) (b := b) (X := X) (Y := Y) f⟩
```

## `CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels`
%%%
tag := "shadow-entry-bridgelandstability-intervalcategory-quasiabelian-categorytheory-triangulated-slicing-intervalcat-hascokernels-199-202"
%%%

`Theorem` | `BridgelandStability.IntervalCategory.QuasiAbelian` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/IntervalCategory/QuasiAbelian.lean#L199) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: intervalCat_hasCokernels&body=**Declaration:** `CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels`%0A**Module:** `BridgelandStability.IntervalCategory.QuasiAbelian`%0A**Source:** BridgelandStability/IntervalCategory/QuasiAbelian.lean:199%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels
```

```collapsibleModule (module := BridgelandStability.IntervalCategory.QuasiAbelian) (anchor := CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels) -defSite
noncomputable instance Slicing.intervalCat_hasCokernels (s : Slicing C) :
    HasCokernels (s.IntervalCat C a b) :=
  ⟨fun {X Y} f ↦ Slicing.intervalCat_hasCokernel (C := C) (s := s)
    (a := a) (b := b) (X := X) (Y := Y) f⟩
```

# IntervalCategory.FiniteLength

Module `BridgelandStability.IntervalCategory.FiniteLength` — *1* declarations (Structure)

## `CategoryTheory.Triangulated.Slicing.IsLocallyFinite`
%%%
tag := "shadow-entry-bridgelandstability-intervalcategory-finitelength-categorytheory-triangulated-slicing-islocallyfinite-260-279"
%%%

`Structure` | `BridgelandStability.IntervalCategory.FiniteLength` | [Source](https://github.com/mattrobball/BridgelandStability/blob/main/BridgelandStability/IntervalCategory/FiniteLength.lean#L260) | [Open Issue](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review: IsLocallyFinite&body=**Declaration:** `CategoryTheory.Triangulated.Slicing.IsLocallyFinite`%0A**Module:** `BridgelandStability.IntervalCategory.FiniteLength`%0A**Source:** BridgelandStability/IntervalCategory/FiniteLength.lean:260%0A**Status:** proved%0A%0A---%0A%0A**Describe the issue:**%0A&labels=exposition-review)

```declAnchorEmbed
CategoryTheory.Triangulated.Slicing.IsLocallyFinite
```

```module (module := BridgelandStability.IntervalCategory.FiniteLength) (anchor := CategoryTheory.Triangulated.Slicing.IsLocallyFinite) -defSite
/-- A slicing is locally finite if there exists `η > 0` with `η < 1/2` such that every
object in each thin interval category `P((t-η, t+η))` has finite length in the
quasi-abelian sense, i.e. ACC/DCC on strict subobjects.

The extra bound `η < 1/2` is a harmless normalization: any Bridgeland witness may be
shrunk to such an `η`, and then the width `2η` is at most `1`, so the thin interval
category carries the exact / quasi-abelian structure proved above. -/
@[informal "Definition 5.7" "per-object strict finite length is weaker than finite length of all chains (paper's assumption)"]
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
```
