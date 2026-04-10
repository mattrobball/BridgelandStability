# Comparator Setup Plan for BridgelandStability

## Date: 2026-03-24

## Summary

Set up `leanprover/comparator` to verify Corollary 1.3
(`NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent`).

## Metaprogram Analysis

Ran `Expr.foldConsts` recursively on the theorem's type, descending into
bodies of non-theorem declarations only. Result: **60 data-carrying
declarations from 11 modules**.

### Declarations by module

**EulerForm (10):** `NumericalK₀`, `NumericalK₀.instAddCommGroup`,
`NumericallyFinite`, `eulerForm`, `eulerFormInner`,
`eulerFormInner_isTriangleAdditive`, `eulerFormObj_contravariant_triangleAdditive`,
`eulerFormRad`, `numericalQuotientMap`, `numericalQuotientMap._proof_1`

**GrothendieckGroup (8):** `IsTriangleAdditive`, `K₀`, `K₀.instAddCommGroup`,
`K₀.lift`, `K₀.lift._proof_1`, `K₀.lift._proof_2`, `K₀.of`, `K₀Subgroup`

**IntervalCategory.FiniteLength (1):** `Slicing.IsLocallyFinite`

**NumericalStability (2):** `IsFiniteType`, `eulerFormObj`

**NumericalStabilityManifold (2):** `NumericalComponent`, theorem itself

**PostnikovTower (3):** `PostnikovTower`, `PostnikovTower.n`,
`PostnikovTower.triangle`

**Slicing.Basic (5):** `HNFiltration`, `HNFiltration.toPostnikovTower`,
`HNFiltration.φ`, `Slicing`, `Slicing.P`

**Slicing.Phase (8):** `HNFiltration.exists_nonzero_first`,
`HNFiltration.exists_nonzero_last`,
`HNFiltration.isZero_factor_last_of_hom_eq_zero._proof_1`, `Slicing.phiMinus`,
`Slicing.phiMinus._proof_1`, `Slicing.phiMinus._proof_2`, `Slicing.phiPlus`,
`Slicing.phiPlus._proof_1`

**StabilityCondition.Basic (12):** `PreStabilityCondition.WithClassMap`,
`PreStabilityCondition.WithClassMap.Z`, `.mk`, `.slicing`,
`.toPreStabilityCondition`, `StabilityCondition`,
`StabilityCondition.WithClassMap`, `.locallyFinite`, `.mk`,
`.toStabilityCondition`, `.toWithClassMap`, `stabilityCondition_compat_apply`

**StabilityCondition.Seminorm (2):** `slicingDist`, `stabSeminorm`

**StabilityCondition.Topology (7):** `WithClassMap.Component`,
`WithClassMap.ComponentIndex`, `WithClassMap.instTopologicalSpace`,
`WithClassMap.topologicalSpace`, `StabilityCondition.topologicalSpace`,
`StabilityCondition.topologicalSpace._proof_1`, `basisNhd`

## Design: Defs files

Extract the 60 declarations into `Defs.lean` files:

- `Slicing/Defs.lean` — 13 decls from `Basic.lean` + `Phase.lean`
- `StabilityCondition/Defs.lean` — 21 decls from `Basic.lean` + `Seminorm.lean` + `Topology.lean`
- `EulerFormDefs.lean` — 22 decls from `EulerForm.lean` + `NumericalStability.lean` + `NumericalStabilityManifold.lean`

`PostnikovTower.lean` and `GrothendieckGroup.lean` are already mostly data-carrying.

### Defs import chain

```
EulerFormDefs.lean
├─ NumericalStability
│  └─ StabilityCondition/Defs.lean
│     └─ Slicing/Defs.lean
│        └─ PostnikovTower.lean
│           └─ GrothendieckGroup.lean
└─ IntervalCategory/FiniteLength.lean
```

### Spec file

`spec/Main.lean` imports `EulerFormDefs.lean` + Mathlib manifold modules.

## Comparator Config

```json
{
  "challenge_module": "BridgelandSpec.Main",
  "solution_module": "BridgelandStability.NumericalStabilityManifold",
  "theorem_names": [
    "CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent"
  ],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
```

## Reference: Real-world comparator users

- `girving/aks` — root-level `Challenge.lean`, builds comparator from source
- `GasStationManager/ArtificialTheorems` — `Spec` module hierarchy, per-theorem configs
- `Smaug123/flp-theorem-vibed` — root-level `Challenge.lean`, Nix-based build

All use `lake env comparator config.json`. None use comparator as a GitHub Action.
