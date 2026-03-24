# Naming Audit for Bridgeland Stability

**Date**: 2026-03-22, updated 2026-03-23  
**Basis**: corrected Mathlib-style reading after checking both the official naming guidance and
nearby Mathlib wrapper implementations

## Summary

The repo does have real naming debt, but the earlier “all `Prop` names should be `snake_case`”
story was too crude.

The corrected picture is:

- some names are bad because they are content-free, not because of casing;
- some names are fine because they are proposition-like named objects rather than theorem proofs;
- some theorem names really do need theorem-style lowercase names;
- and one part of the naming problem is blocked on a design issue: the implementation of
  `NumericalStabilityCondition`.

Since the first draft of this audit, `EulerFormDescends` has been removed from the repo. The
current naming discussion should therefore focus on the live API, not on deleted abstractions.

## Good as-is on naming grounds

These should not be renamed just because of casing:

- `StabilityFunction.HasHNProperty`
- `IsFiniteType`
- `NumericallyFinite`
- `AbelianHNFiltration`

These may still be revisited for broader API reasons, but they are not immediate naming mistakes.

## Highest-priority naming debt

### 1. Recently resolved in the first rename pass

The repo no longer uses the content-free name `bridgelandTheorem_1_2`. It has been renamed to the
contentful proposition-object name:

- `StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents`

Likewise, the first batch of obvious theorem-style casing fixes is now done:

- `StabilityCondition.false_of_all_hn_phases_below`
- `StabilityCondition.false_of_all_hn_phases_above`
- `StabilityCondition.false_of_gt_and_le_phases`

### 2. Rename now: public names built from proof letters or placeholder stems

These are poor public API names even if the proofs are mathematically correct:

- `StabilityCondition.P_of_Q_of_P_semistable`
- `P_phi_of_truncation_of_P_phi_cone`
- `sigmaSemistable_hasDeformedHN`
- `SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound`

The issue is not just style. These names still expose scratch proof letters (`P`, `Q`) or
argument-by-argument scaffolding rather than the mathematical conclusion.

## Design-linked naming debt

### 1. The Corollary 1.3 family is blocked on the numerical-wrapper design

The content-free theorem-number names have now been replaced by:

- `NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents`
- `NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent`

But the best replacement depends on the implementation choice for numerical stability conditions:

- if the current wrapper stays, then the most honest namespace is
  `NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents`;
- if the implementation is refactored into a subtype-style stability-condition specialization, then
  a `StabilityCondition.Numerical...` family becomes more plausible.

For the complex-manifold theorem, the final name should be chosen to match the settled namespace of
the underlying proposition-object.

### 2. The biggest design-linked naming issue is still `NumericalStabilityCondition`

- `NumericalStabilityCondition`

The current implementation is:

- a separate structure,
- with a `toStabilityCondition` field,
- and one extra proof field recording factorization through numerical `K₀`.

Compared with nearby Mathlib patterns, that is not the cleanest implementation.

The nearest Mathlib implementations suggest:

1. proof-only wrappers are usually subtypes;
2. richer bundled wrappers usually use `extends`.

So the current implementation lands in a non-idiomatic middle ground.

That matters for naming because the theorem-family namespace depends on whether numerical stability
conditions are meant to be:

- their own bundled wrapper object,
- or a subtype-style specialization of stability conditions.

This should be resolved before finalizing the Corollary 1.3 theorem names.

## Secondary naming debt

These are not the first things to fix, but they are real style pressure points.

### 1. Abbreviation-heavy public API

- `IsMDQ`
- `FirstStrictSES`
- `PhiPlusHN`
- `PhiPlusMDQ`
- `WPhase`
- `DeformedGtLe`

Some of these are acceptable as internal working names. They are weak as long-term public names.

### 2. The `H0prime` family

This is the least Mathlib-like naming family in the repo.

Examples include:

- `H0prime`
- `H0primeFunctor`
- `H0ObjIsoH0prime`
- `toH0primeHom`

The stem itself is weak, and the family should probably be renamed as a family rather than by
one-off local edits.

### 3. Compact but opaque “class” names

- `heartCohClass`
- `heartCohClassSum`
- `ZOnHeartK0`
- `heartK0ToK0`

These are understandable once you know the development, but they are not yet strong public API.

## Names that are probably acceptable, but worth watching

These are not urgent rename targets, but they should be reconsidered if the API is being polished
for upstreaming:

- `SectorFiniteLength`
- `WideSectorFiniteLength`
- `ThinFiniteLengthInInterval`

These are not clear naming violations in the same way as the theorem-number names or the
capitalized theorem proofs. The main question here is not casing but whether the names are the
best mathematical presentation of the underlying propositions.

## Recommended order of attack

1. Rename the remaining public proof-scaffolding names (`P_of_Q_of_P_semistable`, etc.).
2. Settle the implementation of `NumericalStabilityCondition`.
3. Clean up the larger abbreviation families, especially `H0prime`.

## Bottom line

The repo is not in naming-shape for Mathlib-quality upstreaming yet, but the problems are not all
the same kind.

The highest-value fixes are:

- finish the remaining theorem-proof cleanup,
- eliminate the public proof-scaffolding names,
- and stop deferring the design question behind `NumericalStabilityCondition`.
