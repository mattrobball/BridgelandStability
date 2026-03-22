# Naming Audit for Bridgeland Stability

**Date**: 2026-03-22  
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

## Good as-is on naming grounds

These should not be renamed just because of casing:

- `StabilityFunction.HasHNProperty`
- `IsFiniteType`
- `EulerFormDescends`
- `NumericallyFinite`
- `AbelianHNFiltration`

These may still be revisited for broader API reasons, but they are not immediate naming mistakes.

## Highest-priority naming debt

### 1. Theorem-number names that hide the content

- `bridgelandTheorem_1_2`
- `bridgelandCorollary_1_3`
- `bridgelandCorollary_1_3_complexManifold`

These are the clearest naming failures.

The problem is not mainly casing. The problem is that the names say nothing about the mathematics.

For Theorem 1.2, the current best replacement is:

- `StabilityCondition.CentralChargeIsLocalHomeomorphOnComponents`

For Corollary 1.3, the best name depends on the implementation choice for numerical stability
conditions:

- if the current wrapper stays, then the most honest namespace is
  `NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnComponents`;
- if the implementation is refactored into a subtype-style stability-condition specialization, then
  a `StabilityCondition.Numerical...` family becomes more plausible.

For the complex-manifold theorem, the final name should be chosen only after the Corollary 1.3
namespace decision is settled.

### 2. Public theorem names with capitalized proof stems

These are genuine theorem-style naming problems:

- `StabilityCondition.False_of_all_HN_phases_below`
- `StabilityCondition.False_of_all_HN_phases_above`
- `StabilityCondition.False_of_gt_and_le_phases`

These should become theorem-style lowercase names:

- `StabilityCondition.false_of_all_hn_phases_below`
- `StabilityCondition.false_of_all_hn_phases_above`
- `StabilityCondition.false_of_gt_and_le_phases`

### 3. Public theorem names built from schematic letters

These are poor public API names even if the proof is correct:

- `StabilityCondition.P_of_Q_of_P_semistable`
- `P_phi_of_truncation_of_P_phi_cone`

These need semantic names that describe the mathematical conclusion.

### 4. Theorem names that still look like proof scaffolding

These should be theorem-style names, not development-stage proof labels:

- `sigmaSemistable_hasDeformedHN`
- `SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound`
- `gtProp_of_geProp_of_lt`

Even if some abbreviations remain, these need theorem-style normalization.

## Design-linked naming debt

The biggest design-linked naming issue is:

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

1. Replace theorem-number names with contentful names.
2. Normalize obviously theorem-style declarations to theorem-style names.
3. Settle the implementation of `NumericalStabilityCondition`.
4. Rename the semantic outliers built from placeholder letters.
5. Clean up the larger abbreviation families, especially `H0prime`.

## Bottom line

The repo is not in naming-shape for Mathlib-quality upstreaming yet, but the problems are not all
the same kind.

The highest-value fixes are:

- remove content-free theorem-number names,
- make theorem proofs look like theorem proofs,
- and stop deferring the design question behind `NumericalStabilityCondition`.
