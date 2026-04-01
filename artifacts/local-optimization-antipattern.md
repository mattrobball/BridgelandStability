# Local Optimization Antipattern in AI-Generated Code

## The Problem

AI models have a STRONG impulse toward **local optimization**: minimal changes
to get things working, papering over architectural mismatches with
`simpa`/casts/bridges rather than building at the right level of generality
from the start.

This is **antithetical to the Mathlib ethos**. Mathlib values correct
abstractions, building at the right level of generality, and paying the
upfront cost to avoid technical debt.

## Concrete Example: LocalHomeomorphism.lean

The project has `WithClassMap C v` as the universal abstraction for stability
conditions with a class map. `StabilityCondition C` is just `WithClassMap C id`.
The design intent is that everything flows from `WithClassMap C v`, with
`v = id` and `v = numericalQuotientMap` as specializations.

But the entire 650-line LocalHomeomorphism.lean — `componentRep`,
`componentSeminormSubgroup`, the norm tower, the 340-line proof — was built
directly on `StabilityCondition C` (the `v = id` specialization). Then at the
very end, an awkward `simpa` bridge stitches it back to the `WithClassMap`
statement:

```lean
theorem centralChargeIsLocalHomeomorphOnConnectedComponents :
    StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents C := by
  intro cc
  let cc' : ConnectedComponents (StabilityCondition C) := cc  -- cast!
  let M := componentTopologicalLinearLocalModel C cc'
  ...
  · simpa [cc', WithClassMap.Component] using M.isLocalHomeomorph_chargeMap
```

This is the local-optimization antipattern: the model built the proof at the
easiest level (`v = id`) and then patched the mismatch, rather than building
at the right level (`WithClassMap C v`) from the start.

## How to Detect

- A `simpa`/cast bridge between abstraction levels at the end of a proof is a
  code smell — it means the proof was done at the wrong level.
- Two parallel definition hierarchies doing the same thing for different types
  (e.g., `componentStabilityCondition` vs `Component`) signal that one should
  be generalized to subsume the other.
- If the project has a parameterized abstraction (`WithClassMap C v`), and new
  code targets a specialization (`StabilityCondition C`), the code is at the
  wrong level.

## How to Prevent

When reviewing or generating code:

1. **Identify the intended abstraction level** before writing. Read the
   project's type hierarchy. If `WithClassMap C v` exists, build on it.
2. **Parameterize from the start.** Don't prove for `v = id` and bridge later.
3. **Treat compilation as necessary but not sufficient.** Code that compiles
   but builds at the wrong abstraction level is technical debt.
4. **The abstraction agent prompt should check for this.** See changes below.
