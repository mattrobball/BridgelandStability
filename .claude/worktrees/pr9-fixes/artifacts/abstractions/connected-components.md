# Connected-Component Hierarchy Analysis

## Current Definitions

### Hierarchy A: class-map components (Defs.lean:182-203)

```lean
-- Defs.lean:182
abbrev ComponentIndex (v : K0 C ->+ L) :=
  ConnectedComponents (StabilityCondition.WithClassMap C v)

-- Defs.lean:186
abbrev Component (v : K0 C ->+ L) (cc : ComponentIndex C v) :=
  {s : WithClassMap C v // ConnectedComponents.mk s = cc}

-- Defs.lean:192
def CentralChargeIsLocalHomeomorphOnConnectedComponents {v} : Prop :=
  forall (cc : ComponentIndex C v), exists (V : Submodule C (L ->+ C)) ..., IsLocalHomeomorph ...
```

### Hierarchy B: ordinary components (LocalHomeomorphism.lean:38-267)

```lean
-- LocalHomeomorphism.lean:38
def componentRep (cc : ConnectedComponents (StabilityCondition C)) : StabilityCondition C

-- LocalHomeomorphism.lean:46
abbrev componentStabilityCondition (cc : ConnectedComponents (StabilityCondition C)) :=
  {s : StabilityCondition C // ConnectedComponents.mk s = cc}

-- LocalHomeomorphism.lean:50
def componentSeminormSubgroup (cc) : Submodule C (K0 C ->+ C)

-- LocalHomeomorphism.lean:63-139: componentNorm, componentAddGroupNorm,
--   componentNormedAddCommGroup, componentNormedSpace

-- LocalHomeomorphism.lean:142-197: componentSeminormBall, componentSeminormBasis,
--   componentSeminormTopology, isTopologicalBasis_componentSeminormBasis,
--   componentSeminormTopology_eq_normTopology

-- LocalHomeomorphism.lean:200-267: componentSeminorm_lt_top_of_mem_component,
--   componentNorm_equivalent_of_mem_component, componentZ_mem, componentZMap
```

### Hierarchy C: factorization-subtype components (NumericalStabilityManifold.lean:59-61, 337-533)

```lean
-- NumericalStabilityManifold.lean:59
abbrev ClassMapComponent (v : K0 C ->+ L)
    (cc : ConnectedComponents (ClassMapStabilityCondition C v)) :=
  {s : ClassMapStabilityCondition C v // ConnectedComponents.mk s = cc}

-- NumericalStabilityManifold.lean:337
abbrev ClassMapAmbientLocus (v : K0 C ->+ L) (cc : ConnectedComponents (StabilityCondition C)) :=
  {s : ClassMapStabilityCondition C v // ConnectedComponents.mk (s : StabilityCondition C) = cc}
```

### Hierarchy D: numerical specialization (EulerForm/Basic.lean:640-643)

```lean
-- EulerForm/Basic.lean:640
abbrev NumericalComponent [Linear k C] [IsFiniteType k C] [...]
    (cc : ComponentIndex C (numericalQuotientMap k C)) :=
  Component C (numericalQuotientMap k C) cc
```

## Critical API: What Callers Actually Need

### Load-bearing definitions

| Definition | Where used | Role |
|---|---|---|
| `componentRep` | LocalHomeomorphism.lean (50+ uses) | Chosen representative, anchors seminorm subgroup |
| `componentSeminormSubgroup` | LocalHomeomorphism.lean (~30 uses), NumericalStabilityManifold.lean (via `ComponentTopologicalLinearLocalModel`) | V(Sigma), the normed target space |
| `componentZMap` | LocalHomeomorphism.lean:310, 570 | The actual local homeomorphism map |
| `ComponentTopologicalLinearLocalModel` | LocalHomeomorphism.lean:273-298, NumericalStabilityManifold.lean (368-442, 539-660) | Packages the local-homeomorphism data non-existentially |
| `ClassMapComponent` | NumericalStabilityManifold.lean (~15 uses) | Domain for the manifold theorem per class-map component |

### Convenience/indirection wrappers (not directly load-bearing)

| Definition | Analysis |
|---|---|
| `ComponentIndex C v` | Pure alias for `ConnectedComponents (WithClassMap C v)`. Used 14 times in .lean files, but only because the manifold theorem's statement quantifies over it. Could be inlined. |
| `Component C v cc` | Pure alias for `{s : WithClassMap C v // ConnectedComponents.mk s = cc}`. Used in `CentralChargeIsLocalHomeomorphOnConnectedComponents` and the manifold theorem statements. Could be inlined. |
| `componentStabilityCondition` | Pure alias for `{s : StabilityCondition C // ConnectedComponents.mk s = cc}`. Same pattern as `Component` but for ordinary (non-class-map) stability conditions. Used ~5 times. |
| `NumericalComponent` | Pure alias specializing `Component` to `numericalQuotientMap`. Used in Spec.lean and NumericalStabilityManifold.lean. |
| `ClassMapAmbientLocus` | The double-subtype `{s : ClassMapStabilityCondition C v // mk (s : StabilityCondition C) = cc}`. Used ~10 times but only inside NumericalStabilityManifold.lean. |
| `componentSeminormBall/Basis/Topology` | Used only to prove `componentSeminormTopology_eq_normTopology`, which then lets the main proof go through. Not used outside LocalHomeomorphism.lean. |

## Duplication Findings

### Finding 1: `componentStabilityCondition` vs `Component`

These define exactly the same subtype pattern `{s : X // ConnectedComponents.mk s = cc}` but for different base types:

- `componentStabilityCondition C cc` = `{s : StabilityCondition C // ... = cc}` (LocalHomeomorphism.lean:46)
- `Component C v cc` = `{s : WithClassMap C v // ... = cc}` (Defs.lean:186)
- `ClassMapComponent C v cc` = `{s : ClassMapStabilityCondition C v // ... = cc}` (NumericalStabilityManifold.lean:59)

**Overlap context:** When `v = AddMonoidHom.id (K0 C)`, then `WithClassMap C v = StabilityCondition C`, so `Component C (AddMonoidHom.id _) cc` and `componentStabilityCondition C cc` are definitionally the same type. However, they live in different files and are never actually used interchangeably. The critical proof in LocalHomeomorphism.lean:639-647 (`centralChargeIsLocalHomeomorphOnConnectedComponents`) bridges them with a `simpa [WithClassMap.Component]`.

**Can one replace the other?** Not cleanly. The issue is that:
- Hierarchy B (`componentRep`, `componentSeminormSubgroup`, etc.) is defined for *ordinary* `ConnectedComponents (StabilityCondition C)`, not for `ConnectedComponents (WithClassMap C v)`.
- The WithClassMap component machinery needs its own component index set because the topology on `WithClassMap C v` is the induced topology, whose connected components may differ from those of `StabilityCondition C`.

The homeomorphism `homeomorphClassMapStabilityCondition` (NumericalStabilityManifold.lean:67) and `componentIndexEquivClassMapStabilityCondition` (NumericalStabilityManifold.lean:94) exist precisely to bridge between `ComponentIndex C v` and `ConnectedComponents (ClassMapStabilityCondition C v)`. This bridge is load-bearing for the manifold theorem.

### Finding 2: `componentRep` vs `classMapComponentRep`

Both are `Classical.choose cc.exists_rep` instantiated for different types:
- `componentRep`: for `ConnectedComponents (StabilityCondition C)` (LocalHomeomorphism.lean:38)
- `classMapComponentRep`: for `ConnectedComponents (ClassMapStabilityCondition C v)` (NumericalStabilityManifold.lean:445)

The duplication is structural: the same `Classical.choose cc.exists_rep` pattern. But they serve different purposes and can't easily be merged.

### Finding 3: The seminorm/norm tower on `V(Sigma)`

The tower `componentSeminormSubgroup` -> `componentNorm` -> `componentAddGroupNorm` -> `componentNormedAddCommGroup` -> `componentNormedSpace` (LocalHomeomorphism.lean:50-139) exists only for the ordinary component hierarchy. The class-map hierarchy reaches the same normed space through `ComponentTopologicalLinearLocalModel.V` which wraps the same `componentSeminormSubgroup` (LocalHomeomorphism.lean:306-312).

There is no duplication here -- the class-map hierarchy deliberately routes through the ordinary one. `componentTopologicalLinearLocalModel` (line 304) constructs its `V` field as `componentSeminormSubgroup C cc`, then inherits the `NormedAddCommGroup` and `NormedSpace` instances already built.

## Mathematical Identity and Generalization Landscape

### What is the mathematical object?

A connected component of `Stab(D)` is a connected component of a topological space. The subtype `{s : Stab(D) // ConnectedComponents.mk s = cc}` is the fiber of the quotient map `Stab(D) -> ConnectedComponents(Stab(D))` over the point `cc`. By `connectedComponents_preimage_singleton` (Mathlib), this fiber equals `connectedComponent x` for any representative `x` with `mk x = cc`.

### Mathlib connected-component infrastructure

Mathlib provides:
- `ConnectedComponents X` -- the quotient type (Topology.Connected.Clopen)
- `ConnectedComponents.mk : X -> ConnectedComponents X` -- quotient map
- `connectedComponent x : Set X` -- the connected component containing `x`
- `connectedComponents_preimage_singleton` -- `mk^{-1}({mk x}) = connectedComponent x`
- `coe_eq_coe` / `coe_eq_coe'` -- characterization of when quotient images agree
- `isOpen_connectedComponent` -- for `LocallyConnectedSpace` (Stab(D) is locally connected, proved in ConnectedComponent.lean:57)

Mathlib does NOT provide:
- A named subtype for the fiber `{s : X // ConnectedComponents.mk s = cc}`.
- Any per-component normed space construction (this is specific to Bridgeland theory).

### Could the component machinery use Mathlib more directly?

**The subtype pattern `{s : X // ConnectedComponents.mk s = cc}` is universal.** It appears identically for four different base types in this project. Mathlib does not name this fiber type, but the project could define it once:

```lean
def ConnectedComponents.fiber (cc : ConnectedComponents X) : Type _ :=
  {x : X // ConnectedComponents.mk x = cc}
```

However, this would only save abbreviation definitions -- the real complexity is in the normed space construction and the proofs, not in the subtype definition.

**The seminorm subgroup and norm construction are Bridgeland-specific.** These cannot be replaced by any Mathlib infrastructure. The seminorm is defined in terms of suprema of ratios `|U(E)| / |Z(E)|` over semistable objects, and the proof that it yields a genuine norm on `V(Sigma)` requires Bridgeland-specific arguments (Lemma 6.2, etc.).

## Proposal

### Assessment: The hierarchies are structurally necessary, but the naming introduces unnecessary indirection.

The project has four "hierarchy layers" for connected components, but they serve genuinely different mathematical purposes:

1. **Ordinary components** (Hierarchy B): The normed-space construction `V(Sigma)` and the actual local homeomorphism proof (Theorem 1.2). This is the mathematical core.

2. **Class-map components** (Hierarchy A): The `ComponentIndex`/`Component` types parameterized by the class map `v`. These are the statement types for the general theorem.

3. **Factorization-subtype components** (Hierarchy C): `ClassMapComponent` and `ClassMapAmbientLocus`. These exist because the manifold theorem (Corollary 1.3) needs to go through the factorization subtype `ClassMapStabilityCondition C v` to get finite-dimensionality.

4. **Numerical specialization** (Hierarchy D): `NumericalComponent` = `Component` specialized to `numericalQuotientMap`. This is a one-line abbreviation.

### What can be simplified

**1. Inline `ComponentIndex` and `Component` (Defs.lean:182-187).**

These are `abbrev`s that add names without adding API. They are used in theorem statements but callers always see through them. The only values they provide are:
- Shorter names in theorem signatures.
- Searchability.

**Verdict: Keep them.** They are abbreviations and cost nothing at elaboration time. The names `ComponentIndex` and `Component` are meaningful and used in ~14 and ~12 places respectively. Removing them would make theorem statements harder to read.

**2. Inline `componentStabilityCondition` (LocalHomeomorphism.lean:46).**

This is used in only 5 places and is just `{s : StabilityCondition C // ConnectedComponents.mk s = cc}`. It duplicates the pattern of `Component` but for the case `v = id`.

**Verdict: Replace with direct use of the subtype.** This name adds marginal value and creates confusion about its relationship to `Component`. The 5 use sites can simply write the subtype.

**3. Inline `NumericalComponent` (EulerForm/Basic.lean:640).**

**Verdict: Keep.** It is a one-line abbreviation that appears in the most important theorem statement (Corollary 1.3). Its presence makes the theorem readable.

**4. Consider merging `ClassMapComponent` with `Component`.**

`ClassMapComponent C v cc` = `{s : ClassMapStabilityCondition C v // ConnectedComponents.mk s = cc}` where `ClassMapStabilityCondition C v = {s : StabilityCondition C // s.FactorsThrough v}`.

`Component C v cc` = `{s : WithClassMap C v // ConnectedComponents.mk s = cc}` where `WithClassMap C v` bundles `(Z' : L ->+ C, slicing, compat)`.

These are *not* the same type -- they have different base types. The homeomorphism between them (when `v` is surjective) is `homeomorphClassMapComponent` (NumericalStabilityManifold.lean:115). This homeomorphism is load-bearing for the manifold theorem.

**Verdict: Cannot merge.** The two types serve different purposes:
- `Component` is the domain for the statement of Theorem 1.2 (in terms of the bundled class-map type).
- `ClassMapComponent` is the domain for the manifold construction (in terms of the factorization subtype, where finite-dimensionality is accessible).

**5. The seminorm/norm tower is not duplicated -- no action needed.**

### Concrete Lean code sketch: Remove `componentStabilityCondition`

The only change that would reduce genuine duplication without breaking the structure:

```lean
-- In LocalHomeomorphism.lean, REMOVE:
-- abbrev componentStabilityCondition (cc : ConnectedComponents (StabilityCondition C)) :=
--   {s : StabilityCondition C // ConnectedComponents.mk s = cc}

-- Replace at use sites with the subtype directly:

-- LocalHomeomorphism.lean:266
def componentZMap (cc : ConnectedComponents (StabilityCondition C)) :
    {s : StabilityCondition C // ConnectedComponents.mk s = cc} ->
      componentSeminormSubgroup C cc :=
  fun <s, hs> => <s.Z, componentZ_mem C cc s hs>

-- LocalHomeomorphism.lean:295
def chargeMap (M : ComponentTopologicalLinearLocalModel C cc) :
    {s : StabilityCondition C // ConnectedComponents.mk s = cc} -> M.V :=
  fun <s, hs> => <s.Z, M.mem_charge s hs>

-- LocalHomeomorphism.lean:309 (local let binding)
let comp := {s : StabilityCondition C // ConnectedComponents.mk s = cc}

-- NumericalStabilityManifold.lean:394
{x : {s : StabilityCondition C // ConnectedComponents.mk s = cc} //
  ComponentTopologicalLinearLocalModel.chargeMap M x in
    ambientClassMapFactorSubmodule v M}
```

### Scope and cost

- **Scope:** 5 use sites in 2 files.
- **Cost:** Minimal -- just inline the abbreviation.
- **Risk:** Very low -- `componentStabilityCondition` is an `abbrev`, so callers already see through it.
- **Kill switch:** Restore the `abbrev` line.

### The deeper question: Is there a unifying abstraction?

The user asks whether a single abstraction could capture all four hierarchies. The answer is:

**No useful unifying abstraction exists.**

The reason is that the four hierarchies differ in their *base types* (ordinary stability conditions, bundled class-map, factorization subtype, numerical specialization), and the connected-component subtype pattern `{x : X // ConnectedComponents.mk x = cc}` is already the simplest possible expression of "fiber of the quotient map." There is nothing to abstract over -- the pattern is already a single-line subtype.

The real complexity is in the *data attached to components* (seminorm subgroup, norm, local homeomorphism), and this data is specific to `StabilityCondition C`. It cannot be generalized to arbitrary topological spaces because it depends on Bridgeland-specific structures (semistable objects, central charges, HN filtrations).

### Summary

| Definition | Verdict | Reason |
|---|---|---|
| `ComponentIndex` | Keep | Meaningful name, used in 14 places |
| `Component` | Keep | Meaningful name, used in 12 places, appears in key theorem statements |
| `componentStabilityCondition` | Remove | Duplicates `Component` pattern, used in only 5 places, creates naming confusion |
| `NumericalComponent` | Keep | One-line specialization appearing in the main theorem statement |
| `ClassMapComponent` | Keep | Different base type from `Component`, load-bearing for manifold theorem |
| `ClassMapAmbientLocus` | Keep | Used in ~10 places, genuinely needed intermediate type |
| `componentRep` | Keep | Load-bearing for entire normed-space construction |
| `classMapComponentRep` | Keep | Load-bearing for manifold theorem's basepoint |
| `componentSeminormSubgroup` and norm tower | Keep | Mathematical core, no duplication |
| `ComponentTopologicalLinearLocalModel` | Keep | Non-existential packaging, heavily used |
| `CentralChargeIsLocalHomeomorphOnConnectedComponents` | Keep | Statement of Theorem 1.2 |

The connected-component hierarchy looks heavyweight at first glance, but nearly every definition is either (a) a one-line abbreviation that costs nothing, or (b) a load-bearing construction with significant proof content. The one genuine redundancy is `componentStabilityCondition`, which should be inlined.
