# Connected-Component Hierarchy: Abstraction-Level Audit (v2)

## Current Definitions (brief)

The connected-component machinery spans four source files and serves two end theorems:
Bridgeland's Theorem 1.2 (central charge is a local homeomorphism on each connected component
of Stab(D)) and Corollary 1.3 (each connected component of numerical stability conditions is a
finite-dimensional complex manifold).

### The type hierarchy

```
WithClassMap C v                    -- bundled (Z : Lambda ->+ C, slicing, compat)
  where v : K0 C ->+ Lambda
  topology: induced from StabilityCondition C via toStabilityCondition

StabilityCondition C                -- abbrev for WithClassMap C (AddMonoidHom.id (K0 C))
  topology: GenerateFrom {basisNhd C sigma eps | ...}

ClassMapStabilityCondition C v      -- {sigma : StabilityCondition C // sigma.FactorsThrough v}
  topology: subspace of StabilityCondition C

NumericalStabilityCondition k C     -- abbrev for WithClassMap C (numericalQuotientMap k C)
```

### The definitions under analysis

| Name | File:Line | Definition |
|---|---|---|
| `ComponentIndex C v` | Defs.lean:182 | `ConnectedComponents (WithClassMap C v)` |
| `Component C v cc` | Defs.lean:186 | `{sigma : WithClassMap C v // mk sigma = cc}` |
| `componentRep C cc` | LocalHomeomorphism.lean:38 | `Classical.choose cc.exists_rep` for `ConnectedComponents (StabilityCondition C)` |
| `componentStabilityCondition C cc` | LocalHomeomorphism.lean:46 | `{sigma : StabilityCondition C // mk sigma = cc}` |
| `componentSeminormSubgroup C cc` | LocalHomeomorphism.lean:50 | `Submodule C (K0 C ->+ C)` with carrier `finiteSeminormSubgroup C (componentRep C cc)` |
| `ComponentTopologicalLinearLocalModel C cc` | LocalHomeomorphism.lean:273 | Structure bundling V, norm instances, mem_charge, isLocalHomeomorph_chargeMap |
| `NumericalComponent k C cc` | EulerForm/Basic.lean:640 | `Component C (numericalQuotientMap k C) cc` |
| `ClassMapComponent C v cc` | NumericalStabilityManifold.lean:59 | `{sigma : ClassMapStabilityCondition C v // mk sigma = cc}` |
| `classMapComponentRep C v cc` | NumericalStabilityManifold.lean:445 | `Classical.choose cc.exists_rep` for `ConnectedComponents (ClassMapStabilityCondition C v)` |
| `ClassMapAmbientLocus C v cc` | NumericalStabilityManifold.lean:337 | `{sigma : ClassMapStabilityCondition C v // mk (sigma : StabilityCondition C) = cc}` |

## Critical API (the subset callers actually need)

### Load-bearing (proof content or heavily consumed)

1. **`componentRep C cc`** + **`mk_componentRep`**: Anchors the entire seminorm-subgroup / norm construction. Used 50+ times in LocalHomeomorphism.lean. Consumed downstream in NumericalStabilityManifold.lean (via `componentSeminormSubgroup` and `ComponentTopologicalLinearLocalModel`).

2. **`componentSeminormSubgroup C cc`**: The carrier of V(Sigma). Consumed by:
   - componentNorm, componentAddGroupNorm, componentNormedAddCommGroup, componentNormedSpace (the norm tower, LocalHomeomorphism.lean:63-139)
   - componentSeminormBall, componentSeminormBasis, componentSeminormTopology (topology, LocalHomeomorphism.lean:142-169)
   - componentSeminorm_lt_top_of_mem_component, componentNorm_equivalent_of_mem_component (comparison, LocalHomeomorphism.lean:200-253)
   - componentZ_mem, componentZMap (charge map construction, LocalHomeomorphism.lean:256-267)
   - ComponentTopologicalLinearLocalModel.V field (LocalHomeomorphism.lean:276)

3. **`ComponentTopologicalLinearLocalModel C cc`**: Non-existential reusable package. Consumed by:
   - `ambientClassMapFactorSubmodule` (NumericalStabilityManifold.lean:377)
   - `ambientClassMapChargeMap` (NumericalStabilityManifold.lean:383)
   - `classMapAmbientLocusHomeomorphChargePreimage` (NumericalStabilityManifold.lean:392)
   - `ambientClassMapChargeMap_isLocalHomeomorph` (NumericalStabilityManifold.lean:433)
   - `ambientClassMapFactorSubmodule_finiteDimensional` (NumericalStabilityManifold.lean:539)
   - `existsLocalHomeomorphToComplexModelOnConnectedComponent` (NumericalStabilityManifold.lean:632)

4. **`Component C v cc`**: Appears in the statement of `CentralChargeIsLocalHomeomorphOnConnectedComponents` (Defs.lean:200) and the manifold theorem (NumericalStabilityManifold.lean:743).

5. **`ClassMapComponent C v cc`**: Domain for `existsLocalHomeomorphToComplexModelOnConnectedComponent` and `existsComplexManifoldOnConnectedComponent` (NumericalStabilityManifold.lean:638, 722).

### Convenience wrappers (one-line abbreviations)

- `ComponentIndex C v`: alias for `ConnectedComponents (WithClassMap C v)`. Used ~14 times.
- `componentStabilityCondition C cc`: alias for `{sigma : StabilityCondition C // mk sigma = cc}`. Used ~5 times. Definitionally equal to `Component C (AddMonoidHom.id _) cc`.
- `NumericalComponent k C cc`: alias for `Component C (numericalQuotientMap k C) cc`. Used ~4 times.

---

## PHASE 1.5: Abstraction-Level Audit

### STEP A -- OBSERVATION (factual only, no judgments)

#### Definitions under analysis

DEFINITION: `ComponentIndex C v`
FILE:LINE: Defs.lean:182
ACCEPTS: `C : Type u` (category with full triangulated structure), `v : K0 C ->+ Lambda`
RETURNS: `Type` (specifically `ConnectedComponents (WithClassMap C v)`)
PARAMETERIZED BY: `v : K0 C ->+ Lambda`, `Lambda : Type u'`
COERCIONS USED INTERNALLY: none (it is an abbreviation)

DEFINITION: `Component C v cc`
FILE:LINE: Defs.lean:186
ACCEPTS: `C`, `v : K0 C ->+ Lambda`, `cc : ComponentIndex C v`
RETURNS: `Type` (specifically `{sigma : WithClassMap C v // mk sigma = cc}`)
PARAMETERIZED BY: `v`, `Lambda`
COERCIONS USED INTERNALLY: none (abbreviation)

DEFINITION: `componentRep C cc`
FILE:LINE: LocalHomeomorphism.lean:38
ACCEPTS: `C`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `StabilityCondition C`
PARAMETERIZED BY: nothing beyond `C` -- operates at `v = id` only
COERCIONS USED INTERNALLY: none

DEFINITION: `componentStabilityCondition C cc`
FILE:LINE: LocalHomeomorphism.lean:46
ACCEPTS: `C`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `Type` (specifically `{sigma : StabilityCondition C // mk sigma = cc}`)
PARAMETERIZED BY: nothing beyond `C` -- operates at `v = id` only
COERCIONS USED INTERNALLY: none

DEFINITION: `componentSeminormSubgroup C cc`
FILE:LINE: LocalHomeomorphism.lean:50
ACCEPTS: `C`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `Submodule C (K0 C ->+ C)`
PARAMETERIZED BY: nothing beyond `C` -- operates at `v = id` only
COERCIONS USED INTERNALLY: uses `componentRep C cc` internally to pick a base point

DEFINITION: `componentNorm C cc`
FILE:LINE: LocalHomeomorphism.lean:63
ACCEPTS: `C`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `Norm (componentSeminormSubgroup C cc)`
PARAMETERIZED BY: nothing beyond `C` -- `v = id` only
COERCIONS USED INTERNALLY: coerces `U : componentSeminormSubgroup C cc` to `K0 C ->+ C`

DEFINITION: `componentAddGroupNorm C cc`
FILE:LINE: LocalHomeomorphism.lean:69
ACCEPTS: `C`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `AddGroupNorm (componentSeminormSubgroup C cc)`
PARAMETERIZED BY: nothing beyond `C`
COERCIONS USED INTERNALLY: coerces submodule elements to `K0 C ->+ C`

DEFINITION: `componentNormedAddCommGroup C cc`
FILE:LINE: LocalHomeomorphism.lean:109
ACCEPTS: `C`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `NormedAddCommGroup (componentSeminormSubgroup C cc)`
PARAMETERIZED BY: nothing beyond `C`
COERCIONS USED INTERNALLY: delegates to `componentAddGroupNorm`

DEFINITION: `componentNormedSpace C cc`
FILE:LINE: LocalHomeomorphism.lean:114
ACCEPTS: `C`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `NormedSpace C (componentSeminormSubgroup C cc)`
PARAMETERIZED BY: nothing beyond `C`
COERCIONS USED INTERNALLY: coerces submodule elements

DEFINITION: `ComponentTopologicalLinearLocalModel C cc`
FILE:LINE: LocalHomeomorphism.lean:273
ACCEPTS: `C`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `Type` (structure with fields V, instNormedAddCommGroup, instNormedSpace, mem_charge, isLocalHomeomorph_chargeMap)
PARAMETERIZED BY: nothing beyond `C` -- operates at `v = id` only
COERCIONS USED INTERNALLY: none (bundles the data)

DEFINITION: `componentTopologicalLinearLocalModel C cc`
FILE:LINE: LocalHomeomorphism.lean:304
ACCEPTS: `C`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `ComponentTopologicalLinearLocalModel C cc`
PARAMETERIZED BY: nothing beyond `C`
COERCIONS USED INTERNALLY: builds from `componentSeminormSubgroup C cc`, the norm tower, etc.

DEFINITION: `NumericalComponent k C cc`
FILE:LINE: EulerForm/Basic.lean:640
ACCEPTS: `k` (field), `C`, `cc : ComponentIndex C (numericalQuotientMap k C)`
RETURNS: `Type` (abbreviation for `Component C (numericalQuotientMap k C) cc`)
PARAMETERIZED BY: `k`
COERCIONS USED INTERNALLY: none (abbreviation)

DEFINITION: `ClassMapComponent C v cc`
FILE:LINE: NumericalStabilityManifold.lean:59
ACCEPTS: `C`, `v : K0 C ->+ Lambda`, `cc : ConnectedComponents (ClassMapStabilityCondition C v)`
RETURNS: `Type` (specifically `{sigma : ClassMapStabilityCondition C v // mk sigma = cc}`)
PARAMETERIZED BY: `v`, `Lambda`
COERCIONS USED INTERNALLY: none (abbreviation)

DEFINITION: `ClassMapAmbientLocus C v cc`
FILE:LINE: NumericalStabilityManifold.lean:337
ACCEPTS: `C`, `v : K0 C ->+ Lambda`, `cc : ConnectedComponents (StabilityCondition C)`
RETURNS: `Type` (specifically `{sigma : ClassMapStabilityCondition C v // mk (sigma : StabilityCondition C) = cc}`)
PARAMETERIZED BY: `v`, `Lambda`
COERCIONS USED INTERNALLY: coerces `ClassMapStabilityCondition C v` to `StabilityCondition C` via subtype coercion

#### Definitions that consume the above

DEFINITION: `centralChargeIsLocalHomeomorphOnConnectedComponents` (bridge theorem)
FILE:LINE: LocalHomeomorphism.lean:639
ACCEPTS: `C`
RETURNS: `StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents C`
PARAMETERIZED BY: nothing beyond `C` (statement is about `v = id`)
COERCIONS USED INTERNALLY: `let cc' : ConnectedComponents (StabilityCondition C) := cc` -- recasts `ComponentIndex C id` as `ConnectedComponents (StabilityCondition C)` by definitional unfolding. Uses `simpa [cc']` twice.

DEFINITION: `homeomorphClassMapComponent C v hv cc`
FILE:LINE: NumericalStabilityManifold.lean:115
ACCEPTS: `C`, `v`, `hv : Surjective v`, `cc : ComponentIndex C v`
RETURNS: `Component C v cc homeomorphic to ClassMapComponent C v (componentIndexEquiv ... cc)`
PARAMETERIZED BY: `v`, `Lambda`
COERCIONS USED INTERNALLY: uses `homeomorphClassMapStabilityCondition` (v-parametric) and `componentIndexEquivClassMapStabilityCondition`

DEFINITION: `ambientClassMapChargeMap_isLocalHomeomorph`
FILE:LINE: NumericalStabilityManifold.lean:432
ACCEPTS: `C`, `v`, `M : ComponentTopologicalLinearLocalModel C cc`
RETURNS: `IsLocalHomeomorph (ambientClassMapChargeMap C v M)`
PARAMETERIZED BY: `v`, `Lambda`; but `M` is fixed to a `cc : ConnectedComponents (StabilityCondition C)`, NOT a `v`-parametric component
COERCIONS USED INTERNALLY: uses `IsLocalHomeomorph.codRestrict_preimage` to restrict `M.isLocalHomeomorph_chargeMap` (which is at `v = id` level) to the `v`-factor subspace

DEFINITION: `existsLocalHomeomorphToComplexModelOnConnectedComponent`
FILE:LINE: NumericalStabilityManifold.lean:632
ACCEPTS: `C`, `v`, `cc : ConnectedComponents (ClassMapStabilityCondition C v)`
RETURNS: existence of local homeomorphism from `ClassMapComponent C v cc` to a normed space
PARAMETERIZED BY: `v`, `Lambda`
COERCIONS USED INTERNALLY: uses `componentTopologicalLinearLocalModel C ambientcc` (at `v = id` level), then restricts via `ambientClassMapChargeMap_isLocalHomeomorph`, then composes with homeomorphisms bridging `ClassMapComponent` to `connectedComponent` of `ClassMapAmbientLocus`

DEFINITION: `WithClassMap.existsComplexManifoldOnConnectedComponent`
FILE:LINE: NumericalStabilityManifold.lean:737
ACCEPTS: `C`, `v`, `hv : Surjective v`, `cc : ComponentIndex C v`
RETURNS: existence of complex manifold structure on `Component C v cc`
PARAMETERIZED BY: `v`, `Lambda`
COERCIONS USED INTERNALLY: uses `homeomorphClassMapComponent` to bridge from `Component C v cc` to `ClassMapComponent`, then delegates to `existsLocalHomeomorphToComplexModelOnConnectedComponent`

### STEP B -- ABSTRACTION MAP (factual only)

**1. Does the project define a parameterized type T v where some definitions use T v and others use a fixed instantiation?**

Yes. The parameterized type is `WithClassMap C v` (parameterized by `v : K0 C ->+ Lambda`). The fixed instantiation is `StabilityCondition C` which is `WithClassMap C (AddMonoidHom.id (K0 C))`.

The project also has `ClassMapStabilityCondition C v` (parameterized by `v`), which is a subtype of `StabilityCondition C` (the specialization).

Every specialization:
- `StabilityCondition C` = `WithClassMap C (AddMonoidHom.id (K0 C))`
- `NumericalStabilityCondition k C` = `WithClassMap C (numericalQuotientMap k C)`
- `ClassMapStabilityCondition C v` = `{sigma : StabilityCondition C // sigma.FactorsThrough v}`

**2. For each definition from Step A, which level does it target?**

| Definition | Level |
|---|---|
| `ComponentIndex C v` | parameterized (general `v`) |
| `Component C v cc` | parameterized (general `v`) |
| `componentRep C cc` | specialization (`v = id`) |
| `componentStabilityCondition C cc` | specialization (`v = id`) |
| `componentSeminormSubgroup C cc` | specialization (`v = id`) |
| `componentNorm C cc` | specialization (`v = id`) |
| `componentAddGroupNorm C cc` | specialization (`v = id`) |
| `componentNormedAddCommGroup C cc` | specialization (`v = id`) |
| `componentNormedSpace C cc` | specialization (`v = id`) |
| `ComponentTopologicalLinearLocalModel C cc` | specialization (`v = id`) |
| `componentTopologicalLinearLocalModel C cc` | specialization (`v = id`) |
| `NumericalComponent k C cc` | specialization (`v = numericalQuotientMap k C`) |
| `ClassMapComponent C v cc` | parameterized (general `v`, but via `ClassMapStabilityCondition`) |
| `ClassMapAmbientLocus C v cc` | mixed (general `v`, but `cc` is over `StabilityCondition C`) |
| `centralChargeIsLocalHomeomorphOnConnectedComponents` | bridge: stated for general `v = id`, bridges to `ComponentTopologicalLinearLocalModel` |
| `homeomorphClassMapComponent` | parameterized (general `v`, requires surjectivity) |
| `ambientClassMapChargeMap_isLocalHomeomorph` | mixed: accepts general `v` but `M` is at `v = id` level |
| `existsLocalHomeomorphToComplexModelOnConnectedComponent` | parameterized (general `v`) |
| `existsComplexManifoldOnConnectedComponent` | parameterized (general `v`, requires surjectivity) |

**3. Are there definitions that accept the specialization but whose implementation would work unchanged for the parameterized type?**

The key candidates:

- `componentRep`: takes `cc : ConnectedComponents (StabilityCondition C)`. The body is `Classical.choose cc.exists_rep`. This pattern works for any `ConnectedComponents X`, so it could trivially be parameterized. However, the callers all need `StabilityCondition C` specifically because `stabSeminorm` and `finiteSeminormSubgroup` are defined on `StabilityCondition C`.

- `componentStabilityCondition`: takes `cc : ConnectedComponents (StabilityCondition C)`. It is `{sigma : StabilityCondition C // mk sigma = cc}`. This is literally `Component C (AddMonoidHom.id _) cc` after definitional unfolding.

- The norm tower (`componentSeminormSubgroup` through `componentNormedSpace`): These all accept `cc : ConnectedComponents (StabilityCondition C)`. They use `stabSeminorm`, `finiteSeminormSubgroup`, `stabSeminorm_add_le`, `stabSeminorm_neg`, `stabSeminorm_smul_complex`, `stabSeminorm_zero`, `eq_zero_of_stabSeminorm_toReal_eq_zero` -- all of which are defined on `StabilityCondition C`. The seminorm formula involves `||U(K0.of C E)|| / ||sigma.Z(K0.of C E)||` where both `U` and `sigma.Z` live in `K0 C ->+ C`. There is no way to parameterize this by `v` without changing the codomain type.

- `ComponentTopologicalLinearLocalModel`: takes `cc : ConnectedComponents (StabilityCondition C)`. Its fields reference `StabilityCondition C` and `K0 C ->+ C`. Cannot be generalized without changing the field types.

**Conclusion for question 3**: `componentRep` and `componentStabilityCondition` could be generalized to arbitrary `ConnectedComponents X`. The norm tower and `ComponentTopologicalLinearLocalModel` cannot be generalized because they intrinsically depend on `StabilityCondition C` via the Bridgeland seminorm.

**4. Is there bridge code whose sole purpose is to convert between the parameterized type and the specialization?**

Yes, four pieces:

(a) **LocalHomeomorphism.lean:639-647** -- `centralChargeIsLocalHomeomorphOnConnectedComponents`:
```lean
let cc' : ConnectedComponents (StabilityCondition C) := cc
let M := componentTopologicalLinearLocalModel C cc'
...
simpa [cc', StabilityCondition.WithClassMap.Component] using M.isLocalHomeomorph_chargeMap
```
This bridges from `CentralChargeIsLocalHomeomorphOnConnectedComponents` (stated for general `v`, instantiated at `v = id` in the Prop but quantifying over `ComponentIndex C id = ConnectedComponents (StabilityCondition C)`) to the `v = id` construction. The bridge is thin (two `simpa` calls) because `StabilityCondition C` is *definitionally* `WithClassMap C id`.

(b) **NumericalStabilityManifold.lean:67-90** -- `homeomorphClassMapStabilityCondition`:
Constructs a homeomorphism `WithClassMap C v homeomorphic to ClassMapStabilityCondition C v` under surjectivity of `v`. This bridges between the bundled presentation and the factorization-subtype presentation.

(c) **NumericalStabilityManifold.lean:94-111** -- `componentIndexEquivClassMapStabilityCondition`:
Equivalence between `ComponentIndex C v` and `ConnectedComponents (ClassMapStabilityCondition C v)`. Bridges component index sets across presentations.

(d) **NumericalStabilityManifold.lean:115-153** -- `homeomorphClassMapComponent`:
Homeomorphism between `Component C v cc` and `ClassMapComponent C v (ce cc)`. Bridges per-component types across presentations.

(e) **NumericalStabilityManifold.lean:391-430** -- `classMapAmbientLocusHomeomorphChargePreimage`:
Homeomorphism from `ClassMapAmbientLocus C v cc` to the subtype of `componentStabilityCondition C cc` whose charge lands in the factor submodule. This bridges between the class-map-restricted locus and the charge preimage.

(f) **NumericalStabilityManifold.lean:509-533** -- `connectedComponentClassMapAmbientLocusRepHomeomorphClassMapComponent`:
Homeomorphism from `connectedComponent x0` (inside `ClassMapAmbientLocus`) to `ClassMapComponent C v cc`. More bridge code.

### STEP C -- COMMIT: ABSTRACTION-LEVEL FINDINGS

**Definitions whose signatures could be generalized (from question 3):**

- `componentRep` (LocalHomeomorphism.lean:38) and `classMapComponentRep` (NumericalStabilityManifold.lean:445) are both `Classical.choose cc.exists_rep` for specific topological spaces. Both could be replaced by a single generic `ConnectedComponents.rep` definition that works for any `ConnectedComponents X`.

- `componentStabilityCondition` (LocalHomeomorphism.lean:46) is definitionally equal to `Component C (AddMonoidHom.id _) cc` but named separately. It could be eliminated in favor of the parameterized definition.

- The norm tower (`componentSeminormSubgroup` through `componentNormedSpace`) and `ComponentTopologicalLinearLocalModel` CANNOT be generalized. They intrinsically depend on `stabSeminorm` which operates on `StabilityCondition C`.

**Bridge code identified (from question 4):**

1. LocalHomeomorphism.lean:639-647 -- thin bridge (definitional equality, two simpa calls)
2. NumericalStabilityManifold.lean:67-90 -- `homeomorphClassMapStabilityCondition` (WithClassMap vs ClassMapStabilityCondition)
3. NumericalStabilityManifold.lean:94-111 -- `componentIndexEquivClassMapStabilityCondition`
4. NumericalStabilityManifold.lean:115-153 -- `homeomorphClassMapComponent`
5. NumericalStabilityManifold.lean:391-430 -- `classMapAmbientLocusHomeomorphChargePreimage`
6. NumericalStabilityManifold.lean:509-533 -- `connectedComponentClassMapAmbientLocusRepHomeomorphClassMapComponent`

The bridges in items 2-6 exist because the project maintains TWO parallel presentations of class-map stability conditions: the bundled `WithClassMap C v` and the factorization subtype `ClassMapStabilityCondition C v`. Every bridge theorem in NumericalStabilityManifold.lean converts between them. The Theorem 1.2 proof (LocalHomeomorphism.lean) operates on `StabilityCondition C` = `WithClassMap C id`. The manifold theorem then needs to restrict to `ClassMapStabilityCondition C v` (a subtype of `StabilityCondition C`) and identify this restriction with `WithClassMap C v` components.

---

## PHASE 2: Duplication Findings

### Finding 1: `componentStabilityCondition` duplicates `Component C id cc`

`componentStabilityCondition C cc` (LocalHomeomorphism.lean:46) is definitionally `{sigma : StabilityCondition C // mk sigma = cc}`, which is the same as `Component C (AddMonoidHom.id (K0 C)) cc` after unfolding the `StabilityCondition` abbreviation. It exists because LocalHomeomorphism.lean works entirely in the `StabilityCondition C` world and the author did not want to introduce `WithClassMap` syntax.

Occurrences in .lean files:
- LocalHomeomorphism.lean:266 (componentZMap type)
- LocalHomeomorphism.lean:295 (chargeMap type)
- LocalHomeomorphism.lean:309 (local let)
- NumericalStabilityManifold.lean:394 (classMapAmbientLocusHomeomorphChargePreimage type)

### Finding 2: `componentRep` and `classMapComponentRep` are the same pattern

Both are `Classical.choose cc.exists_rep` for different base spaces. They duplicate a pattern that belongs in Mathlib as `ConnectedComponents.rep`.

`componentRep`: LocalHomeomorphism.lean:38, used ~50 times in that file and ~5 times in NumericalStabilityManifold.lean.
`classMapComponentRep`: NumericalStabilityManifold.lean:445, used ~8 times in that file.

### Finding 3: The WithClassMap / ClassMapStabilityCondition duality generates all bridge code

The project maintains two equivalent presentations of class-map stability conditions:
- `WithClassMap C v`: bundled, carries `Z : Lambda ->+ C` as a field
- `ClassMapStabilityCondition C v`: factorization subtype of `StabilityCondition C`

Under surjectivity of `v`, these are equivalent (NumericalStability/Basic.lean:121). The topology on `WithClassMap C v` is induced from `StabilityCondition C` via `toStabilityCondition` (Defs.lean:171), which coincides with the subspace topology on `ClassMapStabilityCondition C v`.

The Theorem 1.2 construction works on `StabilityCondition C`. To get Corollary 1.3 for `WithClassMap C v`, the proof must:
1. Restrict the local homeomorphism to `ClassMapStabilityCondition C v` (a subtype of `StabilityCondition C`)
2. Further restrict to a connected component of `ClassMapStabilityCondition C v`
3. Identify the result with `Component C v cc` via the `WithClassMap <-> ClassMapStabilityCondition` equivalence

This generates six homeomorphism/equivalence definitions (items 2-6 in the bridge code list above). The question is: would a different architecture avoid this bridge chain?

### Finding 4: No parallel norm tower construction

The norm tower exists once, at the `StabilityCondition C` level. There is no duplicate for `WithClassMap C v` or `ClassMapStabilityCondition C v`. This is correct: the Bridgeland seminorm is intrinsically defined on `K0 C ->+ C`, not on `Lambda ->+ C`.

### Finding 5: Mathlib has no `ConnectedComponents.rep`

Mathlib provides `ConnectedComponents.exists_rep` but not `ConnectedComponents.rep`. Both `componentRep` and `classMapComponentRep` instantiate this pattern.

---

## PHASE 3: Mathematical Identity

### Natural language statement

The **Bridgeland stability manifold** of a triangulated category `D` with respect to a class map `v : K0(D) -> Lambda` is the space `Stab_v(D)` of locally-finite slicings whose central charge factors through `v`. This space carries a topology induced from the full stability space `Stab(D)`, which is defined by basis neighborhoods involving the Bridgeland generalized metric on slicings and a supremum-ratio seminorm on central charges.

**Theorem 1.2** (Bridgeland): For each connected component Sigma of `Stab(D)`, the central charge map `Z : Sigma -> V(Sigma)` is a local homeomorphism, where `V(Sigma) = {U : K0(D) -> C | sup |U(E)|/|Z_sigma(E)| < infinity}` is a complex-normed subspace of `Hom(K0(D), C)`.

**Corollary 1.3**: When Lambda is finitely generated and `v` is surjective, each connected component of `Stab_v(D)` is a finite-dimensional complex manifold, modeled on the subspace of `V(Sigma)` consisting of charges that factor through `v`.

### Most general context where the critical API holds

The critical API consists of:
1. Seminorm equivalence on connected components (finiteSeminormSubgroup_eq_of_connected)
2. Local homeomorphism of the charge map (the entire content of LocalHomeomorphism.lean)
3. Restriction to factor subspace + finite-dimensionality (NumericalStabilityManifold.lean)

Items 1-2 are deeply Bridgeland-specific. They rely on:
- The sector-bound analysis of the Bridgeland deformation theory (phase rigidity)
- The HN filtration structure (semistable decomposition, telescoping)
- The specific form of the Bridgeland metric (supremum over nonzero objects)

There is no natural generalization of items 1-2 to an abstract setting.

Item 3, however, has a clear abstract form: "given a local homeomorphism f : X -> V and a subspace W of V, the restriction f^{-1}(W) -> W is a local homeomorphism." This is `IsLocalHomeomorph.codRestrict_preimage` in Mathlib. The finite-dimensionality argument is also generic.

### The key question: does the bridge chain reflect missing abstraction or genuine mathematical content?

The bridge chain (NumericalStabilityManifold.lean:67-533) does two things:
1. Identifies `WithClassMap C v` with `ClassMapStabilityCondition C v` (equivalence under surjectivity)
2. Identifies connected components across the two presentations and constructs per-component homeomorphisms

Item 1 is genuine mathematical content (the surjectivity hypothesis is essential). Item 2 is the topological consequence of item 1 -- if two spaces are homeomorphic, their connected components correspond. The chain is long because Lean requires explicit construction of per-component homeomorphisms from the global one.

---

## ABSTRACTION-LEVEL FINDINGS (from Phase 1.5 Step C, copied here per protocol)

**Definitions whose signatures could be generalized:**

- `componentRep` (LocalHomeomorphism.lean:38) and `classMapComponentRep` (NumericalStabilityManifold.lean:445) should be unified into a single `ConnectedComponents.rep`.
- `componentStabilityCondition` (LocalHomeomorphism.lean:46) is a definitional duplicate of `Component C (AddMonoidHom.id _) cc`.
- The norm tower and `ComponentTopologicalLinearLocalModel` CANNOT be generalized beyond `v = id`.

**Bridge code:**

1. LocalHomeomorphism.lean:639-647 -- thin, two simpa calls
2. NumericalStabilityManifold.lean:67-90 -- homeomorphism WithClassMap <-> ClassMapStabilityCondition
3. NumericalStabilityManifold.lean:94-111 -- component index equivalence
4. NumericalStabilityManifold.lean:115-153 -- per-component homeomorphism
5. NumericalStabilityManifold.lean:391-430 -- ambient locus homeomorphism
6. NumericalStabilityManifold.lean:509-533 -- connected component in ambient locus homeomorphism

---

## PHASE 4: Proposal

### Reviewing the ABSTRACTION-LEVEL FINDINGS

The findings identify two kinds of issues:
1. **Unifiable patterns**: `componentRep`/`classMapComponentRep` and `componentStabilityCondition`/`Component`
2. **Bridge chain**: six bridge definitions/theorems in NumericalStabilityManifold.lean

### On the unifiable patterns

**Proposal A: Introduce `ConnectedComponents.rep`**

```lean
-- In ForMathlib/ConnectedComponents.lean (or a suitable shared location)
noncomputable def ConnectedComponents.rep {X : Type*} [TopologicalSpace X]
    (cc : ConnectedComponents X) : X :=
  Classical.choose cc.exists_rep

@[simp] theorem ConnectedComponents.mk_rep {X : Type*} [TopologicalSpace X]
    (cc : ConnectedComponents X) : ConnectedComponents.mk cc.rep = cc :=
  Classical.choose_spec cc.exists_rep
```

This eliminates `componentRep` (LocalHomeomorphism.lean:38) and `classMapComponentRep` (NumericalStabilityManifold.lean:445). All call sites (`cc.rep` instead of `componentRep C cc`) become shorter.

Scope: ~63 substitutions across 2 files, plus removing 2 definitions and 2 simp lemmas.
Cost: Low. Purely mechanical.

**Proposal B: Eliminate `componentStabilityCondition`**

Replace its 5 occurrences with either `Component C (AddMonoidHom.id _) cc` (if WithClassMap syntax is acceptable in context) or inline the subtype `{sigma : StabilityCondition C // ConnectedComponents.mk sigma = cc}`.

The latter is cleaner in LocalHomeomorphism.lean since that file works entirely at the `StabilityCondition C` level. Verdict: replace with inline subtype at the 5 call sites and delete the definition.

Scope: 5 substitutions, 1 deletion.
Cost: Trivial.

### On the bridge chain

The bridge chain exists because the project has TWO presentations of class-map stability conditions:
- `WithClassMap C v` (bundled): carries `Z : Lambda ->+ C` directly
- `ClassMapStabilityCondition C v` (factorization subtype): `{sigma : StabilityCondition C // exists Z', sigma.Z = Z'.comp v}`

The Theorem 1.2 proof needs `StabilityCondition C` because the Bridgeland seminorm, topology, and deformation theory operate at that level. The manifold theorem needs `WithClassMap C v` because the public-facing statement quantifies over `Component C v cc`. The factorization subtype `ClassMapStabilityCondition C v` is the natural intermediate -- it lives inside `StabilityCondition C` (so the restriction of Theorem 1.2 applies directly) and is equivalent to `WithClassMap C v` under surjectivity of `v`.

**Could we eliminate `ClassMapStabilityCondition` entirely?** The topology on `WithClassMap C v` is already induced from `StabilityCondition C` via `toStabilityCondition`. If surjectivity of `v` is assumed throughout, we could work directly with `WithClassMap C v` and route the restriction through `toStabilityCondition`. But this would require:
- Showing `toStabilityCondition` is injective under surjectivity (it is -- NumericalStability/Basic.lean:121)
- Showing `toStabilityCondition` is a topological embedding (it is by definition, since the topology is induced)
- Replacing every `ClassMapStabilityCondition C v` usage with `WithClassMap C v` and composing with `toStabilityCondition`

This would eliminate bridges 2-4 and simplify bridges 5-6 but would require reworking the entire NumericalStabilityManifold.lean. The core argument in `existsLocalHomeomorphToComplexModelOnConnectedComponent` currently works by:
1. Taking the ambient connected component `ambientcc` (in `StabilityCondition C`)
2. Restricting the local homeomorphism to `ClassMapAmbientLocus C v ambientcc` (elements of `ClassMapStabilityCondition C v` whose ambient connected component is `ambientcc`)
3. Showing this restricted map is still a local homeomorphism (via `codRestrict_preimage`)
4. Showing connected components of `ClassMapStabilityCondition C v` live inside a single ambient component

An alternative architecture that avoids `ClassMapStabilityCondition` would:
1. Work with `WithClassMap C v` directly
2. Map into `StabilityCondition C` via `toStabilityCondition` (a topological embedding under surjectivity)
3. Use the pullback of the local homeomorphism along this embedding
4. Restrict the codomain to the factor subspace

This alternative is feasible but amounts to a significant rewrite of NumericalStabilityManifold.lean (~400 lines). The mathematical content is the same; the bridge chain would be replaced by pullback/restriction arguments.

**Verdict on the bridge chain:** The bridge chain is long but each piece carries genuine topological content (homeomorphisms between subtypes, identification of connected components). The root cause is the two-presentation design (`WithClassMap` vs `ClassMapStabilityCondition`), which exists because `WithClassMap C v` needs surjectivity of `v` for the equivalence while `ClassMapStabilityCondition C v` does not. Under the project's current structure -- where the general theorem does NOT assume surjectivity until the very end -- the two-presentation design is justified. The bridge code is not eliminable without either assuming surjectivity earlier (changing the theorem structure) or performing a major rewrite.

### Summary of concrete proposals

| Proposal | Scope | Cost | Benefit |
|---|---|---|---|
| A: `ConnectedComponents.rep` | ~63 substitutions, 2 files | Low | Eliminates 4 definitions, shorter call sites |
| B: Eliminate `componentStabilityCondition` | 5 substitutions, 1 file | Trivial | Tighter API surface |

**Proposals NOT made:**

- Generalizing the norm tower to `WithClassMap C v`: impossible, the seminorm intrinsically uses `K0 C ->+ C`.
- Eliminating `ClassMapStabilityCondition C v`: would require major rewrite of NumericalStabilityManifold.lean and would only trade one form of bridge code for another.
- Eliminating `ComponentIndex`/`Component`/`NumericalComponent`: these are meaningful one-line abbreviations used in theorem statements. Removing them would make the public API harder to read.

---

## SELF-CHECK (mandatory)

**1. Did I identify any observations in Phase 1.5 that I later argued away or softened in Phase 4?**

Phase 1.5 identified six pieces of bridge code. In Phase 4, I characterized bridges 2-6 (in NumericalStabilityManifold.lean) as "genuine topological content" rather than symptoms of wrong-level construction. Let me re-examine:

- Bridges 2-4 (`homeomorphClassMapStabilityCondition`, `componentIndexEquivClassMapStabilityCondition`, `homeomorphClassMapComponent`) exist solely to convert between `WithClassMap C v` and `ClassMapStabilityCondition C v`. Their ONLY content is that the equivalence `WithClassMap C v ~ ClassMapStabilityCondition C v` (under surjectivity) is a homeomorphism and respects connected components. This IS bridge code in the strict sense -- it converts between two presentations of the same mathematical object.

- Bridges 5-6 (`classMapAmbientLocusHomeomorphChargePreimage`, `connectedComponentClassMapAmbientLocusRepHomeomorphClassMapComponent`) are consequences of the two-presentation architecture. They identify subtypes of `ClassMapStabilityCondition C v` with subtypes of `componentStabilityCondition C cc`.

I am restoring the finding: **bridges 2-4 are pure bridge code converting between WithClassMap and ClassMapStabilityCondition. They would be unnecessary if the project worked with a single presentation throughout.** The cost of eliminating them (rewriting NumericalStabilityManifold.lean) is high, but the bridge code IS a symptom of the two-presentation design.

**2. Did I use dismissive phrases?**

I used "genuine topological content" for bridges 5-6. Re-examining: bridge 5 (`classMapAmbientLocusHomeomorphChargePreimage`) constructs a homeomorphism between `ClassMapAmbientLocus C v cc` and a subtype of `componentStabilityCondition C cc` restricted by charge membership. This is genuinely needed for the restriction argument -- even in a single-presentation architecture, you need to identify the charge-preimage restriction. So this characterization is backed by the specific constraint that `codRestrict_preimage` operates on a subtype of the source.

Bridge 6 (`connectedComponentClassMapAmbientLocusRepHomeomorphClassMapComponent`) identifies a connected component inside the ambient locus with a `ClassMapComponent`. This IS bridge code between presentations. I retract "genuine topological content" for this piece.

**Revised finding:** Bridges 2-4 and 6 (total ~130 lines) are pure bridge code between the WithClassMap and ClassMapStabilityCondition presentations. Bridge 5 has some irreducible content (charge-preimage restriction).

**3. For each piece of bridge code: did I propose eliminating it, or did I justify its existence?**

I justified the existence of bridges 2-6 by arguing that the two-presentation design is needed because the general theorem does not assume surjectivity until the end. Let me examine this constraint:

- `CentralChargeIsLocalHomeomorphOnConnectedComponents` (Defs.lean:192) is stated for general `v` WITHOUT assuming surjectivity.
- `existsComplexManifoldOnConnectedComponent` (NumericalStabilityManifold.lean:737) DOES assume surjectivity.
- `existsLocalHomeomorphToComplexModelOnConnectedComponent` (NumericalStabilityManifold.lean:632) does NOT assume surjectivity -- it works with `ClassMapStabilityCondition C v` which exists without surjectivity.

So the two-presentation design is justified by the fact that `ClassMapStabilityCondition C v` works without surjectivity while `WithClassMap C v ~ ClassMapStabilityCondition C v` requires it. The bridge code exists at the surjectivity-assuming boundary. This is a genuine constraint, not a rationalization.

However, I note that `CentralChargeIsLocalHomeomorphOnConnectedComponents` (the non-surjective version) is stated but its proof (`centralChargeIsLocalHomeomorphOnConnectedComponents` at LocalHomeomorphism.lean:639) only covers `v = id`. The general-v version is proved only as a manifold theorem under surjectivity. So the non-surjective generality of the statement is aspirational rather than realized.

**This does not change the architectural conclusion:** even if we assumed surjectivity everywhere, we would still need the factorization-subtype approach (or something equivalent) because the Theorem 1.2 proof operates on `StabilityCondition C` and the manifold theorem needs to restrict to a subspace. The bridge chain's length is partly a consequence of Lean's type system requiring explicit per-component constructions, not just an architectural choice.
