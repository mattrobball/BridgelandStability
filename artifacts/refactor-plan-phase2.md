# Refactor Plan: Phase 2 — Generalize to `WithClassMap C v` Throughout

## Ethos

The goal is SIMPLIFICATION. Every change must make the codebase simpler:
fewer definitions, fewer lines, more mechanical proofs. "It compiles" is
necessary but not sufficient. "It's simpler" is the metric.

NO BACKSLIDING: no proof may become longer, harder, or less readable.
No new coercions, no new bridge code, no `toStabilityCondition` usage
in any new or modified code.

## Current state (after Phase 1)

- `stabSeminorm`, `basisNhd`, topology: generalized to `WithClassMap C v`
- All downstream files compile unchanged (they work at `v = id`)
- 1 sorry: `continuous_toStabilityCondition` (bridge infrastructure)
- 1 error: NumericalStabilityManifold.lean:79 (bridge code)

## The observation

Every declaration in Deformation.lean and LocalHomeomorphism.lean says
`StabilityCondition C` in its signature. After Phase 1, `StabilityCondition C`
IS `WithClassMap C (AddMonoidHom.id (K₀ C))`. All proofs compiled because
`stabSeminorm`, `basisNhd`, etc. are now at the `v` level.

These proofs work at general `v` already — they only use `σ.Z`, `σ.slicing`,
`stabSeminorm`, `basisNhd`, `slicingDist`. The signatures just haven't been
updated yet. Changing `StabilityCondition C` to `WithClassMap C v` in the
signatures should require ZERO proof changes.

If a proof breaks when we generalize the signature, that means the proof
depends on `v = id` in a way we need to understand — not paper over.

## Phase 2a: Generalize Deformation.lean signatures

Every declaration currently taking `σ : StabilityCondition C` or
`K₀ C →+ ℂ` gets generalized to `σ : WithClassMap C v` and `Λ →+ ℂ`.

Key declarations (in dependency order):

1. `linearInterpolationZ` — affine interpolation `σ.Z + t • (τ.Z - σ.Z)`
   Currently: `(σ τ : StabilityCondition C) → ℝ → K₀ C →+ ℂ`
   New: `(σ τ : WithClassMap C v) → ℝ → Λ →+ ℂ`
   Proof: definition, no proof content. ZERO changes.

2. `stabSeminorm_smul`, `stabSeminorm_add_le`, `stabSeminorm_neg`
   Currently: on `StabilityCondition C` and `K₀ C →+ ℂ`
   New: on `WithClassMap C v` and `Λ →+ ℂ`
   Proofs: manipulate `‖U(...)‖ / ‖σ.Z(...)‖` abstractly. ZERO changes.

3. `stabSeminorm_dominated_of_basisNhd`,
   `stabSeminorm_center_dominates_of_basisNhd`
   Seminorm comparison from basis neighborhood membership.
   Proofs: use sector bounds, `stabSeminorm`, `basisNhd`. ZERO changes.

4. `basisNhd_self`, `basisNhd_mono`, `exists_basisNhd_subset_basisNhd`
   Basis neighborhood properties.
   Proofs: use `stabSeminorm`, `slicingDist`. ZERO changes.

5. `eq_of_same_Z_near`, `eq_of_same_Z_of_mem_basisNhd`
   Injectivity (Lemma 6.4).
   `eq_of_same_Z_near` takes `hZ : σ.Z = τ.Z`. At general v, this is
   `σ.Z = τ.Z : Λ →+ ℂ`. The proof uses `bridgeland_lemma_6_4` (which
   traces through `phase_eq_of_same_Z`, using `σ.Z(v(K₀.of C E)) = τ.Z(v(K₀.of C E))`
   from `hZ`). Then `WithClassMap.ext` with equal slicing + equal Z.
   This works at general v — equal Λ-charges is STRONGER than equal
   K₀-charges. No surjectivity needed. ZERO proof changes.

6. `basisNhd_subset_connectedComponent_small` — component openness
   Proof: path-lifting from deformation theorem. ZERO changes expected.

7. `exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin` — THE
   deformation theorem (Theorem 7.1).
   Currently: `∃ τ : StabilityCondition C, τ.Z = W ∧ τ ∈ basisNhd C σ ε`
   New: `∃ τ : WithClassMap C v, τ.Z = W ∧ τ ∈ basisNhd C σ ε`
   The proof builds a slicing and pairs it with charge `W`. At v=id,
   `W : K₀ C →+ ℂ`. At general v, `W : Λ →+ ℂ`. The construction
   builds a `WithClassMap C v` with charge `W` — the proof should work
   because it only accesses `W` through `stabSeminorm` (now at v level).
   ZERO proof changes expected — verify carefully.

8. `exists_local_lift_sameComponent_in_basisNhd` — path lifting
   Uses the deformation theorem and component membership.
   ZERO changes expected.

### Verification

After each generalization: `lake build BridgelandStability.StabilityCondition.Deformation`

If ANY proof breaks: STOP. Read the error. The error tells us what
the proof secretly depends on — that's valuable information, not a
problem to work around.

## Phase 2b: Generalize Topology.lean signatures

The declarations in Topology.lean between the seminorm lemmas and the
final Theorem 1.2 statement:

1. `bridgeland_lemma_6_4`, `P_of_Q_of_P_semistable`, etc.
   All take `StabilityCondition C`. Generalize to `WithClassMap C v`.
   ZERO proof changes expected.

2. `continuous_toStabilityCondition` — currently sorry.
   After Phase 2a, `basisNhd_self`, `basisNhd_mono`, etc. are at
   the v level. The proof becomes:
   `toStab⁻¹(basisNhd_id C (toStab σ) ε) = basisNhd_v C σ ε`
   (definitional equality of seminorms), plus `basisNhd_mono` /
   `exists_basisNhd_subset_basisNhd` for arbitrary centers.
   If `toStabilityCondition` becomes unnecessary, DELETE instead of proving.

3. `StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents`
   (Topology.lean:699) — the v=id duplicate of the general Prop in
   Defs.lean. DELETE. The general version subsumes it.

## Phase 2c: Generalize LocalHomeomorphism.lean

Change component definitions from `ConnectedComponents (StabilityCondition C)`
to `ComponentIndex C v`:

1. `componentRep` — `Classical.choose cc.exists_rep` works for any
   `ConnectedComponents X`. Change signature. ZERO proof changes.

2. `componentSeminormSubgroup` — uses `finiteSeminormSubgroup` and
   `componentRep`. Both now at v level. Change signature. ZERO proof changes.

3. The norm tower — delegates to `stabSeminorm` and `componentSeminormSubgroup`.
   Change signatures. ZERO proof changes.

4. `componentStabilityCondition` — DELETE. Use `Component C v cc`.

5. `componentZMap` — maps `σ ↦ σ.Z`. Change signature. ZERO proof changes.

6. `ComponentTopologicalLinearLocalModel` — change `cc` type to
   `ComponentIndex C v`. Fields use `σ.Z : Λ →+ ℂ` and
   `Submodule ℂ (Λ →+ ℂ)`. ZERO proof changes.

7. `componentTopologicalLinearLocalModel` — the 340-line proof.
   Uses `stabSeminorm`, `basisNhd`, `eq_of_same_Z_near`,
   `exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin`, all now at
   the v level. Change signature from `cc : ConnectedComponents (StabilityCondition C)`
   to `cc : ComponentIndex C v`. ZERO proof changes expected — verify
   carefully (this is the critical test).

8. Bridge theorem (lines 639-647) — currently bridges from v=id
   construction to the general Prop. After generalization, the
   construction IS at the general v level. DELETE the bridge.
   The Prop in Defs.lean is proved directly by unpacking
   `componentTopologicalLinearLocalModel`.

## Phase 3: Simplify NumericalStabilityManifold.lean

With everything at the v level, the manifold theorem is:

```
Given: ComponentTopologicalLinearLocalModel C cc
  where cc : ComponentIndex C v, v : K₀ C →+ Λ, [AddGroup.FG Λ]
  V ⊆ Hom(Λ, ℂ), charge map is local homeomorphism

When Λ has finite rank: Hom(Λ, ℂ) is finite-dimensional.
V ⊆ Hom(Λ, ℂ) is finite-dimensional.
Local homeomorphism into finite-dimensional normed space → manifold.
```

This uses the existing generic manifold construction
(lines 566-630 of NumericalStabilityManifold.lean, which stay).

### DELETE (~400 lines):
- `ClassMapComponent` (line 59)
- `homeomorphClassMapStabilityCondition` (lines 67-90)
- `componentIndexEquivClassMapStabilityCondition` (lines 94-111)
- `homeomorphClassMapComponent` (lines 115-153)
- `ClassMapStabilityCondition.*` lemmas (lines 200-235)
- `ClassMapAmbientLocus` and `isOpen_classMapAmbientLocus` (lines 337-370)
- `ambientClassMapFactorSubmodule` (lines 376-380)
- `ambientClassMapChargeMap` (lines 382-390)
- `classMapAmbientLocusHomeomorphChargePreimage` (lines 391-430)
- `ambientClassMapChargeMap_isLocalHomeomorph` (lines 432-443)
- `classMapComponentRep`, `classMapAmbientLocusRep` (lines 445-465)
- `classMapComponent_set_eq_*` (lines 467-507)
- `connectedComponent*Homeomorph*` (lines 509-533)
- `ambientClassMapFactorSubmodule_finiteDimensional` (lines 536-563)
- `ClassMapStabilityCondition.existsLocalHomeomorph*` (lines 632-714)
- `ClassMapStabilityCondition.existsComplexManifold*` (lines 716-734)
- The bridge in `WithClassMap.existsComplexManifold*` (lines 737-762)

### KEEP and SIMPLIFY:
- `ClassMapChargeSpace`, `AmbientChargeSpace` — ASSESS (may not be needed)
- `precomposeClassMap`, `classMapFactorSubmodule` — KEEP if used for
  finite-dimensionality argument
- `classMapChargeSpace_finiteDimensional` (line 285) — KEEP, key fact
- Generic manifold construction (lines 566-630) — KEEP
- `WithClassMap.existsComplexManifoldOnConnectedComponent` — REWRITE
  as direct application of ComponentTopologicalLinearLocalModel +
  finite-dimensionality
- `NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent` —
  REWRITE as specialization

### Expected result: ~400 lines deleted, ~50 lines rewritten. Net -350.

## Phase 4: Clean up

1. `toStabilityCondition` — assess remaining uses. If only in
   NumericalStability/Basic.lean (ClassMapStabilityCondition infrastructure),
   and ClassMapStabilityCondition is no longer needed for the main
   theorems, consider deleting both.

2. `continuous_toStabilityCondition` — if `toStabilityCondition` survives,
   move to Deformation.lean where the proof tools exist. Otherwise DELETE
   (and the sorry disappears).

3. `StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents`
   (Topology.lean) — DELETE (subsumed by Defs.lean version).

4. Run linters. Run style checker. Every file must be clean.

## Success criteria

- [ ] ZERO `sorry` (the existing Spec.lean one excepted)
- [ ] ZERO bridge code between `WithClassMap C v` and `StabilityCondition C`
  in the local homeomorphism / manifold path
- [ ] Net LOC reduction ≥ 300
- [ ] No proof is longer than before
- [ ] `ClassMapStabilityCondition` does not appear in the statement of any
  theorem in the local homeomorphism / manifold path
- [ ] The manifold theorem is stated directly for `Component C v cc`
