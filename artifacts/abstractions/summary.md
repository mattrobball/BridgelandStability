# Abstraction Audit Summary — 10 Core Definitions

## Overall Verdict

All 10 definitions are at maximal usable generality for the mathematics.
The project's abstractions are well-chosen — ℝ, ℂ, and pretriangulated/
triangulated categories are forced by downstream API, not implementation choices.

The entire Bridgeland stability theory (slicings, stability conditions,
deformation theorem, manifold structure) is novel relative to Mathlib.

## Per-definition findings

### Batch 1 (5 definitions)

| Definition | File | Verdict | Key finding |
|---|---|---|---|
| HNFiltration | Slicing/Defs.lean | Maximal | PostnikovTower + HNFiltration extension is clean |
| SkewedStabilityFunction | Deformation/WPhase.lean | Maximal | ℂ codomain and α branch-cut are irreducibly complex-analytic |
| Slicing | Slicing/Defs.lean | Maximal | ℝ indexing forced by 5 code paths (floor, exp, slicingDist, etc.) |
| wPhaseOf | Deformation/WPhase.lean | Maximal | No NormedFieldWithArg typeclass exists; extract pure-ℂ lemmas to ForMathlib |
| ExtensionClosure | ExtensionClosure.lean | Maximal, Mathlib gap | Registered IsTriangulatedClosed₂ + IsClosedUnderIsomorphisms instances |

### Batch 2 (5 definitions)

| Definition | File | Verdict | Key finding |
|---|---|---|---|
| StabilityCondition | StabilityCondition/Defs.lean | Maximal | WithClassMap parametrization well-designed for bare + numerical variants |
| PostnikovTower | PostnikovTower/Defs.lean | Maximal | Deliberately weaker than Mathlib's SpectralObject (no coherence burden) |
| K₀ | GrothendieckGroup/Defs.lean | Maximal | Mathlib has no categorical K₀; add K₀.hom_ext to eliminate 5+ repeated patterns |
| IntervalCat | IntervalCategory/Basic.lean | Maximal | Open interval and b-a≤1 both mathematically forced; quasi-abelian infra is upstream-ready |
| stabSeminorm | StabilityCondition/Defs.lean | Maximal | Could weaken to PreStabilityCondition; register PseudoEMetricSpace on Slicing |

## Actionable items (ordered by value)

### Mathlib contributions
1. **QuasiAbelian category** infrastructure — self-contained in ForMathlib/, upstream-ready
2. **Heart abelianity** proof — Mathlib's TStructure/Heart.lean lists this as TODO
3. **PostnikovTower + HNFiltration** — core structures, no Mathlib equivalent
4. **ExtensionClosure** operator — genuine gap, now has Mathlib-compatible instances
5. **K₀ of triangulated categories** — Mathlib only has algebraic Grothendieck group
6. **TStructure.IsBounded** predicate
7. **Pure-ℂ wPhaseOf lemmas** (~24 with no category dependency)

### Internal improvements
8. **K₀.hom_ext** lemma — eliminates 5+ repeated two-step extension patterns
9. **Register PseudoEMetricSpace** on `Slicing C` — all 3 axioms already proved
10. **Weaken stabSeminorm** to `PreStabilityCondition` — definition doesn't need locallyFinite
11. **AbelianHNFiltration ↔ HNFiltration bridge** — currently ad-hoc in HeartEquivalence
