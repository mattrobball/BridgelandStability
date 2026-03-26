# Abstraction Audit Summary

## Verdict: All 5 core definitions are at maximal usable generality

None of the audited definitions can be meaningfully generalized without losing
downstream consumers. The project's abstractions are well-chosen for the mathematics.

## Per-definition findings

### 1. HNFiltration — Already general
- `PostnikovTower` + `HNFiltration extends PostnikovTower` factoring is clean
- ℝ phases forced by the mathematics (shift by ℤ, interval arithmetic, linarith)
- Pretriangulated base is essential (distinguished triangles in every construction)
- **Minor opportunity:** Formal bridge between triangulated `HNFiltration` and abelian
  `AbelianHNFiltration` (currently ad-hoc in HeartEquivalence)

### 2. SkewedStabilityFunction — Already general
- Parametric in slicing (not tied to specific StabilityCondition) — correct
- ℂ codomain is intrinsic (polar decomposition, arg, branch cuts)
- α branch-cut parameter is irreducibly complex-analytic
- **No changes recommended**

### 3. Slicing — Already general
- ℝ indexing forced by 5 concrete code paths (Int.floor, exp(iπφ), slicingDist, etc.)
- Pretriangulated + IsTriangulated needed for HN existence and t-structure construction
- **Mathlib contribution opportunity:** `TStructure.IsBounded`, `PostnikovTower`,
  `HNFiltration`, and `Slicing → TStructure` construction

### 4. wPhaseOf — Already general
- Domain ℂ cannot be generalized (no `NormedFieldWithArg` typeclass)
- (α-1, α+1] interval is canonical (matches Complex.arg convention)
- **Opportunity:** Extract ~24 pure-ℂ lemmas (no category theory dependency)
  to `ForMathlib/` files for potential upstream contribution

### 5. ExtensionClosure — Already general, genuine Mathlib gap
- Pretriangulated context is essential (uses distTriang)
- Mathlib has one-step `extensionProduct` but NOT the closure operator
- **Actionable items:**
  1. Extract `ExtensionClosure.idempotent` (duplicated 4+ times in callers)
  2. Register `IsTriangulatedClosed₂` and `IsClosedUnderIsomorphisms` instances
  3. Prove Galois connection: `P.ExtensionClosure ≤ Q ↔ P ≤ Q` (for Q ext-closed)

## Potential Mathlib contributions (ordered by impact)

1. `PostnikovTower` + `HNFiltration` (core structures, used everywhere)
2. `ExtensionClosure` as closure operator (genuine gap in Mathlib)
3. `TStructure.IsBounded` predicate
4. `Slicing → TStructure` construction (Bridgeland Prop 3.3)
5. Pure-ℂ `wPhaseOf` lemmas (phase see-saw, perturbation bounds)
6. `AbelianHNFiltration` ↔ `HNFiltration` bridge
