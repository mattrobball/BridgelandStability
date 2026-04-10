# Abstraction Audit: `HNFiltration` (v2 -- Right Abstraction Search)

## 1. The Definition

```lean
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C) extends PostnikovTower C E where
  φ : Fin n → ℝ
  hφ : StrictAnti φ
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j)
```

File: `BridgelandStability/Slicing/Defs.lean` (lines 64--70)

Context: pretriangulated category `C` with standard instances
(`HasZeroObject`, `HasShift C ℤ`, `Preadditive`, additive shift functors,
`Pretriangulated`).

The phase predicate `P : ℝ → ObjectProperty C` is parametric: callers
instantiate it with `s.P` (the slicing predicate), `σ.deformedPred C W hW ε`
(deformed stability), or `fun ψ F => ssf.Semistable C F ψ` (skewed stability
function). This parametricity is load-bearing -- it is not simply `s.P`.

## 2. Full API Surface

### Core operations (Slicing/Defs.lean)

| Declaration | Type | Description |
|---|---|---|
| `HNFiltration.phiPlus` | def | Highest phase `φ ⟨0, h⟩` |
| `HNFiltration.phiMinus` | def | Lowest phase `φ ⟨n-1, _⟩` |
| `HNFiltration.prefix` | def | First `k` factors as sub-filtration |
| `HNFiltration.ofIso` | def | Transport across `E ≅ E'` |
| `HNFiltration.shiftHN` | def | Shift by `a : ℤ`, adds `a` to all phases |
| `HNFiltration.dropFirst` | def | Drop zero first factor |
| `HNFiltration.dropLast` | def | Drop zero last factor |
| `HNFiltration.n_pos` | lemma | Nonzero object implies `0 < n` |
| `HNFiltration.exists_nonzero_factor` | lemma | Some factor is nonzero |
| `HNFiltration.exists_nonzero_first` | lemma | Exists filtration with nonzero first factor |
| `HNFiltration.exists_nonzero_last` | lemma | Exists filtration with nonzero last factor |

### Phase bounds (Slicing/Basic.lean)

| Declaration | Type |
|---|---|
| `HNFiltration.phiMinus_le_phiPlus` | lemma |
| `HNFiltration.phase_mem_range` | lemma |

### Phase uniqueness (Slicing/Phase.lean)

| Declaration | Type |
|---|---|
| `HNFiltration.isZero_factor_zero_of_hom_eq_zero` | lemma |
| `HNFiltration.phiPlus_le_of_nonzero_factor` | theorem |
| `HNFiltration.phiPlus_eq_of_nonzero_factors` | theorem |
| `HNFiltration.isZero_factor_last_of_hom_eq_zero` | lemma |
| `HNFiltration.phiMinus_ge_of_nonzero_last_factor` | theorem |
| `HNFiltration.phiMinus_eq_of_nonzero_last_factors` | theorem |
| `HNFiltration.exists_both_nonzero` | lemma |

### Subcategory predicates (Slicing/HNOperations.lean)

| Declaration | Type |
|---|---|
| `HNFiltration.prefix_phiMinus_gt` | lemma |
| `HNFiltration.chain_obj_gtProp` | lemma |
| `HNFiltration.chain_obj_leProp` | lemma |
| `HNFiltration.chain_obj_ltProp` | lemma |
| `HNFiltration.chain_obj_geProp` | lemma |
| `HNFiltration.appendFactor` | def |

### Constructors (Slicing/TStructure.lean)

| Declaration | Type |
|---|---|
| `HNFiltration.zero` | def |
| `HNFiltration.single` | def |
| `HNFiltration.phaseShift` | def |
| `HNFiltration.unphaseShift` | def |

### Assembly (Deformation/HNFiltrationAssembly.lean)

| Declaration | Type |
|---|---|
| `semistable_of_hn_length_one` | theorem |
| `append_hn_filtration_of_triangle` | theorem |

### Interval category (IntervalCategory/FiniteLength.lean)

| Declaration | Type |
|---|---|
| `HNFiltration.appendStrictFactor` | def |

### Caller pattern summary

The dominant usage patterns across ~50 files are:

1. **Existence + extraction**: `obtain ⟨F, hn, hne⟩ := HNFiltration.exists_nonzero_first C s hE`
   then use `F.φ ⟨0, hn⟩` and `F.semistable`.
2. **Subcategory classification**: `HNFiltration.chain_obj_gtProp` etc. to show chain
   objects satisfy `gtProp`/`leProp`.
3. **Assembly**: Build new filtrations via `appendFactor`, `prefix`, `single`, `phaseShift`.
4. **K-theory**: `K₀.of_postnikovTower_eq_sum` applied to `F.toPostnikovTower`.
5. **Extension closure**: `ExtensionClosure.of_postnikovTower` applied to `F.toPostnikovTower`.

## 3. Duplication Analysis: `AbelianHNFiltration` vs `HNFiltration`

### `AbelianHNFiltration`

```lean
structure AbelianHNFiltration (Z : StabilityFunction A) (E : A) where
  n : ℕ
  hn : 0 < n
  chain : Fin (n + 1) → Subobject E
  chain_strictMono : StrictMono chain
  chain_bot : chain ⟨0, _⟩ = ⊥
  chain_top : chain ⟨n, _⟩ = ⊤
  φ : Fin n → ℝ
  φ_anti : StrictAnti φ
  factor_phase : ∀ j, Z.phase (cokernel (Subobject.ofLE ...)) = φ j
  factor_semistable : ∀ j, Z.IsSemistable (cokernel (Subobject.ofLE ...))
```

File: `StabilityFunction/HarderNarasimhan.lean` (lines 49--68)

### Side-by-side comparison

| Feature | `HNFiltration` | `AbelianHNFiltration` |
|---------|---------------|----------------------|
| Category context | Pretriangulated | Abelian |
| Chain carrier | `ComposableArrows C n` (functorial) | `Fin (n+1) → Subobject E` (set-theoretic) |
| Step data | Distinguished triangle | Subobject inclusion (StrictMono) |
| Factor extraction | `(triangle i).obj₃` | `cokernel (Subobject.ofLE ...)` |
| Phase predicate | Parametric `P : ℝ → ObjectProperty C` | Tied to `StabilityFunction Z` |
| Nonempty | `n` can be 0 (for zero objects) | `0 < n` always |
| Boundary | `base_isZero`, `top_iso` | `chain_bot = ⊥`, `chain_top = ⊤` |
| Factor semistability | `(P (φ j)) (factor j)` | `Z.IsSemistable (cokernel ...)` |
| API size | ~35 declarations | ~5 declarations + uniqueness |

### Shared abstract pattern

Both structures are instances of:

> A **phase-decorated filtration** of an object `E`: a finite chain
> `0 = E₀ → E₁ → ... → Eₙ ≅ E` with successive quotients/factors `Fᵢ`,
> equipped with real-valued phases `φ₀ > φ₁ > ... > φₙ₋₁` such that each `Fᵢ`
> is "semistable of phase `φᵢ`" for some notion of semistability.

The differences are in how "chain", "quotient", and "semistable" are realized:

- **Triangulated**: chain = composable arrows, quotient = cone of distinguished triangle,
  semistable = abstract property `P`.
- **Abelian**: chain = subobject lattice, quotient = cokernel of inclusion,
  semistable = `Z.IsSemistable`.

### Is a common abstraction worth extracting?

**No.** The two versions live in categorically incompatible worlds:

1. **The chain carriers are fundamentally different.** `ComposableArrows C n`
   is a functor `Fin (n+1) ⥤ C`. `Fin (n+1) → Subobject E` is a function
   into a lattice. There is no common type that captures both without losing
   the structure that makes each one useful.

2. **Factor extraction is different.** In the triangulated setting, factors
   are `obj₃` of a distinguished triangle. In the abelian setting, factors are
   cokernels of subobject inclusions. These two notions are connected by the
   heart equivalence (the bridge in `HeartEquivalence/Forward.lean` and
   `HeartEquivalence/Reverse.lean`), but that bridge is a theorem, not a
   definitional identification.

3. **The API surfaces diverge.** `HNFiltration` has a rich operational API
   (`prefix`, `dropFirst`, `dropLast`, `appendFactor`, `shiftHN`, `phaseShift`,
   chain-object subcategory predicates). `AbelianHNFiltration` has a rich
   uniqueness theory (Jordan-Holder-style: `n` and `chain` are unique up to
   the stability function). These are not the same API.

4. **Parametric `P` vs fixed `Z`.** `HNFiltration` is parametric in `P`,
   instantiated with at least 3 different predicates (`s.P`, `deformedPred`,
   `ssf.Semistable`). `AbelianHNFiltration` is tied to a specific
   `StabilityFunction Z`. A common supertype would need to be parametric,
   but the abelian version's `factor_phase` field (asserting phase *equality*,
   not just semistability) has no triangulated analog.

5. **The bridge is already implemented.** The `HeartEquivalence` files
   convert between the two by constructing one from the other using the
   abelian structure of the heart. This is the mathematically correct
   relationship -- they are not the same structure with different coats of paint,
   they are related by a nontrivial theorem (that the heart of a t-structure
   is abelian).

### What about `RelSeries` or `CompositionSeries`?

Mathlib's `RelSeries` is `Fin (n+1) → α` with `r a_i a_{i+1}`. Its
`CompositionSeries` instantiation uses `JordanHolderLattice`, which requires
a lattice with `IsMaximal` and `Iso` on pairs.

Neither `HNFiltration` nor `AbelianHNFiltration` fits this framework:

- `HNFiltration` does not live in a lattice. Its chain objects are objects of a
  category, connected by morphisms, not ordered by a lattice relation.
- `AbelianHNFiltration` *does* have a lattice (`Subobject E`), but its "step
  relation" is not `IsMaximal` -- HN factors need not be simple. And the phase
  decoration has no analog in `JordanHolderLattice`.

A hypothetical `DecoratedRelSeries` (a `RelSeries` plus `Fin n → ℝ` with
`StrictAnti`) would capture only the phase data, not the factor extraction
or semistability. The overhead of one more indirection layer for that tiny
shared piece is not justified.

## 4. Mathematical Identity

### What IS an HN filtration?

An HN filtration is the unique (when it exists) finite filtration of an object
whose successive quotients are semistable with strictly decreasing phases. The
key properties:

1. **Existence**: given by the axiom `hn_exists` in `Slicing`, or by the
   constructive proof in `HarderNarasimhan.lean` for abelian categories with
   finite-length.
2. **Uniqueness of phases**: `phiPlus_eq_of_nonzero_factors`,
   `phiMinus_eq_of_nonzero_last_factors` (triangulated); full chain uniqueness
   for abelian.
3. **Functorial properties**: transport across isomorphisms, shift equivariance,
   prefix/suffix operations.

### Most general context

The mathematical literature recognizes HN filtrations in:

- **Abelian categories** with stability functions (Rudakov, Bridgeland Prop 2.4)
- **Triangulated categories** with slicings (Bridgeland Definition 5.1)
- **Exact categories** with stability conditions (Bruestle-Smith-Treffinger)
- **Extriangulated categories** (Nakaoka-Palu generalization)

The current codebase handles the first two. The exact-category and
extriangulated-category generalizations would require:

- For exact categories: replacing distinguished triangles with conflations
  (admissible short exact sequences). The chain carrier would be
  "composable admissible monomorphisms" rather than `ComposableArrows`.
- For extriangulated categories: a common framework subsuming both
  triangulated and exact. Mathlib does not have extriangulated categories yet.

Both generalizations would require new Mathlib infrastructure that does not
exist. The current split into `HNFiltration` (triangulated) and
`AbelianHNFiltration` (abelian) is the correct factorization for the available
infrastructure.

### Does the literature have a unified framework?

Yes: extriangulated categories (Nakaoka-Palu 2019) unify the exact and
triangulated cases. An HN filtration in an extriangulated category is a
chain of deflations/inflations with semistable cones. But:

1. Mathlib has no `Extriangulated` typeclass.
2. The project's triangulated HN filtrations are parametric in `P`, not tied to
   a fixed stability structure. This parametricity would need to be preserved.
3. Building extriangulated infrastructure is a multi-month Mathlib project
   with no immediate benefit to this formalization.

## 5. Kill Switch Evaluation

### Candidate abstraction: `DecoratedFiltration`

```lean
-- Hypothetical common abstraction
structure DecoratedFiltration (α : Type*) [Preorder α] (n : ℕ) where
  values : Fin n → ℝ
  values_anti : StrictAnti values
```

This captures *only* the `(φ, hφ)` pair. Every consumer would still need to
know whether it came from a `PostnikovTower` or a `Subobject` chain. The
factor extraction, semistability predicate, and all operational API would
remain on the concrete types.

**Cost**: One more layer of indirection. Every `F.φ` becomes `F.decoration.values`.
Every `F.hφ` becomes `F.decoration.values_anti`. Every operation that constructs
an `HNFiltration` must also construct the decoration. No proof becomes shorter.

**Benefit**: The ability to state `StrictAnti` lemmas once. But there are only
2 such lemmas (`phiMinus_le_phiPlus`, `phase_mem_range`), and they are 2 lines
each.

**Verdict: DECLINE.** The shared piece (a strictly decreasing sequence of reals)
is trivially small. The abstraction adds indirection without eliminating any
meaningful duplication. The 2 existing parallel structures (`HNFiltration` and
`AbelianHNFiltration`) are connected by the HeartEquivalence bridge theorem,
which is the mathematically correct relationship.

### Candidate abstraction: Refactor `AbelianHNFiltration` to extend `PostnikovTower`

This would mean embedding an abelian HN filtration into a Postnikov tower via
the derived category. Mathematically appealing, but:

1. The project does not use derived categories.
2. `AbelianHNFiltration` is used only in `StabilityFunction/` and
   `HeartEquivalence/`. Its API is small (existence, uniqueness, `ofIso`).
3. The `Subobject`-based representation is exactly right for the abelian
   uniqueness proof (which uses lattice operations on `Subobject E`).
4. Replacing it with a triangulated representation would make the uniqueness
   proof harder, not easier.

**Verdict: DECLINE.**

## 6. Conclusion

`HNFiltration` is at the right abstraction level. The key design choices are:

1. **`extends PostnikovTower`**: correctly separates filtration data (chain +
   triangles) from phase data (φ + semistability). The two independent
   consumers of `PostnikovTower` (`K₀.of_postnikovTower_eq_sum` and
   `ExtensionClosure.of_postnikovTower`) justify this split.

2. **Parametric `P : ℝ → ObjectProperty C`**: correctly avoids tying the
   structure to a specific slicing. Three distinct instantiations
   (`s.P`, `deformedPred`, `ssf.Semistable`) demonstrate this is load-bearing.

3. **Parallel but separate from `AbelianHNFiltration`**: the two structures
   serve different mathematical contexts (triangulated vs abelian) with
   different API needs (operations vs uniqueness). The HeartEquivalence bridge
   is the correct connection point.

4. **No common "decorated chain" abstraction**: the shared pattern (strictly
   decreasing reals + per-index property) is too thin to justify a type. The
   2 lemmas that could be shared are trivial.

There are no missing abstractions and no profitable refactorings.
