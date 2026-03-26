# Audit: `PostnikovTower` Generality

## 1. The Definition

```lean
structure PostnikovTower (E : C) where
  n : ℕ
  chain : ComposableArrows C n
  triangle : Fin n → Pretriangulated.Triangle C
  triangle_dist : ∀ i, triangle i ∈ distTriang C
  triangle_obj₁ : ∀ i, Nonempty ((triangle i).obj₁ ≅ chain.obj' i.val (by grind))
  triangle_obj₂ : ∀ i, Nonempty ((triangle i).obj₂ ≅ chain.obj' (i.val + 1) (by grind))
  base_isZero : IsZero (chain.left)
  top_iso : Nonempty (chain.right ≅ E)
  zero_isZero : n = 0 → IsZero E
```

File: `/home/matt.linux/lean/bridgeland-extract/BridgelandStability/PostnikovTower/Defs.lean`

Universe variables: `(C : Type u) [Category.{v} C]`, with instances
`[HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]`.

Derived API (same file):
- `PostnikovTower.length` -- just `P.n`
- `PostnikovTower.factor` -- `(P.triangle i).obj₃`
- `PostnikovTower.factors` -- `fun i => P.factor i`

## 2. API Catalog

### Operations defined on `HNFiltration` (extends `PostnikovTower` with phase data)

| Operation | File | Description |
|-----------|------|-------------|
| `HNFiltration.prefix` | Slicing/Defs.lean | First `k` factors |
| `HNFiltration.ofIso` | Slicing/Defs.lean | Transport across `E ≅ E'` |
| `HNFiltration.shiftHN` | Slicing/Defs.lean | Shift by `a : ℤ`, adds `a` to all phases |
| `HNFiltration.dropFirst` | Slicing/Defs.lean | Drop zero first factor |
| `HNFiltration.dropLast` | Slicing/Defs.lean | Drop zero last factor |
| `HNFiltration.appendFactor` | Slicing/HNOperations.lean | Extend by one triangle |
| `HNFiltration.appendStrictFactor` | IntervalCategory/FiniteLength.lean | Extend with strict phase bound |
| `HNFiltration.zero` | Slicing/TStructure.lean | Zero-length filtration of a zero object |
| `HNFiltration.single` | Slicing/TStructure.lean | Single-factor filtration |
| `HNFiltration.phaseShift` | Slicing/TStructure.lean | Translate phases by `t : ℝ` |
| `HNFiltration.unphaseShift` | Slicing/TStructure.lean | Inverse of phaseShift |

### Consumption patterns on `PostnikovTower` directly

| Pattern | Files (representative) |
|---------|----------------------|
| `F.toPostnikovTower.factor i` | Topology.lean, IntervalAbelian.lean, ConnectedComponent.lean, DeformedSlicingHN.lean, DeformedGtLe.lean, Theorem.lean |
| `F.toPostnikovTower.zero_isZero` | TwoHeartEmbedding.lean, HNExistence.lean, PhiPlusMDQ.lean, Basic.lean, DeformedGtLe.lean, TargetEnvelope.lean |
| `F.toPostnikovTower.base_isZero` | Topology.lean |
| `F.toPostnikovTower.top_iso` | Topology.lean |
| `F.toPostnikovTower.chain.left` | Topology.lean |
| `F.toPostnikovTower.chain.obj'` | Topology.lean |
| `F.toPostnikovTower.triangle_dist` | Topology.lean |
| `F.toPostnikovTower.triangle_obj₁/₂` | Topology.lean |
| `K₀.of_postnikovTower_eq_sum` | 14+ files -- the single most used lemma |
| `ExtensionClosure.of_postnikovTower` | ExtensionClosure.lean |

**Key observation:** Nearly all downstream code accesses `PostnikovTower` only through `HNFiltration`'s `.toPostnikovTower` projection. The two theorems that directly accept a `PostnikovTower` are:
1. `K₀.of_postnikovTower_eq_sum` -- K-theory additivity
2. `ExtensionClosure.of_postnikovTower` -- extension closure membership

Both are "walk the chain by induction on `k`" proofs that use `base_isZero`, `triangle_dist`, `triangle_obj₁`, `triangle_obj₂`, `top_iso`, and `factor`.

## 3. Mathematical Analysis

### What this structure captures

A Postnikov tower in a triangulated category is a finite filtration
```
0 = A₀ → A₁ → ⋯ → Aₙ ≅ E
```
where each step `Aᵢ → Aᵢ₊₁` sits in a distinguished triangle `Aᵢ → Aᵢ₊₁ → Fᵢ → Aᵢ[1]`. The factors `Fᵢ` are the successive quotients. This is the triangulated-category analog of a composition series or a chain of subobjects in an abelian category.

The name "Postnikov tower" comes from algebraic topology (where the filtration pieces live in successively higher truncations), but the structure here is more general: there is no constraint on which truncation the factors belong to. The `HNFiltration` extension adds the phase/semistability data that makes it genuinely a Harder-Narasimhan filtration.

### Relationship to `ComposableArrows`

`ComposableArrows C n` is `Fin (n+1) ⥤ C`, i.e., a diagram `X₀ → X₁ → ⋯ → Xₙ` in `C`. The `PostnikovTower` uses this as the chain carrier. This is a good choice: it packages the objects and morphisms functorially and gives access to Mathlib's `ComposableArrows` API (`obj'`, `left`, `right`, `map'`, `mkOfObjOfMapSucc`).

### Relationship to Mathlib's `SpectralObject`

Mathlib (Joël Riou) defines `SpectralObject C ι` as a functor `ω₁ : ComposableArrows ι 1 ⥤ C` equipped with functorial distinguished triangles. This is the **infinite/functorial** version of a Postnikov tower: given an indexing category `ι`, each composable pair in `ι` produces a distinguished triangle.

A `PostnikovTower` is essentially a `SpectralObject C (Fin (n+1))` where:
- `ω₁` evaluated on the arrow `i → i+1` gives `Aᵢ → Aᵢ₊₁`
- The triangle data comes from evaluating `ω₂` on triples

The key differences:
1. `SpectralObject` is **functorial**: the triangles are natural in the indexing category. `PostnikovTower` only requires the triangles to be distinguished and the vertices to be isomorphic (via `Nonempty (_ ≅ _)`), with no naturality requirement.
2. `SpectralObject` has **no base/top constraints**: there is no `base_isZero` or `top_iso`. It is a bare filtration without boundary conditions.
3. `SpectralObject` uses an **arbitrary indexing category**, not just `Fin`.

### Could it work in exact categories?

As defined, `PostnikovTower` requires `[Pretriangulated C]` because it uses `distTriang C` and `Pretriangulated.Triangle C`. The analogous structure in an abelian or exact category would be a chain of short exact sequences `0 → Aᵢ → Aᵢ₊₁ → Fᵢ → 0` rather than distinguished triangles. This would be a different type (perhaps `ExactFiltration` or similar). The current definition is correctly scoped to pretriangulated categories.

### Relationship to Mathlib's `TStructure`

Mathlib's `TStructure` provides a single-step truncation: for each integer `n`, an object decomposes into a `≤ n` part and a `≥ n+1` part via a distinguished triangle. The spectral object attached to a t-structure (`TStructure.spectralObject`) is the iterated truncation tower. A `PostnikovTower` is the finite version of this, without requiring that the filtration comes from a t-structure.

### Relationship to `RelSeries` / `CompositionSeries`

Mathlib's `RelSeries` (used by `CompositionSeries` and the Jordan-Holder machinery) is an order-theoretic abstraction: `Fin (n+1) → α` with a relation between consecutive elements. This is for lattices of subobjects, not for triangulated categories. The concepts are mathematically analogous but the implementations are in different worlds:

| Feature | `RelSeries` | `PostnikovTower` |
|---------|-------------|------------------|
| Context | Lattice/order | Pretriangulated category |
| Chain carrier | `Fin (n+1) → α` | `ComposableArrows C n` |
| Step data | `r a_i a_{i+1}` (relation) | Distinguished triangle |
| Quotient/factor | Implicit (lattice interval) | Explicit (`obj₃` of triangle) |
| Boundary | None required | `base_isZero`, `top_iso` |

## 4. Design Observations

### Strengths

1. **Clean separation of concerns.** The tower structure is purely about filtration data. Phase/semistability is layered on top by `HNFiltration`. This lets `K₀.of_postnikovTower_eq_sum` and `ExtensionClosure.of_postnikovTower` apply to any filtration, not just HN filtrations.

2. **`Nonempty` wrapping on isomorphisms.** The fields `triangle_obj₁`, `triangle_obj₂`, and `top_iso` use `Nonempty (_ ≅ _)` rather than bare isomorphisms. This avoids universe issues and unnecessary data dependencies -- the proofs only need existence of an iso, not a canonical choice. Every use site calls `Classical.choice` to extract the iso when needed.

3. **Factors derived, not stored.** `factor i` is defined as `(triangle i).obj₃` rather than being a separate field. This eliminates a redundant field and the need for a coherence iso `factor i ≅ (triangle i).obj₃`.

4. **`zero_isZero` for the `n = 0` edge case.** When the tower has zero length, the chain is a single object that is both `left` and `right`, so `base_isZero` and `top_iso` together would give `E ≅ 0`. The `zero_isZero` field makes this explicit and avoids needing to compose the chain of reasoning at every use site.

### Potential weaknesses / generalization opportunities

1. **No morphism-level coherence.** There is no field requiring `(triangle i).mor₁` to be compatible with `chain.map' i (i+1)` (up to the `triangle_obj₁`/`triangle_obj₂` isos). The current codebase never needs this: all proofs use only object-level information (isZero, K₀ classes, extension closure membership). If morphism-level arguments were ever needed (e.g., for functoriality of the filtration, or comparing two filtrations of the same object), this gap would need to be filled. For now it is harmless and avoids a significant coherence burden.

2. **Fixed to `ℕ`-indexed finite towers.** The definition uses `Fin n` indexing. An infinite or `ℤ`-indexed generalization would look more like `SpectralObject`. For Bridgeland stability (where HN filtrations are always finite), this is the right choice.

3. **No direct `SpectralObject` bridge.** There is currently no construction `PostnikovTower → SpectralObject C (Fin (n+1))` or vice versa. Building one would require adding the functoriality/naturality that `PostnikovTower` deliberately omits (or weakening `SpectralObject`). This bridge is not needed for the current formalization but could be useful if Mathlib's t-structure API evolves to use spectral objects more centrally.

4. **`grind` in auto-params.** The `by grind` in the types of `triangle_obj₁` and `triangle_obj₂` (to prove `i.val < n + 1` and `i.val + 1 < n + 1`) works but is heavier than necessary; `by omega` or `by lia` would suffice for these pure `Nat` goals. However, per project convention (`lia` over `omega`), `by lia` would be the preferred replacement. This is cosmetic.

## 5. Verdict

The `PostnikovTower` definition is at an appropriate level of generality for its role in this formalization. It correctly:
- Lives in pretriangulated categories (not wider)
- Uses finite indexing (appropriate for HN filtrations)
- Separates filtration data from phase data
- Avoids unnecessary coherence fields

The two realistic generalization paths -- (a) adding morphism coherence, and (b) building a bridge to `SpectralObject` -- are not needed by any current consumer and would add significant complexity. The definition should be left as-is unless a downstream proof requires morphism-level information from the chain.
