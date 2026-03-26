# Abstraction Audit: `Slicing`

**File**: `BridgelandStability/Slicing/Defs.lean`
**Namespace**: `CategoryTheory.Triangulated.Slicing`

---

## PHASE 1: What callers actually need

### The definition

```lean
structure Slicing where
  P : ℝ → ObjectProperty C
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)
```

### Critical API and usage counts

| API | Occurrences | Role |
|-----|------------|------|
| `s.P φ` (direct) | ~291 across 32 files | The primitive: "E is semistable of phase phi" |
| `gtProp`/`leProp`/`geProp`/`ltProp` | ~362 across 24 files | Half-plane subcategory predicates derived from HN phases |
| `phiPlus`/`phiMinus` | ~559 across 32 files | Intrinsic extreme phases of nonzero objects |
| `intervalProp` | ~419 across 32 files | Interval subcategory P((a,b)) |
| `toTStructure` | ~66 across 15 files | Construct a Mathlib `TStructure` from a slicing |
| `phaseShift` | used in TStructureConstruction, IntervalCategory, Deformation | Shift all phases by a real constant |
| `hn_exists` | ~10 direct uses | Invoked in toTStructure, toTStructureGE, boundedness proofs |
| `heart.FullSubcategory` (via toTStructure) | ~349 across 18 files | Heart abelian category for Prop 5.3 |

### What callers actually need

The slicing API is used at two distinct levels:

1. **ℝ-parameterized level** (dominant): `s.P`, `phiPlus`, `phiMinus`, `intervalProp`,
   `gtProp`/`leProp`, `phaseShift`. This is the Bridgeland-specific API that knows about
   real-valued phases, HN filtrations, and continuous phase functions. It accounts for the
   vast majority of downstream usage (~1600+ occurrences).

2. **ℤ-discretized level** (secondary): `toTStructure`, `toTStructureGE`, their hearts and
   boundedness. These are used to access Mathlib's t-structure machinery (abelian heart,
   truncation functors, spectral objects). ~400+ occurrences, concentrated in
   IntervalCategory/ and HeartEquivalence/.

---

## PHASE 2: Duplication analysis

### Within this project

There is no duplication within the project. The `Slicing` type is the single source for
all ℝ-parameterized subcategory data. The `StabilityFunction` type in
`StabilityFunction/` operates on abelian categories and produces its own
`AbelianHNFiltration`, which is a distinct concept (abelian HN filtrations are chains of
subobjects, not Postnikov towers in a triangulated category).

### In Mathlib

Mathlib has exactly one relevant structure:

**`TStructure C`** (in `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`):
```lean
structure TStructure where
  le (n : ℤ) : ObjectProperty C
  ge (n : ℤ) : ObjectProperty C
  -- shift compatibility, hom vanishing, monotonicity, decomposition
```

There is **no** slicing, stability function, weight structure, or "parameterized
subcategory family" abstraction in Mathlib. The TStructure is the closest neighbor.

### Structural comparison: Slicing vs TStructure

| Feature | `Slicing` | `TStructure` |
|---------|-----------|-------------|
| Index set | ℝ (continuous) | ℤ (discrete) |
| Subcategory data | `P : ℝ → ObjectProperty C` | `le, ge : ℤ → ObjectProperty C` |
| Shift compatibility | `P(φ) X ↔ P(φ+1) (X⟦1⟧)` | `le n X → le (n-a) (X⟦a⟧)` |
| Vanishing | pointwise: `φ₂ < φ₁ → Hom(P(φ₁), P(φ₂)) = 0` | `Hom(le 0, ge 1) = 0` |
| Decomposition | HN filtration (finite chain) | Single triangle `X → A → Y` |
| Monotonicity | Implicit (from HN phases) | Explicit axioms: `le 0 ≤ le 1`, `ge 1 ≤ ge 0` |

The key difference: a slicing gives a **family of thin subcategories** `P(φ)` indexed
by ℝ, from which one derives **half-plane predicates** `gtProp(t)` and `leProp(t)` for
all `t ∈ ℝ`. A t-structure gives **two families of thick subcategories** `le(n)` and
`ge(n)` indexed by ℤ.

The slicing produces *infinitely many* t-structures via `phaseShift`: for each `t ∈ ℝ`,
`(s.phaseShift t).toTStructure` gives a different t-structure. The ℤ-indexed t-structure
is a *discretization* that loses the fine ℝ-grading.

### Is there a common "parameterized subcategory family" pattern?

Not in Mathlib. The closest potential abstraction would be something like:
```lean
structure IndexedSubcategoryFamily (I : Type*) [LinearOrder I] where
  P : I → ObjectProperty C
  -- shift, vanishing, decomposition axioms
```
But this does not exist in Mathlib, and the axioms differ enough between slicings
(ℝ-indexed, HN filtrations) and t-structures (ℤ-indexed, single triangles) that
a common abstraction would need to be quite general. The cost-benefit is unclear.

---

## PHASE 3: Mathematical identity (Bridgeland Prop 3.3)

### What the literature says

Bridgeland, Proposition 3.3: *"To give a slicing of D is equivalent to giving a
bounded t-structure on D together with a stability function on its heart having the
Harder-Narasimhan property."*

More precisely, this is an equivalence of data:
- **Forward**: A slicing `s` determines a bounded t-structure `s.toTStructure` and a
  stability function on its heart `Z_s` with HN property.
- **Reverse**: Given a bounded t-structure `t` and a stability function `Z` on its
  heart with HN property, one constructs a slicing whose phase-`φ` subcategory is
  determined by the semistable objects of phase `φ` under `Z`, shifted by `⟦n⟧`.

### What the project proves

- **Forward** (`toTStructure`, `toTStructure_bounded`, `toTStructure_heart_iff`,
  `StabilityCondition.toHeartStabilityData`): fully formalized.
- **Reverse** (`HeartStabilityData.toPhasePackage`, reverse roundtrip): partially
  formalized in `HeartEquivalence/Reverse.lean` and `HeartEquivalence/Forward.lean`.
- **Roundtrip identities**: stated as `StabilityCondition.roundtrip` and
  `HeartStabilityData.roundtrip`.

### Should Slicing BE a TStructure with extra data?

The question is whether to define:
```lean
structure Slicing extends TStructure C where
  -- extra ℝ-grading data refining the ℤ-grading
```

**This would be the wrong abstraction.** Here is why:

1. **The ℝ-indexed family `P : ℝ → ObjectProperty C` is primary data, not derived
   data.** The t-structure is a *coarsening* that forgets information. Making `Slicing`
   extend `TStructure` would force every slicing construction to first build a
   t-structure (which requires `[IsTriangulated C]` for the octahedral axiom) and then
   layer the ℝ-grading on top. But the slicing axioms themselves only require
   `[Pretriangulated C]`. The current code correctly separates these:
   - `Slicing`: defined for `[Pretriangulated C]`
   - `toTStructure`: requires `[IsTriangulated C]`

2. **The dominant API is slicing-native, not t-structure-derived.** The numbers show
   this clearly: `s.P`/`phiPlus`/`phiMinus`/`intervalProp`/`gtProp`/`leProp` account
   for ~1600+ occurrences. The `toTStructure` pathway accounts for ~66 + ~349 (via
   heart). The slicing-native API is the workhorse; the t-structure is accessed only
   when callers need Mathlib's abelian heart machinery (truncation functors, spectral
   objects, heart abelianness).

3. **`toTStructure` is not unique.** A slicing gives *two* natural t-structures:
   `toTStructure` (heart = `P((0,1])`) and `toTStructureGE` (heart = `P([0,1))`).
   And via `phaseShift`, it gives a continuum of t-structures parameterized by ℝ.
   There is no canonical choice to bundle as the parent.

4. **The equivalence (Prop 3.3) is a theorem, not a definition.** The equivalence
   between slicings and bounded-t-structure-plus-stability-function is mathematically
   important but should remain a *proved theorem*, not a *definitional identity*.
   Collapsing the two sides of an equivalence into a single definition would obscure
   the non-trivial content of the proposition.

5. **Universe/typeclass issues.** The TStructure construction requires `[IsTriangulated C]`
   because the decomposition triangle `X → A → Y` for an arbitrary object is built using
   the octahedral axiom (the proof in `exists_triangle_gtProp_leProp` is by induction on
   the HN filtration length, gluing truncated pieces via octahedra). Making this a
   prerequisite for `Slicing` itself would unnecessarily strengthen the typeclass
   requirements for all the ℝ-parameterized API that never touches the octahedral axiom.

---

## PHASE 4: Verdict

### Decline to refactor

The current design is the right abstraction. Specifically:

**`Slicing` should NOT extend `TStructure`.** The relationship between slicings and
t-structures is correctly captured as:
- A function `Slicing.toTStructure : Slicing C → TStructure C` (requiring
  `[IsTriangulated C]`)
- A theorem `Slicing.toTStructure_bounded` proving the result is bounded
- An equivalence (Prop 5.3) between stability conditions and heart stability data

**There is no missing common abstraction in Mathlib.** The ℝ-indexed family `P : ℝ →
ObjectProperty C` with its HN filtration axiom is genuinely different from the
ℤ-indexed `le`/`ge` pair with its single-triangle decomposition. A forced unification
would either:
- Be so general as to provide no useful API (a "parameterized subcategory family"
  with no specific axioms), or
- Require pushing the ℝ-specific axioms into the general framework (which defeats
  the purpose of generalization).

### What could be improved (not abstraction changes)

1. **`TStructure.IsBounded` is project-local.** It is defined in
   `BridgelandStability/Slicing/TStructure.lean:215` as
   `∀ E : C, ∃ a b : ℤ, t.le a E ∧ t.ge b E`. Mathlib does not yet have a bounded
   t-structure concept. When Mathlib adds one, this project should adopt it.

2. **The `C` universe variable threading.** The slicing API passes `C` as an explicit
   variable everywhere (e.g., `s.gtProp C t E`, `s.phiPlus C E hE`). This is a
   Lean 4 section-variable artifact, not an abstraction issue, but it adds syntactic
   noise. This is consistent with the project's other types but worth noting.

3. **`heartFullSubcategoryAbelian` is project-local.** The proof that the heart of a
   t-structure is abelian lives in `BridgelandStability/TStructure/HeartAbelian.lean`.
   Mathlib's TStructure.Heart file has a TODO for this. When Mathlib proves it, the
   project should adopt the Mathlib version.

### Summary

The `Slicing` definition is mathematically faithful, well-abstracted, and correctly
positioned relative to Mathlib's `TStructure`. The `toTStructure` function correctly
mediates between the ℝ-parameterized world (slicings) and the ℤ-discretized world
(t-structures). No refactoring is warranted.
