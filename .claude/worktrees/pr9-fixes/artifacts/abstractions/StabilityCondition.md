# Audit: `StabilityCondition` Generality

**File:** `BridgelandStability/StabilityCondition/Defs.lean`
**Date:** 2026-03-26

---

## 1. Definition (verbatim)

### PreStabilityCondition.WithClassMap

```lean
structure WithClassMap (v : K₀ C →+ Λ) where
  slicing : Slicing C
  Z : Λ →+ ℂ
  compat : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)
```

### StabilityCondition.WithClassMap

```lean
structure WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  locallyFinite : slicing.IsLocallyFinite C
```

### Abbreviations

```lean
abbrev PreStabilityCondition :=
  PreStabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))

abbrev StabilityCondition :=
  StabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))
```

### Variable context (line 47-51)

```lean
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]
```

---

## 2. API Surface

### Fields (from the two structures)

| Field | Type | Structure |
|-------|------|-----------|
| `slicing` | `Slicing C` | `PreStabilityCondition.WithClassMap` |
| `Z` | `Λ →+ ℂ` | `PreStabilityCondition.WithClassMap` |
| `compat` | compatibility proof | `PreStabilityCondition.WithClassMap` |
| `locallyFinite` | `slicing.IsLocallyFinite C` | `StabilityCondition.WithClassMap` |

### Key derived definitions (in Defs.lean)

| Name | Signature | Purpose |
|------|-----------|---------|
| `slicingDist` | `Slicing C → Slicing C → ℝ≥0∞` | Bridgeland generalized metric |
| `stabSeminorm` | `StabilityCondition C → (K₀ C →+ ℂ) → ℝ≥0∞` | Stability seminorm |
| `basisNhd` | `StabilityCondition C → ℝ → Set (StabilityCondition C)` | Basis neighborhoods |
| `StabilityCondition.topologicalSpace` | `TopologicalSpace (StabilityCondition C)` | Bridgeland topology |
| `WithClassMap.topologicalSpace` | induced topology | For `Stab_v(D)` |
| `ComponentIndex` / `Component` | connected-component types | Per-component analysis |
| `CentralChargeIsLocalHomeomorphOnConnectedComponents` | Prop | Bridgeland Theorem 1.2 statement |

### Forgetting maps

- `PreStabilityCondition.WithClassMap.toPreStabilityCondition` : forgets class map to identity
- `StabilityCondition.WithClassMap.toStabilityCondition` : forgets class map to identity

### Usage counts across the codebase

| Name | Occurrences | Files |
|------|-------------|-------|
| `StabilityCondition` (all mentions) | 556 | 39 |
| `WithClassMap` | 90 | 9 |
| `stabSeminorm` | 465 | 22 |
| `slicingDist` | 111 | 7 |
| `basisNhd` | 92 | 5 |

### Key downstream consumers

- **StabilityCondition/Basic.lean**: `ext` theorems, phase rigidity (`phase_eq_of_same_Z`)
- **StabilityCondition/Seminorm.lean**: metric properties, seminorm bounds, sector bound
- **StabilityCondition/Topology.lean**: Lemma 6.4 (local injectivity), `continuous_toStabilityCondition`
- **StabilityCondition/Deformation.lean**: deformation theorem, `eq_of_same_Z_near`
- **StabilityCondition/ConnectedComponent.lean**: open connected components, seminorm equivalence
- **StabilityCondition/LocalHomeomorphism.lean**: Bridgeland Theorem 1.2 proof
- **NumericalStability/Basic.lean**: `ClassMapStabilityCondition`, factorization subtype, equivalence
- **NumericalStabilityManifold.lean**: complex manifold structure on connected components
- **EulerForm/**: numerical quotient map, Corollary 1.3
- **HeartEquivalence/**: Proposition 5.3 equivalence, roundtrip
- **Deformation/**: the full deformation machine (30+ files)

---

## 3. Mathematical Generalization Analysis

### What is this mathematically?

A **Bridgeland stability condition** on a triangulated category `D` (Bridgeland 2007,
Definition 5.3) is a pair `σ = (Z, P)` where:

- `P : ℝ → ObjectProperty D` is a **slicing** (Definition 5.1): a family of full
  subcategories `P(φ)` of "semistable objects of phase φ", satisfying shift-by-1,
  Hom-vanishing, and HN existence.
- `Z : K₀(D) → ℂ` is a **central charge**, an additive group homomorphism.
- **Compatibility**: for every nonzero `E ∈ P(φ)`, `Z([E]) = m · exp(iπφ)` with `m > 0`.
- **Local finiteness**: there exists `η > 0` such that thin interval subcategories
  `P((t-η, t+η))` have ACC+DCC on strict subobjects for all `t`.

The `WithClassMap` variant factors the central charge through a quotient
`v : K₀(D) →+ Λ`, so `Z : Λ →+ ℂ` and the compatibility uses `Z(v([E]))`.
The bare `StabilityCondition` specializes to `v = id`.

### Minimal axioms / what each hypothesis buys

| Hypothesis | Used for |
|------------|----------|
| `Category C` | Objects, morphisms |
| `HasZeroObject C` | Zero objects in `P(φ)`, `IsZero` predicate |
| `HasShift C ℤ` | Shift functor `[1]`, phase shift axiom |
| `Preadditive C` | Additive structure on Hom spaces |
| `(shiftFunctor C n).Additive` | Shift respects additive structure |
| `Pretriangulated C` | Distinguished triangles for K₀ and HN filtrations |
| **`IsTriangulated C`** | **See analysis below** |
| `AddCommGroup Λ` | Target of class map |

### Does it need `IsTriangulated`?

**The structures themselves do not.** The `IsTriangulated C` instance appears in the
`variable` block at line 49 of Defs.lean but is not consumed by:

- `PreStabilityCondition.WithClassMap` (structure definition)
- `StabilityCondition.WithClassMap` (structure definition)
- `slicingDist`, `stabSeminorm`, `basisNhd` (definitions)
- `StabilityCondition.topologicalSpace` (instance)

The `Slicing` structure (in `Slicing/Defs.lean`) requires only `Pretriangulated C`.
The `K₀` definition (in `GrothendieckGroup/Defs.lean`) also requires only
`Pretriangulated C`. The `IsLocallyFinite` condition (in
`IntervalCategory/FiniteLength.lean`) is defined with `omit [IsTriangulated C]`.

**Where `IsTriangulated` is genuinely needed:**

- The octahedral axiom is used in the **deformation machine** (constructing the
  deformed slicing from a nearby central charge), specifically in pullback/pushout
  constructions in `Deformation/Pullback.lean`, `Deformation/BoundaryTriangle.lean`,
  etc.
- The **HeartEquivalence** (Proposition 5.3) uses `IsTriangulated` for bounded
  t-structure theory.
- Many results in Seminorm.lean, Topology.lean carry `omit [IsTriangulated C]`
  annotations, confirming the instance is not needed for those results.

**Verdict:** The `[IsTriangulated C]` in the variable block of Defs.lean is overly
broad. The definitions could live in a `Pretriangulated` context; only the deep
deformation theory and the HeartEquivalence genuinely need the full octahedral axiom.
However, since every downstream consumer of `StabilityCondition` eventually needs
`IsTriangulated` for the deformation theorem or the local-homeomorphism result,
weakening the variable block would create friction (more `omit`/`include` annotations)
without enabling a meaningful new use case. The current design is pragmatic: the
definitions carry a slightly stronger hypothesis than strictly necessary, but the
surplus is consumed by every significant theorem about them.

### Could it work over other base fields?

The central charge is `Z : Λ →+ ℂ` and the compatibility is stated in terms of
`ℝ`-valued phases and `Complex.exp(iπφ)`. This is **intrinsically tied to ℂ/ℝ**:

- The **phase** `φ ∈ ℝ` parametrizes a ray in the upper half-plane of `ℂ` via
  `exp(iπφ)`. This uses the topology and analysis of `ℂ` (specifically `sin`, `cos`,
  `exp`, `π`).
- The **seminorm** divides `|U(E)|` by `|Z(E)|`, using the complex norm.
- The **topology** on `Stab(D)` uses `sin(πε)` in the seminorm ball definition.
- The **local-homeomorphism** theorem maps to a complex vector subspace of `Λ →+ ℂ`.

Generalizing over arbitrary valued fields would require replacing the exponential
parametrization of rays, which would lose the concrete meaning of "phase". This is
not a generalization that the mathematical theory supports: Bridgeland's theory is
specifically about the space of stability conditions as a **complex manifold**, and
the base field `ℂ` is essential to the manifold structure theorem.

One could imagine replacing `ℂ` with an arbitrary normed field and phases with
elements of some ordered group, but this would be a different theory (closer to
"slope stability" on abelian categories, which Mathlib already partially formalizes
via HN filtrations in a more algebraic setting).

---

## 4. Mathlib Comparison

### Searches performed

| Tool | Query | Results |
|------|-------|---------|
| leansearch | "Bridgeland stability condition on triangulated category" | No matches (returned `IsTriangulated`, `TStructure`) |
| leansearch | "central charge group homomorphism to complex numbers" | No matches (returned `Complex.reAddGroupHom`, `Circle.coeHom`) |
| leansearch | "stability function on abelian category with HN filtration" | No matches (returned `Ideal.Filtration.Stable`) |
| leanfinder | "stability condition central charge slicing triangulated category" | No matches (returned `TStructure`, `IsTriangulated`, `Pretriangulated`) |
| leanfinder | "Harder-Narasimhan filtration stability function abelian category" | No matches (returned `Abelian`, `Ideal.Filtration`) |
| leanfinder | "Grothendieck group K0 of triangulated category" | No matches (returned `Triangulated.Subcategory`, `DerivedCategory`) |
| leanfinder | "t-structure heart abelian category derived category" | Returned `DerivedCategory`, `HomotopyCategory` |
| loogle | `"Slicing"` | No matches |
| loogle | `"TStructure"` | Lean kernel matches only |

### What Mathlib has

Mathlib (as of this project's dependency snapshot) has:

- **`CategoryTheory.Triangulated.TStructure`**: t-structures on pretriangulated
  categories, including hearts, truncation functors, boundedness.
- **`CategoryTheory.IsTriangulated`**: the octahedral axiom.
- **`CategoryTheory.Pretriangulated`**: distinguished triangles, rotation.
- **`DerivedCategory`**: derived categories of abelian categories.
- **No stability conditions, no slicings, no central charges, no K₀ of triangulated
  categories, no Bridgeland metric/topology.**

### What this project adds beyond Mathlib

| Concept | This project | Mathlib |
|---------|-------------|---------|
| `Slicing` | Full definition with HN existence | Not present |
| `K₀` of triangulated category | Via `FreeAbelianGroup` quotient | Not present |
| `PreStabilityCondition` | Central charge + slicing + compat | Not present |
| `StabilityCondition` | + local finiteness | Not present |
| `WithClassMap` variant | Factored central charge | Not present |
| Bridgeland metric (`slicingDist`) | Generalized metric on slicings | Not present |
| Stability seminorm (`stabSeminorm`) | On `Hom(K₀, ℂ)` | Not present |
| Bridgeland topology | Generated by basis neighborhoods | Not present |
| Local-homeomorphism (Theorem 1.2) | Statement + proof | Not present |
| Complex manifold structure | On connected components | Not present |
| Heart equivalence (Proposition 5.3) | Roundtrip bijection | Not present |
| Deformation theorem | Full machine | Not present |
| Numerical stability | Euler form, numerical K₀, Cor 1.3 | Not present |
| `PostnikovTower`, `HNFiltration` | Used for HN filtrations | Not present |
| `IntervalCategory` | Quasi-abelian subcategories `P((a,b))` | Not present |

---

## 5. Assessment

### Design quality

The `WithClassMap` parametrization over a class map `v : K₀ C →+ Λ` is a good
design choice. It enables:

1. **Bare stability conditions** via `v = id` (the `StabilityCondition` abbreviation).
2. **Numerical stability conditions** via `v = numericalQuotientMap k C` (Corollary 1.3).
3. **Factorization subtype** `ClassMapStabilityCondition` as a comparison object.
4. **Single proof of Theorem 1.2** that specializes to both cases.

The separation of `Pre`/non-`Pre` (local finiteness) matches the paper's Definition
5.3 vs 5.1.

### Potential improvements (not recommendations)

1. **`IsTriangulated` in variable block**: Could be dropped from Defs.lean with `omit`
   annotations on the few results that do not need it. However, this would be
   cosmetic -- every theorem of substance needs it.

2. **`Slicing` could be abstracted**: A slicing is a ℝ-indexed family of subcategories
   with shift, Hom-vanishing, and HN existence. One could imagine parametrizing over
   the index group (ℝ replaced by an ordered abelian group), but this would break the
   connection to complex exponentials in the compatibility condition.

3. **The central charge target is hardcoded to ℂ**: Replacing `ℂ` with a general
   normed field would lose the phase parametrization. This is mathematically correct
   as stated.

### Verdict on generality

**The definition is at maximal usable generality for Bridgeland's theory.** The
parametrization over class maps is the right abstraction. The `IsTriangulated`
hypothesis is technically stronger than needed for the bare definitions but is
consumed by all significant theorems. The hardcoding of `ℂ` and `ℝ`-valued phases
is a mathematical necessity, not an artificial restriction.
