# ExtensionClosure Abstraction Analysis

## Current Definition

File: `/home/matt.linux/lean/bridgeland-extract/BridgelandStability/ExtensionClosure.lean` (148 lines)

```lean
inductive CategoryTheory.ObjectProperty.ExtensionClosure {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasShift C Z] [Preadditive C]
    [(n : Z), (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) : ObjectProperty C where
  | zero {E : C} : IsZero E -> P.ExtensionClosure E
  | mem {E : C} : P E -> P.ExtensionClosure E
  | ext {X E Y : C} {f : X -> E} {g : E -> Y} {h : Y -> X[[1]]} :
      Triangle.mk f g h in distTriang C ->
      P.ExtensionClosure X -> P.ExtensionClosure Y -> P.ExtensionClosure E
```

Mathematically: given a property `P` on objects of a pretriangulated category,
`P.ExtensionClosure` is the smallest property that contains `P`, contains zero
objects, and is closed under extensions in distinguished triangles (i.e., if
`X -> E -> Y -> X[1]` is distinguished and `X, Y` satisfy the property, then so
does `E`).

## Critical API (Phase 1)

### Lemmas in the `ExtensionClosure.` namespace

| Declaration | Used externally? | Call count |
|---|---|---|
| `ExtensionClosure.mono` | Yes -- 6 call sites in TStructure.lean | 6 |
| `ExtensionClosure.hom_eq_zero` | Yes -- 2 call sites in TStructure.lean | 2 |
| `ExtensionClosure.of_iso` | No (used only via the IsClosedUnderIsomorphisms instance) | 0 direct |
| `ExtensionClosure.of_postnikovTower` | Yes -- 12 call sites across 3 files | 12 |
| `ExtensionClosure.le_of_closed` | No external callers | 0 |
| Instance: `IsClosedUnderIsomorphisms` | Used implicitly | -- |
| Instance: `IsTriangulatedClosed2` | Used implicitly | -- |

### Constructor usage by external callers

| Constructor | Usage pattern | Count |
|---|---|---|
| `.zero` | Building EC terms for zero factors in Postnikov towers | 6 |
| `.mem` | Injecting generators into the closure | 6 |
| `.ext` | Used in ec_idem proofs and in Theorem.lean inductions | 6 |

### Induction on `ExtensionClosure` (pattern-matching on all three constructors)

- `Deformation/Theorem.lean:115-125` -- `deformedGtPred_subset_gtProp` induction
- `Deformation/Theorem.lean:131-142` -- `deformedLtPred_subset_ltProp` induction
- `Deformation/DeformedGtLe.lean:450-453` -- `ec_idem_gt`
- `Deformation/DeformedGtLe.lean:456-460` -- `ec_idem_le`
- `Deformation/DeformedSlicingHN.lean:356-359` -- `ec_idem_le`
- `Deformation/DeformedSlicingHN.lean:363-366` -- `ec_idem_gt`
- `Deformation/DeformedSlicingHN.lean:555` -- ad-hoc iso closure via ec_idem_le

**Load-bearing API**: `mono`, `hom_eq_zero`, `of_postnikovTower`, and the three
constructors (for both building terms and induction). The `le_of_closed`
universal property is defined but unused. The `IsTriangulatedClosed2` instance
is registered but never consumed by downstream code explicitly.

## Duplication Findings (Phase 2)

### A. Within this project

**1. The `deformedGtPred`/`deformedLePred`/`deformedLtPred` definitions are pure
`ExtensionClosure` applications, not parallel constructions.**

File: `Deformation/TStructure.lean:290-310`

```lean
def deformedGtPred ... := (deformedGtGen ...).ExtensionClosure
def deformedLePred ... := (deformedLeGen ...).ExtensionClosure
def deformedLtPred ... := (deformedLtGen ...).ExtensionClosure
```

These are not parallel inductive types -- they are direct applications of
`ExtensionClosure` to different generator properties. No duplication here.

**2. The ec_idem pattern: duplicated 4 times across 2 files.**

The same 4-line proof block appears verbatim:

```lean
have ec_idem_XX : forall {X : C},
    (P.ExtensionClosure).ExtensionClosure X -> P.ExtensionClosure X := by
  intro X hX; induction hX with
  | zero hZ => exact .zero hZ
  | mem h => exact h
  | ext hT _ _ ihX ihY => exact .ext hT ihX ihY
```

Locations:
- `Deformation/DeformedGtLe.lean:447-453` (ec_idem_gt)
- `Deformation/DeformedGtLe.lean:454-460` (ec_idem_le)
- `Deformation/DeformedSlicingHN.lean:353-359` (ec_idem_le)
- `Deformation/DeformedSlicingHN.lean:360-366` (ec_idem_gt)

This is idempotency of `ExtensionClosure` when the generators are themselves
already an `ExtensionClosure`. The missing lemma is:

```lean
theorem ExtensionClosure.idem (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulatedClosed2]
    [P.ContainsZero] :
    P.ExtensionClosure <= P
```

or equivalently (since `P.ExtensionClosure` has these instances):

```lean
theorem ExtensionClosure.idempotent (P : ObjectProperty C) :
    P.ExtensionClosure.ExtensionClosure <= P.ExtensionClosure
```

This follows from `le_of_closed` (which is already defined but unused!). The
4 duplicated blocks exist because nobody calls `le_of_closed`.

**3. The Slicing/ExtensionClosure.lean file -- parallel but distinct.**

This file proves that `leProp`, `gtProp`, `ltProp`, `intervalProp` are closed
under extensions from distinguished triangles. These are ~280 lines of proofs.
However, these are NOT instances of `ExtensionClosure`:

- `leProp` etc. are defined *directly* (not as `SomeGen.ExtensionClosure`).
- Their extension-closedness proofs use HN filtrations, hom-vanishing, and
  coYoneda/Yoneda exact sequences -- domain-specific arguments.
- They do not follow from the abstract `ExtensionClosure` induction.

So Slicing/ExtensionClosure.lean is correctly named (it's about extension-closure
*properties* of slicing predicates) but is not related to the `ExtensionClosure`
*type*.

**4. The Theorem.lean induction pattern.**

At `Deformation/Theorem.lean:110-142`, two proofs induct on `ExtensionClosure`
to show `deformedGtPred <= Q.gtProp` and `deformedLtPred <= Q.ltProp`. These
are applications of `le_of_closed` in spirit:
- zero case: `Q.gtProp` contains zeros
- mem case: generators satisfy `Q.gtProp`
- ext case: `Q.gtProp` is closed under extensions (from Slicing/ExtensionClosure.lean)

These could be one-liners if `le_of_closed` were used, but `le_of_closed`
requires explicit lambdas for each closure condition while the induction is
arguably just as readable.

### B. In Mathlib

**`ObjectProperty.IsTriangulatedClosed2`** (Mathlib.CategoryTheory.Triangulated.Subcategory):
This is the *class* saying a property is closed under extensions in distinguished
triangles. `ExtensionClosure` produces an instance of this class.

**`ObjectProperty.IsClosedUnderExtensions`** (Mathlib.CategoryTheory.ObjectProperty.Extensions):
This is the abelian-category version -- closure under short exact sequences.
Different setting (no triangles, needs ShortComplex.ShortExact).

**`Triangulated.Subcategory`** (Mathlib.CategoryTheory.Triangulated.Subcategory):
A triangulated subcategory requires: (1) contains zero, (2) closed under shifts,
(3) closed under extensions. `ExtensionClosure` gives (1) and (3) but NOT (2).
Extension-closure is a weaker notion than triangulated-subcategory generation.

**No existing Mathlib definition for "extension closure" as a generation operation.**
Mathlib has `isoClosure` (closure under isomorphisms) and the concept of
triangulated subcategory, but no inductive construction that generates the
smallest extension-closed property containing a given property. This is a gap.

## Mathematical Identity (Phase 3)

### What ExtensionClosure IS

In the language of Bridgeland's paper (p.6) and standard triangulated category
theory:

> Given a class S of objects in a triangulated category D, the **extension closure**
> <S> (or Filt(S)) is the smallest full subcategory of D that:
> 1. Contains 0
> 2. Contains S
> 3. Is closed under extensions: if X -> E -> Y -> X[1] is a distinguished
>    triangle with X, Y in <S>, then E in <S>.

This is NOT the same as the thick subcategory generated by S (which also
requires closure under shifts and direct summands) nor the triangulated
subcategory generated by S (which requires closure under shifts).

In Bridgeland's deformation argument, extension closure appears specifically
because the subcategories Q(>t), Q(<=t), Q(<t) are defined as extension
closures of their generators (the Q-semistable objects of the appropriate
phases). These subcategories are NOT shift-closed -- that's essential to the
theory.

### Most general context

The critical API needs:
- `mono`: works for any closure operator on a poset.
- `hom_eq_zero`: uses coYoneda/Yoneda exact sequences from distinguished triangles.
  This is specific to pretriangulated categories.
- `of_postnikovTower`: uses the PostnikovTower structure, which is specific to
  pretriangulated categories.
- `of_iso`: uses distinguished cocone triangles. Specific to pretriangulated.
- The three constructors and induction: pure inductive definition.

The `ext` constructor itself mentions `distTriang C`, so the definition is
inherently tied to pretriangulated categories. One *could* generalize to
"any notion of conflation" (exact categories, extriangulated categories), but:

1. Mathlib does not have extriangulated categories.
2. The project's API (`hom_eq_zero`, `of_postnikovTower`) uses triangle-specific
   machinery (Yoneda/coYoneda exact sequences, Postnikov towers).
3. No other user of such a generalization exists.

### Literature context

- **Bridgeland (2007)**, Section 5: defines subcategories P(phi) as extension
  closures of semistable objects.
- **Beilinson-Bernstein-Deligne (1982)**: t-structures use truncation
  subcategories that are extension-closed, but they are defined by the
  truncation functors, not generated.
- **Happel-Reiten-Smalo (1996)**: tilting theory uses extension-closed
  subcategories of abelian categories.
- **Nakaoka-Palu (2019)**: extriangulated categories provide a common
  generalization, but the formalization infrastructure does not exist.

## Proposal (Phase 4)

### What to do

**A. Extract the missing `idempotent` lemma** (eliminates duplication, small change).

Add to `ExtensionClosure.lean`:

```lean
/-- ExtensionClosure is idempotent: applying it twice is the same as applying
it once. This follows from `le_of_closed` since `P.ExtensionClosure` already
contains zero, contains `P`, and is closed under extensions. -/
theorem ExtensionClosure.idempotent {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasShift C Z] [Preadditive C]
    [(n : Z), (shiftFunctor C n).Additive] [Pretriangulated C]
    {P : ObjectProperty C} :
    P.ExtensionClosure.ExtensionClosure <= P.ExtensionClosure :=
  le_of_closed (fun hZ => .zero hZ) (fun _ h => h) (fun hT h1 h3 => .ext hT h1 h3)
```

This eliminates all 4 `ec_idem_gt`/`ec_idem_le` blocks (16 lines of proof each
time, ~64 lines total across 2 files). Each call site becomes a one-liner like
`ExtensionClosure.idempotent _ hX`.

**B. Do NOT extract a more general "closure operator" abstraction.**

Reasons:
- `ExtensionClosure` is only 148 lines and has a clean, focused API.
- The only duplication found is the idempotency lemma (4 copies), not a
  structural pattern that repeats across fundamentally different types.
- The `leProp_of_triangle`/`gtProp_of_triangle` proofs in
  Slicing/ExtensionClosure.lean look superficially similar but use completely
  different proof techniques (HN filtration analysis vs. induction on the
  inductive type). They are not instances of the same pattern.
- Mathlib's `IsTriangulatedClosed2` already captures the *class* of
  extension-closed properties. `ExtensionClosure` is the *free construction*
  producing such a class from generators. These are dual perspectives and
  both are needed.
- Generalizing to extriangulated categories would require infrastructure
  that doesn't exist in Mathlib and has no second user.

**C. Optionally simplify the Theorem.lean inductions** using `le_of_closed`.

The two induction blocks at `Deformation/Theorem.lean:110-142` could become:

```lean
have deformedGtPred_subset_gtProp : ... :=
  ExtensionClosure.le_of_closed
    (fun hZ => Or.inl hZ)
    (fun E hE => ... )  -- generators
    (fun hT h1 h3 => Q.gtProp_of_triangle C t h1 h3 hT)
```

But this is a minor readability tradeoff (the current explicit induction is
arguably more transparent), so I mark it as optional.

### Scope

| Item | Files changed | Lines removed | Lines added | Net |
|---|---|---|---|---|
| Add `idempotent` lemma | ExtensionClosure.lean | 0 | 8 | +8 |
| Use `idempotent` in DeformedGtLe.lean | DeformedGtLe.lean | 14 | 2 | -12 |
| Use `idempotent` in DeformedSlicingHN.lean | DeformedSlicingHN.lean | 14 | 2 | -12 |
| **Total** | **3 files** | **28** | **12** | **-16** |

### New instances/theorems enabled

The `idempotent` lemma is useful beyond the current call sites whenever one
needs to show that an object built from extension-closure generators (via
`of_postnikovTower`) lies in the extension closure itself. This pattern appears
whenever HN filtrations are re-refined.

### Kill switch

**Keep internal.** This is a missing API lemma for an existing project-specific
definition, not a new abstraction. It should be added to `ExtensionClosure.lean`
and used immediately. Not upstream-ready until Mathlib has a use for
`ExtensionClosure` itself (which would require formalizing Bridgeland stability
conditions or similar deformation arguments).

If `ExtensionClosure` is ever upstreamed to Mathlib (as a companion to
`IsTriangulatedClosed2`, analogous to how Subgroup.closure relates to
Subgroup), then `idempotent` would go with it. But that's a separate decision.
