# Mathlib Naming Notes for Bridgeland Stability

**Date**: 2026-03-22  
**Scope**: naming and wrapper-design conventions relevant to `BridgelandStability`

## Summary

The main lesson is that Mathlib naming is not just about casing. It is about:

- what kind of object a declaration is,
- whether the name is describing mathematical content or only provenance,
- whether a declaration is a theorem proof or a named proposition/object,
- and whether the implementation is a proof-only wrapper or a genuinely richer bundled object.

The biggest correction to an over-simple rule is this:

- theorem and proof names should read like theorem names;
- but proposition-like named objects of `Sort 0` can perfectly well be `UpperCamelCase`;
- and when an `UpperCamelCase` concept appears *inside* the name of a proof, it should appear in
  `lowerCamelCase`.

So a name like `bridgelandCorollary_1_3` is bad, but not because it should be `snake_case`. It is
bad because the name says nothing about the content.

## What names should do

### 1. Put the mathematics in the name

Mathlib names are usually descriptive enough that a reader can guess the shape of the result.
Good names tell you:

- the object under discussion,
- the main conclusion,
- and sometimes the main hypothesis pattern.

Bad public names are usually bad for one of two reasons:

- they encode provenance rather than content, like theorem number or author name;
- they encode proof scaffolding rather than mathematical content.

That is the real problem with names like:

- `bridgelandCorollary_1_3`
- `bridgelandCorollary_1_3_complexManifold`
- `P_of_Q_of_P_semistable`

The issue is not merely syntax. The issue is that the reader learns almost nothing from the name.

### 2. Distinguish proofs from named propositions or objects

Mathlib treats these differently.

Typical theorem/proof names should be theorem-shaped and usually `snake_case`.

Examples from Mathlib include names like:

- `equalizerCondition_of_natIso`
- `solutionSetCondition_of_isRightAdjoint`
- `toMeasure_injective`

By contrast, named proposition-like objects or structures often use `UpperCamelCase`.

Examples include:

- `EqualizerCondition`
- `RightOreCondition`
- `ProbabilityMeasure`
- `FiniteMeasure`
- `ModularForm`

This matters for this project. A declaration of type `Prop` is not automatically a theorem-style
name. If it is being treated as a named proposition or packaged statement, `UpperCamelCase` can be
appropriate.

### 3. If an `UpperCamelCase` concept appears inside a proof name, lower-camelize it

This is a standard Mathlib move.

For example:

- `EqualizerCondition` as a concept,
- but `equalizerCondition_of_natIso` as a theorem about it.

So if a theorem name mentions `ComplexManifold`, `LocalHomeomorph`, or another capitalized concept,
the embedded occurrence should normally appear as `complexManifold`, `localHomeomorph`, and so on.

### 4. Prefer namespaces over redundant prefixes

Mathlib prefers:

- namespace context,
- then contentful local names,

over globally prefixed names that repeat the ambient object.

So a name like

- `StabilityCondition.false_of_all_hn_phases_below`

is much better than baking `StabilityCondition` and a theorem number into a single root-level name.

### 5. Avoid placeholder-letter public names

Names like

- `P_of_Q_of_P_semistable`
- `P_phi_of_truncation_of_P_phi_cone`

may be acceptable as scratch names during proof development, but they are not good public API.

Mathlib-style public names should say what the theorem does, not merely record the letters that
happened to be used in one proof.

### 6. Be conservative with abbreviations in public API

Some abbreviations are standard and tolerable. Others are too local to the project.

The main pressure points here are:

- `HN`
- `MDQ`
- `SES`
- `H0prime`

The closer something is to public API rather than internal scaffolding, the stronger the case for
expanding or regularizing the name.

In particular, `H0prime` is a weak public-facing stem. It is hard to guess, hard to search, and
does not match common Mathlib naming instincts.

## Implementation pattern matters

Naming and implementation are tied together.

Mathlib uses two nearby wrapper patterns.

### Pattern A: proof-only wrapper as a subtype

If the new object is just an old object plus a property, Mathlib often uses a subtype:

- `ProbabilityMeasure := { μ : Measure Ω // IsProbabilityMeasure μ }`
- `FiniteMeasure := { μ : Measure Ω // IsFiniteMeasure μ }`
- `CauchyFilter := { f : Filter α // Cauchy f }`
- `ContMDiffMap := { f : M → M' // CMDiff n f }`
- `FractionalIdeal := { I : Submodule R P // IsFractional S I }`
- `SpecialLinearGroup := { A : Matrix n n R // A.det = 1 }`
- `InfinitePlace := { w : AbsoluteValue K ℝ // ∃ φ, place φ = w }`
- `Fiber p S := { a : 𝒳 // p.obj a = S }`
- `SimpContFract := { g : GenContFract α // g.IsSimpContFract }`
- `Cover X := { S : Sieve X // S ∈ J X }`

In all of these cases, the implementation is a subtype and the API lives in the namespace of the
specialized wrapper object.

### Pattern B: richer bundled object as `structure ... extends ...`

If the new object is treated as a genuinely bundled enhancement of an existing object, Mathlib
often uses `extends`:

- `BoundedContinuousFunction extends ContinuousMap`
- `ZeroAtInftyContinuousMap extends ContinuousMap`
- `CocompactMap extends ContinuousMap`
- `ContinuousOpenMap extends ContinuousMap`
- `Path extends C(I, X)`
- `ModularForm extends SlashInvariantForm`

This is the right pattern when the new object is not just “old object + proof”, but a first-class
bundled object with its own inherited structure and API.

### Consequence for `NumericalStabilityCondition`

The current implementation

```lean
structure NumericalStabilityCondition ... where
  toStabilityCondition : StabilityCondition C
  factors : ...
```

is not the most Mathlib-like version of either pattern.

It would fit Mathlib better in one of these two forms:

1. as a subtype of `StabilityCondition C` with the factorization property;
2. or, if a structure is genuinely preferred, as `extends StabilityCondition C`.

So the implementation itself influences which namespace and theorem names will feel idiomatic.

## Practical naming guidance for this repo

For this project, the most useful short checklist is:

- Do not use author names or theorem numbers in public declaration names.
- Use namespaces to carry ambient context.
- Let theorem proofs read like theorem proofs.
- Let named proposition-objects or bundled objects read like named objects.
- Do not build public theorem names out of placeholder letters.
- Treat project-local abbreviations with suspicion, especially when they leak into public API.
- When you bundle an object with only a proof, prefer a subtype-style implementation.

## Sources consulted

- Lean community naming guide
- Lean community style guide
- current Mathlib naming and linter behavior
- direct comparison against nearby Mathlib wrapper types and namespaces
