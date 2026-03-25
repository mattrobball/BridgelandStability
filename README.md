# BridgelandStability

This repository is an experimental AI-assisted formalization of the main
results of Tom
Bridgeland's paper
[Stability conditions on triangulated categories](https://annals.math.princeton.edu/2007/166-2/p01)
in Lean 4 using Mathlib.

The mathematical target is the deformation-theoretic core of the paper:
the topology on `Stab(D)`, the local-homeomorphism theorem for the central
charge, and the consequent complex manifold structure on connected components
of the space of numerically finite stability conditions.

## What Bridgeland stability conditions are

Classical moduli theory studies stability for objects in abelian categories:
stable vector bundles, semistable coherent sheaves, Harder-Narasimhan
filtrations, wall-crossing, and moduli spaces. Bridgeland's insight was that
the same package can be lifted from abelian categories to triangulated
categories.

A Bridgeland stability condition on a triangulated category `D` consists, at a
high level, of:

- a central charge `Z : K_0(D) -> C`;
- a slicing `P(phi)` of `D` by semistable objects of phase `phi`;
- Harder-Narasimhan type decompositions for all nonzero objects;
- a compatibility condition saying that semistable objects of phase `phi` are
  sent by `Z` to the ray `R_{>0} * exp(i pi phi)`.

One of the key structural facts in the paper is that this can also be described
in terms of a bounded t-structure together with a stability function on its
heart having the Harder-Narasimhan property. That equivalence is one of the
main reasons the theory is usable: it lets one move back and forth between
triangulated and abelian viewpoints.

## Why D-branes show up

The definition did not come out of nowhere. Bridgeland explicitly frames the
paper as a mathematical response to Michael Douglas's work on D-branes and
`Pi`-stability in string theory. In that story, BPS branes on a Calabi-Yau are
expected to be organized by a derived category, while physical stability should
depend on a central charge and vary continuously in moduli. Bridgeland's paper
takes that insight and turns it into a precise piece of homological algebra.

The paper is therefore motivated by physics, but mathematically it is mostly
about the main structural results around slicings, hearts, deformation
estimates, and the topology of the space of stability conditions itself.

## The Local-Homeomorphism Statements

The headline result of the 2007 paper is Theorem 1.2. For each connected
component `Sigma` of the space `Stab(D)` of locally finite stability
conditions, the central charge map is a local homeomorphism

`Z : Sigma -> V(Sigma) subset Hom_Z(K(D), C)`.

So `Stab(D)` is not just a set of structures: locally, each connected component
looks like a linear space of possible central charges.

> For each connected component `Σ ⊂ Stab(D)` there are a linear subspace
> `V(Σ) ⊂ Hom_Z(K(D), C)`, with a well-defined linear topology, and a local
> homeomorphism `Z : Σ → V(Σ)` which maps a stability condition `(Z, P)` to
> its central charge `Z`.

In the current formalization, this paper statement is packaged as the proposition-object
`CategoryTheory.Triangulated.StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents` in
`BridgelandStability/StabilityCondition/Topology.lean`:

```lean
def StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents : Prop :=
  ∀ (cc : ConnectedComponents (StabilityCondition C)),
    ∃ (V : Submodule ℂ (K₀ C →+ ℂ))
      (_ : NormedAddCommGroup V)
      (_ : NormedSpace ℂ V)
      (hZ : ∀ σ : StabilityCondition C,
        ConnectedComponents.mk σ = cc → σ.Z ∈ V),
      @IsLocalHomeomorph
        {σ : StabilityCondition C // ConnectedComponents.mk σ = cc}
        V inferInstance inferInstance
        (fun ⟨σ, hσ⟩ ↦ ⟨σ.Z, hZ σ hσ⟩)
```

The corresponding proof term is assembled in
`BridgelandStability/StabilityCondition/LocalHomeomorphism.lean` as
`StabilityCondition.centralChargeIsLocalHomeomorphOnConnectedComponents`.

Under the hood, the current architecture is class-map-first: the foundational
generic proposition-object is
`CategoryTheory.Triangulated.StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents`,
defined in `BridgelandStability/StabilityCondition/Topology.lean` for a class
map `v : K₀(D) → Λ`. The ordinary theorem above is the explicit `v = id`
wrapper, kept as the paper-facing statement for `Stab(D)`.

Corollary 1.3 is the numerically finite version. In the current Lean code,
the hypothesis `NumericallyFinite k C` means that the numerical Grothendieck
group is finitely generated. Under that hypothesis, for the canonical numerical quotient

`N(D) = K(D) / K(D)^perp`,

the space `Stab_N(D)` of numerical stability conditions has connected
components that are finite-dimensional complex manifolds, with local charts
again given by the central charge map into `Hom_Z(N(D), C)`.

That is the formal geometric payoff of the paper: the stability condition
itself is a point in a manifold, and wall-crossing can be studied by moving in
that manifold.

> Suppose `D` is numerically finite. For each connected component
> `Σ ⊂ Stab_N(D)` there are a subspace `V(Σ) ⊂ Hom_Z(N(D), C)` and a local
> homeomorphism `Z : Σ → V(Σ)` which maps a stability condition to its central
> charge `Z`. In particular `Σ` is a finite-dimensional complex manifold.

The corresponding numerical local-homeomorphism statement is currently formalized as
`CategoryTheory.Triangulated.NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents`
in `BridgelandStability/EulerForm/Basic.lean`:

```lean
abbrev NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents
    [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k] : Prop :=
  StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents
    (C := C) (Λ := NumericalK₀ k C) (v := numericalQuotientMap k C)
```

The corresponding generic and numerical complex-manifold theorems live in
`BridgelandStability/NumericalStabilityManifold.lean`:

```lean
theorem StabilityCondition.WithClassMap.existsComplexManifoldOnConnectedComponent
    {Λ : Type u'} [AddCommGroup Λ] [AddGroup.FG Λ]
    {v : K₀ C →+ Λ} (hv : Function.Surjective v)
    (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (StabilityCondition.WithClassMap.Component C v cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (StabilityCondition.WithClassMap.Component C v cc)

theorem NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent
    [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    [NumericallyFinite k C]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (NumericalComponent (k := k) C cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (NumericalComponent (k := k) C cc)
```

The generic manifold theorem is proved for a surjective class map
`v : K₀ C →+ Λ` with finitely generated class lattice `Λ`. The numerical
theorem is the specialization to the canonical quotient map
`K₀ C →+ NumericalK₀ k C`.

## Techniques from the paper

Bridgeland's construction is powerful because it combines several ideas that
are individually classical but unusually effective together:

- Harder-Narasimhan theory on hearts of bounded t-structures;
- slicings `P(phi)` as a continuous analogue of the discrete cohomological
  truncation data coming from t-structures;
- locally finite interval categories `P((a,b))`, which control exactness and
  finiteness in short phase windows;
- a generalized metric on slicings, measuring how far the phases of objects can
  move;
- a seminorm on central charges, which lets one compare nearby stability
  conditions quantitatively;
- a deformation theorem proving local injectivity and local surjectivity of the
  central charge map.

From a formalization perspective, this is exactly the kind of paper that is
both attractive and painful: the definitions are clean, but the proof depends
on many layers of category theory, homological algebra, topology, and careful
control of coercions between them.

## Why the theory matters now

Bridgeland's original paper has turned into infrastructure for several major
parts of modern geometry and mathematical physics.

- It gives new invariants of triangulated categories via their spaces of
  stability conditions, and already in the original paper the elliptic curve
  case is computed explicitly.
- It led to the detailed study of stability manifolds for K3 surfaces, where a
  distinguished connected component can be described very concretely.
- It became a basic tool for moduli spaces of complexes and for wall-crossing
  in birational geometry. In particular, Bayer and Macri showed that varying a
  Bridgeland stability condition produces nef divisors on moduli spaces and
  gives a systematic link between wall-crossing and the minimal model program.
- In Calabi-Yau 3 settings, stability conditions feed directly into
  Donaldson-Thomas and BPS counting theories, where wall-crossing formulas
  measure how semistable objects change across walls in the stability manifold.
- In another direction, spaces of stability conditions have been identified with
  moduli spaces of quadratic differentials in important classes of examples,
  tying the theory to cluster structures, exact WKB, and mirror-symmetry
  phenomena.

This repository is aimed at the foundation under those applications: if the
basic manifold and deformation story is formalized well, a lot of later
geometry becomes more approachable.

## Project charter

This is an experiment in AI-assisted formalization. Humans write no Lean code
beyond Mathlib; the goal is to study how far a human-led effort can push
AI-assisted formalization on top of Mathlib. Getting Lean to accept a proof
script is not success — the end state has to be Mathlib quality: correct
abstractions, reusable lemmas, sane names, controlled imports, and proofs that
could plausibly survive code review and upstreaming.

## What is formalized

The current codebase formalizes Sections 5-7 of the paper, culminating in
Theorem 1.2 (local homeomorphism) and Corollary 1.3 (complex manifold structure
on numerical stability conditions). The main layers are:

- Stability functions, phases, semistability, HN filtrations, and uniqueness.
- Slicings, phase arithmetic, extension-closure, and the passage between
  slicings and t-structures.
- Ordinary and class-map stability conditions, the Bridgeland topology, the
  seminorm machinery, and the deformation theorem (Section 7).
- The heart-equivalence and interval-category exactness infrastructure used in
  the deformation argument.
- The numerical quotient `NumericalK₀`, the specialization to Euler-form
  stability conditions, and the complex manifold assembly for connected
  components.

The root import is [`BridgelandStability.lean`](BridgelandStability.lean).
This is an active formalization project; some files expose reusable APIs, others
still need the cleanup and renaming that Mathlib would require.

Corollary 1.3 is set up for independent verification via
[`leanprover/comparator`](https://github.com/leanprover/comparator). The
**63 project declarations** that the formal statement depends on are documented
with their paper-level counterparts in
[`artifacts/trusted-formalization-base.md`](artifacts/trusted-formalization-base.md).

## Selected References

This is a deliberately compressed and non-exhaustive list of papers and a small
number of recent preprints: the original motivation, the foundational theorem,
some geometric applications, and recent threefold developments.

1. Michael R. Douglas,
   [D-branes, Categories and N=1 Supersymmetry](https://arxiv.org/abs/hep-th/0011017),
   J. Math. Phys. 42 (2001), 2818-2843.
2. Tom Bridgeland,
   [Stability conditions on triangulated categories](https://annals.math.princeton.edu/2007/166-2/p01),
   Annals of Mathematics 166 (2007), 317-345.
3. Tom Bridgeland,
   [Stability conditions on K3 surfaces](https://ora.ox.ac.uk/objects/uuid:577d12a4-1dd8-497b-af5d-bc52623a2ac1),
   Duke Mathematical Journal 141 (2008), 241-291.
4. Daniele Arcara and Aaron Bertram,
   [Bridgeland-stable moduli spaces for K-trivial surfaces](https://ems.press/journals/jems/articles/4662),
   Journal of the European Mathematical Society 15 (2013), 1-38.
5. Arend Bayer and Emanuele Macri,
   [Projectivity and birational geometry of Bridgeland moduli spaces](https://www.ams.org/jams/2014-27-03/S0894-0347-2014-00790-6/),
   Journal of the American Mathematical Society 27 (2014), 707-752.
6. Arend Bayer and Emanuele Macri,
   [MMP for moduli of sheaves on K3s via wall-crossing: nef and movable cones, Lagrangian fibrations](https://doi.org/10.1007/s00222-014-0501-8),
   Inventiones mathematicae 198 (2014), 505-590.
7. Tom Bridgeland and Ivan Smith,
   [Quadratic differentials as stability conditions](https://link.springer.com/article/10.1007/s10240-014-0066-5),
   Publications mathematiques de l'IHES 121 (2015), 155-278.
8. Marcello Bernardara, Emanuele Macri, Benjamin Schmidt, Xiaolei Zhao,
   [Bridgeland Stability Conditions on Fano Threefolds](https://epiga.episciences.org/3255),
   EpiGA 1 (2017), article 8.
9. Chunyi Li,
   [On stability conditions for the quintic threefold](https://link.springer.com/article/10.1007/s00222-019-00888-z),
   Inventiones mathematicae 218 (2019), 301-340.
10. Arend Bayer, Marti Lahoz, Emanuele Macri, Howard Nuer, Alexander Perry, Paolo Stellari,
   [Stability conditions in families](https://link.springer.com/article/10.1007/s10240-021-00124-6),
   Publications mathematiques de l'IHES 133 (2021), 157-325.
11. Soheyla Feyzbakhsh and Richard P. Thomas,
    [Rank r DT theory from rank 1](https://www.ams.org/jams/2023-36-03/S0894-0347-2023-00922-5/),
    Journal of the American Mathematical Society 36 (2023), 795-826.
12. Soheyla Feyzbakhsh and Richard P. Thomas,
    [Rank r DT theory from rank 0](https://projecteuclid.org/journals/duke-mathematical-journal/volume-173/issue-11/Rank-r-DT-theory-from-rank-0/10.1215/00127094-2023-0085.short),
    Duke Mathematical Journal 173 (2024), 2063-2116.
13. Soheyla Feyzbakhsh, Naoki Koseki, Zhiyu Liu, Nick Rekuski,
    [Stability conditions on Calabi-Yau threefolds via Brill-Noether theory of curves](https://arxiv.org/abs/2509.24990),
    preprint, 2025.
