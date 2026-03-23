# BridgelandStability

This repository is an experimental AI-assisted formalization of the main
results of Tom
Bridgeland's paper
[Stability conditions on triangulated categories](https://annals.math.princeton.edu/2007/166-2/p01)
in Lean 4 using Mathlib.

The mathematical target is the deformation-theoretic core of the paper:
the topology on `Stab(D)`, the local-homeomorphism theorem for the central
charge, and the consequent complex manifold structure on the space of
numerically finite stability conditions. The engineering target is stricter:
this should eventually become Mathlib-quality code, not just code that happens
to compile once.

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

## The main theorem and Corollary 1.3

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

In the current formalization, this paper statement is packaged as the proposition
`CategoryTheory.Triangulated.StabilityCondition.centralCharge_isLocalHomeomorph_onConnectedComponents` in
`BridgelandStability/StabilityCondition/Topology.lean`:

```lean
def StabilityCondition.centralCharge_isLocalHomeomorph_onConnectedComponents : Prop :=
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
`StabilityCondition.centralCharge_isLocalHomeomorph_onConnectedComponents'`.

Corollary 1.3 is the numerically finite version. When the Euler form on `K(D)`
has finite-rank numerical quotient

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

The numerical topological statement is formalized as
`CategoryTheory.Triangulated.bridgelandCorollary_1_3` in
`BridgelandStability/EulerForm.lean`:

```lean
def bridgelandCorollary_1_3 [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] : Prop :=
  let χ := eulerForm k C
  NumericallyFinite C χ →
    ∀ (cc : ConnectedComponents (NumericalStabilityCondition C χ)),
      ∃ (V : Submodule ℂ (NumericalK₀ C χ →+ ℂ))
        (_ : NormedAddCommGroup V)
        (_ : NormedSpace ℂ V)
        (hZ : ∀ σ : NumericalStabilityCondition C χ,
          ConnectedComponents.mk σ = cc →
            σ.factors.choose ∈ V),
        @IsLocalHomeomorph
          {σ : NumericalStabilityCondition C χ //
            ConnectedComponents.mk σ = cc}
          V inferInstance inferInstance
          (fun ⟨σ, hσ⟩ ↦ ⟨σ.factors.choose, hZ σ hσ⟩)
```

The numerical package is now split across three files. The generic quotient
infrastructure lives in `BridgelandStability/NumericalStability.lean`: the
object-level Euler form, the radical, `NumericalK₀`, `NumericallyFinite`, and
`NumericalStabilityCondition`. The concrete descent of the Euler form to `K₀`
and the Corollary 1.3 local-homeomorphism statement live in
`BridgelandStability/EulerForm.lean`. The consequent complex-manifold packaging
lives separately in `BridgelandStability/NumericalStabilityManifold.lean`,
whose theorem `bridgelandCorollary_1_3_complexManifold` builds the
`ChartedSpace` and `IsManifold` structures for numerical connected components.

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

## What is formalized in this repository

The current codebase formalizes a large part of the paper-level infrastructure.
The root file [`BridgelandStability.lean`](BridgelandStability.lean) is now an
umbrella import over the actual module tree. The main pieces are:

- [`BridgelandStability/StabilityFunction/Basic.lean`](BridgelandStability/StabilityFunction/Basic.lean),
  [`BridgelandStability/StabilityFunction/HarderNarasimhan.lean`](BridgelandStability/StabilityFunction/HarderNarasimhan.lean),
  [`BridgelandStability/StabilityFunction/MDQ.lean`](BridgelandStability/StabilityFunction/MDQ.lean),
  and [`BridgelandStability/StabilityFunction/Uniqueness.lean`](BridgelandStability/StabilityFunction/Uniqueness.lean):
  stability functions, phases, semistability, HN filtrations, maximal
  destabilizing quotients, and uniqueness.
- [`BridgelandStability/Slicing/*.lean`](BridgelandStability/Slicing):
  slicings, phase arithmetic, extension-closure properties, HN operations, and
  the passage between slicings and t-structures.
- [`BridgelandStability/StabilityCondition/Basic.lean`](BridgelandStability/StabilityCondition/Basic.lean),
  [`BridgelandStability/StabilityCondition/ConnectedComponent.lean`](BridgelandStability/StabilityCondition/ConnectedComponent.lean),
  [`BridgelandStability/StabilityCondition/Deformation.lean`](BridgelandStability/StabilityCondition/Deformation.lean),
  [`BridgelandStability/StabilityCondition/Seminorm.lean`](BridgelandStability/StabilityCondition/Seminorm.lean),
  [`BridgelandStability/StabilityCondition/Topology.lean`](BridgelandStability/StabilityCondition/Topology.lean),
  and [`BridgelandStability/StabilityCondition/LocalHomeomorphism.lean`](BridgelandStability/StabilityCondition/LocalHomeomorphism.lean):
  stability conditions, the Bridgeland topology, the seminorm machinery, and
  the connected-component and deformation glue, and the componentwise local
  linear model behind Theorem 1.2.
- [`BridgelandStability/Deformation/*.lean`](BridgelandStability/Deformation),
  culminating in [`BridgelandStability/Deformation/Theorem.lean`](BridgelandStability/Deformation/Theorem.lean):
  the Section 7 deformation package, including deformed slicings, phase
  control, HN existence, hom-vanishing, maximal destabilizing quotients, and
  the proof of the deformation theorem.
- [`BridgelandStability/HeartEquivalence/*.lean`](BridgelandStability/HeartEquivalence)
  and [`BridgelandStability/IntervalCategory/*.lean`](BridgelandStability/IntervalCategory):
  the bridge between slicings and hearts, and the interval-category exactness
  infrastructure used in the deformation argument.
- [`BridgelandStability/NumericalStability.lean`](BridgelandStability/NumericalStability.lean),
  [`BridgelandStability/EulerForm.lean`](BridgelandStability/EulerForm.lean),
  and [`BridgelandStability/NumericalStabilityManifold.lean`](BridgelandStability/NumericalStabilityManifold.lean):
  the generic numerical quotient infrastructure (`eulerFormObj`,
  `NumericalK₀`, `NumericallyFinite`, `NumericalStabilityCondition`), the
  concrete descent of the Euler form to `K₀` together with Corollary 1.3 as a
  local-homeomorphism statement, and the separate complex manifold assembly
  for numerical connected components.

The code should be read as an active formalization project, not as a polished
final library. Some files already expose reusable APIs; others still need the
cleanup, consolidation, and renaming that Mathlib would require.

## Project charter

This is an experiment in AI-assisted formalization.

**Rule 1: Humans write no Lean code beyond Mathlib.** The current toolchain is
`claude-code` with Opus 4.6 and `codex` with GPT-5.4 plus FRO Lean skills. The
goal is not to replace human mathematical judgment, but to study how far a
human-led effort can push AI-assisted formalization on top of Mathlib.

**Rule 2: Getting Lean to accept a proof script is not success.** The end state has
to be Mathlib quality: correct abstractions, reusable lemmas, sane names,
controlled imports, documentation, and proofs that could plausibly survive code
review and upstreaming. If we do not reach that bar, the project has failed.

That standard is intentional. A one-off formalization would be easy to
overvalue. The real question is whether AI can help produce library-quality
mathematics in a modern proof assistant on top of Mathlib, with as little
special pleading as possible.

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
