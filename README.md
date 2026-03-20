# BridgelandStability

This repository is an experimental AI-assisted formalization of parts of Tom
Bridgeland's paper
[Stability conditions on triangulated categories](https://annals.math.princeton.edu/2007/166-2/p01)
in Lean 4 and mathlib.

The mathematical target is the deformation-theoretic core of the paper:
the topology on `Stab(D)`, the local-homeomorphism theorem for the central
charge, and the numerical finite-dimensional corollary. The engineering target
is stricter: this should eventually become mathlib-quality code, not just code
that happens to compile once.

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
takes that heuristic and turns it into a precise piece of homological algebra.

The paper is therefore motivated by physics, but mathematically it is mostly
about the internal geometry of triangulated categories: slicings, hearts,
interval subcategories, deformation estimates, and the topology of the space of
stability conditions itself.

## The main theorem and Corollary 1.3

The headline result of the 2007 paper is Theorem 1.2. For each connected
component `Sigma` of the space `Stab(D)` of locally finite stability
conditions, the central charge map is a local homeomorphism

`Z : Sigma -> V(Sigma) subset Hom_Z(K(D), C)`.

So `Stab(D)` is not just a set of structures: locally, each connected component
looks like a linear space of possible central charges.

Corollary 1.3 is the numerically finite version. When the Euler form on `K(D)`
has finite-rank numerical quotient

`N(D) = K(D) / K(D)^perp`,

the space `Stab_N(D)` of numerical stability conditions has connected
components that are finite-dimensional complex manifolds, with local charts
again given by the central charge map into `Hom_Z(N(D), C)`.

That is the formal geometric payoff of the paper: the stability condition
itself is a point in a manifold, and wall-crossing can be studied by moving in
that manifold.

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

This is still an active subject, not just a finished 2007 story. Recent papers
include new existence results for normal surfaces (Langer, 2023/2024), current
survey notes on stability spaces in representation theory (Barbieri, 2024),
new work connecting Bridgeland-Smith type correspondences to
Donaldson-Thomas invariants (Kidwai-Williams, 2024), new wall-crossing results
for higher-rank DT/PT theory (Jardim-Lo-Maciocia-Martinez, 2025), and even new
results about the metric geometry of stability spaces themselves (Fan, 2024/2025).

This repository is aimed at the foundation under those applications: if the
basic manifold and deformation story is formalized well, a lot of later
geometry becomes more approachable.

## What is formalized in this repository

The current codebase formalizes a large part of the paper-level infrastructure.
The most important files are:

- [`BridgelandStability/StabilityFunction.lean`](BridgelandStability/StabilityFunction.lean):
  stability functions on abelian categories, phases, semistability, and
  Harder-Narasimhan filtrations.
- [`BridgelandStability/Slicing.lean`](BridgelandStability/Slicing.lean):
  slicings, HN data, phase bounds, interval predicates, and the passage to
  t-structures.
- [`BridgelandStability/StabilityCondition.lean`](BridgelandStability/StabilityCondition.lean):
  Bridgeland stability conditions, the topology on `Stab(D)`, the seminorm
  machinery, and the paper-style statement of Theorem 1.2.
- [`BridgelandStability/Deformation/*.lean`](BridgelandStability/Deformation):
  the local deformation infrastructure behind Bridgeland's Section 7 proof.
- [`BridgelandStability/DeformationTheorem.lean`](BridgelandStability/DeformationTheorem.lean):
  componentwise local-homeomorphism machinery and the proof package for
  Theorem 1.2.
- [`BridgelandStability/NumericalStability.lean`](BridgelandStability/NumericalStability.lean):
  Euler forms, numerical Grothendieck groups, numerical stability conditions,
  and a paper-style statement of Corollary 1.3.
- [`BridgelandStability/NumericalStabilityManifold.lean`](BridgelandStability/NumericalStabilityManifold.lean):
  finite-dimensional packaging of the numerical charge space and a complex
  manifold theorem for numerical connected components.

The code should be read as an active formalization project, not as a polished
final library. Some files already expose reusable APIs; others still need the
cleanup, consolidation, and renaming that mathlib would require.

## Project charter

This is an experiment in AI-assisted auto-formalization.

Rule 1: no human proof code outside mathlib.

Rule 2: getting Lean to accept a proof script is not success. The end state has
to be mathlib quality: correct abstractions, reusable lemmas, sane names,
controlled imports, documentation, and proofs that could plausibly survive code
review and upstreaming. If we do not reach that bar, the project has failed.

That standard is intentional. A one-off formalization would be easy to
overvalue. The real question is whether AI can help produce library-quality
mathematics in a modern proof assistant on top of mathlib, with as little
special pleading as possible.

## References

### Foundations

1. Tom Bridgeland,
   [Stability conditions on triangulated categories](https://annals.math.princeton.edu/2007/166-2/p01),
   Annals of Mathematics 166 (2007), 317-345.
2. Michael R. Douglas,
   [D-branes, Categories and N=1 Supersymmetry](https://arxiv.org/abs/hep-th/0011017),
   J. Math. Phys. 42 (2001), 2818-2843.
3. Michael R. Douglas,
   [Dirichlet branes, homological mirror symmetry, and stability](https://arxiv.org/abs/math/0207021),
   ICM 2002 proceedings.
4. Tom Bridgeland,
   [Stability conditions on K3 surfaces](https://arxiv.org/abs/math/0307164).
5. Arend Bayer and Emanuele Macri,
   [Projectivity and Birational Geometry of Bridgeland moduli spaces](https://arxiv.org/abs/1203.4613).
6. Maxim Kontsevich and Yan Soibelman,
   [Stability structures, motivic Donaldson-Thomas invariants and cluster transformations](https://arxiv.org/abs/0811.2435).
7. Tom Bridgeland and Ivan Smith,
   [Quadratic differentials as stability conditions](https://arxiv.org/abs/1302.7030).

### More Recent Directions

8. Anna Barbieri,
   [Spaces of Bridgeland stability conditions in representation theory](https://arxiv.org/abs/2409.15131),
   survey article, 2024.
9. Adrian Langer,
   [Bridgeland stability conditions on normal surfaces](https://arxiv.org/abs/2310.04761),
   Ann. Mat. Pura Appl. 203 (2024), 2653-2664.
10. Omar Kidwai and Nicholas J. Williams,
    [Donaldson-Thomas invariants for the Bridgeland-Smith correspondence](https://arxiv.org/abs/2401.10093),
    2024.
11. Howard Nuer,
    [Stability conditions on some families of Calabi-Yau threefolds via orbifolding](https://arxiv.org/abs/2501.06207),
    2025.
12. Marcos Jardim, Jason Lo, Antony Maciocia, Cristian Martinez,
    [Higher rank DT/PT wall-crossing in Bridgeland stability](https://arxiv.org/abs/2503.20008),
    2025.
13. Yu-Wei Fan,
    [A space of stability conditions that is not a length space](https://arxiv.org/abs/2412.04777),
    2024/2025.
