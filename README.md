# BridgelandStability

AI-assisted formalization in Lean 4 / Mathlib of the main results of
Bridgeland's
[Stability conditions on triangulated categories](https://annals.math.princeton.edu/2007/166-2/p01)
(Annals of Mathematics, 2007).

## What Bridgeland stability conditions are

Inspired by Douglas's work on Π-stability in string theory, Bridgeland
showed that the classical stability package — central charges, semistable
objects, Harder-Narasimhan filtrations — can be lifted from abelian categories
to triangulated categories. A Bridgeland stability condition on a triangulated
category `D` consists of a central charge `Z : K₀(D) → ℂ` and a slicing
`P(φ)` into semistable objects of each phase, subject to compatibility and
Harder-Narasimhan existence axioms.

The headline result is that the space `Stab(D)` of all such conditions is
itself a complex manifold, with local charts given by the central charge.
The theory has since become one of the most active areas in modern
mathematics. It provides infrastructure for wall-crossing in birational
geometry, Donaldson-Thomas theory, and the study of moduli spaces of sheaves
on surfaces and threefolds.

## Main results

The formalization covers Sections 2–7 of the paper, culminating in:

- **Theorem 1.2** — the central charge map is a local homeomorphism on each
  connected component of `Stab(D)`.
- **Corollary 1.3** — connected components of `Stab_N(D)` are
  finite-dimensional complex manifolds.

Both are proved for an arbitrary surjective class map `v : K₀(D) →+ Λ` and
specialized to the identity (Theorem 1.2) and the numerical quotient
(Corollary 1.3). The formalization works in class-map generality as in
Bayer–Macrì–Stellari [8, Appendix A] and Bayer–Lahoz–Macrì–Nuer–Perry–Stellari
[11], where the central charge factors through a surjection `v : K₀(D) →+ Λ`;
the classical `Stab(D)` is the specialization `v = id`.

## Documentation

- [**Project website**](https://mattrobball.github.io/BridgelandStability/) —
  informal mathematical descriptions of each declaration, with a table of
  paper statements that currently have exact formal analogs.
- [**API docs**](https://mattrobball.github.io/BridgelandStability/api/) —
  auto-generated Lean API documentation (doc-gen4).
- [**Comparator Manual**](https://mattrobball.github.io/BridgelandStability/comparator/) —
  independent verification of the formal statements against their source,
  listing the trusted base you must audit to trust the proof.

The root import is [`BridgelandStability.lean`](BridgelandStability.lean).

## Project charter

This is an experiment in AI-assisted formalization.

**Rule 1: Humans write no Lean code beyond Mathlib.** The goal is to study how
far a human-led effort can push AI-assisted formalization on top of Mathlib.

**Rule 2: Getting Lean to accept a proof script is not success.** The end state
has to be Mathlib quality: correct abstractions, reusable lemmas, sane names,
controlled imports, and proofs that could plausibly survive code review and
upstreaming.

## Selected references

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
5. Arend Bayer and Emanuele Macrì,
   [Projectivity and birational geometry of Bridgeland moduli spaces](https://www.ams.org/jams/2014-27-03/S0894-0347-2014-00790-6/),
   Journal of the American Mathematical Society 27 (2014), 707-752.
6. Arend Bayer and Emanuele Macrì,
   [MMP for moduli of sheaves on K3s via wall-crossing: nef and movable cones, Lagrangian fibrations](https://doi.org/10.1007/s00222-014-0501-8),
   Inventiones mathematicae 198 (2014), 505-590.
7. Tom Bridgeland and Ivan Smith,
   [Quadratic differentials as stability conditions](https://link.springer.com/article/10.1007/s10240-014-0066-5),
   Publications mathematiques de l'IHES 121 (2015), 155-278.
8. Arend Bayer, Emanuele Macrì, and Paolo Stellari,
   [The space of stability conditions on abelian threefolds, and on some Calabi-Yau threefolds](https://doi.org/10.1007/s00222-016-0665-5),
   Inventiones mathematicae 206 (2016), 869-933.
9. Marcello Bernardara, Emanuele Macrì, Benjamin Schmidt, Xiaolei Zhao,
   [Bridgeland Stability Conditions on Fano Threefolds](https://epiga.episciences.org/3255),
   EpiGA 1 (2017), article 8.
10. Chunyi Li,
    [On stability conditions for the quintic threefold](https://link.springer.com/article/10.1007/s00222-019-00888-z),
    Inventiones mathematicae 218 (2019), 301-340.
11. Arend Bayer, Martí Lahoz, Emanuele Macrì, Howard Nuer, Alexander Perry, Paolo Stellari,
    [Stability conditions in families](https://link.springer.com/article/10.1007/s10240-021-00124-6),
    Publications mathematiques de l'IHES 133 (2021), 157-325.
12. Soheyla Feyzbakhsh and Richard P. Thomas,
    [Rank r DT theory from rank 1](https://www.ams.org/jams/2023-36-03/S0894-0347-2023-00922-5/),
    Journal of the American Mathematical Society 36 (2023), 795-826.
13. Soheyla Feyzbakhsh and Richard P. Thomas,
    [Rank r DT theory from rank 0](https://projecteuclid.org/journals/duke-mathematical-journal/volume-173/issue-11/Rank-r-DT-theory-from-rank-0/10.1215/00127094-2023-0085.short),
    Duke Mathematical Journal 173 (2024), 2063-2116.
14. Soheyla Feyzbakhsh, Naoki Koseki, Zhiyu Liu, Nick Rekuski,
    [Stability conditions on Calabi-Yau threefolds via Brill-Noether theory of curves](https://arxiv.org/abs/2509.24990),
    preprint, 2025.
15. Arend Bayer,
    [A short proof of the deformation property of Bridgeland stability conditions](https://arxiv.org/abs/1606.02169),
    preprint, 2016.
16. Chunyi Li,
    [A Remark on Stability Conditions on Smooth Projective Varieties](https://arxiv.org/abs/2601.22994),
    preprint, 2026.
