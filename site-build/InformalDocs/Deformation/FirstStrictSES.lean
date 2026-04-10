import BridgelandStability.Deformation.FirstStrictSES
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: FirstStrictSES" =>
%%%
htmlSplit := .never
%%%

# exists\_first\_strictShortExact\_of\_not\_semistable

Bridgeland's first strict short exact sequence in a thin category: if an interval object $`X` is not $`W`-semistable, there is a proper strict subobject $`M` of maximal $`W`-phase with $`M` semistable, $`\psi(M) > \psi(X)`, and the inclusion gives a strict SES $`0 \to M \to X \to X/M \to 0`. The finite-length input is finiteness of the strict-subobject set, not an ambient $`\operatorname{Finite}(\operatorname{Subobject}(X))` statement.

Proof: Select a maximal-phase maximal strict subobject $`M` from the finite set. Verify $`M \ne \top` (by `maxPhase_strictSubobject_ne_top_of_not_semistable`), semistability (by `semistable_of_maxPhase_strictSubobject`), the phase gap (by `phase_gt_of_maxPhase_strictSubobject_of_not_semistable`), and the strict SES (by `interval_strictShortExact_cokernel_of_strictMono`).

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_first_strictShortExact_of_not_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FirstStrictSES%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_first\_strictShortExact\_of\_not\_semistable\_of\_strictArtinian

Strict-Artinian descent for the first strict short exact sequence (Bridgeland \S7): given a non-$`W`-semistable interval object $`X` that is strict-Artinian, there exists a proper strict subobject $`M` with $`M \ne \bot`, $`M \ne \top`, $`\psi(M) > \psi(X)`, $`M` is $`W`-semistable, and the inclusion $`M \hookrightarrow X` gives a strict short exact sequence $`0 \to M \to X \to X/M \to 0`.

Proof: Well-founded induction on the strict-subobject lattice. At each step, find a strict subobject of larger phase than the current object. If it is semistable, stop; otherwise, descend to a smaller strict subobject via the existence of a phase-raising destabilizing strict subobject. The descent terminates by the well-foundedness of the strict-subobject partial order.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable_of_strictArtinian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_first_strictShortExact_of_not_semistable_of_strictArtinian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable_of_strictArtinian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FirstStrictSES%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# maxPhase\_strictSubobject\_ne\_top\_of\_not\_semistable

In a non-$`W`-semistable interval object $`X`, a maximal-phase strict subobject $`M` cannot be $`\top`. If it were, then $`M \cong X` via the subobject arrow, and the semistability of $`M` (from maximal-phase selection) would transfer to $`X`, contradicting the non-semistability assumption.

Proof: Assume $`M = \top`. Then $`M \cong X` via the subobject isomorphism, and `semistable_of_iso` transports the semistability of $`M` (established by `semistable_of_maxPhase_strictSubobject`) to $`X`, yielding a contradiction.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.maxPhase_strictSubobject_ne_top_of_not_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20maxPhase_strictSubobject_ne_top_of_not_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.maxPhase_strictSubobject_ne_top_of_not_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FirstStrictSES%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_gt\_of\_maxPhase\_strictSubobject\_of\_not\_semistable

In a non-$`W`-semistable interval object $`X`, a maximal-phase strict subobject $`M` has $`W`-phase strictly larger than that of $`X`: $`\psi(X) < \psi(M)`. If not, the phase ordering on all strict subobjects combined with the semistable characterization would force $`X` itself to be semistable.

Proof: By contradiction: if $`\psi(M) \le \psi(X)`, then every nonzero strict subobject $`K \hookrightarrow X` (appearing in a distinguished triangle) has $`\psi(K) \le \psi(M) \le \psi(X)`, which is exactly the triangle inequality characterizing semistability of $`X`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.phase_gt_of_maxPhase_strictSubobject_of_not_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_gt_of_maxPhase_strictSubobject_of_not_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.phase_gt_of_maxPhase_strictSubobject_of_not_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FirstStrictSES%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_iso

If $`E` is $`W`-semistable of phase $`\psi` and $`E \cong E'`, then $`E'` is also $`W`-semistable of phase $`\psi`. Semistability is an isomorphism-invariant property: the interval membership, nonzero condition, $`K_0`-class, and triangle inequality all transport across the isomorphism.

Proof: Each clause of the semistability predicate is transferred through the isomorphism: interval membership by `prop_of_iso`, nonzero by `Iso.isZero_iff`, $`W`-phase equality by `cl\_iso`, and the triangle test by rotating the distinguished triangle through the isomorphism.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_of_iso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_iso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_of_iso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FirstStrictSES%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# finite\_strictSubobjects\_of\_finite\_leftHeartSubobjects

Finiteness of subobjects in the left-heart image of an interval object implies finiteness of the set of nonzero strict subobjects in the thin interval category. This provides the local finite-length input for the first strict short exact sequence.

Proof: The functor to the left heart preserves strict monomorphisms as monomorphisms, so there is an injection from strict subobjects of $`X` in the interval category to subobjects of $`FL(X)` in the left heart. Finiteness of the target implies finiteness of the source.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.finite_strictSubobjects_of_finite_leftHeartSubobjects}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20finite_strictSubobjects_of_finite_leftHeartSubobjects&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.finite_strictSubobjects_of_finite_leftHeartSubobjects%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FirstStrictSES%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
