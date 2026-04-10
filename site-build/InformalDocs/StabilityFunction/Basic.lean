import BridgelandStability.StabilityFunction.Basic
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityFunction: Basic" =>
%%%
htmlSplit := .never
%%%

# StabilityFunction

**\[Definition 2.1\]**

A stability function on an abelian category $`\mathcal{A}` is a group homomorphism $`Z \colon K_0(\mathcal{A}) \to \mathbb{C}` (here modelled as an object-level map $`Z \colon \operatorname{Ob}(\mathcal{A}) \to \mathbb{C}`) satisfying: (i) $`Z(E) = 0` whenever $`E` is a zero object, (ii) $`Z(B) = Z(A) + Z(C)` for every short exact sequence $`0 \to A \to B \to C \to 0`, and (iii) for every nonzero object $`E`, $`Z(E)` lies in the semi-closed upper half plane $`H \cup \mathbb{R}_{<0} = \{z \in \mathbb{C} \mid \operatorname{Im}(z) > 0\} \cup \{z \in \mathbb{C} \mid \operatorname{Im}(z) = 0,\; \operatorname{Re}(z) < 0\}`. This is Definition 2.1 of Bridgeland (2007).

Construction: The structure carries an object-level function `Zobj : A \to \mathbb{C}` together with proofs of vanishing on zero objects, additivity on short exact sequences (encoded via `ShortComplex.ShortExact`), and the upper-half-plane membership condition for nonzero objects.


{docstring CategoryTheory.StabilityFunction}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20StabilityFunction&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%202.1%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsSemistable

**\[Definition 2.2\]**

An object $`E` of an abelian category is semistable with respect to a stability function $`Z` if $`E` is nonzero and for every nonzero subobject $`B \hookrightarrow E`, $`\phi(B) \le \phi(E)` (Bridgeland, Definition 2.2).

Construction: A conjunction of `\neg \operatorname{IsZero} E` and the universal bound on phases of nonzero subobjects in the `Subobject E` lattice.


{docstring CategoryTheory.StabilityFunction.IsSemistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsSemistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.IsSemistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%202.2%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsStable

An object $`E` is stable if it is nonzero and every nonzero proper subobject $`B \hookrightarrow E` with $`B \ne \top` satisfies $`\phi(B) < \phi(E)`.

Construction: A conjunction of `\neg \operatorname{IsZero} E` and the strict phase bound on nonzero subobjects that are not $`\top`.


{docstring CategoryTheory.StabilityFunction.IsStable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsStable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.IsStable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cokernelBotIso

The cokernel of `ofLE \bot S h` is isomorphic to $`(S : A)`.

Construction: Since `ofLE \bot S h = 0`, the cokernel of zero is the target, giving $`\operatorname{coker}(0 \to S) \cong S`.


{docstring CategoryTheory.StabilityFunction.Subobject.cokernelBotIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernelBotIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.Subobject.cokernelBotIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ofLE\_bot

The morphism `ofLE \bot S h` is the zero morphism, since $`\bot` is a zero object.

Proof: The source is isomorphic to the zero object via `botCoeIsoZero`.

{docstring CategoryTheory.StabilityFunction.Subobject.ofLE_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ofLE_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.Subobject.ofLE_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Zobj\_eq\_of\_iso

$`Z` sends isomorphic objects to the same value: $`E \cong F \implies Z(E) = Z(F)`.

Proof: Use additivity on the short exact sequence $`0 \to E \xrightarrow{\sim} F \to 0`, noting the cokernel of an isomorphism is zero, so $`Z(F) = Z(E) + 0`.

{docstring CategoryTheory.StabilityFunction.Zobj_eq_of_iso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20Zobj_eq_of_iso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.Zobj_eq_of_iso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_destabilizing\_of\_not\_semistable

A nonzero object that is not semistable admits a destabilizing subobject: a nonzero subobject $`B \hookrightarrow E` with $`\phi(B) > \phi(E)`.

Proof: Unfold the negation of the semistability predicate and extract the witness.

{docstring CategoryTheory.StabilityFunction.exists_destabilizing_of_not_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_destabilizing_of_not_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.exists_destabilizing_of_not_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_maxPhase\_subobject

Among all nonzero subobjects of a nonzero object with a finite subobject lattice, there exists one with maximal phase.

Proof: The set of nonzero subobjects is nonempty (contains $`\top`) and finite, so the phase function attains its maximum.

{docstring CategoryTheory.StabilityFunction.exists_maxPhase_subobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_maxPhase_subobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.exists_maxPhase_subobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_semistable\_subobject\_ge\_phase\_of\_artinian

In an Artinian object, every nonzero subobject contains a semistable subobject of at least the same phase. This is the first chain-condition step in Bridgeland's Proposition 2.4.

Proof: Well-founded induction on the subobject lattice (using the Artinian condition). If a subobject $`B` is not semistable, extract a destabilizing subobject $`D`, lift it to $`E`, and recurse. Termination is guaranteed by the strictly descending chain.

{docstring CategoryTheory.StabilityFunction.exists_semistable_subobject_ge_phase_of_artinian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_semistable_subobject_ge_phase_of_artinian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.exists_semistable_subobject_ge_phase_of_artinian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_semistable\_subobject\_gt\_phase\_of\_not\_semistable

In a non-semistable Artinian object, there exists a semistable subobject with strictly larger phase than $`E`.

Proof: Combine `exists_destabilizing_of_not_semistable` to get a destabilizing subobject, then apply `exists_semistable_subobject_ge_phase_of_artinian` to refine it to a semistable one.

{docstring CategoryTheory.StabilityFunction.exists_semistable_subobject_gt_phase_of_not_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_semistable_subobject_gt_phase_of_not_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.exists_semistable_subobject_gt_phase_of_not_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isSemistable\_of\_iso

Semistability is invariant under isomorphisms: if $`X \cong Y` and $`X` is semistable, then $`Y` is semistable.

Proof: Transport the phase bound on subobjects of $`X` to subobjects of $`Y` via the isomorphism, using `phase_eq_of_iso` to compare phases.

{docstring CategoryTheory.StabilityFunction.isSemistable_of_iso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isSemistable_of_iso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.isSemistable_of_iso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# liftSub

Given a subobject $`B` of $`E` and a subobject $`C` of $`(B : A)`, the lifted subobject `liftSub B C` is the subobject of $`E` obtained by composing the inclusion arrows $`C \hookrightarrow B \hookrightarrow E`.

Construction: Defined as `Subobject.mk (C.arrow \gg B.arrow)`.


{docstring CategoryTheory.StabilityFunction.liftSub}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20liftSub&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.liftSub%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# liftSub\_bot

Lifting $`\bot` gives $`\bot`: $`\operatorname{liftSub}(B, \bot) = \bot`.

Proof: The composition involves the zero arrow from $`\bot`.

{docstring CategoryTheory.StabilityFunction.liftSub_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20liftSub_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.liftSub_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# liftSub\_le

The lifted subobject satisfies $`\operatorname{liftSub}(B, C) \le B`.

Proof: The inclusion $`C \to B \to E` factors through $`B`.

{docstring CategoryTheory.StabilityFunction.liftSub_le}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20liftSub_le&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.liftSub_le%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# liftSub\_ne\_bot

Lifting a nonzero subobject gives a nonzero subobject.

Proof: If the lift were $`\bot`, the underlying object would be zero, contradicting non-zeroness of $`C` via the canonical isomorphism.

{docstring CategoryTheory.StabilityFunction.liftSub_ne_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20liftSub_ne_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.liftSub_ne_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# maxPhase\_isSemistable

A subobject $`M` with maximal phase among all nonzero subobjects of $`E` is semistable as an object.

Proof: Any destabilizing subobject of $`(M : A)` lifts to a nonzero subobject of $`E` with higher phase via `liftSub`, contradicting the maximality of $`M`.

{docstring CategoryTheory.StabilityFunction.maxPhase_isSemistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20maxPhase_isSemistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.maxPhase_isSemistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# maxPhase\_ne\_top\_of\_not\_semistable

When $`E` is not semistable, the max-phase subobject $`M` satisfies $`M \ne \top`. Since $`\phi(\top) = \phi(E)` and $`\phi(M) > \phi(E)`, we have $`M \ne \top`.

Proof: If $`M = \top`, then $`M` being semistable would make $`E` semistable via the isomorphism $`\top \cong E`, contradicting the hypothesis.

{docstring CategoryTheory.StabilityFunction.maxPhase_ne_top_of_not_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20maxPhase_ne_top_of_not_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.maxPhase_ne_top_of_not_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# min\_phase\_le\_of\_shortExact

Phase see-saw (lower bound). For a short exact sequence $`0 \to A \to B \to C \to 0` with $`A, C` nonzero, $`\min(\phi(A), \phi(C)) \le \phi(B)`.

Proof: Dual of the upper bound: $`\min(\arg z_1, \arg z_2) \le \arg(z_1 + z_2)` applied to $`Z(B) = Z(A) + Z(C)`.

{docstring CategoryTheory.StabilityFunction.min_phase_le_of_shortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20min_phase_le_of_shortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.min_phase_le_of_shortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase

The phase of an object $`E` with respect to a stability function $`Z` is $`\phi(E) = \frac{1}{\pi} \arg Z(E)`. When $`E` is nonzero, $`Z(E)` lies in $`H \cup \mathbb{R}_{<0}`, so $`\arg Z(E) \in (0, \pi]` and hence $`\phi(E) \in (0, 1]`. For a zero object, the phase is $`0`.

Construction: Defined as `(1 / Real.pi) * arg (Z.Zobj E)`, using the standard branch of the complex argument.


{docstring CategoryTheory.StabilityFunction.phase}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phase%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_eq\_of\_iso

Phase is invariant under isomorphisms: $`E \cong F \implies \phi(E) = \phi(F)`.

Proof: Immediate from `Zobj_eq_of_iso`.

{docstring CategoryTheory.StabilityFunction.phase_eq_of_iso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_eq_of_iso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phase_eq_of_iso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_le\_max\_of\_shortExact

Phase see-saw (upper bound). For a short exact sequence $`0 \to A \to B \to C \to 0` with $`A, C` nonzero, $`\phi(B) \le \max(\phi(A), \phi(C))`.

Proof: From $`Z(B) = Z(A) + Z(C)` and the convexity bound $`\arg(z_1 + z_2) \le \max(\arg z_1, \arg z_2)` for vectors in the upper half plane.

{docstring CategoryTheory.StabilityFunction.phase_le_max_of_shortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_le_max_of_shortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phase_le_max_of_shortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_le\_one

The phase of any object satisfies $`\phi(E) \le 1`.

Proof: Since $`\arg(z) \le \pi` for all $`z \in \mathbb{C}`, dividing by $`\pi` gives $`\phi(E) \le 1`.

{docstring CategoryTheory.StabilityFunction.phase_le_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_le_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phase_le_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_liftSub

The phase of the lifted subobject equals the phase of $`C`: $`\phi(\operatorname{liftSub}(B, C)) = \phi(C)`.

Proof: The underlying objects are isomorphic via the canonical isomorphism from `Subobject.underlyingIso`.

{docstring CategoryTheory.StabilityFunction.phase_liftSub}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_liftSub&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phase_liftSub%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_mem\_Ioc

For a nonzero object $`E`, $`\phi(E) \in (0, 1]`.

Proof: Combines `phase_pos` and `phase_le_one`.

{docstring CategoryTheory.StabilityFunction.phase_mem_Ioc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_mem_Ioc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phase_mem_Ioc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_pos

For a nonzero object $`E`, the phase $`\phi(E)` is strictly positive.

Proof: Since $`Z(E) \in H \cup \mathbb{R}_{<0}`, we have $`\arg Z(E) > 0`, so $`\phi(E) = \frac{1}{\pi} \arg Z(E) > 0`.

{docstring CategoryTheory.StabilityFunction.phase_pos}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_pos&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phase_pos%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shortExact\_of\_mono

For any monomorphism $`f \colon X \hookrightarrow Y` in an abelian category, the short complex $`X \xrightarrow{f} Y \to \operatorname{coker} f` is short exact.

Proof: Combine exactness at $`Y` (from `ShortComplex.exact_cokernel`) with the mono and epi conditions.

{docstring CategoryTheory.StabilityFunction.shortExact_of_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shortExact_of_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.shortExact_of_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# simple\_isSemistable

A simple object is semistable: its only nonzero subobject is $`\top \cong E` itself, so the phase condition $`\phi(B) \le \phi(E)` holds trivially.

Proof: By simplicity the subobject lattice is simple order, so every nonzero subobject equals $`\top`, and the phase bound becomes an equality.

{docstring CategoryTheory.StabilityFunction.simple_isSemistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20simple_isSemistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.simple_isSemistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# subobject\_isZero\_iff\_eq\_bot

A subobject $`B` of $`E` is zero if and only if $`B = \bot` in the subobject lattice.

Proof: Forward: if the underlying object is zero, the arrow is zero, hence `mk` is $`\bot`. Backward: $`\bot` is isomorphic to the zero object.

{docstring CategoryTheory.StabilityFunction.subobject_isZero_iff_eq_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20subobject_isZero_iff_eq_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.subobject_isZero_iff_eq_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# subobject\_ne\_bot\_of\_not\_isZero

A nonzero subobject is not $`\bot`.

Proof: Contrapositive of the forward direction of `subobject_isZero_iff_eq_bot`.

{docstring CategoryTheory.StabilityFunction.subobject_ne_bot_of_not_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20subobject_ne_bot_of_not_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.subobject_ne_bot_of_not_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# subobject\_not\_isZero\_of\_ne\_bot

A subobject that is not $`\bot` is nonzero.

Proof: Contrapositive of the backward direction of `subobject_isZero_iff_eq_bot`.

{docstring CategoryTheory.StabilityFunction.subobject_not_isZero_of_ne_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20subobject_not_isZero_of_ne_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.subobject_not_isZero_of_ne_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# subobject\_top\_ne\_bot\_of\_not\_isZero

For a nonzero object $`E`, $`\top \ne \bot` in the subobject lattice of $`E`.

Proof: If $`\top = \bot` then $`\top` is zero, so $`E \cong (\top : \operatorname{Sub} E)` is zero, contradicting the hypothesis.

{docstring CategoryTheory.StabilityFunction.subobject_top_ne_bot_of_not_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20subobject_top_ne_bot_of_not_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.subobject_top_ne_bot_of_not_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
