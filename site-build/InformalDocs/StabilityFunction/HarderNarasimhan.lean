import BridgelandStability.StabilityFunction.HarderNarasimhan
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityFunction: HarderNarasimhan" =>
%%%
htmlSplit := .never
%%%

# AbelianHNFiltration

**\[Definition 2.3\]** HN filtration for abelian categories

A Harder--Narasimhan filtration of a nonzero object $`E` in an abelian category with respect to a stability function $`Z` is a finite chain of subobjects $`0 = E_0 < E_1 < \cdots < E_n = E` (with $`n \ge 1`) such that the successive quotients $`E_i / E_{i-1}` are semistable with strictly decreasing phases $`\phi_1 > \phi_2 > \cdots > \phi_n`.

Construction: The structure carries the number of factors `n`, the strictly monotone chain `chain : Fin (n+1) \to Subobject E` with `chain(0) = \bot` and `chain(n) = \top`, the phase sequence `\phi : Fin n \to \mathbb{R}` which is `StrictAnti`, and proofs that each successive cokernel is semistable with the prescribed phase.


{docstring CategoryTheory.AbelianHNFiltration}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20AbelianHNFiltration&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.AbelianHNFiltration%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%202.3%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# HasHNProperty

**\[Definition 2.3\]** HN property predicate

A stability function $`Z` has the Harder--Narasimhan property if every nonzero object admits an HN filtration (Bridgeland, Proposition 2.4).

Construction: Defined as the universal statement: for all nonzero $`E`, the type `AbelianHNFiltration Z E` is nonempty.


{docstring CategoryTheory.StabilityFunction.HasHNProperty}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20HasHNProperty&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.HasHNProperty%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%202.3%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hasHN\_of\_finiteLength

Proposition 2.4 (Bridgeland). If every object of $`\mathcal{A}` has a finite subobject lattice, then any stability function on $`\mathcal{A}` has the Harder--Narasimhan property.

Proof: Induction on $`|\operatorname{Sub}(E)|`. If $`E` is semistable, it is its own single-factor HN filtration. Otherwise, find the maximally destabilizing subobject $`M` (max-phase, semistable by `maxPhase_isSemistable`), recurse on $`E/M` (which has strictly fewer subobjects by `card_subobject_cokernel_lt`), and concatenate the result with $`M` as the first factor.

{docstring CategoryTheory.StabilityFunction.hasHN_of_finiteLength}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hasHN_of_finiteLength&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.hasHN_of_finiteLength%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Zobj\_pullback\_eq\_add

$`Z`-additivity for the pullback short exact sequence: $`Z(p^*(B)) = Z(M') + Z(B)` where $`p = \operatorname{coker.\pi}(M')`.

Proof: Apply $`Z`-additivity to the short exact sequence $`M' \hookrightarrow p^*(B) \twoheadrightarrow B`.

{docstring CategoryTheory.Zobj_pullback_eq_add}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20Zobj_pullback_eq_add&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Zobj_pullback_eq_add%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# card\_subobject\_cokernel\_lt

Cardinality decrease. For a nonzero subobject $`M` of $`E` with $`\operatorname{Sub}(E)` finite, $`|\operatorname{Sub}(\operatorname{coker} M)| < |\operatorname{Sub}(E)|`.

Proof: The pullback $`p^* \colon \operatorname{Sub}(\operatorname{coker} M) \hookrightarrow \operatorname{Sub}(E)` is injective but $`M` is not in its image (since every pullback subobject is $`\ge M \ne \bot`), giving the strict inequality.

{docstring CategoryTheory.card_subobject_cokernel_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20card_subobject_cokernel_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.card_subobject_cokernel_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cokernelPullbackIso

The cokernel of consecutive pulled-back subobjects is isomorphic to the original cokernel factor.

Construction: Constructed by showing the natural map between the cokernels is both mono (via a $`Z`-value kernel argument) and epi (since the pullback morphism is epi), hence an isomorphism.


{docstring CategoryTheory.cokernelPullbackIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernelPullbackIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.cokernelPullbackIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cokernelPullbackTopIso

The quotient $`E / p^*(B)` (where $`p = \operatorname{coker.\pi}(M)` and $`B \ne \top`) is canonically isomorphic to $`\operatorname{coker}(B)`.

Construction: Constructed by composing three cokernel isomorphisms: normalizing the arrow via `ofLE`, applying `cokernelPullbackIso`, and unnormalizing.


{docstring CategoryTheory.cokernelPullbackTopIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernelPullbackTopIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.cokernelPullbackTopIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cokernel\_nonzero\_of\_ne\_top

If $`M \ne \top` as a subobject of $`E`, then $`\operatorname{coker}(M.\mathrm{arrow})` is nonzero.

Proof: If the cokernel were zero, $`M.\mathrm{arrow}` would be epi, hence an isomorphism (being also mono), forcing $`M = \top`.

{docstring CategoryTheory.cokernel_nonzero_of_ne_top}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernel_nonzero_of_ne_top&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.cokernel_nonzero_of_ne_top%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_maxPhase\_maximal\_subobject

Among all nonzero subobjects with maximal phase, there exists one that is also maximal in the subobject partial order. Every subobject strictly above it has strictly lower phase.

Proof: First find $`M_0` with maximal phase, then take the largest element (in the subobject order) among those with phase equal to $`\phi(M_0)`. Finiteness ensures this maximum exists.

{docstring CategoryTheory.exists_maxPhase_maximal_subobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_maxPhase_maximal_subobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.exists_maxPhase_maximal_subobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_semistable\_quotient\_le\_phase\_of\_artinian\_noetherian

Every nonzero Artinian--Noetherian object admits a nonzero semistable quotient whose phase is at most the phase of the object.

Proof: Recursive construction: if $`E` is semistable, take the identity. Otherwise find a destabilizing semistable subobject $`A'`, pass to $`E/A'` (which has $`\phi(E/A') < \phi(E)`), and recurse. Termination uses `WellFoundedGT` on the subobject lattice.

{docstring CategoryTheory.exists_semistable_quotient_le_phase_of_artinian_noetherian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_semistable_quotient_le_phase_of_artinian_noetherian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.exists_semistable_quotient_le_phase_of_artinian_noetherian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_zero\_of\_semistable\_phase\_gt

Hom-vanishing. If $`E` is semistable with $`\phi(E) > \phi(F)` and $`F` is semistable, then every morphism $`f \colon E \to F` is zero.

Proof: If $`f \ne 0`, the image $`\operatorname{im}(f)` is nonzero. By `phase_le_of_epi`, $`\phi(E) \le \phi(\operatorname{im} f)`, and by semistability of $`F`, $`\phi(\operatorname{im} f) \le \phi(F)`. This gives $`\phi(E) \le \phi(F)`, contradicting $`\phi(E) > \phi(F)`.

{docstring CategoryTheory.hom_zero_of_semistable_phase_gt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_zero_of_semistable_phase_gt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.hom_zero_of_semistable_phase_gt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isArtinianObject\_of\_epi

Quotients of Artinian objects are Artinian.

Proof: Dual of `isNoetherianObject_of_epi`: pull back a descending chain in $`\operatorname{Sub}(Y)` along the epi $`p` to get a descending chain in $`\operatorname{Sub}(X)^{\mathrm{op}}`, which stabilizes by the Artinian condition.

{docstring CategoryTheory.isArtinianObject_of_epi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isArtinianObject_of_epi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isArtinianObject_of_epi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isNoetherianObject\_of\_epi

Quotients of Noetherian objects are Noetherian.

Proof: Given an ascending chain in $`\operatorname{Sub}(Y)`, pull it back along $`p` to an ascending chain in $`\operatorname{Sub}(X)`. The pulled-back chain stabilizes by Noetherianity of $`X`, and injectivity of $`p^*` forces the original chain to stabilize.

{docstring CategoryTheory.isNoetherianObject_of_epi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isNoetherianObject_of_epi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isNoetherianObject_of_epi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isSemistable\_cokernel\_ofLE\_congr

Semistability transfer when `ofLE` subobject arguments are propositionally equal.

Proof: By substitution.

{docstring CategoryTheory.isSemistable_cokernel_ofLE_congr}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isSemistable_cokernel_ofLE_congr&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isSemistable_cokernel_ofLE_congr%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# le\_pullback\_cokernel

For any subobject $`B` of $`\operatorname{coker}(M')`, the pullback satisfies $`M' \le p^*(B)` where $`p = \operatorname{coker.\pi}(M')`.

Proof: By `pullback_cokernel_bot_eq`, $`p^*(\bot) = M'`, and $`\bot \le B` implies $`p^*(\bot) \le p^*(B)` by monotonicity.

{docstring CategoryTheory.le_pullback_cokernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20le_pullback_cokernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.le_pullback_cokernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_cokernel\_le\_of\_destabilizing\_semistable\_subobject

If $`A'` is a semistable subobject of $`E` with $`\phi(E) < \phi(A')` and $`A' \ne \top`, then $`\phi(\operatorname{coker} A') \le \phi(E)`.

Proof: From the short exact sequence $`A' \hookrightarrow E \twoheadrightarrow E/A'` and the phase see-saw lower bound: $`\min(\phi(A'), \phi(E/A')) \le \phi(E)`. Since $`\phi(A') > \phi(E)`, the minimum must be $`\phi(E/A')`.

{docstring CategoryTheory.phase_cokernel_le_of_destabilizing_semistable_subobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_cokernel_le_of_destabilizing_semistable_subobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.phase_cokernel_le_of_destabilizing_semistable_subobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_cokernel\_lt\_of\_destabilizing\_semistable\_subobject

In the same situation, the quotient has strictly smaller phase: $`\phi(\operatorname{coker} A') < \phi(E)`.

Proof: Uses the strict version of the arg-addition inequality: when the two summands have distinct arguments, the inequality $`\min(\arg z_1, \arg z_2) < \arg(z_1+z_2)` is strict. The arguments are distinct because equality would force $`\phi(A') \le \phi(E)`, contradicting the destabilizing hypothesis.

{docstring CategoryTheory.phase_cokernel_lt_of_destabilizing_semistable_subobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_cokernel_lt_of_destabilizing_semistable_subobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.phase_cokernel_lt_of_destabilizing_semistable_subobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_cokernel\_ofLE\_congr

Phase equality when the `ofLE` subobject arguments are propositionally equal: if $`A_1 = A_2` and $`B_1 = B_2` then $`\phi(\operatorname{coker}(A_1 \hookrightarrow B_1)) = \phi(\operatorname{coker}(A_2 \hookrightarrow B_2))`.

Proof: By substitution.

{docstring CategoryTheory.phase_cokernel_ofLE_congr}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_cokernel_ofLE_congr&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.phase_cokernel_ofLE_congr%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_cokernel\_pullback\_eq

The cokernel of consecutive pulled-back subobjects has the same phase as the original cokernel factor: $`\phi(\operatorname{coker}(p^*(A') \hookrightarrow p^*(B'))) = \phi(\operatorname{coker}(A' \hookrightarrow B'))`.

Proof: Follows from the $`Z`-value equality `Zobj_cokernel_pullback_eq` and the definition of phase in terms of $`\arg`.

{docstring CategoryTheory.phase_cokernel_pullback_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_cokernel_pullback_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.phase_cokernel_pullback_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_le\_of\_epi

For a semistable object $`E`, every nonzero epi quotient $`E \twoheadrightarrow Q` satisfies $`\phi(E) \le \phi(Q)`.

Proof: The kernel $`K` of $`p` has $`\phi(K) \le \phi(E)` by semistability. If $`\phi(Q) < \phi(E)`, the phase see-saw upper bound gives $`\phi(E) \le \max(\phi(K), \phi(Q)) < \phi(E)`, a contradiction.

{docstring CategoryTheory.phase_le_of_epi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_le_of_epi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.phase_le_of_epi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# pullback\_cokernel\_bot\_eq

The pullback of $`\bot` along $`\operatorname{coker.\pi}(M)` equals $`M` as a subobject of $`E`.

Proof: The pullback of $`\bot` consists of elements mapping to $`0` in the cokernel, which is exactly the kernel of $`\operatorname{coker.\pi}(M)`, i.e.\ $`M` itself.

{docstring CategoryTheory.pullback_cokernel_bot_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20pullback_cokernel_bot_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.pullback_cokernel_bot_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# pullback\_obj\_injective\_of\_epi

For an epimorphism $`p \colon X \twoheadrightarrow Y` in an abelian category, the pullback functor $`p^* \colon \operatorname{Sub}(Y) \to \operatorname{Sub}(X)` is injective on objects.

Proof: Two subobjects $`B_1, B_2` of $`Y` with $`p^*(B_1) = p^*(B_2)` have the same image subobject after precomposing with $`p`. Since $`p` is epi, precomposition does not change the image, so $`B_1 = B_2`.

{docstring CategoryTheory.pullback_obj_injective_of_epi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20pullback_obj_injective_of_epi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.pullback_obj_injective_of_epi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.HarderNarasimhan%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
