import BridgelandStability.StabilityCondition.Topology
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityCondition: Topology" =>
%%%
htmlSplit := .never
%%%

# P\_of\_Q\_of\_P\_semistable

Lemma 6.4 for $`\mathcal{P}`-semistable objects. If $`\sigma.Z = \tau.Z`, $`d(\mathcal{P}, \mathcal{Q}) < 1`, $`E` is nonzero and $`\tau`-semistable at $`\phi`, and $`E` is also $`\sigma`-semistable at some phase $`c`, then $`c = \phi` and $`E \in \mathcal{P}(\phi)`.

Proof: Combines the metric phase bound $`|c - \phi| < 2` with `phase_eq_of_same_Z` to force $`c = \phi`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_of_Q_of_P_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_of_Q_of_P_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_of_Q_of_P_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# false\_of\_all\_hn\_phases\_above

One-sided phase impossibility (above). Symmetric version: all nonzero HN factors have phase strictly above $`\phi` (and below $`\phi + 1`) leads to contradiction.

Proof: Identical structure to the below case: each divided term has strictly positive imaginary part via $`\sin(\pi(\theta_i - \phi)) > 0`, contradicting the real LHS.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_all_hn_phases_above}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20false_of_all_hn_phases_above&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_all_hn_phases_above%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# false\_of\_all\_hn\_phases\_below

One-sided phase impossibility (below). If $`\sigma` and $`\tau` have the same central charge, $`E` is nonzero and $`\tau`-semistable of phase $`\phi`, and all nonzero factors in a $`\sigma`-HN filtration of $`E` have phase strictly below $`\phi` (and above $`\phi - 1`), then we reach a contradiction. This is the core imaginary-part argument underlying Lemma 6.4.

Proof: Decomposes $`Z(E) = \sum Z(F_i)` via $`K_0` additivity, divides by $`e^{i\pi\phi}`, and shows the imaginary part is both zero (since $`Z(E)` lies on the ray at angle $`\pi\phi`) and strictly negative (each nonzero factor contributes $`b_i \sin(\pi(\theta_i - \phi)) < 0`).

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_all_hn_phases_below}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20false_of_all_hn_phases_below&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_all_hn_phases_below%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# false\_of\_gt\_and\_le\_phases

Cross-slicing imaginary part contradiction. If $`\sigma.Z = \tau.Z`, $`X` is nonzero, all $`\sigma`-HN phases of $`X` lie in $`(\phi, \phi + 1)`, and all $`\tau`-HN phases lie in $`(\phi - 1, \phi]`, then $`\mathsf{False}`. From the $`\sigma`-decomposition, $`\operatorname{Im}(Z(X)/e^{i\pi\phi}) > 0`; from the $`\tau`-decomposition, $`\operatorname{Im}(Z(X)/e^{i\pi\phi}) \leq 0`.

Proof: Decomposes $`Z(X)` via both $`\sigma`- and $`\tau`-HN filtrations and shows the imaginary part of $`Z(X) \cdot e^{-i\pi\phi}` is simultaneously strictly positive (from the $`\sigma`-sum) and nonpositive (from the $`\tau`-sum).

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_gt_and_le_phases}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20false_of_gt_and_le_phases&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_gt_and_le_phases%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# false\_of\_hn\_phases\_le\_with\_lt

One-sided phase impossibility (below with equality). If all $`\sigma`-HN phases are $`\leq \phi` with at least one nonzero factor strictly below $`\phi`, and $`E` is $`\tau`-semistable at $`\phi` with the same central charge, then $`\mathsf{False}`.

Proof: The terms with phase $`= \phi` contribute zero imaginary part; the term with phase $`< \phi` contributes strictly negative imaginary part. The sum is strictly negative, contradicting the real LHS.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_hn_phases_le_with_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20false_of_hn_phases_le_with_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_hn_phases_le_with_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_le\_le\_phiPlus

Phase straddling for Lemma 6.4. If $`\sigma.Z = \tau.Z`, $`d(\mathcal{P}, \mathcal{Q}) < 1`, and $`E` is nonzero $`\tau`-semistable at $`\phi`, then $`\phi^-_\sigma(E) \leq \phi \leq \phi^+_\sigma(E)`. This pins $`\phi` between the extreme $`\sigma`-HN phases of $`E`.

Proof: Each direction proceeds by contradiction: if $`\phi < \phi^-`, all HN phases are above $`\phi`, contradicting `false_of_all_hn_phases_above`; if $`\phi^+ < \phi`, all are below, contradicting `false_of_all_hn_phases_below`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.phiMinus_le_le_phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_le_le_phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.phiMinus_le_le_phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# bridgeland\_lemma\_6\_4

Bridgeland's Lemma 6.4. If two stability conditions $`\sigma` and $`\tau` have the same central charge and $`d(\mathcal{P}, \mathcal{Q}) < 1`, then their slicings agree on all phases: $`\mathcal{P}(\phi) = \mathcal{Q}(\phi)` for all $`\phi \in \mathbb{R}`. In particular, the central charge map $`\sigma \mapsto Z(\sigma)` is locally injective on $`\operatorname{Stab}(\mathcal{D})`.

Proof: The biconditional is proved by applying the one-direction argument (`bridgeland_6_4_one_dir`) twice. The one-direction proof for $`E \in \mathcal{Q}(\phi) \Rightarrow E \in \mathcal{P}(\phi)` proceeds in four steps: (1) split $`E` at the cutoff $`\phi` using $`\sigma`'s t-structure; (2) show $`\tau.\phi^+(X) \leq \phi` by hom-vanishing; (3) conclude $`X = 0` via the cross-slicing imaginary part argument; (4) transfer semistability from $`Y \cong E` using the imaginary part argument to force all phases equal to $`\phi`.

{docstring CategoryTheory.Triangulated.bridgeland_lemma_6_4}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20bridgeland_lemma_6_4&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.bridgeland_lemma_6_4%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gt\_phases\_of\_gtProp

For a nonzero object with $`\mathcal{P}(>\phi)` property, the intrinsic minimum HN phase satisfies $`\phi^-(X) > \phi`.

Proof: Uses the characterization of $`\mathcal{P}(>\phi)` in terms of a filtration whose minimum phase exceeds $`\phi`, then compares with the canonical HN filtration.

{docstring CategoryTheory.Triangulated.gt_phases_of_gtProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gt_phases_of_gtProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.gt_phases_of_gtProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_divided\_of\_semistable

For a $`\sigma`-semistable nonzero object $`F` of phase $`\psi`, the imaginary part of $`Z(F) \cdot e^{-i\pi\phi}` equals $`b \cdot \sin(\pi(\psi - \phi))` for some $`b > 0`. This factors out the repeated divide-by-exponential-and-rewrite-to-sine computation used throughout the Lemma 6.4 proofs.

Proof: Obtains the ray decomposition $`Z([F]) = b \cdot e^{i\pi\psi}` from compatibility, then applies `im_ofReal_mul_exp_mul_exp_neg`.

{docstring CategoryTheory.Triangulated.im_divided_of_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_divided_of_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_divided_of_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_le\_of\_leProp

For a nonzero object with $`\mathcal{P}(\leq \phi)` property, the intrinsic maximum HN phase satisfies $`\phi^+(Y) \leq \phi`.

Proof: Dual to `gt_phases_of_gtProp`, using the $`\phi^+` characterization.

{docstring CategoryTheory.Triangulated.phiPlus_le_of_leProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_le_of_leProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phiPlus_le_of_leProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Topology%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
