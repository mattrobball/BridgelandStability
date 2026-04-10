import BridgelandStability.StabilityCondition.Deformation
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityCondition: Deformation" =>
%%%
htmlSplit := .never
%%%

# eq\_of\_same\_Z\_near

**\[Lemma 6.4\]**

Lemma 6.4 consequence: two stability conditions with the same central charge and $`d(\mathcal{P}, \mathcal{Q}) < 1` are equal.

Proof: Applies `bridgeland_lemma_6_4` to conclude $`\mathcal{P} = \mathcal{Q}`, then uses extensionality with $`Z_\sigma = Z_\tau`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.eq_of_same_Z_near}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eq_of_same_Z_near&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.eq_of_same_Z_near%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Lemma%206.4%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eq\_of\_same\_Z\_of\_mem\_basisNhd

Two stability conditions in the same $`B_\varepsilon(\sigma)` with the same central charge are equal.

Proof: Triangle inequality on slicing distances gives $`d(\mathcal{P}_1, \mathcal{P}_2) < 2\varepsilon < 1`, then applies `eq_of_same_Z_near`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.eq_of_same_Z_of_mem_basisNhd}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eq_of_same_Z_of_mem_basisNhd&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.eq_of_same_Z_of_mem_basisNhd%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_epsilon0\_tenth

Every stability condition admits a local $`\varepsilon_0 < 1/10` witness for Theorem 7.1, obtained by halving the standard `exists_epsilon0` witness.

Proof: Takes the standard $`\varepsilon_1 < 1/8` from `exists_epsilon0` and sets $`\varepsilon_0 = \varepsilon_1/2`, applying `wideSectorFiniteLength_mono`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_epsilon0_tenth}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_epsilon0_tenth&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_epsilon0_tenth%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_eq\_Z\_and\_mem\_basisNhd\_of\_stabSeminorm\_lt\_sin

Theorem 7.1 (local surjectivity). A small deformation of the central charge lifts to a stability condition inside $`B_\varepsilon(\sigma)`: if $`\|W - Z(\sigma)\|_\sigma < \sin(\pi\varepsilon)` and the wide-sector finite length condition holds, then there exists $`\tau` with $`\tau.Z = W` and $`\tau \in B_\varepsilon(\sigma)`.

Proof: Invokes the deformation theorem to obtain $`\tau` with $`\tau.Z = W` and controlled slicing distance, then verifies both the seminorm and distance conditions for membership in $`B_\varepsilon(\sigma)`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# basisNhd\_mono

Shrinking the radius shrinks the neighborhood: if $`\delta \leq \varepsilon < 1/8`, then $`B_\delta(\sigma) \subseteq B_\varepsilon(\sigma)`.

Proof: Both the $`\sin(\pi\delta) \leq \sin(\pi\varepsilon)` bound and $`\delta \leq \varepsilon` are monotone.

{docstring CategoryTheory.Triangulated.basisNhd_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20basisNhd_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.basisNhd_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# basisNhd\_self

A basis neighborhood contains its center: $`\sigma \in B_\varepsilon(\sigma)`.

Proof: The charge difference is zero (seminorm zero), and the slicing distance is zero.

{docstring CategoryTheory.Triangulated.basisNhd_self}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20basisNhd_self&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.basisNhd_self%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# basisNhd\_subset\_connectedComponent\_small

A small Bridgeland basis neighborhood (with radius below the local Theorem 7.1 witness) lies inside the connected component of its center. This is the direct straight-line interpolation argument from Bridgeland Section 7.

Proof: Constructs a continuous path $`\gamma \colon [0, 1] \to \operatorname{Stab}` from $`\sigma` to $`\tau` by lifting the straight-line charge interpolation $`Z_t = (1-t) Z(\sigma) + t Z(\tau)` via repeated application of Theorem 7.1. Continuity of $`\gamma` follows from the local lifting: for each $`t`, nearby times lift to nearby stability conditions via the same deformation theorem. The path connects $`\sigma` and $`\tau`, placing them in the same path component.

{docstring CategoryTheory.Triangulated.basisNhd_subset_connectedComponent_small}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20basisNhd_subset_connectedComponent_small&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.basisNhd_subset_connectedComponent_small%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_basisNhd\_subset\_basisNhd

If $`\tau \in B_\varepsilon(\sigma)`, then some smaller basis neighborhood of $`\tau` is contained in $`B_\varepsilon(\sigma)`. This is the local basis-refinement step.

Proof: Chooses $`\delta` small enough that $`K \cdot \sin(\pi\delta)` absorbs the gap in both the seminorm and slicing distance bounds, using the local domination constant and the triangle inequality.

{docstring CategoryTheory.Triangulated.exists_basisNhd_subset_basisNhd}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_basisNhd_subset_basisNhd&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_basisNhd_subset_basisNhd%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_local\_lift\_sameComponent\_in\_basisNhd

Local continuation along the straight-line charge interpolation. Starting from a lifted point $`\rho_0` over time $`t`, nearby times also admit lifts inside the same ambient basis neighborhood and in the same connected component as $`\rho_0`.

Proof: Chooses $`\eta` small enough that $`|s - t| < \eta` implies the seminorm $`\|Z_s - Z(\rho_0)\|_{\rho_0} < \sin(\pi\delta)` (using the scaling property of the seminorm), then applies Theorem 7.1 at $`\rho_0` and verifies the lifted point lies in both the ambient basis neighborhood (by monotonicity) and the correct connected component (by `basisNhd_subset_connectedComponent_small`).

{docstring CategoryTheory.Triangulated.exists_local_lift_sameComponent_in_basisNhd}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_local_lift_sameComponent_in_basisNhd&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_local_lift_sameComponent_in_basisNhd%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# linearInterpolationZ

The affine interpolation between the central charges of $`\sigma` and $`\tau`: $`Z_t = Z(\sigma) + t \cdot (Z(\tau) - Z(\sigma))` for $`t \in \mathbb{R}`.

Construction: Defined as $`\sigma.Z + t \cdot (\tau.Z - \sigma.Z)` using scalar multiplication on additive group homomorphisms.


{docstring CategoryTheory.Triangulated.linearInterpolationZ}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20linearInterpolationZ&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.linearInterpolationZ%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# linearInterpolationZ\_one

$`Z_1 = Z(\tau)`: the interpolation at $`t = 1` recovers the target charge.

Proof: Immediate from $`\sigma.Z + 1 \cdot (\tau.Z - \sigma.Z) = \tau.Z`.

{docstring CategoryTheory.Triangulated.linearInterpolationZ_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20linearInterpolationZ_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.linearInterpolationZ_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# linearInterpolationZ\_sub

$`Z_t - Z(\sigma) = t \cdot (Z(\tau) - Z(\sigma))`.

Proof: Direct computation from the definition of the interpolation.

{docstring CategoryTheory.Triangulated.linearInterpolationZ_sub}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20linearInterpolationZ_sub&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.linearInterpolationZ_sub%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# linearInterpolationZ\_sub\_sub

$`Z_t - Z_s = (t - s) \cdot (Z(\tau) - Z(\sigma))`.

Proof: Subtracts the two interpolation formulas and simplifies.

{docstring CategoryTheory.Triangulated.linearInterpolationZ_sub_sub}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20linearInterpolationZ_sub_sub&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.linearInterpolationZ_sub_sub%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# linearInterpolationZ\_zero

$`Z_0 = Z(\sigma)`: the interpolation at $`t = 0` recovers the initial charge.

Proof: Immediate from $`0 \cdot (\tau.Z - \sigma.Z) = 0`.

{docstring CategoryTheory.Triangulated.linearInterpolationZ_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20linearInterpolationZ_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.linearInterpolationZ_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_add\_le

The Bridgeland seminorm satisfies the triangle inequality: $`\|U + V\|_\sigma \leq \|U\|_\sigma + \|V\|_\sigma`.

Proof: For each semistable object, $`\|(U + V)([E])\| / \|Z([E])\| \leq \|U([E])\| / \|Z([E])\| + \|V([E])\| / \|Z([E])\|` by the norm triangle inequality, then takes the supremum.

{docstring CategoryTheory.Triangulated.stabSeminorm_add_le}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_add_le&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_add_le%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_center\_dominates\_of\_basisNhd

Local forward domination. If $`\tau \in B_\varepsilon(\sigma)`, then $`\|U\|_\tau \leq K \cdot \|U\|_\sigma` for some finite $`K`.

Proof: Direct application of the explicit seminorm comparison `stabSeminorm_le_of_near` with the constant $`K = 1 / (\cos(\pi\varepsilon) - M_Z)`.

{docstring CategoryTheory.Triangulated.stabSeminorm_center_dominates_of_basisNhd}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_center_dominates_of_basisNhd&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_center_dominates_of_basisNhd%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_dominated\_of\_basisNhd

Local seminorm domination. If $`\tau \in B_\varepsilon(\sigma)` with $`\varepsilon < 1/8`, then there exists a finite constant $`K` such that $`\|U\|_\sigma \leq K \cdot \|U\|_\tau` for all $`U`. This is the local form of Lemma 6.2.

Proof: Bounds $`\|\tau.Z - \sigma.Z\|_\tau` using the explicit seminorm comparison, verifies $`M_Z / (c - M_Z) < c` via the trigonometric inequality, then constructs the reverse comparison constant $`K = 1 / (c - N_Z)`.

{docstring CategoryTheory.Triangulated.stabSeminorm_dominated_of_basisNhd}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_dominated_of_basisNhd&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_dominated_of_basisNhd%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_neg

The Bridgeland seminorm satisfies $`\|-U\|_\sigma = \|U\|_\sigma`.

Proof: Follows from $`\|-U([E])\| = \|U([E])\|`.

{docstring CategoryTheory.Triangulated.stabSeminorm_neg}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_neg&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_neg%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_smul

The Bridgeland seminorm is $`\mathbb{R}`-homogeneous: $`\|t \cdot U\|_\sigma = |t| \cdot \|U\|_\sigma`.

Proof: Pulls $`|t|` out of each term $`\|tU([E])\| / \|Z([E])\|` using $`\|tU([E])\| = |t| \cdot \|U([E])\|`, then factors through the supremum.

{docstring CategoryTheory.Triangulated.stabSeminorm_smul}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_smul&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_smul%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_smul\_complex

The Bridgeland seminorm is $`\mathbb{C}`-homogeneous: $`\|t \cdot U\|_\sigma = \|t\| \cdot \|U\|_\sigma` for $`t \in \mathbb{C}`.

Proof: Same as `stabSeminorm_smul` using $`\|tU([E])\| = \|t\| \cdot \|U([E])\|`.

{docstring CategoryTheory.Triangulated.stabSeminorm_smul_complex}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_smul_complex&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_smul_complex%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wideSectorFiniteLength\_mono

Wide-sector finite length is monotone under shrinking $`\varepsilon_0`: if the condition holds for $`\varepsilon_0`, it holds for any $`\varepsilon_1 \leq \varepsilon_0`.

Proof: The interval $`[t - 4\varepsilon_1, t + 4\varepsilon_1]` is contained in $`[t - 4\varepsilon_0, t + 4\varepsilon_0]`, so any object in the smaller interval category embeds into the larger one, which has finite length by hypothesis.

{docstring CategoryTheory.Triangulated.wideSectorFiniteLength_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wideSectorFiniteLength_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wideSectorFiniteLength_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Deformation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
