import BridgelandStability.StabilityCondition.ConnectedComponent
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityCondition: ConnectedComponent" =>
%%%
htmlSplit := .never
%%%

# Z\_mem\_finiteSeminormSubgroup

$`Z(\sigma)` has finite $`\sigma`-seminorm: $`\|Z(\sigma)\|_\sigma \leq 1`, so $`Z(\sigma) \in V(\sigma)`.

Proof: Each term in the supremum is $`\|Z([E])\| / \|Z([E])\| \leq 1` (or $`0` when $`Z([E]) = 0`).

{docstring CategoryTheory.Triangulated.Z_mem_finiteSeminormSubgroup}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20Z_mem_finiteSeminormSubgroup&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Z_mem_finiteSeminormSubgroup%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# basisNhdFamily

The generating family of Bridgeland basis neighborhoods: $`\{\, B_\varepsilon(\sigma) : \sigma \in \operatorname{Stab}_v(\mathcal{D}),\, 0 < \varepsilon < 1/8 \,\}`.

Construction: Defined as the set of sets of the form `basisNhd C σ ε` with the positivity and upper bound constraints on $`\varepsilon`.


{docstring CategoryTheory.Triangulated.basisNhdFamily}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20basisNhdFamily&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.basisNhdFamily%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eq\_zero\_of\_stabSeminorm\_toReal\_eq\_zero

If the Bridgeland seminorm of $`U` is finite and equal to zero, then $`U = 0` (assuming $`v` is surjective).

Proof: Zero seminorm means $`\|U([E])\| \leq 0` for every semistable nonzero $`E`, so $`U([E]) = 0` for every semistable object. By the HN filtration decomposition and $`K_0` additivity, $`U` vanishes on all class images, and surjectivity of $`v` gives $`U = 0`.

{docstring CategoryTheory.Triangulated.eq_zero_of_stabSeminorm_toReal_eq_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eq_zero_of_stabSeminorm_toReal_eq_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eq_zero_of_stabSeminorm_toReal_eq_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eq\_zero\_of\_vanishes\_on\_cl

An additive homomorphism $`U \colon \Lambda \to \mathbb{C}` is zero if it vanishes on all class images $`\operatorname{cl}_v(E)` and $`v` is surjective.

Proof: The vanishing on class images means $`U \circ v = 0` on $`K_0(\mathcal{C})` (by the universal property). Surjectivity of $`v` then forces $`U = 0`.

{docstring CategoryTheory.Triangulated.eq_zero_of_vanishes_on_cl}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eq_zero_of_vanishes_on_cl&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eq_zero_of_vanishes_on_cl%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_basisNhd\_subset\_connectedComponent

Every stability condition admits a small Bridgeland basis neighborhood contained in its topological connected component. Concretely, there exists $`\varepsilon \in (0, 1/8)` such that $`B_\varepsilon(\sigma)` is contained in the connected component of $`\sigma`.

Proof: Takes the $`\varepsilon_0 < 1/10` witness from `exists_epsilon0_tenth`, sets $`\varepsilon = \varepsilon_0/2`, and applies `basisNhd_subset_connectedComponent_small`.

{docstring CategoryTheory.Triangulated.exists_basisNhd_subset_connectedComponent}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_basisNhd_subset_connectedComponent&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_basisNhd_subset_connectedComponent%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_basisNhd\_subset\_of\_mem\_nhds

Neighborhood-form extraction: if $`s \in \mathcal{N}(\sigma)`, then there exists $`\varepsilon` with $`B_\varepsilon(\sigma) \subseteq s`.

Proof: Uses `isTopologicalBasis_basisNhd` to extract a basis element from the neighborhood filter, then applies `exists_basisNhd_subset_basisNhd` to recenter.

{docstring CategoryTheory.Triangulated.exists_basisNhd_subset_of_mem_nhds}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_basisNhd_subset_of_mem_nhds&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_basisNhd_subset_of_mem_nhds%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_basisNhd\_subset\_of\_mem\_open

Every open neighborhood of $`\sigma` contains a centered Bridgeland basis neighborhood $`B_\varepsilon(\sigma)`.

Proof: Induction on the structure of `TopologicalSpace.GenerateOpen`: basic opens are basis neighborhoods (handled by `exists_basisNhd_subset_basisNhd`); intersections use the minimum of radii; unions are inherited from members.

{docstring CategoryTheory.Triangulated.exists_basisNhd_subset_of_mem_open}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_basisNhd_subset_of_mem_open&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_basisNhd_subset_of_mem_open%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# finiteSeminormSubgroup\_eq\_of\_connected

Lemma 6.2: On a connected component, the finite-seminorm subgroups agree: $`V(\sigma) = V(\tau)` whenever $`\sigma` and $`\tau` are in the same component.

Proof: Both directions follow from `stabSeminorm_dominated_of_connected`: finite seminorm is preserved under multiplication by a finite constant.

{docstring CategoryTheory.Triangulated.finiteSeminormSubgroup_eq_of_connected}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20finiteSeminormSubgroup_eq_of_connected&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.finiteSeminormSubgroup_eq_of_connected%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isTopologicalBasis\_basisNhd

The Bridgeland basis neighborhoods form a topological basis for $`\operatorname{Stab}_v(\mathcal{D})`.

Proof: Verifies the two conditions of `isTopologicalBasis_of_isOpen_of_nhds`: each basis neighborhood is open in the generated topology, and every open set containing a point contains a basis neighborhood of that point (via `exists_basisNhd_subset_of_mem_open`).

{docstring CategoryTheory.Triangulated.isTopologicalBasis_basisNhd}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isTopologicalBasis_basisNhd&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.isTopologicalBasis_basisNhd%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_dominated\_of\_connected

**\[Lemma 6.2\]** one direction; apply both ways for full equivalence

Lemma 6.2: On a connected component, seminorms are dominated. If $`\sigma` and $`\tau` lie in the same connected component $`\Sigma` of $`\operatorname{Stab}(\mathcal{D})`, then there exists a finite constant $`K` such that $`\|U\|_\sigma \leq K \cdot \|U\|_\tau` for all $`U \in \operatorname{Hom}(\Lambda, \mathbb{C})`.

Proof: Uses the preconnected induction lemma `IsPreconnected.induction₂'` on the connected component, with the local step provided by `stabSeminorm_dominated_of_basisNhd` and transitivity from the multiplicativity of domination constants.

{docstring CategoryTheory.Triangulated.stabSeminorm_dominated_of_connected}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_dominated_of_connected&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_dominated_of_connected%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Lemma%206.2%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabilityCondition\_isOpen\_connectedComponent

Connected components of $`\operatorname{Stab}(\mathcal{D})` are open. Every connected component is an open subset in the Bridgeland topology.

Proof: For each point $`x` in the connected component, `exists_basisNhd_subset_connectedComponent` provides a basis neighborhood inside the component, which is open by construction. So every point is an interior point.

{docstring CategoryTheory.Triangulated.stabilityCondition_isOpen_connectedComponent}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabilityCondition_isOpen_connectedComponent&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabilityCondition_isOpen_connectedComponent%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.ConnectedComponent%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
