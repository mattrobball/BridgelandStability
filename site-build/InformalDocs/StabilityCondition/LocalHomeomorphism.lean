import BridgelandStability.StabilityCondition.LocalHomeomorphism
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityCondition: LocalHomeomorphism" =>
%%%
htmlSplit := .never
%%%

# ComponentTopologicalLinearLocalModel

A reusable non-existential package for Bridgeland's Theorem 1.2 on a fixed connected component $`\Sigma`. Bundles: (1) the complex-linear charge space $`V(\Sigma)`, (2) a `NormedAddCommGroup` and `NormedSpace \mathbb{C}` instance on it, (3) the proof that all central charges in $`\Sigma` lie in $`V(\Sigma)`, and (4) the proof that the restricted charge map is a local homeomorphism.

Construction: A structure with fields `V`, `instNormedAddCommGroup`, `instNormedSpace`, `mem_charge`, and `isLocalHomeomorph_chargeMap`.


{docstring CategoryTheory.Triangulated.ComponentTopologicalLinearLocalModel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ComponentTopologicalLinearLocalModel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.ComponentTopologicalLinearLocalModel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# chargeMap

The restricted central charge map attached to a component local model: $`\sigma \mapsto Z(\sigma) \in V`.

Construction: Defined by $`\langle \sigma, h_\sigma \rangle \mapsto \langle \sigma.Z, M.\text{mem\_charge}(\sigma, h_\sigma) \rangle`.


{docstring CategoryTheory.Triangulated.ComponentTopologicalLinearLocalModel.chargeMap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20chargeMap&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.ComponentTopologicalLinearLocalModel.chargeMap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# centralChargeIsLocalHomeomorphOnConnectedComponents

**\[Theorem 1.2\]**

Bridgeland's Theorem 1.2: for each connected component $`\Sigma` of the stability space $`\mathrm{Stab}(\mathcal{C})`, the central charge map $`Z : \Sigma \to V(\Sigma)` is a local homeomorphism onto a linear subspace $`V(\Sigma) \subset \mathrm{Hom}(\Lambda, \mathbb{C})` equipped with a natural normed topology.

Proof: The proof assembles the `ComponentTopologicalLinearLocalModel` for each connected component, which packages: the normed subspace $`V(\Sigma)`, the fact that every central charge lands in $`V(\Sigma)`, and the local homeomorphism property of the charge map (proved via a seminorm ball argument showing openness and continuity of $`Z`).

{docstring CategoryTheory.Triangulated.centralChargeIsLocalHomeomorphOnConnectedComponents}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20centralChargeIsLocalHomeomorphOnConnectedComponents&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.centralChargeIsLocalHomeomorphOnConnectedComponents%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Theorem%201.2%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentAddGroupNorm

The restricted Bridgeland seminorm is a genuine additive group norm on $`V(\Sigma)`: it satisfies the triangle inequality, is symmetric under negation, and the only element with norm zero is the zero homomorphism.

Construction: Constructs an `AddGroupNorm` from the Bridgeland seminorm, using `stabSeminorm_add_le` for the triangle inequality, `stabSeminorm_neg` for negation symmetry, and `eq_zero_of_stabSeminorm_toReal_eq_zero` for definiteness.


{docstring CategoryTheory.Triangulated.componentAddGroupNorm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentAddGroupNorm&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentAddGroupNorm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentNorm

The Bridgeland norm $`\|U\| = (\|U\|_{\sigma_0})_{\text{toReal}}` on $`V(\Sigma)`, attached to the chosen representative.

Proof: Directly converts the $`\mathbb{R}_{\geq 0}^\infty`-valued seminorm to a real norm via `ENNReal.toReal`.

{docstring CategoryTheory.Triangulated.componentNorm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentNorm&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentNorm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentNorm\_equivalent\_of\_mem\_component

The chosen norm on $`V(\Sigma)` is equivalent to the Bridgeland norm coming from any representative $`\sigma \in \Sigma`: there exist $`K, L > 0` with $`\|U\| \leq K \cdot \|U\|_\sigma` and $`\|U\|_\sigma \leq L \cdot \|U\|`.

Proof: Obtains domination constants from `stabSeminorm_dominated_of_connected` in both directions, then converts the $`\mathbb{R}_{\geq 0}^\infty` bounds to real inequalities.

{docstring CategoryTheory.Triangulated.componentNorm_equivalent_of_mem_component}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentNorm_equivalent_of_mem_component&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentNorm_equivalent_of_mem_component%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentNormedAddCommGroup

$`V(\Sigma)` is a normed additive commutative group under the Bridgeland norm.

Proof: Obtained from `componentAddGroupNorm` via `AddGroupNorm.toNormedAddCommGroup`.

{docstring CategoryTheory.Triangulated.componentNormedAddCommGroup}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentNormedAddCommGroup&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentNormedAddCommGroup%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentNormedSpace

$`V(\Sigma)` is a $`\mathbb{C}`-normed space under the Bridgeland norm.

Proof: Verifies the `NormedSpace.ofCore` axioms: nonnegativity (trivial from $`\mathbb{R}_{\geq 0}^\infty`), homogeneity (from `stabSeminorm_smul_complex`), triangle inequality (from `componentAddGroupNorm`), and definiteness (from `eq_zero_of_stabSeminorm_toReal_eq_zero`).

{docstring CategoryTheory.Triangulated.componentNormedSpace}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentNormedSpace&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentNormedSpace%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentRep

A chosen representative $`\sigma_0` of a connected component $`\Sigma \in \pi_0(\operatorname{Stab}_v(\mathcal{D}))`.

Construction: Obtained via `Classical.choose` from `ConnectedComponents.exists_rep`.


{docstring CategoryTheory.Triangulated.componentRep}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentRep&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentRep%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentSeminormBall

The seminorm ball in $`V(\Sigma)`: $`\{\, F \in V(\Sigma) : \|F - W\|_{\sigma_0} < r \,\}`.

Construction: Defined directly in terms of the $`\mathbb{R}_{\geq 0}^\infty`-valued Bridgeland seminorm.


{docstring CategoryTheory.Triangulated.componentSeminormBall}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentSeminormBall&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentSeminormBall%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentSeminormBall\_eq\_ball

The seminorm balls coincide with the metric balls for the induced norm on $`V(\Sigma)`.

Proof: Unfolds both definitions and converts between $`\mathbb{R}_{\geq 0}^\infty` and $`\mathbb{R}` comparisons via `ENNReal.ofReal_lt_ofReal_iff` and `ENNReal.ofReal_toReal`.

{docstring CategoryTheory.Triangulated.componentSeminormBall_eq_ball}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentSeminormBall_eq_ball&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentSeminormBall_eq_ball%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentSeminormBasis

The basis of seminorm balls defining a topology on $`V(\Sigma)`.

Construction: The set of sets of the form `componentSeminormBall C cc W r` with $`r > 0`.


{docstring CategoryTheory.Triangulated.componentSeminormBasis}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentSeminormBasis&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentSeminormBasis%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentSeminormSubgroup

Bridgeland's $`V(\Sigma)`: the $`\mathbb{C}`-linear subspace of $`\operatorname{Hom}(\Lambda, \mathbb{C})` consisting of homomorphisms with finite Bridgeland seminorm relative to the chosen representative $`\sigma_0 \in \Sigma`.

Construction: Defined as a `Submodule ℂ (Λ →+ ℂ)` whose carrier is `finiteSeminormSubgroup C (componentRep C cc)`. Closure under $`\mathbb{C}`-scalar multiplication uses `stabSeminorm_smul_complex`.


{docstring CategoryTheory.Triangulated.componentSeminormSubgroup}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentSeminormSubgroup&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentSeminormSubgroup%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentSeminormTopology

The topology on $`V(\Sigma)` generated by seminorm balls for one representative.

Construction: Defined as `TopologicalSpace.generateFrom (componentSeminormBasis C cc)`.


{docstring CategoryTheory.Triangulated.componentSeminormTopology}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentSeminormTopology&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentSeminormTopology%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentSeminormTopology\_eq\_normTopology

The topology generated by seminorm balls agrees with the topology induced by the Bridgeland norm on $`V(\Sigma)`.

Proof: Follows from `isTopologicalBasis_componentSeminormBasis` and the characterization of a topology by its topological basis.

{docstring CategoryTheory.Triangulated.componentSeminormTopology_eq_normTopology}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentSeminormTopology_eq_normTopology&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentSeminormTopology_eq_normTopology%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentSeminorm\_lt\_top\_of\_mem\_component

Any element of $`V(\Sigma)` has finite Bridgeland seminorm with respect to any stability condition in the same connected component.

Proof: Uses `finiteSeminormSubgroup_eq_of_connected` to transfer the finiteness from the chosen representative to any other member of the component.

{docstring CategoryTheory.Triangulated.componentSeminorm_lt_top_of_mem_component}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentSeminorm_lt_top_of_mem_component&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentSeminorm_lt_top_of_mem_component%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentStabilityCondition

The type of stability conditions in a fixed connected component $`\Sigma`.

Construction: Defined as the subtype $`\{\, \sigma : \operatorname{Stab}_v(\mathcal{D}) \mid [\sigma] = \Sigma \,\}`.


{docstring CategoryTheory.Triangulated.componentStabilityCondition}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentStabilityCondition&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentStabilityCondition%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentTopologicalLinearLocalModel

Bridgeland's Theorem 1.2: the canonical componentwise local linear model. For each connected component $`\Sigma` of $`\operatorname{Stab}_v(\mathcal{D})`, the central charge map $`\sigma \mapsto Z(\sigma)` is a local homeomorphism from $`\Sigma` to the complex normed space $`V(\Sigma)`. Specializing to $`v = \operatorname{id}` recovers Bridgeland's Theorem 1.2; specializing to the numerical quotient recovers Corollary 1.3.

Construction: Constructs a `ComponentTopologicalLinearLocalModel` by assembling the seminorm topology agreement (`componentSeminormTopology_eq_normTopology`), continuity of the charge map (Proposition 6.3 + Lemma 6.2), injectivity (Lemma 6.4), and openness (Theorem 7.1 + Lemma 6.2 reverse comparison).


{docstring CategoryTheory.Triangulated.componentTopologicalLinearLocalModel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentTopologicalLinearLocalModel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentTopologicalLinearLocalModel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentZMap

The central charge map restricted to a connected component and landing in $`V(\Sigma)`: $`\sigma \mapsto Z(\sigma) \in V(\Sigma)`.

Construction: Defined by $`\langle \sigma, h_\sigma \rangle \mapsto \langle \sigma.Z, \text{componentZ\_mem}(\sigma, h_\sigma) \rangle`.


{docstring CategoryTheory.Triangulated.componentZMap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentZMap&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentZMap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# componentZ\_mem

For $`\sigma \in \Sigma`, its central charge $`Z(\sigma)` lies in $`V(\Sigma)`.

Proof: Uses `finiteSeminormSubgroup_eq_of_connected` to transfer `Z_mem_finiteSeminormSubgroup` from $`\sigma` to the chosen representative.

{docstring CategoryTheory.Triangulated.componentZ_mem}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20componentZ_mem&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.componentZ_mem%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isTopologicalBasis\_componentSeminormBasis

The seminorm-ball basis is a genuine topological basis for the norm topology on $`V(\Sigma)`.

Proof: Verifies that each seminorm ball is open in the norm topology (since it equals a metric ball) and that every neighborhood contains a seminorm ball (since metric balls are seminorm balls).

{docstring CategoryTheory.Triangulated.isTopologicalBasis_componentSeminormBasis}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isTopologicalBasis_componentSeminormBasis&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.isTopologicalBasis_componentSeminormBasis%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mk\_componentRep

The chosen representative satisfies $`[\sigma_0] = \Sigma`.

Proof: Immediate from `Classical.choose_spec`.

{docstring CategoryTheory.Triangulated.mk_componentRep}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mk_componentRep&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.mk_componentRep%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.LocalHomeomorphism%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
