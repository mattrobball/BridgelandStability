import BridgelandStability.StabilityCondition.Defs
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityCondition: Defs" =>
%%%
htmlSplit := .never
%%%

# PreStabilityCondition

A Bridgeland prestability condition on $`\mathcal{C}`, defined as the specialization of `PreStabilityCondition.WithClassMap` to the identity class map $`\operatorname{id} \colon K_0(\mathcal{C}) \to K_0(\mathcal{C})`.

Construction: An abbreviation for `PreStabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))`.


{docstring CategoryTheory.Triangulated.PreStabilityCondition}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20PreStabilityCondition&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.PreStabilityCondition%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# PreStabilityCondition.WithClassMap

**\[Definition 5.1\]**

A Bridgeland prestability condition on a triangulated category $`\mathcal{C}` with respect to a class map $`v \colon K_0(\mathcal{C}) \to \Lambda` consists of a slicing $`\mathcal{P}` together with a group homomorphism $`Z \colon \Lambda \to \mathbb{C}` (the central charge) such that for every nonzero $`\mathcal{P}(\phi)`-semistable object $`E`, one has $`Z(v([E])) = m \cdot e^{i\pi\phi}` for some $`m > 0`. This is Definition 5.1 of Bridgeland (2007), lifted to an arbitrary class lattice.

Construction: The structure packages the slicing, the central charge on $`\Lambda`, and the compatibility proof that the image of each semistable class lies on the correct ray in $`\mathbb{C}`.


{docstring CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20WithClassMap&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%205.1%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# StabilityCondition

A Bridgeland stability condition on $`\mathcal{C}`, the specialization of `StabilityCondition.WithClassMap` to the identity class map. This is the classical object $`\operatorname{Stab}(\mathcal{C})` from Bridgeland (2007).

Construction: An abbreviation for `StabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))`.


{docstring CategoryTheory.Triangulated.StabilityCondition}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20StabilityCondition&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# StabilityCondition.WithClassMap

**\[Definition 5.7\]**

A Bridgeland stability condition on a triangulated category $`\mathcal{C}` with respect to a class map $`v \colon K_0(\mathcal{C}) \to \Lambda` is a prestability condition whose underlying slicing is locally finite: for every $`\phi \in \mathbb{R}` and every bounded interval of phases, every object in the corresponding quasi-abelian category has finite length. This is Definition 5.3 of Bridgeland (2007).

Construction: Extends `PreStabilityCondition.WithClassMap` with a proof that the slicing satisfies the `IsLocallyFinite` condition.


{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20WithClassMap&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%205.7%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# CentralChargeIsLocalHomeomorphOnConnectedComponents

**\[Theorem 1.2\]** statement only; proof is componentTopologicalLinearLocalModel

The Bridgeland Theorem 1.2 statement in existential form: for every connected component $`\Sigma` of $`\operatorname{Stab}_v(\mathcal{D})`, there exists a complex normed subspace $`V(\Sigma) \subseteq \operatorname{Hom}(\Lambda, \mathbb{C})` such that every central charge in $`\Sigma` lies in $`V(\Sigma)`, and the restricted central charge map $`\sigma \mapsto Z(\sigma)` is a local homeomorphism from $`\Sigma` onto $`V(\Sigma)`.

Construction: A proposition quantifying over component indices, asserting existence of a $`\mathbb{C}`-normed submodule and an `IsLocalHomeomorph` instance.


{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20CentralChargeIsLocalHomeomorphOnConnectedComponents&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Theorem%201.2%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Component

The type of stability conditions in a fixed connected component $`\Sigma` of $`\operatorname{Stab}_v(\mathcal{D})`.

Construction: Defined as the subtype of stability conditions whose `ConnectedComponents.mk` equals the given component index.


{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20Component&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.Component%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ComponentIndex

The set of connected components of $`\operatorname{Stab}_v(\mathcal{D})`, i.e., the quotient $`\pi_0(\operatorname{Stab}_v(\mathcal{D}))`.

Construction: An abbreviation for `ConnectedComponents (StabilityCondition.WithClassMap C v)`.


{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ComponentIndex&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ComponentIndex%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# topologicalSpace

The Bridgeland topology on $`\operatorname{Stab}_v(\mathcal{D})`, generated by $`\{\, B_\varepsilon(\sigma) : \sigma \in \operatorname{Stab}_v(\mathcal{D}),\, 0 < \varepsilon < 1/8 \,\}`. This is the BLMNPS topology: the coarsest making both the charge map $`\sigma \mapsto \sigma.Z` and the slicing map continuous.

Proof: Constructed via `TopologicalSpace.generateFrom` applied to the family of basis neighborhoods.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20topologicalSpace&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.topologicalSpace%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# basisNhd

The basis neighborhood $`B_\varepsilon(\sigma)` for the Bridgeland topology on $`\operatorname{Stab}_v(\mathcal{D})`: $`B_\varepsilon(\sigma) = \{\, \tau : \|\tau.Z - \sigma.Z\|_\sigma < \sin(\pi\varepsilon) \text{ and } d(\mathcal{P}_\sigma, \mathcal{P}_\tau) < \varepsilon \,\}`.

Construction: Defined as the set of stability conditions satisfying both the seminorm bound on the central charge difference and the slicing distance bound.


{docstring CategoryTheory.Triangulated.basisNhd}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20basisNhd&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.basisNhd%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_ofReal\_mul\_exp\_mul\_exp\_neg

The phase rotation identity: $`\operatorname{Im}(m \cdot e^{i\pi\psi} \cdot e^{-i\pi\phi}) = m \cdot \sin(\pi(\psi - \phi))`. This factorization underlies all sign arguments in Bridgeland's deformation theory (Lemmas 6.1--6.4).

Proof: Combines the exponentials via $`e^{i\pi\psi} \cdot e^{-i\pi\phi} = e^{i\pi(\psi - \phi)}`, then extracts the imaginary part using Euler's formula.

{docstring CategoryTheory.Triangulated.im_ofReal_mul_exp_mul_exp_neg}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_ofReal_mul_exp_mul_exp_neg&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_ofReal_mul_exp_mul_exp_neg%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# slicingDist

The Bridgeland generalized metric on slicings. For slicings $`\mathcal{P}_1` and $`\mathcal{P}_2`, this is $`d(\mathcal{P}_1, \mathcal{P}_2) = \sup_{E \neq 0} \max(|\phi_1^+(E) - \phi_2^+(E)|,\, |\phi_1^-(E) - \phi_2^-(E)|)` where $`\phi^{\pm}` denote the maximum/minimum HN phases.

Construction: Defined as an $`\mathbb{R}_{\geq 0}^{\infty}`-valued supremum over all nonzero objects of the maximum of the absolute phase differences.


{docstring CategoryTheory.Triangulated.slicingDist}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20slicingDist&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.slicingDist%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm

The Bridgeland seminorm $`\|U\|_\sigma` on $`\operatorname{Hom}(\Lambda, \mathbb{C})`. For a stability condition $`\sigma = (Z, \mathcal{P})` with class map $`v` and a group homomorphism $`U \colon \Lambda \to \mathbb{C}`, this is $`\|U\|_\sigma = \sup \{\, |U(v[E])| / |Z(v[E])| : E \text{ is } \sigma\text{-semistable and nonzero}\,\}`.

Construction: Defined as an $`\mathbb{R}_{\geq 0}^{\infty}`-valued supremum indexed over objects, phases, semistability witnesses, and nonzero witnesses.


{docstring CategoryTheory.Triangulated.stabSeminorm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabilityCondition\_compat\_apply

The compatibility condition for a stability condition with identity class map: for every nonzero $`\mathcal{P}(\phi)`-semistable object $`E`, the central charge satisfies $`Z([E]) = m \cdot e^{i\pi\phi}` for some $`m > 0`.

Proof: Immediate by simplifying the general compatibility statement when $`v = \operatorname{id}`.

{docstring CategoryTheory.Triangulated.stabilityCondition_compat_apply}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabilityCondition_compat_apply&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabilityCondition_compat_apply%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
