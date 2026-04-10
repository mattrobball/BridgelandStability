import BridgelandStability.NumericalStabilityManifold
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "NumericalStabilityManifold" =>
%%%
htmlSplit := .never
%%%

# NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent

**\[Corollary 1.3\]** complex manifold conclusion only

Corollary 1.3 (Bridgeland 2007). Each connected component of the space of numerical stability conditions on a triangulated category $`\mathcal{C}` is a finite-dimensional complex manifold. Here $`\mathcal{C}` is a $`k`-linear triangulated category of finite type that is numerically finite, and the stability conditions are numerical in the sense that they factor through the numerical Grothendieck group.

Proof: The proof (currently `sorry`) should construct local charts by showing that the forgetful map from stability conditions to the space of central charges (a finite-dimensional complex vector space) is a local homeomorphism on each connected component, using the deformation result (Theorem 1.2) and the support property.

{docstring CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20existsComplexManifoldOnConnectedComponent&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.NumericalStabilityManifold%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Corollary%201.3%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# WithClassMap.existsComplexManifoldOnConnectedComponent

**\[Corollary 1.3\]** class-map generalization; manifold consequence only

Bridgeland's Corollary 1.3 for $`\operatorname{Stab}_v(\mathcal{D})`. Each connected component of the class-map stability space carries the structure of a complex manifold modeled on a finite-dimensional complex normed space, provided $`v` is surjective and $`\Lambda` is finitely generated.

Proof: The local model from Theorem 1.2 (`componentTopologicalLinearLocalModel`) gives a local homeomorphism into $`V(\Sigma)`. Since $`\Lambda` has finite rank, $`\operatorname{Hom}(\Lambda, \mathbb{C})` is finite-dimensional (`classMapChargeSpace_finiteDimensional`), hence so is the submodule $`V(\Sigma)`. Feeding this into `exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model` completes the proof.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.existsComplexManifoldOnConnectedComponent}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20existsComplexManifoldOnConnectedComponent&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.existsComplexManifoldOnConnectedComponent%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.NumericalStabilityManifold%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Corollary%201.3%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# classMapChargeSpace\_finiteDimensional

When the class lattice $`\Lambda` is finitely generated as an abelian group, the charge space $`\operatorname{Hom}_{\mathbb{Z}}(\Lambda, \mathbb{C})` is finite-dimensional over $`\mathbb{C}`.

Proof: Chooses a surjection $`\mathbb{Z}^n \twoheadrightarrow \Lambda` from the finite generation hypothesis. Precomposition gives an injection $`\operatorname{Hom}(\Lambda, \mathbb{C}) \hookrightarrow `\operatorname(Hom)(\mathbb(Z)^n, \mathbb(C)) \cong \mathbb(C)^n$, and finite-dimensionality follows from `FiniteDimensional.of_injective`.

{docstring CategoryTheory.Triangulated.classMapChargeSpace_finiteDimensional}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20classMapChargeSpace_finiteDimensional&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.classMapChargeSpace_finiteDimensional%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.NumericalStabilityManifold%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_chartedSpace\_and\_complexManifold\_of\_isLocalHomeomorph\_to\_complex\_model

If $`f : M \to E` is a local homeomorphism into a finite-dimensional complex normed space, then $`M` admits the structure of a complex manifold modeled on $`E`. This is the abstract topological-to-manifold bridge for Corollary 1.3.

Proof: Combines `exists_chartedSpace_and_hasGroupoid_idRestr_of_isLocalHomeomorph_to_complex_model` with `isManifold_of_hasGroupoid_idRestr`.

{docstring CategoryTheory.Triangulated.exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.NumericalStabilityManifold%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_chartedSpace\_and\_hasGroupoid\_idRestr\_of\_isLocalHomeomorph\_to\_complex\_model

If $`f : M \to E` is a local homeomorphism into a normed space, then $`M` admits a charted space structure modeled on $`E` whose transition maps lie in the identity-restriction groupoid.

Proof: For each $`x \in M`, `Classical.choose` extracts a chart from the local homeomorphism hypothesis. The atlas is the range of these charts. Since all charts agree with $`f`, the transition maps $`e_y^{-1} \circ e_x` are the identity on their domain, hence belong to `idRestrGroupoid`.

{docstring CategoryTheory.Triangulated.exists_chartedSpace_and_hasGroupoid_idRestr_of_isLocalHomeomorph_to_complex_model}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_chartedSpace_and_hasGroupoid_idRestr_of_isLocalHomeomorph_to_complex_model&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_chartedSpace_and_hasGroupoid_idRestr_of_isLocalHomeomorph_to_complex_model%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.NumericalStabilityManifold%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isManifold\_of\_hasGroupoid\_idRestr

A charted space whose structure groupoid is contained in the identity-restriction groupoid is automatically a smooth (in fact $`C^\infty`) complex manifold.

Proof: The identity-restriction groupoid is contained in $`\operatorname{contDiff}^\infty` by `closedUnderRestriction_iff_id_le`. The result follows from `hasGroupoid_of_le` and `IsManifold.mk'`.

{docstring CategoryTheory.Triangulated.isManifold_of_hasGroupoid_idRestr}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isManifold_of_hasGroupoid_idRestr&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.isManifold_of_hasGroupoid_idRestr%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.NumericalStabilityManifold%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
