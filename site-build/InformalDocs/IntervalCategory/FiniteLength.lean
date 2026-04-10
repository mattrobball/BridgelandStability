import BridgelandStability.IntervalCategory.FiniteLength
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "IntervalCategory: FiniteLength" =>
%%%
htmlSplit := .never
%%%

# appendStrictFactor

Append a semistable strict quotient in $`\mathcal{P}((a,b))` to an HN filtration of the kernel. Given an HN filtration $`G` of $`S.X_1` and a strict short exact sequence $`S.X_1 \hookrightarrow S.X_2 \twoheadrightarrow S.X_3` with $`S.X_3 \in \mathcal{P}(\psi)` and $`\psi` below all phases of $`G`, this produces an HN filtration of $`S.X_2`.

Construction: Lifts the strict SES to a distinguished triangle and applies `HNFiltration.appendFactor` with identity isomorphisms.


{docstring CategoryTheory.Triangulated.HNFiltration.appendStrictFactor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20appendStrictFactor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.appendStrictFactor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# SkewedStabilityFunction

**\[Definition 4.4\]** weaker: only σ-semistable nonvanishing, not all nonzero objects

A skewed stability function on a thin subcategory $`\mathcal{P}((a, b))` consists of a group homomorphism $`W : \Lambda \to \mathbb{C}` (the charge), a class map $`v : K_0(\mathcal{C}) \to \Lambda`, and a skewing parameter $`\alpha \in (a, b)`, such that $`W(v[E]) \ne 0` for every nonzero $`\sigma`-semistable object $`E` with phase in $`(a, b)`. In the deformation theorem, $`W` is a perturbation of the central charge $`Z` of a stability condition.

Construction: The structure bundles the homomorphism $`W`, the parameter $`\alpha` with its interval membership proof, and the non-vanishing condition on semistable objects.


{docstring CategoryTheory.Triangulated.SkewedStabilityFunction}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20SkewedStabilityFunction&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%204.4%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strict\_additive

The central charge of a skewed stability function is additive on strict short exact sequences: $`W(v[X_2]) = W(v[X_1]) + W(v[X_3])` for a strict SES $`X_1 \hookrightarrow X_2 \twoheadrightarrow X_3` in $`\mathcal{P}((a,b))`.

Proof: The $`K_0` relation from `K0_of_strictShortExact` gives $`[X_2] = [X_1] + [X_3]` in $`K_0(\mathcal{C})`, and $`W \circ v` is a group homomorphism, so it respects the sum.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.strict_additive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strict_additive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.strict_additive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# K0\_of\_strictShortExact

A strict short exact sequence $`X_1 \hookrightarrow X_2 \twoheadrightarrow X_3` in $`\mathcal{P}((a,b))` yields the $`K_0` relation $`[X_2] = [X_1] + [X_3]` in the Grothendieck group of $`\mathcal{C}`.

Proof: Lift the strict SES to a distinguished triangle in $`\mathcal{C}`. The $`K_0` additivity on distinguished triangles gives the relation.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.K0_of_strictShortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20K0_of_strictShortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.K0_of_strictShortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# comp\_strictEpi

Strict epimorphisms in $`\mathcal{P}((a,b))` are closed under composition: if $`f` and $`g` are strict epimorphisms, then $`f \circ g` is a strict epimorphism.

Proof: Both $`f` and $`g` map to epimorphisms in the left heart by `epi_toLeftHeart_of_strictEpi`. Their composition $`F_L(f \circ g) = F_L(f) \circ F_L(g)` is therefore epi in the abelian heart. Then `strictEpi_of_epi_toLeftHeart` recovers strictness.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.comp_strictEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20comp_strictEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.comp_strictEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# comp\_strictMono

Strict monomorphisms in $`\mathcal{P}((a,b))` are closed under composition: if $`f` and $`g` are strict monomorphisms, then $`f \circ g` is a strict monomorphism.

Proof: Both $`f` and $`g` map to monomorphisms in the right heart by `mono_toRightHeart_of_strictMono`. Their composition $`F_R(f \circ g) = F_R(f) \circ F_R(g)` is therefore mono in the abelian heart. Then `strictMono_of_mono_toRightHeart` recovers strictness.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.comp_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20comp_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.comp_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_distTriang\_of\_shortExact\_toLeftHeart

A short exact sequence in the left heart $`\mathcal{P}((a,a+1])` with vertices in $`\mathcal{P}((a,b))` extends to a distinguished triangle in $`\mathcal{C}`.

Proof: In the abelian heart, the epi $`g` lifts to a distinguished triangle via the admissible subcategory structure. The kernel comparison isomorphism identifies the first vertex with $`S.X_1`, giving a distinguished triangle on the original objects.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_distTriang_of_shortExact_toLeftHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_distTriang\_of\_strictShortExact

A strict short exact sequence in $`\mathcal{P}((a,b))` extends to a distinguished triangle in $`\mathcal{C}`.

Proof: The strict mono $`S.f` maps to a mono in the right heart, and the strict epi $`S.g` maps to an epi in the left heart. The homology data from the strict short exact sequence gives a short exact sequence in the left heart, from which `exists_distTriang_of_shortExact_toLeftHeart` produces the distinguished triangle.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distTriang_of_strictShortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_distTriang_of_strictShortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distTriang_of_strictShortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# finite\_subobject\_of\_leftHeart

Finite subobjects in the left heart transfer to finite subobjects in $`\mathcal{P}((a,b))`: if $`F_L(X)` has finitely many subobjects, then $`X` has finitely many subobjects.

Proof: The left heart embedding is faithful and preserves monomorphisms (it preserves finite limits). Faithful functors that preserve monos reflect the finiteness of the subobject poset.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.finite_subobject_of_leftHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20finite_subobject_of_leftHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.finite_subobject_of_leftHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strictMono\_strictEpi\_of\_distTriang

A distinguished triangle in $`\mathcal{C}` whose three vertices lie in $`\mathcal{P}((a,b))` forces the first map to be a strict monomorphism and the second to be a strict epimorphism in $`\mathcal{P}((a,b))`.

Proof: The triangle lifts to short exact sequences in both hearts via the abelian subcategory theory. Apply `strictMono_strictEpi_of_shortExact_toLeftRightHearts`.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.strictMono_strictEpi_of_distTriang}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strictMono_strictEpi_of_distTriang&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.strictMono_strictEpi_of_distTriang%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strictMono\_strictEpi\_of\_shortExact\_toLeftRightHearts

If a short complex in $`\mathcal{P}((a,b))` is short exact in both the left heart $`\mathcal{P}((a, a+1])` and the right heart $`\mathcal{P}([b-1, b))`, then its left map is a strict monomorphism and its right map is a strict epimorphism.

Proof: Short exactness in the right heart gives mono on $`f` (reflecting through the right heart gives strict mono). Short exactness in the left heart gives epi on $`g` (reflecting through the left heart gives strict epi).

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.strictMono_strictEpi_of_shortExact_toLeftRightHearts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strictMono_strictEpi_of_shortExact_toLeftRightHearts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.strictMono_strictEpi_of_shortExact_toLeftRightHearts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strictShortExact\_iff\_exists\_distTriang

Strict short exact sequences in $`\mathcal{P}((a,b))` are in bijection with distinguished triangles in $`\mathcal{C}` whose three vertices lie in $`\mathcal{P}((a,b))`.

Proof: Forward: `exists_distTriang_of_strictShortExact`. Backward: `strictShortExact_of_distTriang`.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_iff_exists_distTriang}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strictShortExact_iff_exists_distTriang&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_iff_exists_distTriang%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strictShortExact\_inclusion

A strict short exact sequence in a smaller thin interval $`\mathcal{P}((a_1, b_1))` remains strict in any larger thin interval $`\mathcal{P}((a_2, b_2))` containing it.

Proof: Lift the strict SES to a distinguished triangle via `exists_distTriang_of_strictShortExact`. The triangle's vertices lie in the larger interval by `intervalProp_mono`. Apply `strictShortExact_of_distTriang` in the larger interval.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strictShortExact_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strictShortExact\_of\_distTriang

A distinguished triangle in $`\mathcal{C}` whose three vertices lie in $`\mathcal{P}((a,b))` defines a strict short exact sequence in $`\mathcal{P}((a,b))`.

Proof: From `strictMono_strictEpi_of_distTriang`, the first map is strict mono and the second is strict epi. Exactness follows from the abelian heart SES: the triangle gives kernel and cokernel limit cones in both hearts, reflecting through the faithful embeddings yields exactness in $`\mathcal{P}((a,b))`.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_of_distTriang}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strictShortExact_of_distTriang&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_of_distTriang%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toLeftHeart\_additive

The left heart embedding $`F_L : \mathcal{P}((a,b)) \to \mathcal{P}((a, a+1])` is an additive functor.

Proof: The functor acts as the identity on morphisms, so additivity is immediate.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_additive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toLeftHeart_additive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_additive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toLeftHeart\_preservesFiniteLimits

The left heart embedding $`F_L : \mathcal{P}((a,b)) \to \mathcal{P}((a, a+1])` preserves all finite limits.

Proof: Since $`F_L` is additive and preserves kernels, it preserves all finite limits by the general criterion for additive functors between preadditive categories.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_preservesFiniteLimits}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toLeftHeart_preservesFiniteLimits&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_preservesFiniteLimits%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toLeftHeart\_preservesKernel

The left heart embedding $`F_L : \mathcal{P}((a,b)) \to \mathcal{P}((a, a+1])` preserves kernels.

Proof: The kernel of $`f` in $`\mathcal{P}((a,b))` maps to the kernel of $`F_L(f)` in the left heart via the comparison isomorphism `toLeftHeartKernelIso`. Transporting the limit cone through this isomorphism shows $`F_L` preserves the kernel.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_preservesKernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toLeftHeart_preservesKernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_preservesKernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toRightHeart\_additive

The right heart embedding $`F_R : \mathcal{P}((a,b)) \to \mathcal{P}([b-1, b))` is an additive functor.

Proof: The functor acts as the identity on morphisms, so additivity is immediate.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_additive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toRightHeart_additive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_additive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toRightHeart\_preservesCokernel

The right heart embedding $`F_R : \mathcal{P}((a,b)) \to \mathcal{P}([b-1, b))` preserves cokernels.

Proof: The cokernel of $`f` in $`\mathcal{P}((a,b))` maps to the cokernel of $`F_R(f)` in the right heart via the comparison isomorphism `toRightHeartCokernelIso`. Transporting the colimit cocone through this isomorphism shows $`F_R` preserves the cokernel.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_preservesCokernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toRightHeart_preservesCokernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_preservesCokernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toRightHeart\_preservesFiniteColimits

The right heart embedding $`F_R : \mathcal{P}((a,b)) \to \mathcal{P}([b-1, b))` preserves all finite colimits.

Proof: Since $`F_R` is additive and preserves cokernels, it preserves all finite colimits by the general criterion for additive functors between preadditive categories.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_preservesFiniteColimits}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toRightHeart_preservesFiniteColimits&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_preservesFiniteColimits%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsLocallyFinite

**\[Definition 5.7\]** per-object strict finite length is weaker than finite length of all chains (paper's assumption)

A slicing $`\mathcal{P}` is locally finite if there exists $`\eta > 0` with $`\eta < 1/2` such that every object in each thin interval category $`\mathcal{P}((t - \eta, t + \eta))` has finite length in the quasi-abelian sense (i.e., satisfies both ACC and DCC on strict subobjects).

Construction: The structure witnesses $`\eta`, the positivity bound, the normalization $`\eta < 1/2` (ensuring width $`2\eta \le 1` for the quasi-abelian structure), and for each center $`t \in \mathbb{R}`, the strict Artinian and strict Noetherian conditions on every object.


{docstring CategoryTheory.Triangulated.Slicing.IsLocallyFinite}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsLocallyFinite&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IsLocallyFinite%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%205.7%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasBinaryBiproducts

The thin interval category $`\mathcal{P}((a, b))` has binary biproducts.

Proof: Follows from having binary products (proved earlier) and the additive/preadditive structure.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasBinaryBiproducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasBinaryBiproducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasBinaryBiproducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasCoequalizers

The thin interval category $`\mathcal{P}((a, b))` has coequalizers.

Proof: In a preadditive category, coequalizers follow from the existence of cokernels.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasCoequalizers}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasCoequalizers&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasCoequalizers%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasEqualizers

The thin interval category $`\mathcal{P}((a, b))` has equalizers.

Proof: In a preadditive category, equalizers follow from the existence of kernels.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasEqualizers}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasEqualizers&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasEqualizers%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasFiniteCoproducts

The thin interval category $`\mathcal{P}((a, b))` has finite coproducts.

Proof: Follows from having binary coproducts and an initial object.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasFiniteCoproducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasFiniteCoproducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasFiniteCoproducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasPullbacks

The thin interval category $`\mathcal{P}((a, b))` has pullbacks.

Proof: Follows from having binary products and equalizers.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasPullbacks}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasPullbacks&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasPullbacks%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasPushouts

The thin interval category $`\mathcal{P}((a, b))` has pushouts.

Proof: Follows from having binary coproducts and coequalizers.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasPushouts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasPushouts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasPushouts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_quasiAbelian

The thin interval category $`\mathcal{P}((a, b))` with $`a < b` and $`b - a \le 1` is quasi-abelian.

Proof: The two quasi-abelian axioms are: (1) pullbacks of strict epimorphisms are strict epi, and (2) pushouts of strict monomorphisms are strict mono. For (1): a strict epi $`g` maps to an epi in the left heart; the left heart is abelian, so the pullback of an epi is epi; the left heart embedding preserves pullbacks (it preserves finite limits); reflecting back gives a strict epi. For (2): dual argument using the right heart and pushouts.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_quasiAbelian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_quasiAbelian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_quasiAbelian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.FiniteLength%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
