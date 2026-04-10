import BridgelandStability.Deformation.Pullback
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: Pullback" =>
%%%
htmlSplit := .never
%%%

# interval\_cokernel\_pullbackTopIso

The cokernel of the pullback of a subobject $`B \hookrightarrow \operatorname{coker}(M)` along $`\operatorname{coker\_proj}(M)` is isomorphic to $`\operatorname{coker}(B)`: $`\operatorname{coker}(\mathrm{pullback}) \cong \operatorname{coker}(B)`.

Construction: Constructs the canonical isomorphism using the nine-lemma / pullback-cokernel comparison in the interval category, detected via the left-heart functor.


{docstring CategoryTheory.Triangulated.interval_cokernel_pullbackTopIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_cokernel_pullbackTopIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_cokernel_pullbackTopIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_fIsKernel\_of\_strictShortExact

In a strict short exact sequence $`0 \to A \xrightarrow{f} B \xrightarrow{g} C \to 0` in a thin interval category, $`f` is a kernel of $`g`.

Construction: Constructs an `IsLimit` cone for the kernel fork of $`g` at $`f`, using the strict short exact sequence data. The lift is obtained from the left-heart factorization.


{docstring CategoryTheory.Triangulated.interval_fIsKernel_of_strictShortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_fIsKernel_of_strictShortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_fIsKernel_of_strictShortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_le\_pullback\_cokernel

For any subobject $`M \hookrightarrow X` in the thin interval category and any subobject $`B` of $`\mathrm{coker}(M \hookrightarrow X)`, we have $`M \le (\pi^* B)` in the subobject lattice of $`X`, where $`\pi^* B` denotes the pullback of $`B` along the cokernel projection $`\pi\colon X \to \mathrm{coker}(M)`. This is the key inclusion placing $`M` below the pullback-cokernel subobject.

Proof: The proof uses the universal property of the pullback: the map $`M \to \pi^*B` is constructed by lifting $`(0, M.\mathrm{arrow})` through the pullback square. Concretely, `Subobject.isPullback` provides the lift, using the fact that $`M.\mathrm{arrow} \circ \pi = 0` (the cokernel condition).

{docstring CategoryTheory.Triangulated.interval_le_pullback_cokernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_le_pullback_cokernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_le_pullback_cokernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_ofLE\_pullbackπ\_eq\_zero

The composite $`M \xrightarrow{\mathrm{ofLE}} \pi^*B \xrightarrow{\pi^*\pi} B` is zero, where $`\pi^*\pi` is the pullback projection from $`\pi^*B` to $`B`. This says the map $`M \to B` induced by the inclusion $`M \le \pi^*B` factors through zero — geometrically, $`M` maps to zero in $`B` because $`M.\mathrm{arrow} \circ \pi = 0`.

Proof: The proof cancels the monomorphism $`B.\mathrm{arrow}` and traces the chain of equalities through the pullback square: the composite $`M \to \pi^*B \to B` equals $`M \to \pi^*B \to X \to \mathrm{coker}(M) = 0 \to B`, using `Subobject.ofLE_arrow` and the cokernel condition.

{docstring CategoryTheory.Triangulated.interval_ofLE_pullbackπ_eq_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_ofLE_pullback%CF%80_eq_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_ofLE_pullback%CF%80_eq_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_pullback\_arrow\_strictMono\_of\_strictMono

Pullback of a strict monomorphism along a morphism in a thin interval category preserves strict monicity: if $`B \hookrightarrow X` is strict mono and $`f : Y \to X` is any morphism, the pullback arrow is strict mono.

Proof: The pullback square in the interval category maps to a pullback square in the left heart (exact functor). Monomorphisms pull back in abelian categories. Transport the mono back to strict mono in the interval category.

{docstring CategoryTheory.Triangulated.interval_pullback_arrow_strictMono_of_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_pullback_arrow_strictMono_of_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_pullback_arrow_strictMono_of_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_pullbackπ\_strictEpi\_of\_strictEpi

Pullback of a strict epimorphism in a thin interval category is a strict epimorphism: if $`f : A \twoheadrightarrow B` is strict epi and $`g : C \to B` is any morphism, then $`\pi_1 : A \times_B C \to C` is strict epi.

Proof: Strict epimorphisms in the thin interval category are detected by the left-heart functor. Pullbacks in the interval category map to pullbacks in the left heart (abelian), where the pullback of an epimorphism is epi. Transport back.

{docstring CategoryTheory.Triangulated.interval_pullbackπ_strictEpi_of_strictEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_pullback%CF%80_strictEpi_of_strictEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_pullback%CF%80_strictEpi_of_strictEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictShortExact\_ofLE\_pullbackπ\_cokernel

The pullback of a cokernel projection along a subobject inclusion gives a strict short exact sequence relating the subobject, its pullback, and the cokernel.

Proof: Combine `interval_strictShortExact_pullback_right` with the strict SES $`0 \to M \to X \to \operatorname{coker}(M) \to 0`.

{docstring CategoryTheory.Triangulated.interval_strictShortExact_ofLE_pullbackπ_cokernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictShortExact_ofLE_pullback%CF%80_cokernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictShortExact_ofLE_pullback%CF%80_cokernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictShortExact\_of\_kernel\_strictEpi

A short complex $`K \hookrightarrow X \twoheadrightarrow Q` in a thin interval category is a strict short exact sequence when $`K = \ker(q)` and $`q` is strict epi.

Proof: The complex maps to a short exact sequence in the left heart: $`K` maps to the kernel, $`q` maps to an epimorphism. The left-heart short exact sequence gives the strict short exact sequence in the interval category.

{docstring CategoryTheory.Triangulated.interval_strictShortExact_of_kernel_strictEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictShortExact_of_kernel_strictEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictShortExact_of_kernel_strictEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictShortExact\_pullback\_left

Pullback of a strict short exact sequence along a morphism yields a strict short exact sequence on the left: given $`0 \to A \to B \to C \to 0` and $`f : D \to B`, the pullback gives $`0 \to A \to D \times_B B \to D \times_B C \to 0`.

Proof: Map to the left heart, apply the abelian pullback lemma, transport back.

{docstring CategoryTheory.Triangulated.interval_strictShortExact_pullback_left}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictShortExact_pullback_left&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictShortExact_pullback_left%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictShortExact\_pullback\_right

Pullback of a strict short exact sequence along a morphism on the right: given $`0 \to A \to B \to C \to 0` and $`g : D \to C`, the pullback gives $`0 \to A \to B \times_C D \to D \to 0`.

Proof: Map to the left heart, apply the standard abelian pullback-along-epi lemma, transport back.

{docstring CategoryTheory.Triangulated.interval_strictShortExact_pullback_right}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictShortExact_pullback_right&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictShortExact_pullback_right%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_upper\_inclusion

Semistability transfers through upper interval inclusion: if $`E` is $`\operatorname{ssf}`-semistable in $`\mathcal{P}((a, b_1))` and $`b_1 \le b_2` with $`\mathcal{P}((a, b_1)) \subseteq \mathcal{P}((a, b_2))`, then $`E` is semistable in $`\mathcal{P}((a, b_2))` at the same phase.

Proof: Use `semistable_of_target_envelope_triangleTest`: the $`W`-phase independence across branch cuts ensures the phase is unchanged, and the triangle test passes because the larger interval contains the smaller one.

{docstring CategoryTheory.Triangulated.semistable_of_upper_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_upper_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.semistable_of_upper_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Pullback%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
