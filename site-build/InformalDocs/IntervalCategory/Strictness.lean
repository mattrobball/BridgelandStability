import BridgelandStability.IntervalCategory.Strictness
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "IntervalCategory: Strictness" =>
%%%
htmlSplit := .never
%%%

# epi\_toLeftHeart\_of\_strictEpi

A strict epimorphism $`g` in $`\mathcal{P}((a, b))` becomes an epimorphism in the left heart $`\mathcal{P}((a, a+1])`.

Proof: From the strict epi structure, $`g` is a cokernel of $`\ker(g)`. The left heart kernel isomorphism `toLeftHeartKernelIso` allows comparison of the cokernel in $`\mathcal{P}((a,b))` with the abelian coimage in the left heart. The resulting factorization through the cokernel of the kernel inclusion is shown to be an epimorphism.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20epi_toLeftHeart_of_strictEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Strictness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mono\_toRightHeart\_of\_strictMono

A strict monomorphism $`f` in $`\mathcal{P}((a, b))` becomes a monomorphism in the right heart $`\mathcal{P}([b-1, b))`.

Proof: From the strict mono structure, $`f` is a kernel of $`\operatorname{coker}(f)`. The right heart embedding preserves this kernel via `toRightHeartCokernelIso`. The abelian image factorization in the right heart shows $`f` maps to a monomorphism: the image-kernel comparison is an isomorphism, and the epimorphic factor-through-image composed with it gives a mono-epi factorization.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.mono_toRightHeart_of_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mono_toRightHeart_of_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.mono_toRightHeart_of_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Strictness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strictEpi\_of\_epi\_toLeftHeart

If a morphism $`g` in $`\mathcal{P}((a, b))` becomes an epimorphism in the left heart $`\mathcal{P}((a, a+1])`, then $`g` is a strict epimorphism in $`\mathcal{P}((a, b))`.

Proof: In the abelian left heart, epi implies cokernel-of-kernel. The kernel comparison isomorphism `toLeftHeartKernelIso` transforms this into a cokernel cofork for $`\ker(g)` in $`\mathcal{P}((a,b))`. Reflecting the colimit through the faithful functor yields strictness.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strictEpi_of_epi_toLeftHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Strictness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strictMono\_of\_mono\_toRightHeart

If a morphism $`f` in $`\mathcal{P}((a, b))` becomes a monomorphism in the right heart $`\mathcal{P}([b-1, b))`, then $`f` is a strict monomorphism in $`\mathcal{P}((a, b))`.

Proof: In the abelian right heart, mono implies kernel-of-cokernel. The cokernel comparison isomorphism `toRightHeartCokernelIso` transforms this into a kernel fork for $`\operatorname{coker}(f)` in $`\mathcal{P}((a,b))`. Reflecting the limit through the faithful functor yields strictness.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.strictMono_of_mono_toRightHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strictMono_of_mono_toRightHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.strictMono_of_mono_toRightHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Strictness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toLeftHeartKernelIso

The kernel of a morphism $`f` in $`\mathcal{P}((a,b))`, when embedded in the left heart $`\mathcal{P}((a, a+1])`, is isomorphic to the kernel of $`f` computed directly in the left heart.

Construction: Constructs the isomorphism by comparing the kernel in $`\mathcal{P}((a,b))` (which maps into the left heart) with the kernel computed in the abelian left heart, using the universal property of kernels and the fact that both represent the same limit cone.


{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeartKernelIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toLeftHeartKernelIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeartKernelIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Strictness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toLeftHeartKernelIso\_hom\_comp\_ι

The kernel inclusion in the left heart factors through `toLeftHeartKernelIso`: $`\mathrm{iso} \circ \ker.\iota(F_L(f)) = F_L(\ker.\iota(f))`.

Proof: Unfolds the construction of `toLeftHeartKernelIso` and verifies the factoring by tracking the kernel inclusion through the comparison isomorphism.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toLeftHeartKernelIso_hom_comp_%CE%B9&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_%CE%B9%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Strictness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
