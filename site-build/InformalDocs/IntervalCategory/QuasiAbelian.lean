import BridgelandStability.IntervalCategory.QuasiAbelian
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "IntervalCategory: QuasiAbelian" =>
%%%
htmlSplit := .never
%%%

# epi\_toRightHeart\_of\_strictEpi

A strict epimorphism $`g` in $`\mathcal{P}((a, b))` becomes an epimorphism in the right heart $`\mathcal{P}([b-1, b))`.

Proof: Analogous to `epi_toLeftHeart_of_strictEpi` but using the right heart. The cokernel of $`\ker(g)` in the right heart is computed via a distinguished triangle from the abelian heart structure, and the resulting cokernel comparison shows $`g` maps to an epimorphism.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.epi_toRightHeart_of_strictEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20epi_toRightHeart_of_strictEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.epi_toRightHeart_of_strictEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mono\_toLeftHeart\_of\_strictMono

A strict monomorphism $`f` in $`\mathcal{P}((a, b))` becomes a monomorphism in the left heart $`\mathcal{P}((a, a+1])`.

Proof: Analogous to `mono_toRightHeart_of_strictMono` but using the left heart. The kernel of $`\operatorname{coker}(f) \circ \operatorname{coker.\pi}` in the left heart is computed, and the resulting kernel comparison shows $`f` maps to a monomorphism.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.mono_toLeftHeart_of_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mono_toLeftHeart_of_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.mono_toLeftHeart_of_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toRightHeartCokernelIso

The cokernel of a morphism $`f` in $`\mathcal{P}((a,b))`, when embedded in the right heart $`\mathcal{P}([b-1, b))`, is isomorphic to the cokernel of $`f` computed directly in the right heart.

Construction: Constructs the isomorphism by comparing the cokernel in $`\mathcal{P}((a,b))` (which maps into the right heart) with the cokernel computed in the abelian right heart, using the universal property and the fact that both satisfy the same cocone condition.


{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeartCokernelIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toRightHeartCokernelIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeartCokernelIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toRightHeartCokernelIso\_π\_comp\_hom

The cokernel projection in the right heart factors through `toRightHeartCokernelIso`: $`F_R(\operatorname{coker.\pi}(f)) \circ \mathrm{iso} = \operatorname{coker.\pi}(F_R(f))`.

Proof: Unfolds the construction of `toRightHeartCokernelIso` and verifies the factoring by tracking the cokernel projection through the comparison isomorphism.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toRightHeartCokernelIso_%CF%80_comp_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeartCokernelIso_%CF%80_comp_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# LeftHeart

The left ambient abelian heart $`\mathcal{P}((a, a+1])`, defined as the heart of the t-structure induced by the slicing shifted by $`a`.

Construction: The full subcategory of the heart of `(s.phaseShift C a).toTStructure`.


{docstring CategoryTheory.Triangulated.Slicing.LeftHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20LeftHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.LeftHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# RightHeart

The right ambient abelian heart $`\mathcal{P}([b-1, b))`, defined as the heart of the dual t-structure induced by the slicing shifted by $`b - 1`.

Construction: The full subcategory of the heart of `(s.phaseShift C (b - 1)).toTStructureGE`.


{docstring CategoryTheory.Triangulated.Slicing.RightHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20RightHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.RightHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasCokernel

Every morphism $`f : X \to Y` in the thin interval category $`\mathcal{P}((a, b))` with $`b - a \le 1` has a cokernel.

Proof: Embed into the right abelian heart $`\mathcal{P}([b-1, b))`, compute the cokernel there, and show the cokernel object lies in $`\mathcal{P}((a, b))` via `third_intervalProp_of_triangle`. The right heart gives $`\operatorname{geProp}(b-1)` on the kernel object and $`\operatorname{ltProp}(b)` on the cokernel, enabling the triangle test.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasCokernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasCokernels

The thin interval category $`\mathcal{P}((a, b))` with $`a < b` and $`b - a \le 1` has all cokernels.

Proof: Immediate from `intervalCat_hasCokernel` applied to each morphism.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasCokernels&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasKernel

Every morphism $`f : X \to Y` in the thin interval category $`\mathcal{P}((a, b))` with $`b - a \le 1` has a kernel.

Proof: Embed into the left abelian heart $`\mathcal{P}((a, a+1])`, compute the kernel there, and show the kernel object lies in $`\mathcal{P}((a, b))` via `first_intervalProp_of_triangle`. The key is that the abelian cokernel of $`\ker(f_H) \hookrightarrow X_H` lives in the heart with $`\operatorname{leProp}(a+1)`, and $`\ker(f_H)` has $`\operatorname{gtProp}(a)` from heart membership, so the triangle test applies.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasKernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasKernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasKernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasKernels

The thin interval category $`\mathcal{P}((a, b))` with $`a < b` and $`b - a \le 1` has all kernels.

Proof: Immediate from `intervalCat_hasKernel` applied to each morphism.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasKernels&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.QuasiAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
