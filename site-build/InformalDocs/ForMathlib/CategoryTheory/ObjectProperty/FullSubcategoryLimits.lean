import BridgelandStability.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategoryLimits
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "ForMathlib: CategoryTheory.ObjectProperty.FullSubcategoryLimits" =>
%%%
htmlSplit := .never
%%%

# cokernel\_condition\_hom

In a full subcategory, the cokernel condition $`f \circ \pi = 0` holds at the level of underlying morphisms: $`f.\mathrm{hom} \circ (\operatorname{coker}(f).\pi).\mathrm{hom} = 0`.

Proof: Apply `congr_arg (·.hom)` to `cokernel.condition f`.

{docstring CategoryTheory.ObjectProperty.FullSubcategory.cokernel_condition_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernel_condition_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.ObjectProperty.FullSubcategory.cokernel_condition_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategoryLimits%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cokernel\_condition\_homMk

Variant of `cokernel_condition_hom` for the post-`simp` normal form: if the morphism is presented as `homMk g`, then $`g \circ (\operatorname{coker}(\operatorname{homMk}\ g).\pi).\mathrm{hom} = 0`.

Proof: Reduces to `cokernel_condition_hom (ObjectProperty.homMk g)`.

{docstring CategoryTheory.ObjectProperty.FullSubcategory.cokernel_condition_homMk}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernel_condition_homMk&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.ObjectProperty.FullSubcategory.cokernel_condition_homMk%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategoryLimits%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cokernel\_π\_desc\_hom

In a full subcategory, the cokernel universal property at the level of underlying morphisms: $`(\operatorname{coker}(f).\pi).\mathrm{hom} \circ (\operatorname{desc}(f, g, h)).\mathrm{hom} = g.\mathrm{hom}`.

Proof: Apply `congr_arg (·.hom)` to `cokernel.π_desc f g h`.

{docstring CategoryTheory.ObjectProperty.FullSubcategory.cokernel_π_desc_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernel_%CF%80_desc_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.ObjectProperty.FullSubcategory.cokernel_%CF%80_desc_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategoryLimits%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# homMk\_eq\_zero

In a full subcategory, `homMk f = 0` if and only if $`f = 0` in the ambient category.

Proof: Both directions follow from the fact that `.hom` is injective on morphisms in the full subcategory.

{docstring CategoryTheory.ObjectProperty.FullSubcategory.homMk_eq_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20homMk_eq_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.ObjectProperty.FullSubcategory.homMk_eq_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategoryLimits%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# kernel\_condition\_hom

In a full subcategory, the kernel condition $`\iota \circ f = 0` holds at the level of underlying morphisms: $`(\ker(f).\iota).\mathrm{hom} \circ f.\mathrm{hom} = 0`.

Proof: Apply `congr_arg (·.hom)` to `kernel.condition f`.

{docstring CategoryTheory.ObjectProperty.FullSubcategory.kernel_condition_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20kernel_condition_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.ObjectProperty.FullSubcategory.kernel_condition_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategoryLimits%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# kernel\_condition\_homMk

Variant of `kernel_condition_hom` for the post-`simp` normal form: if the morphism is `homMk g`, then $`(\ker(\operatorname{homMk}\ g).\iota).\mathrm{hom} \circ g = 0`.

Proof: Reduces to `kernel_condition_hom (ObjectProperty.homMk g)`.

{docstring CategoryTheory.ObjectProperty.FullSubcategory.kernel_condition_homMk}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20kernel_condition_homMk&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.ObjectProperty.FullSubcategory.kernel_condition_homMk%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategoryLimits%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# kernel\_lift\_ι\_hom

In a full subcategory, the kernel universal property at the level of underlying morphisms: $`(\operatorname{lift}(f, g, h)).\mathrm{hom} \circ (\ker(f).\iota).\mathrm{hom} = g.\mathrm{hom}`.

Proof: Apply `congr_arg (·.hom)` to `kernel.lift_ι f g h`.

{docstring CategoryTheory.ObjectProperty.FullSubcategory.kernel_lift_ι_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20kernel_lift_%CE%B9_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.ObjectProperty.FullSubcategory.kernel_lift_%CE%B9_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategoryLimits%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
