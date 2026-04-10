import BridgelandStability.IntervalCategory.Basic
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "IntervalCategory: Basic" =>
%%%
htmlSplit := .never
%%%

# IntervalCat

The interval subcategory $`\mathcal{P}((a, b))` of a slicing $`\mathcal{P}` on a pretriangulated category $`\mathcal{C}` is the full subcategory on objects $`E` that are either zero or admit an HN filtration whose phases all lie in the open interval $`(a, b) \subset \mathbb{R}`. This is Bridgeland's Definition 4.1 specialized to open intervals.

Construction: Defined as the full subcategory on the object property `s.intervalProp C a b`, which is the disjunction: $`E` is zero, or $`E` has an HN filtration with all phases in $`(a, b)`.


{docstring CategoryTheory.Triangulated.Slicing.IntervalCat}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IntervalCat&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# inclusion

The inclusion functor $`\mathcal{P}((a_1, b_1)) \hookrightarrow \mathcal{P}((a_2, b_2))` for nested intervals with $`a_2 \le a_1` and $`b_1 \le b_2`.

Construction: Defined via `ObjectProperty.ιOfLE` using `intervalProp_mono`.


{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isZero\_of\_obj\_isZero

If the underlying object of an interval subcategory element $`X \in \mathcal{P}((a, b))` is zero in $`\mathcal{C}`, then $`X` is zero in $`\mathcal{P}((a, b))`.

Proof: Constructs an isomorphism between $`X` and the zero object of $`\mathcal{P}((a, b))` by lifting the isomorphism of their underlying objects.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.isZero_of_obj_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isZero_of_obj_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.isZero_of_obj_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ι

The inclusion functor $`\iota : \mathcal{P}((a, b)) \hookrightarrow \mathcal{C}` from the interval subcategory into the ambient category.

Construction: The forgetful functor from the full subcategory to the ambient category, given by `ObjectProperty.ι`.


{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.ι}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20%CE%B9&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.%CE%B9%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalCat\_hasFiniteProducts

The thin interval subcategory $`\mathcal{P}((a, b))` has finite products.

Proof: Follows from having binary products and a terminal object.

{docstring CategoryTheory.Triangulated.Slicing.intervalCat_hasFiniteProducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalCat_hasFiniteProducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalCat_hasFiniteProducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalFiniteLength

For an object $`E \in \mathcal{P}((a, b))` with $`b - a \le 2\eta`, if every object in each $`\eta`-interval subcategory has a finite subobject lattice, then $`E` has a finite subobject lattice.

Proof: Choose $`t = (a + b)/2`. Then $`(a, b) \subseteq (t - \eta, t + \eta)`, so $`E` lies in the $`\eta`-interval centered at $`t`, where the hypothesis provides finiteness.

{docstring CategoryTheory.Triangulated.Slicing.intervalFiniteLength}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalFiniteLength&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalFiniteLength%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalHom\_eq\_zero

Hom-vanishing between disjoint intervals. If $`A \in \mathcal{P}((a_1, b_1))` and $`B \in \mathcal{P}((a_2, b_2))` with $`b_2 \le a_1`, then $`\operatorname{Hom}(A, B) = 0`.

Proof: Every HN factor of $`A` has phase $`> a_1 \ge b_2` and every HN factor of $`B` has phase $`< b_2`, so the slicing's hom-vanishing axiom kills each factor-to-factor component. The conclusion follows by induction on the filtration lengths.

{docstring CategoryTheory.Triangulated.Slicing.intervalHom_eq_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalHom_eq_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalHom_eq_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_biprod

The interval property $`\mathcal{P}((a, b))` is closed under binary biproducts: if $`X, Y \in \mathcal{P}((a, b))`, then $`X \oplus Y \in \mathcal{P}((a, b))`.

Proof: The binary biproduct triangle $`X \to X \oplus Y \to Y \to X[1]` is distinguished, and the interval property is extension-closed.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_biprod}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_biprod&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_biprod%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_closedUnderBinaryProducts

The interval property $`\mathcal{P}((a, b))` is closed under binary products.

Proof: Follows from closure under binary biproducts via the isomorphism between categorical products and biproducts in a preadditive category.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_closedUnderBinaryProducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_closedUnderBinaryProducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_closedUnderBinaryProducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_closedUnderFiniteProducts

The interval property $`\mathcal{P}((a, b))` is closed under finite products.

Proof: Induction from closure under binary products and the zero object.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_closedUnderFiniteProducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_closedUnderFiniteProducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_closedUnderFiniteProducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_closedUnderIso

The interval property $`\mathcal{P}((a, b))` is closed under isomorphisms in $`\mathcal{C}`.

Proof: A zero object remains zero under isomorphism; an HN filtration transfers across an isomorphism of the base object.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_closedUnderIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_closedUnderIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_closedUnderIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_containsZero

The interval property $`\mathcal{P}((a, b))` contains the zero object, witnessed by the canonical zero of $`\mathcal{C}`.

Proof: Applies `intervalProp_of_isZero` to the canonical zero object.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_containsZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_containsZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_containsZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_mono

Narrower intervals are contained in wider ones: if $`a' \le a` and $`b \le b'`, then $`\mathcal{P}((a, b)) \subseteq \mathcal{P}((a', b'))`.

Proof: An HN filtration with all phases in $`(a, b)` automatically has all phases in the larger interval $`(a', b')`.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_isZero

Any zero object lies in every interval subcategory $`\mathcal{P}((a, b))`.

Proof: Immediate from the left disjunct of the interval property definition.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_of_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_of_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_semistable

A $`\sigma`-semistable object $`E \in \mathcal{P}(\phi)` with phase $`\phi \in (a, b)` lies in the interval subcategory $`\mathcal{P}((a, b))`.

Proof: If $`E` is zero this is trivial. Otherwise, semistability forces $`\phi^+(E) = \phi^-(E) = \phi`, so all HN phases lie in $`(a, b)` since $`a < \phi < b`.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_of_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_of_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_stableUnderRetracts

The interval property $`\mathcal{P}((a, b))` is stable under retracts: if $`X` is a retract of $`Y \in \mathcal{P}((a, b))`, then $`X \in \mathcal{P}((a, b))`.

Proof: If $`X` is zero, we are done. Otherwise, by contradiction: if $`\phi^+(X) \ge b`, the top HN factor of $`X` maps to zero through $`Y` (by hom-vanishing since all phases of $`Y` are $`< b`), and composing with the retraction forces it to map to zero through $`X` as well, contradicting non-triviality. A dual argument handles $`\phi^-(X) \le a`.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_stableUnderRetracts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_stableUnderRetracts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_stableUnderRetracts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
