import BridgelandStability.IntervalCategory.TwoHeartEmbedding
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "IntervalCategory: TwoHeartEmbedding" =>
%%%
htmlSplit := .never
%%%

# toLeftHeart

The fully faithful embedding $`\mathcal{P}((a,b)) \hookrightarrow \mathcal{P}((a, a+1])` into the left abelian heart.

Construction: Maps objects by packaging the left-heart membership proof from `intervalProp_implies_leftHeart`, and maps morphisms by unwrapping to the underlying hom in $`\mathcal{C}`.


{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toLeftHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toLeftHeart\_faithful

The left heart embedding $`\mathcal{P}((a,b)) \to \mathcal{P}((a, a+1])` is faithful.

Proof: Injectivity on hom-sets is immediate since the functor acts as the identity on underlying morphisms.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_faithful}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toLeftHeart_faithful&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_faithful%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toLeftHeart\_full

The left heart embedding $`\mathcal{P}((a,b)) \to \mathcal{P}((a, a+1])` is full.

Proof: Every morphism in the heart between objects from $`\mathcal{P}((a,b))` is already a morphism in $`\mathcal{C}` between those objects.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_full}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toLeftHeart_full&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_full%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toRightHeart

The fully faithful embedding $`\mathcal{P}((a,b)) \hookrightarrow \mathcal{P}([b-1, b))` into the right abelian heart.

Construction: Maps objects by packaging the right-heart membership proof from `intervalProp_implies_rightHeart`, and maps morphisms by unwrapping to the underlying hom in $`\mathcal{C}`.


{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toRightHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toRightHeart\_faithful

The right heart embedding $`\mathcal{P}((a,b)) \to \mathcal{P}([b-1, b))` is faithful.

Proof: Injectivity on hom-sets is immediate since the functor acts as the identity on underlying morphisms.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_faithful}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toRightHeart_faithful&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_faithful%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toRightHeart\_full

The right heart embedding $`\mathcal{P}((a,b)) \to \mathcal{P}([b-1, b))` is full.

Proof: Every morphism in the heart between objects from $`\mathcal{P}((a,b))` is already a morphism in $`\mathcal{C}` between those objects.

{docstring CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_full}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toRightHeart_full&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_full%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# first\_intervalProp\_of\_triangle

Kernel/image containment in thin intervals. In a distinguished triangle $`K \to E \to Q \to K[1]` where $`E \in \mathcal{P}((a,b))`, $`Q` satisfies $`\operatorname{leProp}(a+1)`, and $`K` satisfies $`\operatorname{gtProp}(a)`, then $`K \in \mathcal{P}((a, b))`.

Proof: The upper bound $`\phi^+(K) < b` comes from `phiPlus_lt_of_triangle_with_leProp` (with $`c = a + 1 < b + 1`). The lower bound $`\phi^-(K) > a` comes from $`\operatorname{gtProp}(a)`. Together these place all HN phases in $`(a, b)`.

{docstring CategoryTheory.Triangulated.Slicing.first_intervalProp_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20first_intervalProp_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.first_intervalProp_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_of\_intervalProp

If all HN phases of $`E` lie in $`(a, b)`, then $`\phi^-(E) > a`, i.e.\ $`E` satisfies $`\operatorname{gtProp}(a)`.

Proof: The bottom HN factor has phase $`> a` by the interval membership condition, and the zero case is trivial.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_extension\_closed

The interval subcategory $`\mathcal{P}((a,b))` is extension-closed in the triangulated category: if $`A, B \in \mathcal{P}((a,b))` and $`A \to E \to B \to A[1]` is distinguished, then $`E \in \mathcal{P}((a,b))`.

Proof: Follows from the general extension closure for the interval property of a slicing.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_extension_closed}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_extension_closed&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_extension_closed%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_implies\_leftHeart

Left heart containment (Lemma 4.3a). If $`b - a \le 1` and $`E \in \mathcal{P}((a, b))`, then $`E` lies in the heart of the t-structure induced by the slicing shifted by $`a`. This heart is the half-open interval $`\mathcal{P}((a, a+1])`.

Proof: Phases in $`(a, b)` satisfy $`> a` (giving $`\operatorname{gtProp}(0)` after shifting) and $`< b \le a + 1` (giving $`\operatorname{leProp}(1)` after shifting). These are exactly the heart membership conditions for the shifted t-structure.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_implies_leftHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_implies_leftHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_implies_leftHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_implies\_rightHeart

Right heart containment (Lemma 4.3b). If $`b - a \le 1` and $`E \in \mathcal{P}((a, b))`, then $`E` lies in the heart of the dual t-structure induced by the slicing shifted by $`b - 1`. This heart is the half-open interval $`\mathcal{P}([b-1, b))`.

Proof: Phases in $`(a, b)` satisfy $`\ge b - 1` (since $`a \le b - 1` when $`b - a \le 1`, and all phases are $`> a`) and $`< b` (directly from the interval condition). Together with left heart containment, this establishes the two-heart embedding: every object in a thin interval lies in both an abelian heart controlling kernels and one controlling cokernels.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_implies_rightHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_implies_rightHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_implies_rightHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_implies\_rightWindow

If $`b - a \le 1` and $`E \in \mathcal{P}((a, b))`, then $`E` satisfies the phase-window conditions $`\operatorname{geProp}(b - 1)` and $`\operatorname{ltProp}(b)`, placing it in the half-open interval $`[b-1, b)`.

Proof: The $`\operatorname{geProp}(b-1)` bound follows from $`\operatorname{gtProp}(a)` and $`a \ge b - 1`. The $`\operatorname{ltProp}(b)` bound is direct from interval membership.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_implies_rightWindow}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_implies_rightWindow&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_implies_rightWindow%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_epi\_rightHeart

If $`f : X \to Y` is an epimorphism in the right heart $`\mathcal{P}([b-1, b))` and $`X \in \mathcal{P}((a, b))`, then $`Y \in \mathcal{P}((a, b))`. This is the cokernel-side closure from Bridgeland Lemma 4.2.

Proof: In the abelian heart, the kernel $`K` of $`f` exists and the SES lifts to a distinguished triangle. Since $`K` has $`\operatorname{geProp}(b-1)` from right heart membership and $`Y` has $`\operatorname{ltProp}(b)`, `third_intervalProp_of_triangle` gives $`Y \in \mathcal{P}((a,b))`.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_of_epi_rightHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_epi_rightHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_of_epi_rightHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_mono\_leftHeart

If $`f : X \to Y` is a monomorphism in the left heart $`\mathcal{P}((a, a+1])` and $`Y \in \mathcal{P}((a, b))`, then $`X \in \mathcal{P}((a, b))`. This is the kernel-side closure from Bridgeland Lemma 4.2.

Proof: In the abelian heart, the cokernel $`Q` of $`f` exists and the SES $`X \hookrightarrow Y \twoheadrightarrow Q` lifts to a distinguished triangle. Since $`Q` is in the heart with $`\operatorname{leProp}(a+1)` and $`X` has $`\operatorname{gtProp}(a)` from heart membership, `first_intervalProp_of_triangle` applies.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_of_mono_leftHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_mono_leftHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_of_mono_leftHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_of\_intervalProp

If all HN phases of $`E` lie in $`(a, b)`, then $`\phi^+(E) \le b`, i.e.\ $`E` satisfies $`\operatorname{leProp}(b)`.

Proof: The top HN factor has phase $`< b \le b` by the interval membership condition.

{docstring CategoryTheory.Triangulated.Slicing.leProp_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_ge\_of\_semistable\_triangle

Phase lower bound from Lemma 3.4. In a distinguished triangle $`K \to F \to Q \to K[1]` with $`F \in \mathcal{P}(\phi)` semistable and $`K, Q \in \mathcal{P}((a, b))` with $`b \le a + 1`, if $`Q` is nonzero then $`\phi \le \phi^-(Q)`.

Proof: Since $`F` is semistable, $`\phi^-(F) = \phi`. The result then follows from the general triangle phase bound `phiMinus_triangle_le`.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_ge_of_semistable_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_ge_of_semistable_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_ge_of_semistable_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_gt\_of\_triangle\_with\_geProp

Phase lower bound from non-strict one-sided containment. In a triangle $`K \to E \to Q \to K[1]`, if $`\phi^-(E) > a` and $`K` satisfies $`\operatorname{geProp}(c)` (phases $`\ge c`) with $`a < c + 1`, then if $`Q` is nonzero, $`a < \phi^-(Q)`.

Proof: Same strategy as `phiMinus_gt_of_triangle_with_gtProp`, but with the non-strict bound $`\operatorname{geProp}` instead of $`\operatorname{gtProp}`. The shifted filtration of $`K[1]` has phases $`\ge c + 1 > a`, still providing the hom-vanishing gap.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_triangle_with_geProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_gt_of_triangle_with_geProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_triangle_with_geProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_gt\_of\_triangle\_with\_gtProp

Phase lower bound from one-sided containment (dual). In a triangle $`K \to E \to Q \to K[1]`, if $`\phi^-(E) > a` and $`K` satisfies $`\operatorname{gtProp}(c)` with $`a < c + 1`, then if $`Q` is nonzero, $`a < \phi^-(Q)`.

Proof: Dual of `phiPlus_lt_of_triangle_with_leProp`. By contradiction: if the bottom HN factor of $`Q` has phase $`\le a`, then $`E \to \text{bottom factor}` vanishes by hom-vanishing, and the Yoneda exact sequence forces the map to factor through $`K[1]`. Since $`K[1]`'s phases are $`> c + 1 > a`, this factoring also vanishes, contradicting non-triviality.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_triangle_with_gtProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_gt_of_triangle_with_gtProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_triangle_with_gtProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_le\_of\_semistable\_triangle

Phase upper bound from Lemma 3.4. In a distinguished triangle $`K \to F \to Q \to K[1]` with $`F \in \mathcal{P}(\phi)` semistable and $`K, Q \in \mathcal{P}((a, b))` with $`b \le a + 1` and $`\phi \in (a, b)`, if $`K` is nonzero then $`\phi^+(K) \le \phi`.

Proof: Since $`F` is semistable, $`\phi^+(F) = \phi`. The result then follows from the general triangle phase bound `phiPlus_triangle_le`.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_le_of_semistable_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_le_of_semistable_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_le_of_semistable_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_lt\_of\_triangle\_with\_leProp

Phase upper bound from one-sided containment. In a triangle $`K \to E \to Q \to K[1]`, if $`\phi^+(E) < b` and $`Q` satisfies $`\operatorname{leProp}(c)` with $`c < b + 1`, then if $`K` is nonzero, $`\phi^+(K) < b`.

Proof: By contradiction: if the top HN factor of $`K` has phase $`\ge b`, it maps to zero in both $`E` (by hom-vanishing, since $`E`'s phases are $`< b`) and $`Q[-1]` (since $`Q[-1]`'s phases are $`\le c - 1 < b`). The coyoneda exact sequence on the inverse-rotated triangle forces the map to factor through both, giving zero, contradicting non-triviality of the factor.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_triangle_with_leProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_lt_of_triangle_with_leProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_triangle_with_leProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# third\_intervalProp\_of\_triangle

Cokernel/quotient containment in thin intervals (Lemma 4.3 dual). In a distinguished triangle $`K \to E \to Q \to K[1]` where $`E \in \mathcal{P}((a,b))`, $`K` has $`\operatorname{geProp}(b-1)`, and $`Q` has $`\operatorname{ltProp}(b)`, then $`Q \in \mathcal{P}((a, b))`.

Proof: The upper bound $`\phi^+(Q) < b` is immediate from $`\operatorname{ltProp}(b)`. The lower bound $`\phi^-(Q) > a` comes from `phiMinus_gt_of_triangle_with_geProp` with $`c = b - 1` (so $`a < (b-1) + 1 = b`). Together with `first_intervalProp_of_triangle`, this establishes the quasi-abelian structure of $`\mathcal{P}((a,b))`.

{docstring CategoryTheory.Triangulated.Slicing.third_intervalProp_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20third_intervalProp_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.third_intervalProp_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.IntervalCategory.TwoHeartEmbedding%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
