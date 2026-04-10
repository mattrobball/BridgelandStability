import BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "ForMathlib: Analysis.SpecialFunctions.Complex.ArgConvexity" =>
%%%
htmlSplit := .never
%%%

# arg\_add\_le\_max

For $`z_1, z_2` in the semi-closed upper half plane, $`\arg(z_1 + z_2) \leq \max(\arg z_1, \arg z_2)`. This is the key analytical bound ensuring the phase of an extension is bounded by the phases of its subobjects.

Proof: WLOG $`\arg z_1 \leq \arg z_2`. Show $`\arg(z_1+z_2) \leq \arg z_2` via the cross-product criterion `arg_le_of_cross_nonneg`: the cross product $`(z_1+z_2).\mathrm{re} \cdot z_2.\mathrm{im} - (z_1+z_2).\mathrm{im} \cdot z_2.\mathrm{re}` equals $`z_1.\mathrm{re} \cdot z_2.\mathrm{im} - z_1.\mathrm{im} \cdot z_2.\mathrm{re} \geq 0` by `cross_nonneg_of_arg_le`.

{docstring CategoryTheory.arg_add_le_max}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20arg_add_le_max&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.arg_add_le_max%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# arg\_add\_lt\_max

For $`z_1, z_2` in the semi-closed upper half plane with $`\arg z_1 \neq \arg z_2`, the strict inequality $`\arg(z_1 + z_2) < \max(\arg z_1, \arg z_2)` holds.

Proof: WLOG $`\arg z_1 < \arg z_2`. Then the cross product $`z_1.\mathrm{re} \cdot z_2.\mathrm{im} - z_1.\mathrm{im} \cdot z_2.\mathrm{re} > 0` by `cross_pos_of_arg_lt`, and the self-cancellation identity shows the cross product of $`(z_1+z_2)` with $`z_2` is the same positive quantity, giving $`\arg(z_1+z_2) < \arg z_2` via `arg_lt_of_cross_pos`.

{docstring CategoryTheory.arg_add_lt_max}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20arg_add_lt_max&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.arg_add_lt_max%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# arg\_le\_of\_cross\_nonneg

If $`z_1, z_2 \neq 0`, $`\arg z_2 > 0`, and the cross product $`z_1.\mathrm{re} \cdot z_2.\mathrm{im} - z_1.\mathrm{im} \cdot z_2.\mathrm{re} \geq 0`, then $`\arg z_1 \leq \arg z_2`.

Proof: Write the cross product as $`\|z_1\| \|z_2\| \sin(\arg z_2 - \arg z_1)`. If $`\arg z_1 > \arg z_2` then $`\arg z_2 - \arg z_1 < 0` and $`> -\pi`, so $`\sin < 0`, contradicting the nonnegativity.

{docstring CategoryTheory.arg_le_of_cross_nonneg}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20arg_le_of_cross_nonneg&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.arg_le_of_cross_nonneg%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# arg\_lt\_of\_cross\_pos

If $`z_1, z_2 \neq 0`, $`\arg z_2 > 0`, and the cross product $`z_1.\mathrm{re} \cdot z_2.\mathrm{im} - z_1.\mathrm{im} \cdot z_2.\mathrm{re} > 0`, then $`\arg z_1 < \arg z_2`.

Proof: The cross product equals $`\|z_1\|\|z_2\| \sin(\arg z_2 - \arg z_1) > 0`, so $`\sin(\arg z_2 - \arg z_1) > 0`, which forces $`\arg z_2 - \arg z_1 \in (0, \pi)`, i.e., $`\arg z_1 < \arg z_2`.

{docstring CategoryTheory.arg_lt_of_cross_pos}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20arg_lt_of_cross_pos&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.arg_lt_of_cross_pos%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# arg\_pos\_of\_mem\_upperHalfPlaneUnion

Every element of the semi-closed upper half plane $`\{\mathrm{Im}(z) > 0\} \cup \{\mathrm{Im}(z) = 0, \mathrm{Re}(z) < 0\}` has strictly positive argument $`\arg(z) > 0`.

Proof: In the strict upper half plane, $`\arg \geq 0` and $`\arg = 0 \Rightarrow \mathrm{Im} = 0`, contradiction. On the negative real axis, $`\arg = \pi > 0`.

{docstring CategoryTheory.arg_pos_of_mem_upperHalfPlaneUnion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20arg_pos_of_mem_upperHalfPlaneUnion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.arg_pos_of_mem_upperHalfPlaneUnion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# arg\_sum\_le\_sup'\_of\_upperHalfPlane

If $`f(i) \in \overline{\mathbb{H}}` for all $`i \in s`, then $`\arg\bigl(\sum_{i \in s} f(i)\bigr) \leq \sup_{i \in s} \arg(f(i))`.

Proof: Induction on $`s` using `Finset.Nonempty.cons_induction`, applying `arg_add_le_max` at each step and using `sum_mem_upperHalfPlane` to maintain the membership condition.

{docstring CategoryTheory.arg_sum_le_sup'_of_upperHalfPlane}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20arg_sum_le_sup%27_of_upperHalfPlane&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.arg_sum_le_sup%27_of_upperHalfPlane%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cross\_eq\_norm\_mul\_sin

The 2D cross product satisfies $`z_1.\mathrm{re} \cdot z_2.\mathrm{im} - z_1.\mathrm{im} \cdot z_2.\mathrm{re} = \|z_1\| \cdot \|z_2\| \cdot \sin(\arg z_2 - \arg z_1)`.

Proof: Substitute the polar decompositions $`z_j = \|z_j\|(\cos(\arg z_j) + i\sin(\arg z_j))` and apply the sine subtraction formula.

{docstring CategoryTheory.cross_eq_norm_mul_sin}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cross_eq_norm_mul_sin&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.cross_eq_norm_mul_sin%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cross\_nonneg\_of\_arg\_le

If $`z_1.\mathrm{im} \geq 0`, $`z_1, z_2 \neq 0`, and $`\arg z_1 \leq \arg z_2`, then $`z_1.\mathrm{re} \cdot z_2.\mathrm{im} - z_1.\mathrm{im} \cdot z_2.\mathrm{re} \geq 0`.

Proof: The cross product equals $`\|z_1\|\|z_2\|\sin(\arg z_2 - \arg z_1)`. Since $`\arg z_2 - \arg z_1 \in [0, \pi]` (using $`\arg z_1 \geq 0` from $`z_1.\mathrm{im} \geq 0`), $`\sin \geq 0`.

{docstring CategoryTheory.cross_nonneg_of_arg_le}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cross_nonneg_of_arg_le&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.cross_nonneg_of_arg_le%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cross\_pos\_of\_arg\_lt

If $`\arg z_1 > 0`, $`z_1, z_2 \neq 0`, and $`\arg z_1 < \arg z_2`, then the cross product $`z_1.\mathrm{re} \cdot z_2.\mathrm{im} - z_1.\mathrm{im} \cdot z_2.\mathrm{re} > 0`.

Proof: The cross product equals $`\|z_1\|\|z_2\|\sin(\arg z_2 - \arg z_1) > 0` since $`\arg z_2 - \arg z_1 \in (0, \pi)` (using $`\arg z_1 > 0` and $`\arg z_2 \leq \pi`).

{docstring CategoryTheory.cross_pos_of_arg_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cross_pos_of_arg_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.cross_pos_of_arg_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_nonneg\_of\_mem\_upperHalfPlaneUnion

Every element of the semi-closed upper half plane $`\{\mathrm{Im}(z) > 0\} \cup \{\mathrm{Im}(z) = 0, \mathrm{Re}(z) < 0\}` has nonneg imaginary part.

Proof: Immediate from the two cases in the definition of `upperHalfPlaneUnion`.

{docstring CategoryTheory.im_nonneg_of_mem_upperHalfPlaneUnion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_nonneg_of_mem_upperHalfPlaneUnion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.im_nonneg_of_mem_upperHalfPlaneUnion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# inf'\_le\_arg\_sum\_of\_upperHalfPlane

If $`f(i) \in \overline{\mathbb{H}}` for all $`i \in s`, then $`\inf_{i \in s} \arg(f(i)) \leq \arg\bigl(\sum_{i \in s} f(i)\bigr)`. This is the dual lower bound to `arg_sum_le_sup'_of_upperHalfPlane`.

Proof: Induction on $`s` using `Finset.Nonempty.cons_induction`, applying `min_arg_le_arg_add` at each step.

{docstring CategoryTheory.inf'_le_arg_sum_of_upperHalfPlane}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20inf%27_le_arg_sum_of_upperHalfPlane&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.inf%27_le_arg_sum_of_upperHalfPlane%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mem\_upperHalfPlaneUnion\_of\_add

The semi-closed upper half plane is closed under addition: if $`z_1, z_2 \in \overline{\mathbb{H}}`, then $`z_1 + z_2 \in \overline{\mathbb{H}}`.

Proof: Case split: if either $`\mathrm{Im}(z_j) > 0`, the sum has positive imaginary part. Otherwise both lie on the negative real axis, so the sum has $`\mathrm{Im} = 0` and $`\mathrm{Re} < 0`.

{docstring CategoryTheory.mem_upperHalfPlaneUnion_of_add}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mem_upperHalfPlaneUnion_of_add&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.mem_upperHalfPlaneUnion_of_add%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# min\_arg\_le\_arg\_add

For $`z_1, z_2` in the semi-closed upper half plane, $`\min(\arg z_1, \arg z_2) \leq \arg(z_1 + z_2)`. This is the lower companion to `arg_add_le_max`.

Proof: WLOG $`\arg z_1 \leq \arg z_2`. Show $`\arg z_1 \leq \arg(z_1+z_2)` via `arg_le_of_cross_nonneg` applied to the cross product of $`z_1` with $`z_1+z_2`, which self-cancels to $`z_1.\mathrm{re} \cdot z_2.\mathrm{im} - z_1.\mathrm{im} \cdot z_2.\mathrm{re} \geq 0`.

{docstring CategoryTheory.min_arg_le_arg_add}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20min_arg_le_arg_add&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.min_arg_le_arg_add%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# min\_arg\_lt\_arg\_add

For $`z_1, z_2` in the semi-closed upper half plane with $`\arg z_1 \neq \arg z_2`, the strict lower bound $`\min(\arg z_1, \arg z_2) < \arg(z_1 + z_2)` holds.

Proof: WLOG $`\arg z_1 < \arg z_2`. The cross product of $`z_1` with $`z_1 + z_2` equals the original cross product $`> 0` by `cross_pos_of_arg_lt`, giving $`\arg z_1 < \arg(z_1+z_2)` via `arg_lt_of_cross_pos`.

{docstring CategoryTheory.min_arg_lt_arg_add}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20min_arg_lt_arg_add&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.min_arg_lt_arg_add%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# sum\_mem\_upperHalfPlane

A nonempty finite sum of elements of the semi-closed upper half plane again lies in the semi-closed upper half plane.

Proof: Induction on the finite set using `mem_upperHalfPlaneUnion_of_add`.

{docstring CategoryTheory.sum_mem_upperHalfPlane}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20sum_mem_upperHalfPlane&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.sum_mem_upperHalfPlane%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# upperHalfPlaneUnion

Bridgeland's semi-closed upper half plane: the set $`\{z \in \mathbb{C} \mid \mathrm{Im}(z) > 0\} \cup \{z \in \mathbb{C} \mid \mathrm{Im}(z) = 0,\ \mathrm{Re}(z) < 0\}`. For $`z` in this set, $`\arg(z) \in (0, \pi]`, matching Bridgeland's condition $`Z(E) \in \mathbb{H} \cup \mathbb{R}_{<0}`.

Construction: The union of the open upper half plane and the open negative real axis, as a subset of $`\mathbb{C}`.


{docstring CategoryTheory.upperHalfPlaneUnion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20upperHalfPlaneUnion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.upperHalfPlaneUnion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# upperHalfPlaneUnion\_ne\_zero

Every element of the semi-closed upper half plane is nonzero.

Proof: In the upper half plane case, $`\mathrm{Im}(z) > 0 \neq 0`; on the negative real axis, $`\mathrm{Re}(z) < 0 \neq 0`.

{docstring CategoryTheory.upperHalfPlaneUnion_ne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20upperHalfPlaneUnion_ne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.upperHalfPlaneUnion_ne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
