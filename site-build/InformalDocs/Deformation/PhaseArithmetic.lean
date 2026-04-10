import BridgelandStability.Deformation.PhaseArithmetic
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: PhaseArithmetic" =>
%%%
htmlSplit := .never
%%%

# hperturb\_of\_stabSeminorm

Phase perturbation from stabSeminorm. If $`\|W - Z\|_\sigma < \sin(\pi\varepsilon_0)` and $`b - a < 1`, then for every nonzero $`\sigma`-semistable $`F` with phase $`\phi \in (a, b)`, the W-phase satisfies $`|\operatorname{wPhaseOf}(W(F), (a+b)/2) - \phi| < \varepsilon_0`.

Proof: The stabSeminorm bound gives $`\|(W-Z)(F)\| \le M \|Z(F)\|` with $`M < \sin(\pi\varepsilon_0)`. Since $`\phi \in (a, b)` and $`b - a < 1`, we have $`\phi \in ((a+b)/2 - 1/2, (a+b)/2 + 1/2)`. Apply `wPhaseOf_perturbation`.

{docstring CategoryTheory.Triangulated.hperturb_of_stabSeminorm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hperturb_of_stabSeminorm&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.hperturb_of_stabSeminorm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_W\_neg\_of\_intervalProp

Im negativity from HN factors. Dual of `im_W_pos_of_intervalProp`: if every factor has $`\operatorname{Im}(W(F_j) \cdot e^{-i\pi\psi}) < 0`, then $`\operatorname{Im}(W(E) \cdot e^{-i\pi\psi}) < 0`.

Proof: Negate and apply the same $`K_0` decomposition argument.

{docstring CategoryTheory.Triangulated.im_W_neg_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_W_neg_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_W_neg_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_W\_pos\_of\_intervalProp

Im positivity from HN factors. If $`E \in \mathcal{P}((a, b))` is nonzero and every nonzero $`\sigma`-semistable factor has $`\operatorname{Im}(W(F_j) \cdot e^{-i\pi\psi}) > 0`, then $`\operatorname{Im}(W(E) \cdot e^{-i\pi\psi}) > 0`.

Proof: Decompose $`W([E]) = \sum W([F_j])` via $`K_0` additivity. The imaginary part is additive, each term is positive, and the first nonzero factor gives strict positivity.

{docstring CategoryTheory.Triangulated.im_W_pos_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_W_pos_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_W_pos_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_eq\_zero\_of\_wPhaseOf\_eq

If $`\operatorname{wPhaseOf}(w, \alpha) = \psi`, then $`\operatorname{Im}(w \cdot e^{-i\pi\psi}) = 0`.

Proof: From the polar decomposition, $`w \cdot e^{-i\pi\psi} = \|w\|`, which is real.

{docstring CategoryTheory.Triangulated.im_eq_zero_of_wPhaseOf_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_eq_zero_of_wPhaseOf_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_eq_zero_of_wPhaseOf_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_mul\_exp\_neg\_eq\_norm\_mul\_sin

Rotated imaginary part identity. For any $`w \in \mathbb{C}` and $`\alpha, \psi \in \mathbb{R}`, $`\operatorname{Im}(w \cdot e^{-i\pi\psi}) = \|w\| \cdot \sin(\pi(\operatorname{wPhaseOf}(w, \alpha) - \psi))`.

Proof: Substitute the polar decomposition $`w = \|w\| \cdot e^{i\pi \cdot \operatorname{wPhaseOf}(w, \alpha)}` and simplify.

{docstring CategoryTheory.Triangulated.im_mul_exp_neg_eq_norm_mul_sin}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_mul_exp_neg_eq_norm_mul_sin&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_mul_exp_neg_eq_norm_mul_sin%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_neg\_of\_phase\_below

If $`w = m \cdot e^{i\pi\phi}` with $`m > 0` and $`\phi \in (\psi - 1, \psi)`, then $`\operatorname{Im}(w \cdot e^{-i\pi\psi}) < 0`. Dual of `im_pos_of_phase_above`.

Proof: After rotation, $`\operatorname{Im} = m \sin(\pi(\phi - \psi))`, and $`\sin < 0` on $`(-\pi, 0)`.

{docstring CategoryTheory.Triangulated.im_neg_of_phase_below}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_neg_of_phase_below&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_neg_of_phase_below%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_pos\_of\_phase\_above

If $`w = m \cdot e^{i\pi\phi}` with $`m > 0` and $`\phi \in (\psi, \psi + 1)`, then $`\operatorname{Im}(w \cdot e^{-i\pi\psi}) > 0`.

Proof: After rotation, $`\operatorname{Im} = m \sin(\pi(\phi - \psi))`, and $`\sin > 0` on $`(0, \pi)`.

{docstring CategoryTheory.Triangulated.im_pos_of_phase_above}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_pos_of_phase_above&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_pos_of_phase_above%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_pos\_of\_sum\_zero\_and\_neg

If $`w_1 + w_2 = w` and $`\operatorname{Im}(w \cdot e^{-i\pi\psi}) = 0` and $`\operatorname{Im}(w_2 \cdot e^{-i\pi\psi}) < 0`, then $`\operatorname{Im}(w_1 \cdot e^{-i\pi\psi}) > 0`.

Proof: Additivity of the imaginary part: $`\operatorname{Im}(w_1 \cdot r) = \operatorname{Im}(w \cdot r) - \operatorname{Im}(w_2 \cdot r) = 0 - (\text{negative}) > 0`.

{docstring CategoryTheory.Triangulated.im_pos_of_sum_zero_and_neg}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_pos_of_sum_zero_and_neg&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_pos_of_sum_zero_and_neg%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_sum\_neg\_of\_all\_neg

If each rotated vector $`f(i) \cdot e^{-i\pi\psi}` has strictly negative imaginary part, then so does the sum $`\bigl(\sum_{i\in s} f(i)\bigr)\cdot e^{-i\pi\psi}`. This is the dual of `im_sum_pos_of_all_pos` and is used to propagate phase-below bounds through $`K_0` decompositions.

Proof: The proof rewrites the imaginary part of the product-sum as a sum of imaginary parts (using additivity of $`\mathrm{Im}`) and then applies `Finset.sum_neg` to conclude from the pointwise negativity hypothesis.

{docstring CategoryTheory.Triangulated.im_sum_neg_of_all_neg}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_sum_neg_of_all_neg&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_sum_neg_of_all_neg%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_sum\_pos\_of\_all\_pos

If each rotated vector $`f(i) \cdot e^{-i\pi\psi}` has strictly positive imaginary part, then so does the sum $`\bigl(\sum_{i\in s} f(i)\bigr)\cdot e^{-i\pi\psi}`. This is used to propagate phase-above bounds through $`K_0` decompositions.

Proof: The proof rewrites the imaginary part of the product-sum as a sum of imaginary parts (using additivity of $`\mathrm{Im}`) and then applies `Finset.sum_pos` to conclude from the pointwise positivity hypothesis.

{docstring CategoryTheory.Triangulated.im_sum_pos_of_all_pos}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_sum_pos_of_all_pos&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_sum_pos_of_all_pos%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mem\_upperHalfPlaneUnion\_of\_arg\_pos

A nonzero complex number $`z` with $`\arg(z) > 0` lies in the upper half-plane union $`\{z : \mathrm{Im}(z) > 0\} \cup \{z : \mathrm{Im}(z) = 0,\, \mathrm{Re}(z) > 0\}`. This is the entry point connecting the argument condition to upper half-plane membership used in the W-phase comparison lemmas.

Proof: The proof splits on whether $`\mathrm{Im}(z) > 0` (then $`z` is in the open upper half-plane) or $`\mathrm{Im}(z) \le 0`. In the latter case, non-negativity of $`\arg(z)` forces $`\mathrm{Im}(z) = 0`, and the assumption $`\arg(z) > 0` then rules out $`\mathrm{Re}(z) \le 0` via `Complex.arg_eq_zero_iff`.

{docstring CategoryTheory.Triangulated.mem_upperHalfPlaneUnion_of_arg_pos}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mem_upperHalfPlaneUnion_of_arg_pos&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.mem_upperHalfPlaneUnion_of_arg_pos%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mem\_upperHalfPlaneUnion\_of\_wPhaseOf\_gt

If $`\psi < \mathrm{wPhaseOf}(w, \psi)`, then $`w \cdot e^{-i\pi\psi}` lies in the upper half-plane union. This is the converse of `wPhaseOf_gt_of_mem_upperHalfPlaneUnion`: the W-phase comparison is equivalent to upper half-plane membership of the rotated vector.

Proof: The proof unfolds the definition of $`\mathrm{wPhaseOf}` to read off that $`\arg(w \cdot e^{-i\pi\psi})/\pi > 0`, and then applies `mem_upperHalfPlaneUnion_of_arg_pos`.

{docstring CategoryTheory.Triangulated.mem_upperHalfPlaneUnion_of_wPhaseOf_gt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mem_upperHalfPlaneUnion_of_wPhaseOf_gt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.mem_upperHalfPlaneUnion_of_wPhaseOf_gt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_Z\_eq

Coarse phase perturbation bound. If $`E` is $`\sigma`-semistable of phase $`\phi \in (\alpha - 1, \alpha + 1]`, then $`\operatorname{wPhaseOf}(Z(E), \alpha) = \phi`.

Proof: From compatibility, $`Z(E) = m \cdot e^{i\pi\phi}` with $`m > 0`. Apply `wPhaseOf_of_exp`.

{docstring CategoryTheory.Triangulated.wPhaseOf_Z_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_Z_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_Z_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_gt\_of\_im\_pos

If $`\mathrm{Im}(w \cdot e^{-i\pi\psi}) > 0` and $`\mathrm{wPhaseOf}(w, \alpha) \in (\psi - 1, \psi + 1)`, then $`\mathrm{wPhaseOf}(w, \alpha) > \psi`. The range hypothesis rules out the aliased branch where $`\sin > 0` could arise from a phase difference in $`(-2, -1)`.

Proof: Assume for contradiction $`\mathrm{wPhaseOf}(w,\alpha) \le \psi`. Combined with the range hypothesis, the phase difference $`\mathrm{wPhaseOf}(w,\alpha) - \psi \in (-1, 0]`. The polar compatibility identity gives $`\mathrm{Im}(w \cdot e^{-i\pi\psi}) = \|w\| \cdot \sin(\pi(\mathrm{wPhaseOf} - \psi))`, and $`\sin \le 0` on $`(-\pi, 0]` yields a non-positive imaginary part, contradicting the hypothesis.

{docstring CategoryTheory.Triangulated.wPhaseOf_gt_of_im_pos}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_gt_of_im_pos&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_gt_of_im_pos%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_gt\_of\_intervalProp

W-phase lower bound for interval objects (Lemma 7.3(b)). If $`E \in \mathcal{P}((a, b))` is nonzero and every nonzero $`\sigma`-semistable factor of phase $`\phi \in (a, b)` has W-phase in $`(a - \varepsilon, a - \varepsilon + 1)`, then $`\operatorname{wPhaseOf}(W(E), \alpha) > a - \varepsilon`.

Proof: Each factor has $`\operatorname{Im}(W(F) \cdot e^{-i\pi(a-\varepsilon)}) > 0` (from the phase window). By $`K_0` decomposition, $`\operatorname{Im}(W(E) \cdot e^{-i\pi(a-\varepsilon)}) > 0`. A contrapositive sin-sign argument converts this to a phase lower bound.

{docstring CategoryTheory.Triangulated.wPhaseOf_gt_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_gt_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_gt_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_gt\_of\_mem\_upperHalfPlaneUnion

If $`w \cdot e^{-i\pi\psi}` lies in the upper half-plane union, then $`\psi < \mathrm{wPhaseOf}(w, \psi)`. Together with `mem_upperHalfPlaneUnion_of_wPhaseOf_gt`, this gives an equivalence between upper half-plane membership of the rotated vector and $`\mathrm{wPhaseOf}(w, \psi) > \psi`.

Proof: The proof extracts $`\arg(w \cdot e^{-i\pi\psi}) > 0` from the upper half-plane union membership via `arg_pos_of_mem_upperHalfPlaneUnion`, then converts to $`\mathrm{wPhaseOf} > \psi` by dividing by $`\pi > 0` and unfolding the definition.

{docstring CategoryTheory.Triangulated.wPhaseOf_gt_of_mem_upperHalfPlaneUnion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_gt_of_mem_upperHalfPlaneUnion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_gt_of_mem_upperHalfPlaneUnion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_lt\_of\_add\_le\_gt

If $`w = w_1 + w_2`, the total W-phase $`\mathrm{wPhaseOf}(w, \alpha) \le \psi`, one summand satisfies $`\mathrm{wPhaseOf}(w_1, \alpha) > \psi` (with $`w_1 \ne 0` and both summands in the branch window $`(\psi - 1, \psi + 1)`), then the other summand satisfies $`\mathrm{wPhaseOf}(w_2, \alpha) < \psi`. This is the one-sided source-envelope phase seesaw: a super-phase summand forces the complementary summand to be sub-phase.

Proof: Rotating by $`e^{-i\pi\psi}`: $`\mathrm{Im}(w \cdot \mathrm{rot}) \le 0` (from the phase $`\le \psi` condition and the range hypothesis), $`\mathrm{Im}(w_1 \cdot \mathrm{rot}) > 0` (from $`w_1 \ne 0` and phase $`> \psi`), so by additivity of $`\mathrm{Im}` we get $`\mathrm{Im}(w_2 \cdot \mathrm{rot}) < 0`. Then `wPhaseOf_lt_of_im_neg` concludes.

{docstring CategoryTheory.Triangulated.wPhaseOf_lt_of_add_le_gt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_lt_of_add_le_gt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_lt_of_add_le_gt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_lt\_of\_add\_le\_lt

If $`w = w_1 + w_2` where $`\mathrm{wPhaseOf}(w_1, \alpha) \in (\psi - 1, \psi]` and $`\mathrm{wPhaseOf}(w_2, \alpha) < \psi` with $`w_2 \ne 0`, and the total W-phase $`\mathrm{wPhaseOf}(w, \alpha)` lies in $`(\psi - 1, \psi + 1)`, then $`\mathrm{wPhaseOf}(w, \alpha) < \psi`. Both summands being sub-phase (with $`w_1` weakly so and $`w_2` strictly) forces the total phase to be strictly below $`\psi`.

Proof: Rotating by $`e^{-i\pi\psi}`: $`\mathrm{Im}(w_1 \cdot \mathrm{rot}) \le 0` (from the phase $`\le \psi` constraint and the range), $`\mathrm{Im}(w_2 \cdot \mathrm{rot}) < 0` (from $`w_2 \ne 0` and strict phase $`< \psi`), so $`\mathrm{Im}(w \cdot \mathrm{rot}) < 0` by additivity. Then `wPhaseOf_lt_of_im_neg` and the range hypothesis conclude.

{docstring CategoryTheory.Triangulated.wPhaseOf_lt_of_add_le_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_lt_of_add_le_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_lt_of_add_le_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_lt\_of\_im\_neg

If $`\mathrm{Im}(w \cdot e^{-i\pi\psi}) < 0` and $`\mathrm{wPhaseOf}(w, \alpha) \in (\psi - 1, \psi + 1)`, then $`\mathrm{wPhaseOf}(w, \alpha) < \psi`. This is the dual of `wPhaseOf_gt_of_im_pos`.

Proof: Assume for contradiction $`\psi \le \mathrm{wPhaseOf}(w,\alpha)`. Combined with the range hypothesis, the phase difference lies in $`[0, 1)` so $`\sin(\pi(\mathrm{wPhaseOf} - \psi)) \ge 0`. The polar compatibility identity then gives $`\mathrm{Im}(w \cdot e^{-i\pi\psi}) = \|w\| \cdot \sin(\ldots) \ge 0`, contradicting the hypothesis.

{docstring CategoryTheory.Triangulated.wPhaseOf_lt_of_im_neg}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_lt_of_im_neg&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_lt_of_im_neg%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_lt\_of\_intervalProp

W-phase upper bound for interval objects. Dual of `wPhaseOf_gt_of_intervalProp`: if every factor has W-phase in $`(b + \varepsilon - 1, b + \varepsilon)`, then $`\operatorname{wPhaseOf}(W(E), \alpha) < b + \varepsilon`.

Proof: Each factor has $`\operatorname{Im}(W(F) \cdot e^{-i\pi(b+\varepsilon)}) < 0`. By $`K_0` decomposition, $`\operatorname{Im}(W(E) \cdot e^{-i\pi(b+\varepsilon)}) < 0`, giving the upper phase bound.

{docstring CategoryTheory.Triangulated.wPhaseOf_lt_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_lt_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_lt_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_perturbation

Phase perturbation for $`\sigma`-semistable objects. If $`E` is $`\sigma`-semistable of phase $`\phi \in (\alpha - 1/2, \alpha + 1/2)` and $`\|(W-Z)(E)\| / \|Z(E)\| < \sin(\pi\varepsilon)` with $`0 < \varepsilon \le 1/2`, then $`|\operatorname{wPhaseOf}(W(E), \alpha) - \phi| < \varepsilon`.

Proof: Write $`W(E) = Z(E) + \delta = m \cdot e^{i\pi\phi}(1 + u)` where $`u = \delta / Z(E)`. The bound $`\|u\| < \sin(\pi\varepsilon)` follows from the seminorm estimate. Apply `wPhaseOf_perturbation_generic`.

{docstring CategoryTheory.Triangulated.wPhaseOf_perturbation}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_perturbation&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_perturbation%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_seesaw

Phase see-saw. If $`w = w_1 + w_2` with $`\operatorname{wPhaseOf}(w, \alpha) = \psi`, $`\operatorname{wPhaseOf}(w_1, \alpha) \in (\psi - 1, \psi]`, and $`w_2 \ne 0` with $`\operatorname{wPhaseOf}(w_2, \alpha) \in (\psi - 1, \psi + 1)`, then $`\operatorname{wPhaseOf}(w_2, \alpha) \ge \psi`.

Proof: By the imaginary-part sign argument: $`\operatorname{Im}(w \cdot r) = 0` (phase $`= \psi`), $`\operatorname{Im}(w_1 \cdot r) \le 0` (phase $`\le \psi`). If $`\operatorname{wPhaseOf}(w_2) < \psi`, then $`\operatorname{Im}(w_2 \cdot r) < 0`, giving $`\operatorname{Im}(w \cdot r) < 0`, a contradiction.

{docstring CategoryTheory.Triangulated.wPhaseOf_seesaw}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_seesaw&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_seesaw%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_seesaw\_dual

Dual strict phase see-saw. If $`w = w_1 + w_2` with $`\operatorname{wPhaseOf}(w, \alpha) = \psi` and $`\operatorname{wPhaseOf}(w_1, \alpha) > \psi`, then $`\operatorname{wPhaseOf}(w_2, \alpha) < \psi`.

Proof: $`\operatorname{Im}(w_1 \cdot r) > 0` and $`\operatorname{Im}(w_2 \cdot r) \ge 0` would give $`\operatorname{Im}(w \cdot r) > 0`, contradicting phase $`= \psi`.

{docstring CategoryTheory.Triangulated.wPhaseOf_seesaw_dual}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_seesaw_dual&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_seesaw_dual%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_seesaw\_strict

Strict phase see-saw. If $`w = w_1 + w_2` with $`\operatorname{wPhaseOf}(w, \alpha) = \psi`, $`\operatorname{wPhaseOf}(w_2, \alpha) < \psi`, $`w_2 \ne 0`, and both summands in the branch window $`(\psi - 1, \psi + 1)`, then $`\operatorname{wPhaseOf}(w_1, \alpha) > \psi`.

Proof: Dual of `wPhaseOf_seesaw`: $`\operatorname{Im}(w_2 \cdot r) < 0` forces $`\operatorname{Im}(w_1 \cdot r) > 0`, hence phase $`> \psi`.

{docstring CategoryTheory.Triangulated.wPhaseOf_seesaw_strict}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_seesaw_strict&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_seesaw_strict%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_sum\_gt

W-phase lower bound for sums. If complex numbers $`w_1, \ldots, w_n` all have $`\operatorname{wPhaseOf}(w_j, \psi) > \psi`, then their sum satisfies $`\operatorname{wPhaseOf}(\sum w_j, \psi) > \psi`.

Proof: Rotate by $`e^{-i\pi\psi}`: each $`w_j \cdot e^{-i\pi\psi}` lies in the upper half-plane (since phase $`> \psi`). The upper half-plane is closed under addition, so the sum lies there too, giving phase $`> \psi`.

{docstring CategoryTheory.Triangulated.wPhaseOf_sum_gt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_sum_gt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_sum_gt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseArithmetic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
