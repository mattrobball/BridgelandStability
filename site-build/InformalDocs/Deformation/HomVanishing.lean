import BridgelandStability.Deformation.HomVanishing
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: HomVanishing" =>
%%%
htmlSplit := .never
%%%

# deformedPred

Deformed slicing predicate (Node 7.Q). Given a stability condition $`\sigma`, a perturbation $`W` with $`\|W - Z\|_\sigma < 1`, the deformed slicing $`Q(\psi)` consists of zero objects and objects that are W-semistable of W-phase $`\psi` in some thin interval $`\mathcal{P}((a, b))` with $`b - a + 2\varepsilon_0 < 1` and the enveloping condition $`a + \varepsilon_0 \le \psi \le b - \varepsilon_0`.

Construction: Defined as a disjunction: either $`E` is zero, or there exist $`a < b` with the thinness and enveloping constraints such that $`E` is W-semistable of phase $`\psi` in $`\mathcal{P}((a, b))`.


{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedPred&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedPred\_closedUnderIso

The deformed predicate $`Q(\psi)` is closed under isomorphisms.

Proof: Transport the interval membership, W-nonvanishing, phase equality, and semistability condition across the isomorphism using $`K_0` invariance and HN filtration transport.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_closedUnderIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedPred_closedUnderIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_closedUnderIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedPred\_zero

Zero objects lie in every $`Q(\psi)`.

Proof: Immediate from the left disjunct of the deformed predicate.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedPred_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_eq\_zero\_of\_deformedPred

Sharp hom-vanishing for $`Q` (Bridgeland's Lemma 7.6). If $`E \in Q(\psi_1)` and $`F \in Q(\psi_2)` with $`\psi_1 > \psi_2`, then every morphism $`E \to F` is zero.

Proof: Two cases. \*\*Large gap\*\* ($`\psi_1 > \psi_2 + 2\varepsilon_0`): phase confinement puts $`E` and $`F` in disjoint $`\sigma`-intervals, so interval hom-vanishing applies. \*\*Small gap\*\* ($`\psi_1 - \psi_2 \le 2\varepsilon_0`): embed both in the abelian heart $`\mathcal{P}((c, c+1])` of a $`\sigma`-t-structure. Factor $`f` as $`E \twoheadrightarrow \operatorname{im}(f) \hookrightarrow F`. The $`K_0` identity $`W(E) = W(\ker f) + W(\operatorname{im} f)` with $`\operatorname{wPhaseOf}(W(\operatorname{im} f)) \le \psi_2 < \psi_1` forces $`\operatorname{wPhaseOf}(W(\ker f)) > \psi_1`, contradicting $`E`'s W-semistability.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_deformedPred}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_eq_zero_of_deformedPred&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_deformedPred%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# geProp\_leProp\_of\_phaseShiftHeart

If $`E` is a nonzero object in the heart of the phase-shifted t-structure $`\mathcal{P}((a-1,a])` and $`\ell \leq \phi^-(E)`, then $`E \in \mathcal{P}(\geq \ell)` and $`E \in \mathcal{P}(\leq a+1)`.

Proof: Membership in the heart gives $`\phi^-(E) > a` (from the $`\mathcal{P}(>a)` part) and $`\phi^+(E) \leq a+1` (from the $`\mathcal{P}(\leq a+1)` part); the lower bound $`\ell \leq \phi^-(E)` then implies $`E \in \mathcal{P}(\geq \ell)`.

{docstring CategoryTheory.Triangulated.geProp_leProp_of_phaseShiftHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20geProp_leProp_of_phaseShiftHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.geProp_leProp_of_phaseShiftHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_leProp\_of\_phaseShiftHeart

If $`E` is a nonzero object in the heart of the phase-shifted t-structure $`\mathcal{P}((a-1,a])` and $`\phi^+(E) \leq u`, then $`E \in \mathcal{P}(>a)` and $`E \in \mathcal{P}(\leq u)`.

Proof: Heart membership directly gives $`E \in \mathcal{P}(>a)` via the shifted slicing, and the upper bound $`\phi^+(E) \leq u` gives $`E \in \mathcal{P}(\leq u)` by monotonicity.

{docstring CategoryTheory.Triangulated.gtProp_leProp_of_phaseShiftHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_leProp_of_phaseShiftHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.gtProp_leProp_of_phaseShiftHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mem\_phaseShiftHeart\_of\_midpoint\_left

If $`E` is nonzero with $`\psi_1 - \varepsilon_0 \leq \phi^-(E)` and $`\phi^+(E) \leq \psi_1 + \varepsilon_0` (so $`E` has phases near $`\psi_1`), $`\psi_2 < \psi_1`, $`\psi_1 \leq \psi_2 + 2\varepsilon_0`, and $`\varepsilon_0 < 1/4`, then $`E` lies in the heart of the t-structure $`\mathcal{P}\bigl((\tfrac{\psi_1+\psi_2}{2}-\tfrac{3}{2},\, \tfrac{\psi_1+\psi_2}{2}-\tfrac{1}{2}]\bigr)`.

Proof: By `mem_phaseShiftHeart_of_phaseBounds_smallGap`, it suffices to show $`\tfrac{\psi_1+\psi_2}{2} - \tfrac{1}{2} < \phi^-(E)` and $`\phi^+(E) \leq \tfrac{\psi_1+\psi_2}{2} + \tfrac{1}{2}`; both follow from the hypotheses on $`\psi_1, \psi_2, \varepsilon_0` by linear arithmetic.

{docstring CategoryTheory.Triangulated.mem_phaseShiftHeart_of_midpoint_left}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mem_phaseShiftHeart_of_midpoint_left&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.mem_phaseShiftHeart_of_midpoint_left%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mem\_phaseShiftHeart\_of\_midpoint\_right

If $`E` is nonzero with $`\psi_2 - \varepsilon_0 \leq \phi^-(E)` and $`\phi^+(E) \leq \psi_2 + \varepsilon_0` (so $`E` has phases near $`\psi_2`), $`\psi_2 < \psi_1`, $`\psi_1 \leq \psi_2 + 2\varepsilon_0`, and $`\varepsilon_0 < 1/4`, then $`E` lies in the heart $`\mathcal{P}\bigl((\tfrac{\psi_1+\psi_2}{2}-\tfrac{3}{2},\, \tfrac{\psi_1+\psi_2}{2}-\tfrac{1}{2}]\bigr)`.

Proof: Analogous to `mem_phaseShiftHeart_of_midpoint_left`, by `mem_phaseShiftHeart_of_phaseBounds_smallGap`, using that the phases of $`E` near $`\psi_2` together with $`\psi_2 < \psi_1 \leq \psi_2 + 2\varepsilon_0` and $`\varepsilon_0 < 1/4` place $`E` in the required window.

{docstring CategoryTheory.Triangulated.mem_phaseShiftHeart_of_midpoint_right}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mem_phaseShiftHeart_of_midpoint_right&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.mem_phaseShiftHeart_of_midpoint_right%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mem\_phaseShiftHeart\_of\_phaseBounds\_smallGap

An object $`E` with $`\phi^-(E) > t` and $`\phi^+(E) \le t + 1` lies in the heart of the t-structure $`\mathcal{P}((t, t+1])`.

Proof: The bounds place $`E` in both the $`\le 0` and $`\ge 0` parts of the shifted slicing, hence in the heart.

{docstring CategoryTheory.Triangulated.mem_phaseShiftHeart_of_phaseBounds_smallGap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mem_phaseShiftHeart_of_phaseBounds_smallGap&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.mem_phaseShiftHeart_of_phaseBounds_smallGap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# midpoint\_image\_window\_thin

If $`\psi_2 < \psi_1 \leq \psi_2 + 2\varepsilon_0` and $`\varepsilon_0 < 1/8`, then the interval width $`(\psi_2 + \varepsilon_0) - (\psi_1 - \varepsilon_0) + 2\varepsilon_0 < 1`.

Proof: A direct linear arithmetic computation from the hypotheses.

{docstring CategoryTheory.Triangulated.midpoint_image_window_thin}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20midpoint_image_window_thin&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.midpoint_image_window_thin%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# midpoint\_left\_target\_thin

If $`\psi_1 \leq \psi_2 + 2\varepsilon_0` and $`\varepsilon_0 < 1/8`, then $`(\psi_1 + \varepsilon_0) - \bigl(\tfrac{\psi_1+\psi_2}{2} - \tfrac{1}{2}\bigr) + 2\varepsilon_0 < 1`.

Proof: A direct linear arithmetic computation from the hypotheses.

{docstring CategoryTheory.Triangulated.midpoint_left_target_thin}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20midpoint_left_target_thin&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.midpoint_left_target_thin%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# midpoint\_right\_target\_thin

If $`\psi_1 \leq \psi_2 + 2\varepsilon_0` and $`\varepsilon_0 < 1/8`, then $`\bigl(\tfrac{\psi_1+\psi_2}{2} + \tfrac{1}{2}\bigr) - (\psi_2 - \varepsilon_0) + 2\varepsilon_0 < 1`.

Proof: A direct linear arithmetic computation from the hypotheses.

{docstring CategoryTheory.Triangulated.midpoint_right_target_thin}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20midpoint_right_target_thin&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.midpoint_right_target_thin%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HomVanishing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
