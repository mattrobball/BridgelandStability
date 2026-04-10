import BridgelandStability.Deformation.TargetEnvelope
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: TargetEnvelope" =>
%%%
htmlSplit := .never
%%%

# gtProp\_of\_wSemistable\_phase\_gt

$`\mathcal{P}(> t)` from $`W`-semistability: if $`E` is $`W`-semistable at phase $`\psi` and $`t < \psi - \varepsilon_0`, then $`E \in \mathcal{P}(> t)`. Phase confinement gives $`\varphi^-(E) > \psi - \varepsilon_0 > t`.

Proof: Phase confinement gives $`\varphi^-(E) > \psi - \varepsilon_0 > t`, then `gtProp_of_phiMinus_gt` yields $`E \in \mathcal{P}(> t)`.

{docstring CategoryTheory.Triangulated.gtProp_of_wSemistable_phase_gt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_of_wSemistable_phase_gt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.gtProp_of_wSemistable_phase_gt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.TargetEnvelope%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_of\_wSemistable\_phase\_lt

$`\mathcal{P}(< t)` from $`W`-semistability: if $`E` is $`W`-semistable at phase $`\psi` and $`\psi + \varepsilon_0 < t`, then $`E \in \mathcal{P}(< t)`. Phase confinement gives $`\varphi^+(E) < \psi + \varepsilon_0 < t`.

Proof: Phase confinement gives $`\varphi^+(E) < \psi + \varepsilon_0 < t`, then `ltProp_of_phiPlus_lt` yields $`E \in \mathcal{P}(< t)`.

{docstring CategoryTheory.Triangulated.ltProp_of_wSemistable_phase_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_of_wSemistable_phase_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.ltProp_of_wSemistable_phase_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.TargetEnvelope%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_confinement\_from\_stabSeminorm

Phase confinement from the stability seminorm: if $`E` is $`\operatorname{ssf}`-semistable at phase $`\psi` in a thin interval $`(a, b)` with perturbation parameter $`\varepsilon_0`, then $`\psi - \varepsilon_0 < \varphi^-(E)` and $`\varphi^+(E) < \psi + \varepsilon_0`. This is the $`\operatorname{stabSeminorm}`-based wrapper for `phase_confinement_of_wSemistable`.

Proof: Derive the perturbation bounds from `hperturb_of_stabSeminorm`, then apply `phase_confinement_of_wSemistable`.

{docstring CategoryTheory.Triangulated.phase_confinement_from_stabSeminorm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_confinement_from_stabSeminorm&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phase_confinement_from_stabSeminorm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.TargetEnvelope%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_target\_envelope\_triangleTest

Semistability in a target envelope: if $`E` is $`\operatorname{ssf}`-semistable at phase $`\psi` in $`(a_1, b_1)`, lies in $`\mathcal{P}((a_2, b_2))`, $`\psi \in [a_2 + \varepsilon_0, b_2 - \varepsilon_0]`, and the triangle test holds in $`(a_2, b_2)`, then $`E` is semistable in $`(a_2, b_2)` at phase $`\psi`.

Proof: The interval membership and nonzero condition are given. The phase equation follows from `wPhaseOf_eq_of_semistable_of_target_envelope`. The triangle test is the provided hypothesis.

{docstring CategoryTheory.Triangulated.semistable_of_target_envelope_triangleTest}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_target_envelope_triangleTest&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.semistable_of_target_envelope_triangleTest%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.TargetEnvelope%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_lt\_cos\_of\_hsin\_hthin

Seminorm comparison: if $`\|W - Z\|_\sigma < \sin(\pi\varepsilon_0)` and $`b - a + 2\varepsilon_0 < 1`, then $`\|W - Z\|_\sigma < \cos(\pi(b-a)/2)`. This bridges the sine-based perturbation hypothesis to the cosine-based $`W \ne 0` condition.

Proof: The inequality $`\sin(\pi\varepsilon_0) < \cos(\pi(b-a)/2)` follows from the complementary angle identity and the thinness condition $`b - a + 2\varepsilon_0 < 1`. Transitivity gives the result.

{docstring CategoryTheory.Triangulated.stabSeminorm_lt_cos_of_hsin_hthin}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_lt_cos_of_hsin_hthin&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_lt_cos_of_hsin_hthin%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.TargetEnvelope%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_eq\_of\_intervalProp\_lower\_inclusion

$`W`-phase equality under lower interval inclusion: if $`E \in \mathcal{P}((a_1, b))` with $`a_2 \le a_1` and the thinness condition holds for $`(a_2, b)`, then $`\operatorname{wPhaseOf}(W(E), (a_1+b)/2) = \operatorname{wPhaseOf}(W(E), (a_2+b)/2)`.

Proof: Symmetric to `wPhaseOf_eq_of_intervalProp_upper_inclusion`: derive perturbation bounds for the narrower interval, verify branch-window overlap, apply `wPhaseOf_indep`.

{docstring CategoryTheory.Triangulated.wPhaseOf_eq_of_intervalProp_lower_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_eq_of_intervalProp_lower_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_eq_of_intervalProp_lower_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.TargetEnvelope%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_eq\_of\_intervalProp\_upper\_inclusion

$`W`-phase equality under upper interval inclusion: if $`E \in \mathcal{P}((a, b_1))` with $`b_1 \le b_2` and the thinness condition holds for $`(a, b_2)`, then $`\operatorname{wPhaseOf}(W(E), (a+b_1)/2) = \operatorname{wPhaseOf}(W(E), (a+b_2)/2)`.

Proof: Derive perturbation bounds for the narrower interval $`(a, b_1)`, show the $`W`-phase lies in the overlap of both branch windows, then apply `wPhaseOf_indep`.

{docstring CategoryTheory.Triangulated.wPhaseOf_eq_of_intervalProp_upper_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_eq_of_intervalProp_upper_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_eq_of_intervalProp_upper_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.TargetEnvelope%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_eq\_of\_semistable\_of\_target\_envelope

$`W`-phase independence across target envelopes: if $`E` is $`\operatorname{ssf}`-semistable at phase $`\psi` in one interval $`(a_1, b_1)`, and $`\psi \in [a_2 + \varepsilon_0, b_2 - \varepsilon_0]` for a second thin interval $`(a_2, b_2)`, then $`\operatorname{wPhaseOf}(W(E), (a_2 + b_2)/2) = \psi`.

Proof: The branch-cut independence `wPhaseOf_indep` applies because $`\psi` lies in the overlap of both branch windows. The original phase equation $`\operatorname{wPhaseOf}(W(E), (a_1 + b_1)/2) = \psi` transfers to the new center.

{docstring CategoryTheory.Triangulated.wPhaseOf_eq_of_semistable_of_target_envelope}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_eq_of_semistable_of_target_envelope&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_eq_of_semistable_of_target_envelope%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.TargetEnvelope%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_mem\_Ioo\_of\_intervalProp\_target\_envelope

For $`E \in \mathcal{P}((a, b))` nonzero, the $`W`-phase at center $`(a+b)/2` lies in the open interval $`(\psi - 1, \psi + 1)` whenever $`\psi \in [a + \varepsilon_0, b - \varepsilon_0]`. This is the branch-cut membership needed for `wPhaseOf_indep`.

Proof: The global perturbation bounds give $`a - \varepsilon_0 < \operatorname{wPhaseOf}(W(E), (a+b)/2) < b + \varepsilon_0`. Since $`\psi \in [a + \varepsilon_0, b - \varepsilon_0]` and $`b - a + 2\varepsilon_0 < 1`, both $`\psi - 1` and $`\psi + 1` are outside the $`W`-phase range, giving strict containment.

{docstring CategoryTheory.Triangulated.wPhaseOf_mem_Ioo_of_intervalProp_target_envelope}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_mem_Ioo_of_intervalProp_target_envelope&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_mem_Ioo_of_intervalProp_target_envelope%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.TargetEnvelope%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
