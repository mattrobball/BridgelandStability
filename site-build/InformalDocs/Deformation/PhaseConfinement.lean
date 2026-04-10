import BridgelandStability.Deformation.PhaseConfinement
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: PhaseConfinement" =>
%%%
htmlSplit := .never
%%%

# phase\_le\_of\_strictQuotient

A nonzero strict quotient of a W-semistable interval object has W-phase at least $`\psi`. Delegates to `phase_le_of_triangle_quotient` after extracting the distinguished triangle from the strict short exact sequence.

Proof: Lift the strict epimorphism $`E \twoheadrightarrow Y` to a short exact sequence in the abelian heart, extract the corresponding distinguished triangle, then apply `phase_le_of_triangle_quotient`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.phase_le_of_strictQuotient}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_le_of_strictQuotient&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.phase_le_of_strictQuotient%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseConfinement%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_le\_of\_triangle\_quotient

A nonzero quotient in a distinguished triangle $`K \to E \to Q \to K[1]` of a W-semistable object $`E` has W-phase $`\ge \psi`, provided both $`K, Q \in \mathcal{P}((a, b))`.

Proof: If $`K = 0`, then $`Q \cong E` and the result is trivial. Otherwise, W-semistability gives $`\operatorname{wPhaseOf}(W(K)) \le \psi`. The $`K_0` identity $`W(E) = W(K) + W(Q)` and the phase see-saw lemma give $`\operatorname{wPhaseOf}(W(Q)) \ge \psi`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.phase_le_of_triangle_quotient}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_le_of_triangle_quotient&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.phase_le_of_triangle_quotient%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseConfinement%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_eq\_zero\_of\_wSemistable\_gap

Weak hom-vanishing for W-semistable objects. If $`E` is W-semistable of phase $`\psi_1` and $`F` is W-semistable of phase $`\psi_2` with $`\psi_1 > \psi_2 + 2\varepsilon_0`, then $`\operatorname{Hom}(E, F) = 0`.

Proof: Phase confinement puts $`E` and $`F` in disjoint $`\sigma`-intervals: $`E \in \mathcal{P}((\psi_1 - \varepsilon_0 - \delta, \psi_1 + \varepsilon_0 + \delta))` and $`F \in \mathcal{P}((\psi_2 - \varepsilon_0 - \delta, \psi_2 + \varepsilon_0 + \delta))`. For small enough $`\delta`, these are disjoint, so interval hom-vanishing applies.

{docstring CategoryTheory.Triangulated.hom_eq_zero_of_wSemistable_gap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_eq_zero_of_wSemistable_gap&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.hom_eq_zero_of_wSemistable_gap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseConfinement%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# perturb\_gt\_of\_perturb

Shift per-factor perturbation bounds $`\phi - \varepsilon_0 < w < \phi + \varepsilon_0` to the lower endpoint: $`a - \varepsilon_0 < w < a - \varepsilon_0 + 1`. Used by all phase confinement arguments.

Proof: Immediate arithmetic from the per-factor bounds and the thinness constraint $`b - a + 2\varepsilon_0 < 1`.

{docstring CategoryTheory.Triangulated.perturb_gt_of_perturb}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20perturb_gt_of_perturb&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.perturb_gt_of_perturb%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseConfinement%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# perturb\_lt\_of\_perturb

Shift per-factor perturbation bounds to the upper endpoint: $`b + \varepsilon_0 - 1 < w < b + \varepsilon_0`.

Proof: Symmetric arithmetic manipulation of the per-factor bounds.

{docstring CategoryTheory.Triangulated.perturb_lt_of_perturb}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20perturb_lt_of_perturb&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.perturb_lt_of_perturb%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseConfinement%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_confinement\_of\_wSemistable

Bridgeland's Lemma 7.3 (phase confinement). If $`E` is W-semistable of W-phase $`\psi` in $`\mathcal{P}((a, b))` and the interval is thin enough, then $`\psi - \varepsilon_0 < \sigma.\phi^-(E)` and $`\sigma.\phi^+(E) < \psi + \varepsilon_0`.

Proof: Combines `phiMinus_gt_of_wSemistable` and `phiPlus_lt_of_wSemistable`.

{docstring CategoryTheory.Triangulated.phase_confinement_of_wSemistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_confinement_of_wSemistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phase_confinement_of_wSemistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseConfinement%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_gt\_of\_wSemistable

Bridgeland's Lemma 7.3 (lower bound). If $`E` is W-semistable of W-phase $`\psi` in $`\mathcal{P}((a, b))`, then $`\psi - \varepsilon_0 < \sigma.\phi^-(E)`.

Proof: Split $`E` at cutoff $`\psi - \varepsilon_0`. The quotient $`Y` (with $`\sigma`-phases $`\le \psi - \varepsilon_0`) has $`\operatorname{Im}(W(Y) \cdot e^{-i\pi\psi}) < 0` via the sin/Im argument. Combined with $`\operatorname{Im}(W(E) \cdot e^{-i\pi\psi}) = 0`, this gives $`\operatorname{Im}(W(K) \cdot e^{-i\pi\psi}) > 0`, hence $`\operatorname{wPhaseOf}(W(K)) > \psi`, contradicting W-semistability.

{docstring CategoryTheory.Triangulated.phiMinus_gt_of_wSemistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_gt_of_wSemistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phiMinus_gt_of_wSemistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseConfinement%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_lt\_of\_wSemistable

Bridgeland's Lemma 7.3 (upper bound). If $`E` is W-semistable of W-phase $`\psi` in $`\mathcal{P}((a, b))` with the interval thin enough ($`b - a + 2\varepsilon_0 < 1`) and each nonzero semistable factor has W-phase within $`\varepsilon_0` of its $`\sigma`-phase, then $`\sigma.\phi^+(E) < \psi + \varepsilon_0`.

Proof: By contradiction: assume $`\phi^+(E) \ge \psi + \varepsilon_0`. Split $`E` at the gap below $`\phi = \phi^+(E)` in the HN filtration. The resulting top-phase subobject $`K \in \mathcal{P}(\phi)` has $`\operatorname{wPhaseOf}(W(K)) > \phi - \varepsilon_0 \ge \psi`, contradicting W-semistability.

{docstring CategoryTheory.Triangulated.phiPlus_lt_of_wSemistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_lt_of_wSemistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phiPlus_lt_of_wSemistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhaseConfinement%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
