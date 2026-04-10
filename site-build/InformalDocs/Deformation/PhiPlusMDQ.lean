import BridgelandStability.Deformation.PhiPlusMDQ
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: PhiPlusMDQ" =>
%%%
htmlSplit := .never
%%%

# exists\_strictMDQ\_with\_quotient\_bound

MDQ existence with $`\varphi^+` case split (Bridgeland p.23). Same recursion as `exists_strictMDQ_of_finiteLength` but replaces `hHom` with perturbation data and a quotient lower bound, and replaces `hDestabBound` with `phiPlus_bound_of_destabilizing_subobject` when $`\varphi^+(Q_S) \le \psi(Q_S) + \varepsilon`. When $`\varphi^+(Q_S) > \psi(Q_S) + \varepsilon`, a $`\sigma`-phase split branch applies.

Proof: Noetherian induction on the strict-subobject poset. Case 1 (semistable): identity MDQ. Case 2 ($`\varphi^+ \le \psi + \varepsilon`): find a destabilizing strict subobject via the first strict SES, bound its phase by $`b - \varepsilon` using `phiPlus_bound_of_destabilizing_subobject`, pull back, recurse, and compose via `comp_of_destabilizing_with_quotient_bound`. Case 3 ($`\varphi^+ > \psi + \varepsilon`): extract the $`\sigma`-HN filtration, split at cutoff $`\psi + \varepsilon`, get the high-phase part $`X_{\mathrm{hi}}` and low part $`Q_{S,\mathrm{lo}}`, find an MDQ on $`\operatorname{coker}(A_{\mathrm{hi}})` via recursion, then compose via `mdq_of_sigma_phase_split`.

{docstring CategoryTheory.Triangulated.exists_strictMDQ_with_quotient_bound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_strictMDQ_with_quotient_bound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_strictMDQ_with_quotient_bound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhiPlusMDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_gt\_of\_narrow\_interval

Phase lower bound via Im argument (generalized). If $`E \in \mathcal{P}((c, d))` and every $`\sigma`-semistable factor of phase $`\phi \in (c, d)` has $`W`-phase strictly between $`\psi` and $`\psi + 1`, then $`\operatorname{wPhaseOf}(W(E), \alpha) > \psi`. Replaces the older `h\alpha\_ge` condition with a direct width bound.

Proof: The imaginary part of $`W(E) \cdot e^{-i\pi\psi}` is positive: each $`\sigma`-semistable factor contributes a positive imaginary part (from the phase gap hypothesis), and positivity is additive over the HN filtration. If $`\operatorname{wPhaseOf}(W(E), \alpha) \le \psi`, then $`\sin(\pi(\theta - \psi)) \le 0`, contradicting positivity of the imaginary part.

{docstring CategoryTheory.Triangulated.wPhaseOf_gt_of_narrow_interval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_gt_of_narrow_interval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_gt_of_narrow_interval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhiPlusMDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
