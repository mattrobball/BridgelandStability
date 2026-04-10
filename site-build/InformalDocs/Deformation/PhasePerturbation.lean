import BridgelandStability.Deformation.PhasePerturbation
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: PhasePerturbation" =>
%%%
htmlSplit := .never
%%%

# wPhaseOf\_perturbation\_generic

Generic phase perturbation bound. If $`w = m \cdot e^{i\pi\phi} \cdot (1 + u)` with $`m > 0`, $`\phi \in (\alpha - 1/2, \alpha + 1/2)`, and $`\|u\| < \sin(\pi\varepsilon)` with $`0 < \varepsilon \le 1/2`, then $`|\operatorname{wPhaseOf}(w, \alpha) - \phi| < \varepsilon`.

Proof: Split $`\arg` of the product using $`\arg(z_1 z_2) = \arg(z_1) + \arg(z_2)` (valid when the sum stays in $`(-\pi, \pi]`). Compute $`\arg(m \cdot e^{i\pi(\phi - \alpha)}) = \pi(\phi - \alpha)`, and bound $`|\arg(1 + u)| < \pi\varepsilon` from the pure complex analysis lemma `abs_arg_one_add_lt`.

{docstring CategoryTheory.Triangulated.wPhaseOf_perturbation_generic}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_perturbation_generic&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_perturbation_generic%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhasePerturbation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
