import BridgelandStability.Deformation.PhiPlusHN
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: PhiPlusHN" =>
%%%
htmlSplit := .never
%%%

# hn\_exists\_with\_phiPlus\_reduction

HN existence with $`\varphi^+` reduction (Bridgeland p.23--24). Drops both `hHom` and `hDestabBound` from the older HN existence theorem. Instead takes perturbation data and a quotient lower bound $`t \ge a + \varepsilon`. At each step: (1) call `exists_strictMDQ_with_quotient_bound`, (2) extract the kernel and lift to a smaller strict subobject, (3) recurse with the MDQ phase as new lower bound. The $`\varphi^+` invariant ($`\varphi^+(Y) < b - 4\varepsilon`) is propagated through kernels via `phiPlus_triangle_le`.

Proof: Well-founded induction on the strict-subobject poset. Semistable case: single-factor filtration. Non-semistable case: derive $`\psi(Y) < b - 3\varepsilon` from $`\varphi^+(Y) < b - 4\varepsilon` via `wPhaseOf_lt_of_phiPlus_lt`. Call `exists_strictMDQ_with_quotient_bound` (which handles Hom vanishing and destabilizing bounds internally). Extract kernel $`K`, lift to $`T < S`, propagate $`\varphi^+(K) \le \varphi^+(Y) < b - 4\varepsilon` via `phiPlus_triangle_le`, then recurse on $`T`.

{docstring CategoryTheory.Triangulated.hn_exists_with_phiPlus_reduction}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hn_exists_with_phiPlus_reduction&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.hn_exists_with_phiPlus_reduction%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhiPlusHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_lt\_of\_phiPlus\_lt

$`W`-phase upper bound from $`\varphi^+` bound. If $`E \in \mathcal{P}((a, b))` with $`\varphi^+(E) < b - 4\varepsilon` and the interval is wide enough ($`6\varepsilon \le b - a`), then $`\psi(E) < b - 3\varepsilon`. This key estimate propagates through the HN recursion.

Proof: From $`\varphi^+(E) < b - 4\varepsilon` and $`\varphi^-(E) > a`, deduce $`E \in \mathcal{P}((a, b - 4\varepsilon))`. Apply `wPhaseOf_lt_of_intervalProp` with the narrower interval $`(a, b - 4\varepsilon)` and perturbation $`\varepsilon`. The condition $`(a+b)/2 \le (b-4\varepsilon) + \varepsilon = b - 3\varepsilon` follows from $`6\varepsilon \le b - a`.

{docstring CategoryTheory.Triangulated.wPhaseOf_lt_of_phiPlus_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_lt_of_phiPlus_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_lt_of_phiPlus_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhiPlusHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
