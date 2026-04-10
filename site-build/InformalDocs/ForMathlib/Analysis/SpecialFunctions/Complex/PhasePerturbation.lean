import BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.PhasePerturbation
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "ForMathlib: Analysis.SpecialFunctions.Complex.PhasePerturbation" =>
%%%
htmlSplit := .never
%%%

# abs\_arg\_one\_add\_lt

Phase bound for near-identity perturbation: if $`\|u\| < \sin(\pi\varepsilon)` with $`0 < \varepsilon \leq 1/2`, then $`|\arg(1 + u)| < \pi\varepsilon`.

Proof: Since $`\|u\| < 1`, the number $`1+u` has positive real part, so $`|\arg(1+u)| < \pi/2`. Then $`|\sin(\arg(1+u))| \leq \|u\|` by `abs_sin_arg_le_norm_sub_one`, and monotonicity of sine on $`[0, \pi/2]` gives the conclusion.

{docstring abs_arg_one_add_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20abs_arg_one_add_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60abs_arg_one_add_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.PhasePerturbation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# abs\_sin\_arg\_le\_norm\_sub\_one

For any nonzero $`z \in \mathbb{C}`, $`|\sin(\arg z)| \leq \|z - 1\|`.

Proof: Since $`\sin(\arg z) = z.\mathrm{im} / \|z\|`, the inequality follows from the geometric estimate $`z.\mathrm{im}^2 \leq \|z-1\|^2 \cdot \|z\|^2` via `im_sq_le_norm_sq_mul`.

{docstring abs_sin_arg_le_norm_sub_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20abs_sin_arg_le_norm_sub_one&body=%2A%2ADeclaration%3A%2A%2A%20%60abs_sin_arg_le_norm_sub_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.PhasePerturbation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_sq\_le\_norm\_sq\_mul

For any $`z \in \mathbb{C}`, $`z.\mathrm{im}^2 \leq \|z - 1\|^2 \cdot \|z\|^2`.

Proof: Expand both sides using $`\|w\|^2 = w.\mathrm{re}^2 + w.\mathrm{im}^2` and check the resulting polynomial inequality by `nlinarith`.

{docstring im_sq_le_norm_sq_mul}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_sq_le_norm_sq_mul&body=%2A%2ADeclaration%3A%2A%2A%20%60im_sq_le_norm_sq_mul%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.PhasePerturbation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# sin\_abs\_eq\_abs\_sin

For $`|x| < \pi/2`, $`\sin|x| = |\sin x|`.

Proof: Case split on the sign of $`x`: if $`x \geq 0` both sides equal $`\sin x \geq 0`; if $`x < 0`, then $`|x| = -x` and $`\sin x < 0`, so $`\sin|x| = \sin(-x) = -\sin x = |\sin x|`.

{docstring sin_abs_eq_abs_sin}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20sin_abs_eq_abs_sin&body=%2A%2ADeclaration%3A%2A%2A%20%60sin_abs_eq_abs_sin%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.PhasePerturbation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
