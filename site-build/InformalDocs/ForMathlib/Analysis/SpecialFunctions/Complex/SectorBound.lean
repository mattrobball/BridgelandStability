import BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.SectorBound
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "ForMathlib: Analysis.SpecialFunctions.Complex.SectorBound" =>
%%%
htmlSplit := .never
%%%

# eq\_of\_pos\_mul\_exp\_eq

Ray rigidity: if $`m_1 \cdot e^{i\pi\varphi} = m_2 \cdot e^{i\pi\psi}` with $`m_1, m_2 > 0` and $`|\varphi - \psi| < 2`, then $`\varphi = \psi`. This ensures that a semistable object's phase is uniquely determined by its central charge value.

Proof: Extract the argument equality, reduce to $`\pi\psi - \pi\varphi = n \cdot 2\pi` for some $`n \in \mathbb{Z}`, and show $`n = 0` using the bound $`|\varphi - \psi| < 2`.

{docstring eq_of_pos_mul_exp_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eq_of_pos_mul_exp_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60eq_of_pos_mul_exp_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.SectorBound%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# norm\_sum\_exp\_ge\_cos\_mul\_sum

Sector norm bound (explicit form): if $`m_i \geq 0` and phases $`\theta_i \in [\alpha, \alpha + w]` with $`w < \pi`, then $`\cos(w/2) \cdot \sum_i m_i \leq \bigl\|\sum_i m_i e^{i\theta_i}\bigr\|`.

Proof: Project each summand onto the bisector direction $`\beta = \alpha + w/2`: pointwise $`\cos(w/2) \cdot m_i \leq \mathrm{Re}(m_i e^{i\theta_i} e^{-i\beta})` by the cosine bound on $`|\theta_i - \beta| \leq w/2`. Sum, bound the real part by the norm, and cancel the unit exponential.

{docstring norm_sum_exp_ge_cos_mul_sum}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20norm_sum_exp_ge_cos_mul_sum&body=%2A%2ADeclaration%3A%2A%2A%20%60norm_sum_exp_ge_cos_mul_sum%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.SectorBound%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# norm\_sum\_ge\_cos\_mul\_sum\_norm

Sector norm bound: if all $`z_i` have $`\arg(z_i) \in (\alpha, \alpha + w)` with $`w < \pi`, then $`\cos(w/2) \cdot \sum_i \|z_i\| \leq \bigl\|\sum_i z_i\bigr\|`.

Proof: Sum the pointwise bound from `re_mul_exp_neg_ge_cos_mul_norm`, collect into the rotated sum's real part, and bound by the norm.

{docstring norm_sum_ge_cos_mul_sum_norm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20norm_sum_ge_cos_mul_sum_norm&body=%2A%2ADeclaration%3A%2A%2A%20%60norm_sum_ge_cos_mul_sum_norm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.SectorBound%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# re\_mul\_exp\_neg\_ge\_cos\_mul\_norm

Sector projection bound: if $`\arg(z) \in (\alpha, \alpha + w)` with $`w < \pi`, then $`\cos(w/2) \cdot \|z\| \leq \mathrm{Re}(z \cdot e^{-i(\alpha + w/2)})`.

Proof: Using the polar form $`z = \|z\| e^{i\arg z}`, compute $`\mathrm{Re}(z e^{-i\beta}) = \|z\| \cos(\arg z - \beta)` where $`\beta = \alpha + w/2`. Since $`|\arg z - \beta| < w/2` and cosine is decreasing, $`\cos(\arg z - \beta) \geq \cos(w/2)`.

{docstring re_mul_exp_neg_ge_cos_mul_norm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20re_mul_exp_neg_ge_cos_mul_norm&body=%2A%2ADeclaration%3A%2A%2A%20%60re_mul_exp_neg_ge_cos_mul_norm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.SectorBound%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
