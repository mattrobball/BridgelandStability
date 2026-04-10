import BridgelandStability.StabilityCondition.Basic
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityCondition: Basic" =>
%%%
htmlSplit := .never
%%%

# PreStabilityCondition.WithClassMap.ext

Extensionality for prestability conditions: two class-map prestability conditions $`\sigma` and $`\tau` over the same class map $`v` are equal if and only if their slicings agree ($`\mathcal{P}_\sigma = \mathcal{P}_\tau`) and their central charges agree ($`Z_\sigma = Z_\tau`). The compatibility datum is a proposition and hence unique by proof irrelevance.

Proof: Destructs both structures, applies the hypotheses to collapse slicing and charge fields, then uses `Subsingleton.elim` on the compatibility proof.

{docstring CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.ext}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ext&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.ext%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# StabilityCondition.WithClassMap.ext

Extensionality for stability conditions: two class-map stability conditions are equal if and only if their slicings and central charges agree. The local finiteness field is propositional.

Proof: Reduces to `PreStabilityCondition.WithClassMap.ext` on the parent structure, then uses `Subsingleton.elim` for the `locallyFinite` field.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ext}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ext&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ext%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_eq\_of\_same\_Z

Lemma 6.4 sublemma (phase rigidity). If two stability conditions $`\sigma` and $`\tau` share the same central charge $`Z`, and a nonzero object $`E` is $`\sigma`-semistable of phase $`\phi` and $`\tau`-semistable of phase $`\psi` with $`|\phi - \psi| < 2`, then $`\phi = \psi`. This is the key uniqueness ingredient: the central charge determines the phase of any semistable object.

Proof: Obtains $`Z([E]) = m_1 e^{i\pi\phi} = m_2 e^{i\pi\psi}` from both compatibility conditions, then applies the uniqueness lemma `eq_of_pos_mul_exp_eq` for positive real multiples of exponentials.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.phase_eq_of_same_Z}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_eq_of_same_Z&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.phase_eq_of_same_Z%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# no\_exp\_decomp\_above

Symmetric version: a real multiple of $`e^{i\pi\psi}` cannot equal a sum of positive real multiples of $`e^{i\pi\theta_j}` where all $`\theta_j` lie strictly above $`\psi` and below $`\psi + 1`.

Proof: Identical structure to `no_exp_decomp_below` with reversed sign: each divided term has strictly positive imaginary part via `sin_pos_of_pos_of_lt_pi`, giving a positive sum that contradicts the real LHS.

{docstring CategoryTheory.Triangulated.no_exp_decomp_above}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20no_exp_decomp_above&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.no_exp_decomp_above%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# no\_exp\_decomp\_below

A real multiple of $`e^{i\pi\psi}` cannot equal a sum $`\sum_j b_j \, e^{i\pi\theta_j}` with all $`b_j > 0` and all $`\theta_j` strictly below $`\psi` (and above $`\psi - 1`). The proof divides by $`e^{i\pi\psi}` and takes imaginary parts: each term contributes $`b_j \sin(\pi(\theta_j - \psi)) < 0`, so the total imaginary part is strictly negative, contradicting the real LHS.

Proof: Divides by $`e^{i\pi\psi}` to reduce to a real vs. negative-imaginary-part contradiction. Uses `sin_neg_of_neg_of_neg_pi_lt` to show each divided term has strictly negative imaginary part, then `Finset.sum_neg` for the sum.

{docstring CategoryTheory.Triangulated.no_exp_decomp_below}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20no_exp_decomp_below&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.no_exp_decomp_below%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# preStabilityCondition\_compat\_apply

The compatibility condition for a prestability condition with class map $`v`, simplified: for every nonzero $`\mathcal{P}(\phi)`-semistable object $`E`, $`Z(\operatorname{cl}_v(E)) = m \cdot e^{i\pi\phi}` for some $`m > 0`.

Proof: Immediate simplification of the general compatibility statement.

{docstring CategoryTheory.Triangulated.preStabilityCondition_compat_apply}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20preStabilityCondition_compat_apply&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.preStabilityCondition_compat_apply%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
