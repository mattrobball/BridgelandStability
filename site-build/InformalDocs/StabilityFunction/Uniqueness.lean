import BridgelandStability.StabilityFunction.Uniqueness
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityFunction: Uniqueness" =>
%%%
htmlSplit := .never
%%%

# hn\_phiMinus\_eq

The lowest phase $`\phi(n-1)` of an HN filtration is independent of the filtration choice.

Proof: Parallels `hn_unique`: induction on $`|\operatorname{Sub}(E)|`. For semistable objects the result reduces to `hn_phiPlus_eq`. Otherwise, the tail filtrations on $`E/M` have the same lowest phase by the inductive hypothesis, and `tailHNFiltration_phiMinus` transports this back to the original filtration.

{docstring CategoryTheory.StabilityFunction.hn_phiMinus_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hn_phiMinus_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.hn_phiMinus_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Uniqueness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hn\_phiPlus\_eq

The highest phase $`\phi(0)` of an HN filtration is independent of the filtration choice.

Proof: For semistable objects, $`n = 1` forces $`\phi(0) = \phi(E)`. For non-semistable objects, $`\phi(0) = \phi(\operatorname{chain}(1))` by `chain_one_phase`, and $`\operatorname{chain}(1) = M` (the unique MDS) by `chain_one_eq_MDS`.

{docstring CategoryTheory.StabilityFunction.hn_phiPlus_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hn_phiPlus_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.hn_phiPlus_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Uniqueness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hn\_unique

Proposition 2.3 (Bridgeland). HN filtrations are essentially unique: when all objects have finite subobject lattices, any two HN filtrations of the same nonzero object have the same number of semistable factors.

Proof: Induction on $`|\operatorname{Sub}(E)|`. If $`E` is semistable, both filtrations have $`n = 1` (by `hn_n_eq_one_of_semistable`). Otherwise, both have $`n \ge 2`, and the semistable descent lemma forces $`\operatorname{chain}(1) = M` for the unique maximally destabilizing subobject $`M`. Quotienting by $`M` gives tail filtrations on $`E/M` with strictly fewer subobjects, and the inductive hypothesis yields $`n_1 - 1 = n_2 - 1`.

{docstring CategoryTheory.StabilityFunction.hn_unique}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hn_unique&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.hn_unique%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Uniqueness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus

The intrinsic lowest phase $`\phi^-(E)` of a nonzero object $`E`: the phase of the last HN factor. Well-defined by `hn_phiMinus_eq`.

Construction: Defined as $`F.\phi(n-1)` for an arbitrary HN filtration $`F` obtained via `Classical.choice`.


{docstring CategoryTheory.StabilityFunction.phiMinus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phiMinus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Uniqueness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_eq

$`\phi^-(E) = F.\phi(n-1)` for any HN filtration $`F` of $`E`.

Proof: Immediate from `hn_phiMinus_eq`.

{docstring CategoryTheory.StabilityFunction.phiMinus_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phiMinus_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Uniqueness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_le\_phiPlus

$`\phi^-(E) \le \phi^+(E)` for nonzero objects.

Proof: Both values come from the same HN filtration's phase sequence, which is strictly anti-monotone. The last index $`n-1 \ge 0` gives $`\phi(n-1) \le \phi(0)`.

{docstring CategoryTheory.StabilityFunction.phiMinus_le_phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_le_phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phiMinus_le_phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Uniqueness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus

The intrinsic highest phase $`\phi^+(E)` of a nonzero object $`E`: the phase of the maximally destabilizing subobject. Well-defined by `hn_phiPlus_eq`.

Construction: Defined as $`F.\phi(0)` for an arbitrary HN filtration $`F` obtained via `Classical.choice`.


{docstring CategoryTheory.StabilityFunction.phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Uniqueness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_eq

$`\phi^+(E) = F.\phi(0)` for any HN filtration $`F` of $`E`.

Proof: Immediate from `hn_phiPlus_eq`.

{docstring CategoryTheory.StabilityFunction.phiPlus_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phiPlus_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Uniqueness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_eq\_phiMinus\_of\_semistable

For semistable objects, $`\phi^+(E) = \phi^-(E) = \phi(E)`.

Proof: By `hn_n_eq_one_of_semistable`, the HN filtration has $`n = 1`, so the only phase index is $`0 = n - 1` and both $`\phi^+` and $`\phi^-` equal $`\phi(E)`.

{docstring CategoryTheory.StabilityFunction.phiPlus_eq_phiMinus_of_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_eq_phiMinus_of_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.phiPlus_eq_phiMinus_of_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.Uniqueness%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
