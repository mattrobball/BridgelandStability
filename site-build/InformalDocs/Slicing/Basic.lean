import BridgelandStability.Slicing.Basic
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Slicing: Basic" =>
%%%
htmlSplit := .never
%%%

# phase\_mem\_range

Every phase $`\phi_i` of an HN filtration lies in the interval $`[\phi^-(F),\, \phi^+(F)]`. That is, $`\phi^- \le \phi_i \le \phi^+` for all $`i`.

Proof: Both inequalities follow directly from the strict antitonicity of the phase assignment via the monotonicity of the index comparison.

{docstring CategoryTheory.Triangulated.HNFiltration.phase_mem_range}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_mem_range&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.phase_mem_range%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_le\_phiPlus

For any HN filtration $`0 = E_0 \to E_1 \to \cdots \to E_n = E` with $`n > 0`, the lowest phase $`\phi^-(F) = \phi_n` satisfies $`\phi^-(F) \le \phi^+(F) = \phi_1`. In other words, the highest phase is at least the lowest phase.

Proof: Immediate from strict antitonicity of the phase sequence: $`\phi_1 > \phi_2 > \cdots > \phi_n`.

{docstring CategoryTheory.Triangulated.HNFiltration.phiMinus_le_phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_le_phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.phiMinus_le_phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# geProp

The subcategory predicate $`\mathcal{P}(\ge t)`: an object $`E` satisfies this if it is zero or admits an HN filtration whose lowest phase $`\phi^-(F) \ge t`.

Construction: Defined as the disjunction: $`E` is zero, or there exists an HN filtration $`F` of $`E` with $`0 < n` and $`t \le \phi^-(F)`.


{docstring CategoryTheory.Triangulated.Slicing.geProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20geProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.geProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# geProp\_anti

The subcategory predicate $`\mathcal{P}(\ge \cdot)` is antitone: if $`t_1 \le t_2` then $`\mathcal{P}(\ge t_2) \subseteq \mathcal{P}(\ge t_1)`.

Proof: If $`t_2 \le \phi^-(F)` and $`t_1 \le t_2`, then $`t_1 \le \phi^-(F)`.

{docstring CategoryTheory.Triangulated.Slicing.geProp_anti}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20geProp_anti&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.geProp_anti%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# geProp\_of\_gtProp

$`\mathcal{P}(> t) \subseteq \mathcal{P}(\ge t)`: a strict lower phase bound implies a non-strict one.

Proof: Immediate from $`t < \phi^-(F) \implies t \le \phi^-(F)`.

{docstring CategoryTheory.Triangulated.Slicing.geProp_of_gtProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20geProp_of_gtProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.geProp_of_gtProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# geProp\_zero

The zero object lies in $`\mathcal{P}(\ge t)` for every $`t \in \mathbb{R}`.

Proof: By the left disjunct of the definition: the zero object is zero.

{docstring CategoryTheory.Triangulated.Slicing.geProp_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20geProp_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.geProp_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp

The subcategory predicate $`\mathcal{P}(> t)`: an object $`E` satisfies this if it is zero or admits an HN filtration whose lowest phase $`\phi^-(F) > t`.

Construction: Defined as the disjunction: $`E` is zero, or there exists an HN filtration $`F` of $`E` with $`0 < n` and $`t < \phi^-(F)`.


{docstring CategoryTheory.Triangulated.Slicing.gtProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_anti

The subcategory predicate $`\mathcal{P}(> \cdot)` is antitone: if $`t_1 \le t_2` then $`\mathcal{P}(> t_2) \subseteq \mathcal{P}(> t_1)`.

Proof: If $`t_2 < \phi^-(F)` and $`t_1 \le t_2`, then $`t_1 < \phi^-(F)`.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_anti}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_anti&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_anti%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_zero

The zero object lies in $`\mathcal{P}(> t)` for every $`t \in \mathbb{R}`.

Proof: By the left disjunct of the definition: the zero object is zero.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_eq\_zero\_of\_gt\_phases

A morphism from a semistable object $`A \in \mathcal{P}(\psi)` to an HN-filtered object $`E` whose phases are all strictly less than $`\psi` is zero.

Proof: Follows from `chain_hom_eq_zero_of_gt` applied at the top of the chain, using the isomorphism $`E_n \cong E`.

{docstring CategoryTheory.Triangulated.Slicing.hom_eq_zero_of_gt_phases}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_eq_zero_of_gt_phases&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.hom_eq_zero_of_gt_phases%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_eq\_zero\_of\_lt\_phases

A morphism from an HN-filtered object $`E` whose phases are all strictly greater than $`\psi` to a semistable object $`B \in \mathcal{P}(\psi)` is zero.

Proof: Follows from `chain_hom_eq_zero_of_lt` at the top of the chain, using $`E_n \cong E`.

{docstring CategoryTheory.Triangulated.Slicing.hom_eq_zero_of_lt_phases}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_eq_zero_of_lt_phases&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.hom_eq_zero_of_lt_phases%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_eq\_zero\_of\_phase\_gap

If two HN-filtered objects $`X` and $`Y` have a phase gap---every phase of $`F_X` is strictly greater than every phase of $`F_Y`---then $`\operatorname{Hom}(X, Y) = 0`.

Proof: Follows from `chain_hom_eq_zero_gap` applied at the top of the chain for $`F_X`, using the isomorphism $`X_n \cong X`.

{docstring CategoryTheory.Triangulated.Slicing.hom_eq_zero_of_phase_gap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_eq_zero_of_phase_gap&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.hom_eq_zero_of_phase_gap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp

The subcategory predicate $`\mathcal{P}(\le t)`: an object $`E` satisfies this if it is zero or admits an HN filtration whose highest phase $`\phi^+(F) \le t`.

Construction: Defined as the disjunction: $`E` is zero, or there exists an HN filtration $`F` of $`E` with $`0 < n` and $`\phi^+(F) \le t`.


{docstring CategoryTheory.Triangulated.Slicing.leProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_mono

The subcategory predicates are monotone in the parameter: if $`t_1 \le t_2` then $`\mathcal{P}(\le t_1) \subseteq \mathcal{P}(\le t_2)`.

Proof: If $`\phi^+(F) \le t_1 \le t_2`, then $`\phi^+(F) \le t_2` by transitivity.

{docstring CategoryTheory.Triangulated.Slicing.leProp_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_of\_ltProp

$`\mathcal{P}(< t) \subseteq \mathcal{P}(\le t)`: a strict upper phase bound implies a non-strict one.

Proof: Immediate from $`\phi^+(F) < t \implies \phi^+(F) \le t`.

{docstring CategoryTheory.Triangulated.Slicing.leProp_of_ltProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_of_ltProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_of_ltProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_zero

The zero object lies in $`\mathcal{P}(\le t)` for every $`t \in \mathbb{R}`.

Proof: By the left disjunct of the definition: the zero object is zero.

{docstring CategoryTheory.Triangulated.Slicing.leProp_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp

The subcategory predicate $`\mathcal{P}(< t)`: an object $`E` satisfies this if it is zero or admits an HN filtration whose highest phase $`\phi^+(F) < t`.

Construction: Defined as the disjunction: $`E` is zero, or there exists an HN filtration $`F` of $`E` with $`0 < n` and $`\phi^+(F) < t`.


{docstring CategoryTheory.Triangulated.Slicing.ltProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ltProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_mono

The subcategory predicate $`\mathcal{P}(< \cdot)` is monotone: if $`t_1 \le t_2` then $`\mathcal{P}(< t_1) \subseteq \mathcal{P}(< t_2)`.

Proof: If $`\phi^+(F) < t_1 \le t_2`, then $`\phi^+(F) < t_2`.

{docstring CategoryTheory.Triangulated.Slicing.ltProp_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ltProp_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_of\_intervalProp

If $`E \in \mathcal{P}((a, b))` (all HN phases in the open interval), then $`E \in \mathcal{P}(< b)`.

Proof: The interval condition gives $`\phi_i < b` for all factors; the first factor's phase is $`\phi^+(F) < b`.

{docstring CategoryTheory.Triangulated.Slicing.ltProp_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ltProp_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_zero

The zero object lies in $`\mathcal{P}(< t)` for every $`t \in \mathbb{R}`.

Proof: By the left disjunct of the definition: the zero object is zero.

{docstring CategoryTheory.Triangulated.Slicing.ltProp_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ltProp_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# chain\_hom\_eq\_zero\_gap

Any morphism from the $`k`-th chain object of an HN filtration $`F_X` to an object $`Y` admitting a filtration $`F_Y` is zero, provided every phase of $`F_X` is strictly greater than every phase of $`F_Y`.

Proof: Induction on $`k`. The base is trivial ($`E_0 = 0`). For the inductive step, the Yoneda exact sequence factors the map through the $`k`-th semistable factor of $`F_X`, and `hom_eq_zero_of_gt_phases` shows this factor maps to zero into $`Y`.

{docstring CategoryTheory.Triangulated.chain_hom_eq_zero_gap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20chain_hom_eq_zero_gap&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.chain_hom_eq_zero_gap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# chain\_hom\_eq\_zero\_of\_gt

Any morphism from a semistable object $`A \in \mathcal{P}(\psi)` to the $`k`-th chain object $`E_k` of an HN filtration whose phases all satisfy $`\phi_i < \psi` is zero.

Proof: Induction on $`k`. The base $`k = 0` is trivial since $`E_0 = 0`. For the inductive step, the coYoneda exact sequence on the $`k`-th distinguished triangle gives that any map $`A \to E_k` factors through the $`k`-th semistable factor, but $`\operatorname{Hom}(A, A_k) = 0` by the phase gap axiom.

{docstring CategoryTheory.Triangulated.chain_hom_eq_zero_of_gt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20chain_hom_eq_zero_of_gt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.chain_hom_eq_zero_of_gt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# chain\_hom\_eq\_zero\_of\_lt

Any morphism from the $`k`-th chain object of an HN filtration (whose phases are all strictly greater than $`\psi`) to a semistable object $`B \in \mathcal{P}(\psi)` is zero.

Proof: Induction on $`k`. The base is trivial. For the inductive step, the Yoneda exact sequence factors the map through the $`k`-th semistable factor $`A_k`, and the pointwise Hom-vanishing axiom gives $`\operatorname{Hom}(A_k, B) = 0` since $`\phi_k > \psi`.

{docstring CategoryTheory.Triangulated.chain_hom_eq_zero_of_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20chain_hom_eq_zero_of_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.chain_hom_eq_zero_of_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
