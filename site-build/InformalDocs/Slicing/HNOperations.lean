import BridgelandStability.Slicing.HNOperations
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Slicing: HNOperations" =>
%%%
htmlSplit := .never
%%%

# appendFactor

Extend an HN filtration by appending one semistable factor via a distinguished triangle. Given an HN filtration $`G` of $`Y'` and a distinguished triangle $`Y' \to Z \to F \to Y'[1]` where $`F \in \mathcal{P}(\psi)` with $`\psi` strictly less than all phases of $`G`, produce an HN filtration of $`Z` with the additional factor $`F` appended at the end.

Construction: Constructs a new composable-arrows chain of length $`n + 1` by extending the existing chain with the new object $`Z` as the top. The phase assignment appends $`\psi` after the existing phases. Strict antitonicity of the extended phase sequence follows from $`\psi < \phi_j` for all existing phases.


{docstring CategoryTheory.Triangulated.HNFiltration.appendFactor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20appendFactor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.appendFactor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# chain\_obj\_geProp

The chain object $`E_k` at the split point of an HN filtration satisfies $`\mathcal{P}(\ge t)` if all phases before the split are $`\ge t`.

Proof: The prefix filtration's lowest phase $`\phi_{k-1} \ge t` by hypothesis.

{docstring CategoryTheory.Triangulated.HNFiltration.chain_obj_geProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20chain_obj_geProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.chain_obj_geProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# chain\_obj\_gtProp

The chain object $`E_k` at the split point of an HN filtration satisfies $`\mathcal{P}(> t)` if all phases before the split are $`> t`.

Proof: The prefix filtration provides an HN filtration of $`E_k` whose phases are all $`> t`, giving the result via the definition of $`\mathcal{P}(> t)`.

{docstring CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20chain_obj_gtProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# chain\_obj\_leProp

The chain object $`E_k` at the split point of an HN filtration satisfies $`\mathcal{P}(\le t)` if all phases before the split are $`\le t`.

Proof: The prefix filtration of $`E_k` has highest phase $`\phi_1` among the first $`k` phases, all of which are $`\le t`.

{docstring CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20chain_obj_leProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# chain\_obj\_ltProp

The chain object $`E_k` at the split point of an HN filtration satisfies $`\mathcal{P}(< t)` if all phases before the split are $`< t`.

Proof: Analogous to `chain_obj_leProp` with strict inequality: the prefix's highest phase $`\phi_1 < t`.

{docstring CategoryTheory.Triangulated.HNFiltration.chain_obj_ltProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20chain_obj_ltProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.chain_obj_ltProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# prefix\_phiMinus\_gt

The prefix of an HN filtration truncated at step $`k` has lowest phase $`\phi^-(\text{prefix}) > t` provided every phase $`\phi_j` for $`j < k` exceeds $`t`.

Proof: The lowest phase of the prefix is $`\phi_{k-1}`, which is among the phases bounded below by $`t` by hypothesis.

{docstring CategoryTheory.Triangulated.HNFiltration.prefix_phiMinus_gt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20prefix_phiMinus_gt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.prefix_phiMinus_gt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# geProp\_closedUnderIso

The property $`\mathcal{P}(\ge t)` is closed under isomorphisms.

Proof: Transport the HN filtration across the isomorphism using `HNFiltration.ofIso`; the phase bounds are preserved.

{docstring CategoryTheory.Triangulated.Slicing.geProp_closedUnderIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20geProp_closedUnderIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.geProp_closedUnderIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# geProp\_of\_hn

An HN-filtered object $`E` satisfies $`\mathcal{P}(\ge t)` if all its phases are $`\ge t` and the filtration length is positive.

Proof: Direct from the definition: the lowest phase $`\phi^- = \phi_n \ge t` by hypothesis.

{docstring CategoryTheory.Triangulated.Slicing.geProp_of_hn}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20geProp_of_hn&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.geProp_of_hn%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_closedUnderIso

The property $`\mathcal{P}(> t)` is closed under isomorphisms: if $`E \cong E'` and $`E \in \mathcal{P}(> t)`, then $`E' \in \mathcal{P}(> t)`.

Proof: Zero objects are preserved under isomorphisms. For the non-zero case, transport the HN filtration across the isomorphism using `HNFiltration.ofIso`.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_closedUnderIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_closedUnderIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_closedUnderIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_of\_hn

An HN-filtered object $`E` satisfies $`\mathcal{P}(> t)` if all its phases are $`> t` and the filtration length is positive.

Proof: Direct from the definition: the lowest phase $`\phi^- = \phi_{n}` is $`> t` by hypothesis.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_of_hn}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_of_hn&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_of_hn%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_closedUnderIso

The property $`\mathcal{P}(\le t)` is closed under isomorphisms.

Proof: Transport the HN filtration across the isomorphism using `HNFiltration.ofIso`; the phase bounds are preserved.

{docstring CategoryTheory.Triangulated.Slicing.leProp_closedUnderIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_closedUnderIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_closedUnderIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_of\_hn

An HN-filtered object $`E` satisfies $`\mathcal{P}(\le t)` if all its phases are $`\le t` and the filtration length is positive.

Proof: Direct from the definition: the highest phase $`\phi^+ = \phi_1 \le t` by hypothesis.

{docstring CategoryTheory.Triangulated.Slicing.leProp_of_hn}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_of_hn&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_of_hn%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_closedUnderIso

The property $`\mathcal{P}(< t)` is closed under isomorphisms.

Proof: Transport the HN filtration across the isomorphism using `HNFiltration.ofIso`; the strict phase bounds are preserved.

{docstring CategoryTheory.Triangulated.Slicing.ltProp_closedUnderIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_closedUnderIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ltProp_closedUnderIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_of\_hn

An HN-filtered object $`E` satisfies $`\mathcal{P}(< t)` if all its phases are $`< t` and the filtration length is positive.

Proof: Direct from the definition: the highest phase $`\phi^+ = \phi_1 < t` by hypothesis.

{docstring CategoryTheory.Triangulated.Slicing.ltProp_of_hn}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_of_hn&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ltProp_of_hn%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.HNOperations%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
