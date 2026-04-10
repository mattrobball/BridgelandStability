import BridgelandStability.Deformation.HNFiltrationAssembly
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: HNFiltrationAssembly" =>
%%%
htmlSplit := .never
%%%

# append\_hn\_filtration\_of\_triangle

Concatenate HN filtrations across a distinguished triangle $`X \to E \to Y \to X[1]`: given filtrations $`G_X` of $`X` and $`G_Y` of $`Y` with all phases of $`G_Y` strictly less than all phases of $`G_X`, produce a filtration $`G` of $`E` whose phases are all $`> t`. This is the generic Postnikov-splicing step for assembling the faithful \S7 HN filtration from filtrations on successive $`\sigma`-semistable factors.

Proof: Induction on the length of $`G_Y`. Base: $`Y = 0` implies $`X \cong E`, transport $`G_X`. Inductive step: if $`n(G_Y) = 1`, use `appendFactor` directly. Otherwise, peel off the last factor of $`G_Y` via an octahedral axiom construction, recurse on the prefix, then append the last factor.

{docstring CategoryTheory.Triangulated.append_hn_filtration_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20append_hn_filtration_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.append_hn_filtration_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HNFiltrationAssembly%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# append\_hn\_filtration\_of\_triangle\_le

Upper-bound companion for `append_hn_filtration_of_triangle`: if all input phases of $`G_X` and $`G_Y` are $`\le U`, then all output phases of $`G` are also $`\le U`. Follows from the phase structure of `appendFactor`.

Proof: Same induction as `append_hn_filtration_of_triangle`, additionally tracking the upper bound $`U` through each recursive call. The `appendFactor` construction preserves the upper bound since it assigns phases from the input filtrations.

{docstring CategoryTheory.Triangulated.append_hn_filtration_of_triangle_le}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20append_hn_filtration_of_triangle_le&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.append_hn_filtration_of_triangle_le%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HNFiltrationAssembly%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_hn\_length\_one

An HN filtration of length one certifies that the object is semistable: if $`G` is an HN filtration of $`Y` with $`n = 1`, then $`Y \in \mathcal{P}(\phi_0)`. The single distinguished triangle $`0 \to E_1 \to F_0` with $`E_0 = 0` gives $`E_1 \cong F_0` and $`E_1 \cong Y` (via the top isomorphism), so $`Y \cong F_0 \in \mathcal{P}(\phi_0)`.

Proof: The zeroth triangle has $`T.\mathrm{obj}_1 \cong 0` (base), so $`T.\mathrm{mor}_2` is an isomorphism. Compose with the top isomorphism to get $`F_0 \cong Y`, then transport the semistability through the isomorphism.

{docstring CategoryTheory.Triangulated.semistable_of_hn_length_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_hn_length_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.semistable_of_hn_length_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HNFiltrationAssembly%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# split\_hn\_filtration\_at\_cutoff

Split an HN filtration $`F` of $`A` at an arbitrary cutoff $`t`: there exist objects $`X, Y` with filtrations $`G_X, G_Y`, a distinguished triangle $`X \to A \to Y \to X[1]`, with all phases of $`G_X` strictly $`> t` and all phases of $`G_Y` at most $`t`. The $`Y`-part phases are bounded below by the last phase of $`F`, and $`G_X` phases are a subset of $`F` phases.

Proof: Induction on the length of $`F`. Base: $`n = 0` gives trivial splits. Inductive step: if the last phase $`\phi_{n-1} > t`, the entire filtration goes to $`X`. If $`n = 1` and $`\phi_0 \le t`, everything goes to $`Y`. Otherwise, recurse on the prefix of $`F` (dropping the last factor), then re-attach the last factor via the distinguished triangle from the original filtration.

{docstring CategoryTheory.Triangulated.split_hn_filtration_at_cutoff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20split_hn_filtration_at_cutoff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.split_hn_filtration_at_cutoff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HNFiltrationAssembly%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
