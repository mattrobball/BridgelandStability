import BridgelandStability.Deformation.DeformedGtLe
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: DeformedGtLe" =>
%%%
htmlSplit := .never
%%%

# P\_in\_deformedGtPred

$`\mathcal{P}(s) \subset Q(>t)` for $`s \ge t + \varepsilon` (Bridgeland p.24). A $`\sigma`-semistable object of phase $`s \ge t + \varepsilon` lies in $`Q(>t)`: obtain a $`Q`-HN filtration via `sigmaSemistable_hasDeformedHN`, split at $`t`, then show the $`Q(\le t)` part vanishes.

Proof: Get the Q-HN filtration with phases in $`(s - 2\varepsilon, s + 4\varepsilon)`. For the last nonzero factor $`j_0`, phase confinement gives $`s - \varepsilon < Q\text{-phase}(j_0)`. Since $`s \ge t + \varepsilon`, all Q-phases exceed $`t`. Build the extension closure witness from the Postnikov tower.

{docstring CategoryTheory.Triangulated.P_in_deformedGtPred}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_in_deformedGtPred&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.P_in_deformedGtPred%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedGtLe%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_in\_deformedLtPred

$`\mathcal{P}(s) \subset Q(<t)` for $`s \le t - \varepsilon` (dual). A $`\sigma`-semistable object of phase $`s \le t - \varepsilon` lies in $`Q(<t)`.

Proof: Dual of `P_in_deformedGtPred`: get Q-HN, find the first nonzero factor, use $`\phi^+(\text{factor}) \le s` and phase confinement to show all Q-phases are $`< t`.

{docstring CategoryTheory.Triangulated.P_in_deformedLtPred}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_in_deformedLtPred&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.P_in_deformedLtPred%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedGtLe%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedGtLe\_triangle

$`Q(>t)/Q(\le t)` truncation triangle (Bridgeland Step 2). For any object $`E`, there exists a distinguished triangle $`X \to E \to Y` with $`X \in Q(>t)` and $`Y \in Q(\le t)`.

Proof: Decompose $`E` via its $`\sigma`-HN filtration. Each $`\sigma`-semistable factor has a $`Q(>t)/Q(\le t)` truncation by `sigmaSemistable_deformedGtLe_triangle`. Assemble these via iterated octahedral axiom applications along the Postnikov tower.

{docstring CategoryTheory.Triangulated.deformedGtLe_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedGtLe_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.deformedGtLe_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedGtLe%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# sigmaSemistable\_deformedGtLe\_triangle

For a $`\sigma`-semistable object $`E` of phase $`s` and cutoff $`t` with $`s - \varepsilon < t < s + \varepsilon`, there exists a distinguished triangle $`X \to E \to Y` with $`X \in Q(>t)` and $`Y \in Q(\le t)`.

Proof: Get the Q-HN filtration. Split the Postnikov tower at the cutoff $`t`: factors with Q-phase $`> t` give $`X \in Q(>t)` and the rest give $`Y \in Q(\le t)`.

{docstring CategoryTheory.Triangulated.sigmaSemistable_deformedGtLe_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20sigmaSemistable_deformedGtLe_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.sigmaSemistable_deformedGtLe_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedGtLe%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
