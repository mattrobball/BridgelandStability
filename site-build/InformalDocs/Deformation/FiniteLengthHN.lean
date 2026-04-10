import BridgelandStability.Deformation.FiniteLengthHN
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: FiniteLengthHN" =>
%%%
htmlSplit := .never
%%%

# hn\_exists\_in\_thin\_interval

Every nonzero object in a thin finite-length interval $`\mathcal{P}((a,b))` admits an HN filtration with $`\operatorname{ssf}`-semistable factors whose phases lie in $`(L, U)`, given a global $`W`-phase window $`(L, U)` of width $`< 1`, Hom vanishing for semistable objects, and a destabilizing phase bound. This is the legacy interface to `hn_exists_in_thin_interval_of_quotientLowerBound` obtained by feeding in the global lower window bound $`L`.

Proof: Derives the quotient lower bound from the global window: every proper strict quotient is nonzero, hence its $`W`-phase is $`> L` by the window hypothesis. Then delegates to `hn_exists_in_thin_interval_of_quotientLowerBound`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.hn_exists_in_thin_interval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hn_exists_in_thin_interval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.hn_exists_in_thin_interval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FiniteLengthHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hn\_exists\_in\_thin\_interval\_of\_quotientLowerBound

Given a thin finite-length interval $`\mathcal{P}((a,b))` and a nonzero interval object $`X`, if every proper strict quotient of $`X` has $`W`-phase strictly greater than a given lower bound $`t`, then $`X` admits an HN filtration with $`\operatorname{ssf}`-semistable factors whose phases all lie in $`(t, U)`. This is the faithful Bridgeland \S7 recursion with the paper's $`G/H`-style input exposed: the lower phase bound for quotients is propagated through the recursive kernel step to smaller strict subobjects.

Proof: By well-founded induction on the strict-subobject poset of $`X`. If $`X` is already $`W`-semistable, a single-factor filtration suffices. Otherwise, extract a strict MDQ $`q : X \twoheadrightarrow B` and its kernel $`K = \ker(q)`. Lift $`K` to a strict subobject $`T < X`, recurse on $`T` with the MDQ phase $`\psi(B)` as the new lower bound, then assemble the resulting filtration by appending $`B` as the last factor.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hn_exists_in_thin_interval_of_quotientLowerBound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FiniteLengthHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hn\_exists\_in\_thin\_interval\_of\_strictQuotientLowerBound

Quotient-form wrapper for the faithful \S7 HN recursion: the lower phase bound is stated for nonzero strict quotients $`X \twoheadrightarrow B` rather than cokernel subobjects. This is the interface closest to Bridgeland's classes $`G` and $`H`, converted internally to the kernel/cokernel subobject language used by the recursion.

Proof: Translates the strict-quotient lower bound into the cokernel-subobject language (each strict quotient corresponds to a cokernel of a strict mono), then delegates to `hn_exists_in_thin_interval_of_quotientLowerBound`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.hn_exists_in_thin_interval_of_strictQuotientLowerBound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hn_exists_in_thin_interval_of_strictQuotientLowerBound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.hn_exists_in_thin_interval_of_strictQuotientLowerBound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FiniteLengthHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_of\_postnikovTower

If all factors of a Postnikov tower have phases strictly greater than $`t` (i.e., lie in $`\mathcal{P}(>t)`), then the total object also lies in $`\mathcal{P}(>t)`.

Proof: By induction on the tower length: the base is the zero object (which trivially satisfies $`\mathcal{P}(>t)`), and each extension step uses `gtProp_of_triangle` applied to the distinguished triangle at the next level.

{docstring CategoryTheory.Triangulated.gtProp_of_postnikovTower}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_of_postnikovTower&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.gtProp_of_postnikovTower%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FiniteLengthHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_chain\_of\_postnikovTower

If all factors of a Postnikov tower lie in $`\mathcal{P}((a,b))`, then every intermediate chain object of the tower also lies in $`\mathcal{P}((a,b))`.

Proof: By induction on $`k`: the base object is zero (hence in $`\mathcal{P}((a,b))`), and each step applies `intervalProp_of_triangle` to the distinguished triangle connecting the $`k`-th chain object, its successor, and the corresponding factor.

{docstring CategoryTheory.Triangulated.intervalProp_chain_of_postnikovTower}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_chain_of_postnikovTower&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalProp_chain_of_postnikovTower%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FiniteLengthHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_postnikovTower

If all factors of a Postnikov tower lie in $`\mathcal{P}((a,b))`, then the total object also lies in $`\mathcal{P}((a,b))`.

Proof: This follows immediately from `intervalProp_chain_of_postnikovTower` applied at the top of the tower, using the isomorphism between the top chain object and the total object.

{docstring CategoryTheory.Triangulated.intervalProp_of_postnikovTower}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_postnikovTower&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalProp_of_postnikovTower%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FiniteLengthHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_of\_postnikovTower

If all factors of a Postnikov tower have phases strictly less than $`t` (i.e., lie in $`\mathcal{P}(<t)`), then the total object also lies in $`\mathcal{P}(<t)`.

Proof: By induction on the tower length, applying `ltProp_of_triangle` at each extension step, analogously to `gtProp_of_postnikovTower`.

{docstring CategoryTheory.Triangulated.ltProp_of_postnikovTower}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_of_postnikovTower&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.ltProp_of_postnikovTower%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.FiniteLengthHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
