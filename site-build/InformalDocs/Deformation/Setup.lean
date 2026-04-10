import BridgelandStability.Deformation.Setup
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: Setup" =>
%%%
htmlSplit := .never
%%%

# SectorFiniteLength

The predicate asserting that for a stability condition $`\sigma` and parameter $`\varepsilon_0 > 0`, every interval subcategory $`\mathcal{P}((t - 2\varepsilon_0, t + 2\varepsilon_0))` has strict finite length. This is the thin-sector hypothesis used to start the deformation argument.

Construction: A universal quantification over $`t \in \mathbb{R}`: for each $`t`, every object in $`\mathcal{P}((t - 2\varepsilon_0, t + 2\varepsilon_0))` is both strict Artinian and strict Noetherian.


{docstring CategoryTheory.Triangulated.SectorFiniteLength}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20SectorFiniteLength&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SectorFiniteLength%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Setup%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_epsilon0

Given a stability condition $`\sigma`, there exists a positive real $`\varepsilon_0 < 1/8` such that for all $`t \in \mathbb{R}`, every object in the interval subcategory $`\mathcal{P}((t - 4\varepsilon_0, t + 4\varepsilon_0))` has strict finite length. The width $`8\varepsilon_0` is chosen to fit inside the local finiteness parameter $`2\eta`.

Proof: Extract $`\eta > 0` from the local finiteness axiom and set $`\varepsilon_0 = \eta/4`. Then $`4\varepsilon_0 = \eta`, so each window of radius $`4\varepsilon_0` is exactly the local finiteness window of radius $`\eta`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_epsilon0}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_epsilon0&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_epsilon0%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Setup%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_epsilon0\_sector

Variant of $`\varepsilon_0` extraction providing $`2\varepsilon_0`-intervals for the sector bound: there exists $`\varepsilon_0 < 1/4` such that every $`\mathcal{P}((t - 2\varepsilon_0, t + 2\varepsilon_0))` has strict finite length.

Proof: Set $`\varepsilon_0 = \eta/2` where $`\eta` is the local finiteness parameter, so $`2\varepsilon_0 = \eta`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_epsilon0_sector}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_epsilon0_sector&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_epsilon0_sector%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Setup%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# slicingDist\_le\_of\_near

If $`\sigma` and $`\tau` have pointwise phase bounds $`|\phi^+(E; \sigma) - \phi^+(E; \tau)| \le \varepsilon` and $`|\phi^-(E; \sigma) - \phi^-(E; \tau)| \le \varepsilon` for all nonzero $`E`, then $`d(\mathcal{P}, \mathcal{Q}) \le \varepsilon`.

Proof: Delegates to `slicingDist_le_of_phase_bounds`, which packages the pointwise bounds into the supremum definition of slicing distance.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.slicingDist_le_of_near}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20slicingDist_le_of_near&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.slicingDist_le_of_near%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Setup%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# WideSectorFiniteLength

The wide local-finiteness predicate: every interval of radius $`4\varepsilon_0` has strict finite length. This is the witness needed to apply Lemma 7.7 in the windows $`\mathcal{P}((t - 3\varepsilon_0, t + 5\varepsilon_0))`.

Construction: A universal quantification over $`t \in \mathbb{R}`: for each $`t`, every object in $`\mathcal{P}((t - 4\varepsilon_0, t + 4\varepsilon_0))` is both strict Artinian and strict Noetherian.


{docstring CategoryTheory.Triangulated.WideSectorFiniteLength}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20WideSectorFiniteLength&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.WideSectorFiniteLength%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Setup%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_semistable\_near

Phase confinement. If $`d(\sigma.\mathcal{P}, \tau.\mathcal{P}) < \varepsilon` and $`E` is $`\tau`-semistable of phase $`\phi`, then $`E` lies in the $`\sigma`-interval subcategory $`\mathcal{P}((\phi - \varepsilon, \phi + \varepsilon))`. This is the fundamental input for the deformation construction.

Proof: From the slicing distance bound, extract HN phase bounds $`\phi^+(E), \phi^-(E) \in (\phi - \varepsilon, \phi + \varepsilon)`. Each HN factor phase is then sandwiched between these bounds by monotonicity.

{docstring CategoryTheory.Triangulated.intervalProp_of_semistable_near}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_semistable_near&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalProp_of_semistable_near%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Setup%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_widen

Embedding an interval in a wider one centered at the same point: if $`E \in \mathcal{P}((\phi - \varepsilon, \phi + \varepsilon))` and $`\varepsilon \le \varepsilon'`, then $`E \in \mathcal{P}((\phi - \varepsilon', \phi + \varepsilon'))`.

Proof: Immediate from interval monotonicity: $`(\phi - \varepsilon, \phi + \varepsilon) \subseteq (\phi - \varepsilon', \phi + \varepsilon')`.

{docstring CategoryTheory.Triangulated.intervalProp_widen}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_widen&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalProp_widen%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Setup%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_phiMinus\_in\_interval

If $`E \in \mathcal{P}((\phi - \varepsilon, \phi + \varepsilon))` is nonzero, then both $`\phi^+(E)` and $`\phi^-(E)` lie in the open interval $`(\phi - \varepsilon, \phi + \varepsilon)`.

Proof: Combines the four existing lemmas `phiPlus_gt/lt_of_intervalProp` and `phiMinus_gt/lt_of_intervalProp`.

{docstring CategoryTheory.Triangulated.phiPlus_phiMinus_in_interval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_phiMinus_in_interval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phiPlus_phiMinus_in_interval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Setup%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_phiMinus\_near

If $`d(\mathcal{P}, \mathcal{Q}) < \varepsilon` and $`E` is $`\tau`-semistable of phase $`\phi`, then both $`\sigma.\phi^+(E)` and $`\sigma.\phi^-(E)` lie in $`(\phi - \varepsilon, \phi + \varepsilon)`.

Proof: Compose `intervalProp_of_semistable_near` with `phiPlus_phiMinus_in_interval`.

{docstring CategoryTheory.Triangulated.phiPlus_phiMinus_near}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_phiMinus_near&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phiPlus_phiMinus_near%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Setup%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
