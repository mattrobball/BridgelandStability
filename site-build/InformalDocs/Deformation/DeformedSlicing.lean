import BridgelandStability.Deformation.DeformedSlicing
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: DeformedSlicing" =>
%%%
htmlSplit := .never
%%%

# deformedSlicing

Deformed slicing (Nodes 7.Q + 7.6 + 7.7). The slicing $`Q` with $`Q(\psi) = \operatorname{deformedPred}(\sigma, W, \varepsilon, \psi)`, where $`\varepsilon < \varepsilon_0 < 1/10` is the perturbation parameter.

Construction: Constructed as a `Slicing` whose predicate is `deformedPred`. The `closedUnderIso` field transports W-semistability across isomorphisms. The `shift_iff` field uses `deformedPred_shift_one` and its converse. The `hom_vanishing` field is Lemma 7.6 via `hom_eq_zero_of_deformedPred`. The `hn_exists` field delegates to `deformedSlicing_hn_exists`.


{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedSlicing}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedSlicing&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedSlicing%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedSlicing\_compat

W-compatibility of the deformed slicing. For every nonzero $`Q`-semistable object $`E` of $`Q`-phase $`\psi`, the central charge $`W([E])` lies on the ray $`\mathbb{R}_+ \cdot e^{i\pi\psi}`.

Proof: The `Semistable` structure stores $`\operatorname{wPhaseOf}(W([E]), \alpha) = \psi`, which by `wPhaseOf_compat` gives $`W([E]) = \|W([E])\| \cdot e^{i\pi\psi}` with $`\|W([E])\| > 0`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedSlicing_compat}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedSlicing_compat&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedSlicing_compat%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformed\_intervalProp\_subset\_sigma\_intervalProp

A $`Q`-interval of radius $`\varepsilon_0` is contained in a $`\sigma`-interval of radius $`2\varepsilon_0`: $`\mathcal{Q}((t - \varepsilon_0, t + \varepsilon_0)) \subseteq \mathcal{P}((t - 2\varepsilon_0, t + 2\varepsilon_0))`.

Proof: For each $`Q`-HN factor of an object in $`\mathcal{Q}((t - \varepsilon_0, t + \varepsilon_0))`, phase confinement gives $`\sigma`-phases within $`\varepsilon` of the Q-phase, which lies in $`(t - \varepsilon_0, t + \varepsilon_0)`. Since $`\varepsilon < \varepsilon_0`, the $`\sigma`-phases lie in $`(t - 2\varepsilon_0, t + 2\varepsilon_0)`.

{docstring CategoryTheory.Triangulated.deformed_intervalProp_subset_sigma_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformed_intervalProp_subset_sigma_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.deformed_intervalProp_subset_sigma_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# sigma\_semistable\_intervalProp

Reverse phase confinement. If $`E` is $`\sigma`-semistable of phase $`\phi` and $`\|W - Z\|_\sigma < \sin(\pi\varepsilon)`, then $`E` lies in the $`Q`-interval $`\mathcal{Q}((\phi - 2\varepsilon - \delta, \phi + 4\varepsilon + \delta))` for any $`\delta > 0`.

Proof: Apply `sigmaSemistable_hasDeformedHN` to obtain a Q-HN filtration with phases in $`(\phi - 2\varepsilon, \phi + 4\varepsilon)`, then widen by $`\delta`.

{docstring CategoryTheory.Triangulated.sigma_semistable_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20sigma_semistable_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.sigma_semistable_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicing%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
