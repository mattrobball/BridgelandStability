import BridgelandStability.Deformation.Theorem
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: Theorem" =>
%%%
htmlSplit := .never
%%%

# deformed

The canonical deformed stability condition attached to a nearby central charge $`W`. This packages the actual object constructed in the deformation proof as a `StabilityCondition.WithClassMap`, rather than hiding it behind an existential.

Construction: Constructs the deformed slicing $`Q` via `deformedSlicing`, pairs it with $`W` as the central charge, verifies compatibility, then establishes local finite length by showing each deformed interval $`Q((t - \varepsilon_0, t + \varepsilon_0))` embeds into the $`\sigma`-interval $`\mathcal{P}((t - 2\varepsilon_0, t + 2\varepsilon_0))` which has sector finite length.


{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformed}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformed&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformed%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Theorem%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformed\_Z

The central charge of the deformed stability condition is $`W`: $`\tau.Z = W`.

Proof: Definitional: `deformed` stores $`W` as its central charge component.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformed_Z}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformed_Z&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformed_Z%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Theorem%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_eq\_Z\_and\_slicingDist\_lt\_of\_stabSeminorm\_lt\_sin

**\[Theorem 7.1\]** ε₀ and WideSectorFiniteLength (= ∀ t, P((t-4ε₀,t+4ε₀)) per-object strict finite length) taken as parameters; both follow from local finiteness for ε₀ < η/4

Bridgeland's Theorem 7.1 (deformation of stability conditions). Under the small-deformation hypothesis $`\|W - Z\|_\sigma < \sin(\pi\varepsilon)`, there exists a locally-finite stability condition $`\tau = (W, Q)` with $`d(P, Q) < \varepsilon`.

Proof: The strict hypothesis $`\|W - Z\|_\sigma < \sin(\pi\varepsilon)` allows shrinking: find $`\varepsilon' < \varepsilon` with $`\|W - Z\|_\sigma < \sin(\pi\varepsilon')` via the intermediate value theorem (more precisely, by taking $`\varepsilon' = \operatorname{arcsin}(y)/\pi` where $`y` is the midpoint between the seminorm and $`\sin(\pi\varepsilon)`). Apply `slicingDist_deformed_le` at $`\varepsilon'` to get $`d(P, Q) \le \varepsilon' < \varepsilon`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_eq_Z_and_slicingDist_lt_of_stabSeminorm_lt_sin}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_eq_Z_and_slicingDist_lt_of_stabSeminorm_lt_sin&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_eq_Z_and_slicingDist_lt_of_stabSeminorm_lt_sin%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Theorem%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Theorem%207.1%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# slicingDist\_deformed\_le

The canonical deformation has slicing distance at most $`\varepsilon` from the original: $`d(P, Q) \le \varepsilon`.

Proof: Apply `slicingDist_le_of_phase_bounds`: show $`|\varphi^+(E; P) - \varphi^+(E; Q)| \le \varepsilon` and $`|\varphi^-(E; P) - \varphi^-(E; Q)| \le \varepsilon` for all nonzero $`E`. Forward direction (\sigma \to Q$`): Q`-HN factors are `deformedPred`, so phase confinement gives $`\sigma`-phases within $`\varepsilon` of $`Q`-phases. Reverse direction ($`Q \to \sigma`): $`\sigma`-HN factors are mapped into $`Q(> t)` and $`Q(< t)` predicates, giving $`Q`-phases within $`\varepsilon` of $`\sigma`-phases.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.slicingDist_deformed_le}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20slicingDist_deformed_le&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.slicingDist_deformed_le%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.Theorem%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
