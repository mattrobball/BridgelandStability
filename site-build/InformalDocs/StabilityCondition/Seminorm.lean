import BridgelandStability.StabilityCondition.Seminorm
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityCondition: Seminorm" =>
%%%
htmlSplit := .never
%%%

# finiteSeminormSubgroup

The finite seminorm subgroup $`V(\sigma) = \{\, U \in \operatorname{Hom}(\Lambda, \mathbb{C}) : \|U\|_\sigma < \infty \,\}`. On a connected component of $`\operatorname{Stab}(\mathcal{D})`, this subgroup is independent of the chosen $`\sigma` (by Lemma 6.2).

Construction: Defined as the `AddSubgroup` of $`\Lambda \to \mathbb{C}` consisting of those $`U` with finite Bridgeland seminorm. Closure under addition uses the seminorm triangle inequality; closure under negation uses $`\|-U\|_\sigma = \|U\|_\sigma`.


{docstring CategoryTheory.Triangulated.finiteSeminormSubgroup}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20finiteSeminormSubgroup&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.finiteSeminormSubgroup%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# finiteSeminormSubgroup\_eq\_of\_basisNhd

Proposition 6.3 (V equality for nearby stability conditions). If $`\tau \in B_\varepsilon(\sigma)` with $`\varepsilon < 1/8`, then $`V(\sigma) = V(\tau)`. The key inequality is $`\sin(\pi\varepsilon)(1 + \cos(\pi\varepsilon)) < \cos^2(\pi\varepsilon)` for $`\varepsilon < 1/8`, which ensures the reverse comparison $`\|\sigma.Z - \tau.Z\|_\tau < \cos(\pi\varepsilon)`.

Proof: Forward direction uses `stabSeminorm_lt_top_of_near`. Reverse direction bounds $`\|\sigma.Z - \tau.Z\|_\tau` via the explicit seminorm comparison, then verifies $`M_Z / (c - M_Z) < c` using the trigonometric inequality $`\sin(x)(1 + \cos(x)) < \cos^2(x)` for $`x = \pi\varepsilon`.

{docstring CategoryTheory.Triangulated.finiteSeminormSubgroup_eq_of_basisNhd}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20finiteSeminormSubgroup_eq_of_basisNhd&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.finiteSeminormSubgroup_eq_of_basisNhd%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# finiteSeminormSubgroup\_eq\_of\_same\_Z

Proposition 6.3 (same $`Z` case). If $`\sigma.Z = \tau.Z` and $`d(\mathcal{P}, \mathcal{Q}) < \varepsilon < 1/2`, then $`V(\sigma) = V(\tau)`.

Proof: Applies `stabSeminorm_lt_top_of_same_Z` in both directions (swapping $`\sigma` and $`\tau` and using symmetry of the slicing distance).

{docstring CategoryTheory.Triangulated.finiteSeminormSubgroup_eq_of_same_Z}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20finiteSeminormSubgroup_eq_of_same_Z&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.finiteSeminormSubgroup_eq_of_same_Z%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# instPseudoEMetricSpaceSlicing

**\[Lemma 6.1\]** pseudo-emetric (not generalized metric: missing separation); Lean uses sup of phase differences, paper uses inf of containment radii — equivalence not proved

The space of slicings of $`\mathcal{C}` carries a pseudo-extended-metric structure with distance $`d(\mathcal{P}, \mathcal{Q}) = \sup_{0 \neq E} \max(|\phi^+_{\mathcal{P}}(E) - \phi^+_{\mathcal{Q}}(E)|, |\phi^-_{\mathcal{P}}(E) - \phi^-_{\mathcal{Q}}(E)|)`, corresponding to Lemma 6.1 of Bridgeland.

Construction: The `edist` field is `slicingDist`; the three axioms (self-distance zero, symmetry, triangle inequality) are supplied by `slicingDist_self`, `slicingDist_symm`, and `slicingDist_triangle`. Note this is a pseudo-emetric (distances may be $`+\infty` and distinct slicings may have distance zero), not a genuine metric.


{docstring CategoryTheory.Triangulated.instPseudoEMetricSpaceSlicing}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20instPseudoEMetricSpaceSlicing&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.instPseudoEMetricSpaceSlicing%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Lemma%206.1%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_semistable\_slicingDist

Lemma 6.1 (one direction). If $`d(\mathcal{P}_1, \mathcal{P}_2) < \varepsilon` and $`E` is $`\mathcal{P}_2`-semistable of phase $`\phi`, then $`\phi_1^+(E), \phi_1^-(E) \in (\phi - \varepsilon, \phi + \varepsilon)`. In words: the HN phases of a semistable object with respect to one slicing are controlled by the slicing distance.

Proof: Uses `phiPlus_eq_phiMinus_of_semistable` to replace both $`\phi_2^\pm(E)` by $`\phi`, then applies the phase difference bounds.

{docstring CategoryTheory.Triangulated.intervalProp_of_semistable_slicingDist}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_semistable_slicingDist&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalProp_of_semistable_slicingDist%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# norm\_Z\_le\_of\_tau\_semistable

For a $`\tau`-semistable nonzero object $`E` with $`d(\sigma, \tau) < \varepsilon < 1/2` and $`\|\tau.Z - \sigma.Z\|_\sigma \leq M`, one has $`(1 - M/\cos(\pi\varepsilon)) \cdot \|\sigma.Z([E])\| \leq \|\tau.Z([E])\|`. This controls $`\|Z([E])\|` by $`\|W([E])\|` via the reverse triangle inequality and the sector bound.

Proof: The $`\sigma`-HN width of $`E` is less than $`2\varepsilon` (from semistability and the metric bound). Applies the sector bound with $`\eta = 2\varepsilon` and $`U = \tau.Z - \sigma.Z`, then uses the reverse triangle inequality.

{docstring CategoryTheory.Triangulated.norm_Z_le_of_tau_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20norm_Z_le_of_tau_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.norm_Z_le_of_tau_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_sub\_lt\_of\_slicingDist

If $`d(\mathcal{P}_1, \mathcal{P}_2) < \varepsilon`, then $`|\phi_1^-(E) - \phi_2^-(E)| < \varepsilon` for every nonzero $`E`. This is the $`\phi^-` direction of Lemma 6.1.

Proof: Identical to `phiPlus_sub_lt_of_slicingDist` using the $`\phi^-` component of the maximum.

{docstring CategoryTheory.Triangulated.phiMinus_sub_lt_of_slicingDist}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_sub_lt_of_slicingDist&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phiMinus_sub_lt_of_slicingDist%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_sub\_lt\_of\_slicingDist

If $`d(\mathcal{P}_1, \mathcal{P}_2) < \varepsilon`, then $`|\phi_1^+(E) - \phi_2^+(E)| < \varepsilon` for every nonzero $`E`. This is one direction of Lemma 6.1.

Proof: Contrapositive: if $`|\phi_1^+(E) - \phi_2^+(E)| \geq \varepsilon`, then the supremum defining $`d` is at least $`\varepsilon`.

{docstring CategoryTheory.Triangulated.phiPlus_sub_lt_of_slicingDist}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_sub_lt_of_slicingDist&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phiPlus_sub_lt_of_slicingDist%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# sector\_bound

Sector bound (Lemma 6.2 core). For a stability condition $`\sigma = (Z, \mathcal{P})` and $`U \colon \Lambda \to \mathbb{C}`, if $`\|U([A])\| \leq M \cdot \|Z([A])\|` for every semistable factor $`A`, then for any object $`E` with HN phase width at most $`\eta < 1`, $`\|U([E])\| \leq \frac{M}{\cos(\pi\eta/2)} \cdot \|Z([E])\|`. This is the quantitative heart of Bridgeland's seminorm comparison theory.

Proof: Decomposes $`U([E]) = \sum U([F_i])` and $`Z([E]) = \sum Z([F_i])` via the HN filtration and $`K_0` additivity. Bounds $`\sum \|U([F_i])\| \leq M \sum \|Z([F_i])\|` pointwise, then applies the sector estimate $`\cos(\pi\eta/2) \cdot \sum \|Z([F_i])\| \leq \|Z([E])\|`.

{docstring CategoryTheory.Triangulated.sector_bound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20sector_bound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.sector_bound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# sector\_bound'

Variant of the sector bound using the intrinsic phase width $`\phi^+(E) - \phi^-(E) \leq \eta`.

Proof: Reduces to `sector_bound` by extracting the canonical HN filtration and its intrinsic width.

{docstring CategoryTheory.Triangulated.sector_bound'}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20sector_bound%27&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.sector_bound%27%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# slicingDist\_le\_of\_phase\_bounds

Converse direction: if $`|\phi_1^+(E) - \phi_2^+(E)| \leq \varepsilon` and $`|\phi_1^-(E) - \phi_2^-(E)| \leq \varepsilon` for all nonzero $`E`, then $`d(\mathcal{P}_1, \mathcal{P}_2) \leq \varepsilon`.

Proof: Takes the supremum of the pointwise bounds.

{docstring CategoryTheory.Triangulated.slicingDist_le_of_phase_bounds}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20slicingDist_le_of_phase_bounds&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.slicingDist_le_of_phase_bounds%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# slicingDist\_self

The Bridgeland generalized metric is zero on the diagonal: $`d(\mathcal{P}, \mathcal{P}) = 0`.

Proof: Each phase difference is $`|\phi^\pm(E) - \phi^\pm(E)| = 0`, so the supremum is $`0`.

{docstring CategoryTheory.Triangulated.slicingDist_self}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20slicingDist_self&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.slicingDist_self%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# slicingDist\_symm

The Bridgeland generalized metric is symmetric: $`d(\mathcal{P}_1, \mathcal{P}_2) = d(\mathcal{P}_2, \mathcal{P}_1)`.

Proof: Follows from $`|a - b| = |b - a|` applied to each phase difference.

{docstring CategoryTheory.Triangulated.slicingDist_symm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20slicingDist_symm&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.slicingDist_symm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# slicingDist\_triangle

The Bridgeland generalized metric satisfies the triangle inequality: $`d(\mathcal{P}_1, \mathcal{P}_3) \leq d(\mathcal{P}_1, \mathcal{P}_2) + d(\mathcal{P}_2, \mathcal{P}_3)`.

Proof: For each nonzero $`E`, applies the absolute value triangle inequality $`|a - c| \leq |a - b| + |b - c|` to both $`\phi^+` and $`\phi^-`, then takes the supremum.

{docstring CategoryTheory.Triangulated.slicingDist_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20slicingDist_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.slicingDist_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_bound\_real

For $`\sigma`-semistable nonzero $`A` of phase $`\psi`, the ratio $`\|U([A])\| / \|Z([A])\|` is bounded by the toReal of the Bridgeland seminorm $`\|U\|_\sigma`.

Proof: The ratio is one term in the supremum defining $`\|U\|_\sigma`, so it is at most the supremum. Converts via `ENNReal.toReal_mono` and clears the division.

{docstring CategoryTheory.Triangulated.stabSeminorm_bound_real}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_bound_real&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_bound_real%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_le\_of\_near

General Lemma 6.2 (explicit seminorm bound). If $`d(\mathcal{P}, \mathcal{Q}) < \varepsilon < 1/2` and $`\|\tau.Z - \sigma.Z\|_\sigma < \cos(\pi\varepsilon)`, then $`\|U\|_\tau \leq \frac{\|U\|_\sigma}{\cos(\pi\varepsilon) - \|\tau.Z - \sigma.Z\|_\sigma}`.

Proof: Uses the sector bound on each $`\tau`-semistable object (HN width $`< 2\varepsilon`) with the pointwise seminorm bound and the reverse triangle inequality estimate on $`\|Z([E])\|`.

{docstring CategoryTheory.Triangulated.stabSeminorm_le_of_near}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_le_of_near&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_le_of_near%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_lt\_top\_of\_near

General Lemma 6.2 (seminorm finiteness comparison). Under the hypotheses of `stabSeminorm_le_of_near`, $`\|U\|_\sigma < \infty` implies $`\|U\|_\tau < \infty`.

Proof: Immediate from `stabSeminorm_le_of_near` since the bound is finite.

{docstring CategoryTheory.Triangulated.stabSeminorm_lt_top_of_near}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_lt_top_of_near&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_lt_top_of_near%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_lt\_top\_of\_same\_Z

Seminorm comparison for same central charge. If $`\sigma` and $`\tau` share the same $`Z` and $`d(\mathcal{P}, \mathcal{Q}) < \varepsilon < 1/2`, then $`\|U\|_\tau < \infty` whenever $`\|U\|_\sigma < \infty`. This shows $`V(\sigma) \subseteq V(\tau)` for nearby conditions with the same charge.

Proof: Bounds each term in $`\|U\|_\tau` using the sector bound: the $`\sigma`-HN width of each $`\tau`-semistable object is at most $`2\varepsilon`, so $`\|U([E])\| / \|\tau.Z([E])\| \leq M / \cos(\pi\varepsilon)`.

{docstring CategoryTheory.Triangulated.stabSeminorm_lt_top_of_same_Z}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_lt_top_of_same_Z&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_lt_top_of_same_Z%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_nonneg

The Bridgeland seminorm is nonnegative: $`\|U\|_\sigma \geq 0`. Trivially true since $`\|U\|_\sigma \in \mathbb{R}_{\geq 0}^\infty`.

Proof: Immediate from the definition of $`\mathbb{R}_{\geq 0}^\infty`.

{docstring CategoryTheory.Triangulated.stabSeminorm_nonneg}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_nonneg&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_nonneg%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabSeminorm\_zero

The seminorm at zero is zero: $`\|0\|_\sigma = 0`.

Proof: Each term in the supremum is $`\|0\| / \|Z([E])\| = 0`.

{docstring CategoryTheory.Triangulated.stabSeminorm_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabSeminorm_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.stabSeminorm_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityCondition.Seminorm%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
