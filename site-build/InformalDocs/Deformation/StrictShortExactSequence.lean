import BridgelandStability.Deformation.StrictShortExactSequence
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: StrictShortExactSequence" =>
%%%
htmlSplit := .never
%%%

# Wobj\_cokernel\_pullback\_eq

For a strict monomorphism $`M \hookrightarrow X` and a strict monomorphism $`B \hookrightarrow \mathrm{coker}(M)`, the deformed charge of the cokernel of the pullback-cokernel subobject $`\pi^*B \hookrightarrow X` equals the deformed charge of the cokernel of $`B`: $`W([\mathrm{coker}(\pi^*B)]) = W([\mathrm{coker}(B)])`. This reflects a $`K_0` cancellation in the diamond of subobjects.

Proof: Three instances of the strict short exact sequence $`K_0` identity `interval_K0_of_strictMono` give: $`W(X) = W(M) + W(\mathrm{coker}(M))`, $`W(X) = W(\pi^*B) + W(\mathrm{coker}(\pi^*B))`, and $`W(\mathrm{coker}(M)) = W(B) + W(\mathrm{coker}(B))`. Combined with `Wobj_pullback_eq_add` giving $`W(\pi^*B) = W(M) + W(B)`, the four equations yield $`W(\mathrm{coker}(\pi^*B)) = W(\mathrm{coker}(B))` by cancellation.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.Wobj_cokernel_pullback_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20Wobj_cokernel_pullback_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.Wobj_cokernel_pullback_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Wobj\_liftSub\_cokernel\_eq\_add

For strict monomorphisms $`A \hookrightarrow M \hookrightarrow X` in the thin interval category, the deformed charge of the cokernel of the composed inclusion $`A \hookrightarrow X` (the `liftSub` subobject) satisfies $`W([\mathrm{coker}(A \hookrightarrow X)]) = W([\mathrm{coker}(A \hookrightarrow M)]) + W([\mathrm{coker}(M \hookrightarrow X)])`. This is the $`W`-additivity for a three-term filtration step.

Proof: Three $`K_0` additivity identities from `interval_K0_of_strictMono` give $`W(X) = W(M) + W(\mathrm{coker}(M))`, $`W(M) = W(A) + W(\mathrm{coker}(A \hookrightarrow M))`, and $`W(X) = W(\mathrm{liftA}) + W(\mathrm{coker}(\mathrm{liftA}))`. Since $`\mathrm{liftA}` is isomorphic to $`A` (the underlying object is the same), we have $`W(\mathrm{liftA}) = W(A)`, and cancelling $`W(A)` from both expansions of $`W(X)` yields the result.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.Wobj_liftSub_cokernel_eq_add}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20Wobj_liftSub_cokernel_eq_add&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.Wobj_liftSub_cokernel_eq_add%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Wobj\_pullback\_eq\_add

For a strict monomorphism $`M \hookrightarrow X` and a subobject $`B` of $`\mathrm{coker}(M)`, the deformed charge of the pullback-cokernel subobject satisfies $`W([\pi^*B]) = W([M]) + W([B])`. This is the $`W`-additivity for the strict short exact sequence $`0 \to M \to \pi^*B \to B \to 0` in the thin interval category.

Proof: The pair $`(M \le \pi^*B,\ \pi^*B \to B)` from `interval_le_pullback_cokernel` and `interval_ofLE_pullbackπ_eq_zero` assembles into a strict short exact sequence via `interval_strictShortExact_ofLE_pullbackπ_cokernel`. Then $`W`-additivity on strict short exact sequences (`ssf.strict_additive`) gives the formula.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.Wobj_pullback_eq_add}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20Wobj_pullback_eq_add&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.Wobj_pullback_eq_add%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_first\_strictShortExact\_of\_not\_semistable\_of\_finite\_leftHeartSubobjects

If an interval object $`X` is not W-semistable at its own W-phase and has finite subobject lattice in the left heart, then $`X` admits Bridgeland's first strict short exact sequence: a proper strict subobject $`M` with $`\operatorname{wPhaseOf}(W(M)) > \operatorname{wPhaseOf}(W(X))` that is itself W-semistable.

Proof: Finiteness of the left-heart subobject lattice implies finiteness of the strict subobject set. Apply `exists_first_strictShortExact_of_not_semistable` with this finite witness.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable_of_finite_leftHeartSubobjects}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_first_strictShortExact_of_not_semistable_of_finite_leftHeartSubobjects&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable_of_finite_leftHeartSubobjects%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_cokernel\_lt\_of\_phase\_gt\_strictSubobject

If $`M` is a strict subobject of W-semistable $`X` with $`\operatorname{wPhaseOf}(W(M)) > \psi`, then the cokernel has $`\operatorname{wPhaseOf}(W(\operatorname{coker})) < \psi`.

Proof: From $`W(X) = W(M) + W(\operatorname{coker})` and $`\operatorname{wPhaseOf}(W(X)) = \psi < \operatorname{wPhaseOf}(W(M))`, the dual see-saw gives $`\operatorname{wPhaseOf}(W(\operatorname{coker})) < \psi`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.phase_cokernel_lt_of_phase_gt_strictSubobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_cokernel_lt_of_phase_gt_strictSubobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.phase_cokernel_lt_of_phase_gt_strictSubobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_le\_of\_strictQuotient\_of\_window

A strict quotient of a W-semistable object in a windowed interval has W-phase at least $`\psi`, with the stronger hypothesis that the window satisfies the enveloping condition.

Proof: Extract the distinguished triangle from the strict short exact sequence and apply `phase_le_of_triangle_quotient`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.phase_le_of_strictQuotient_of_window}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_le_of_strictQuotient_of_window&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.phase_le_of_strictQuotient_of_window%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_cokernel\_of\_minPhase\_strictKernel

If $`M` is a strict subobject of a W-semistable object $`X` with $`\operatorname{wPhaseOf}(W(M)) > \psi`, then the strict cokernel is W-semistable at phase $`\operatorname{wPhaseOf}(W(\operatorname{coker}))`.

Proof: The strict short exact sequence $`M \hookrightarrow X \twoheadrightarrow Q` gives $`W(X) = W(M) + W(Q)`. The phase see-saw forces $`\operatorname{wPhaseOf}(W(Q)) < \psi`. For any further subobject of $`Q`, iterate the $`K_0` argument.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_cokernel_of_minPhase_strictKernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_cokernel\_nonzero\_of\_ne\_top

If $`M` is a strict subobject of $`X` in the thin interval category with $`M \ne \top` (i.e., $`M` is a proper strict subobject), then $`\mathrm{coker}(M \hookrightarrow X)` is nonzero. Contrapositively, if the cokernel vanishes then the inclusion is an epimorphism, hence an isomorphism (since it is also a strict monomorphism), so $`M = \top`.

Proof: If $`\mathrm{coker}(M) \cong 0`, then $`M.\mathrm{arrow}` is both a strict mono and (by `Preadditive.epi_of_isZero_cokernel`) an epi, so it is an isomorphism. Then `Subobject.eq_top_of_isIso_arrow` gives $`M = \top`, contradicting $`M \ne \top`.

{docstring CategoryTheory.Triangulated.interval_cokernel_nonzero_of_ne_top}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_cokernel_nonzero_of_ne_top&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_cokernel_nonzero_of_ne_top%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_lt\_pullback\_cokernel\_of\_ne\_bot

If $`B \ne \bot` is a nonzero subobject of $`\mathrm{coker}(M)`, then the pullback $`\pi^*B` is strictly larger than $`M` in the subobject lattice of $`X`: $`M < \pi^*B`. This is a strict version of `interval_le_pullback_cokernel` exploiting that a non-bottom subobject of the cokernel pulls back strictly above $`M`.

Proof: Equality $`M = \pi^*B` would force the pullback projection $`\pi^* B \to B` to be zero (via `interval_ofLE_pullbackπ_eq_zero` and the iso-arrow), but the pullback projection is a strict epi (by `interval_pullbackπ_strictEpi_of_strictEpi`), hence an epi, and a zero epi forces $`B \cong 0`, i.e., $`B = \bot`, contradicting $`B \ne \bot`.

{docstring CategoryTheory.Triangulated.interval_lt_pullback_cokernel_of_ne_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_lt_pullback_cokernel_of_ne_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_lt_pullback_cokernel_of_ne_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_pullback\_cokernel\_bot\_eq

The pullback of $`\bot` along the cokernel projection $`\operatorname{coker}(M) \twoheadrightarrow \cdot` recovers $`M` itself.

Proof: The pullback of $`\bot` is the kernel of the cokernel projection, which equals $`M` by the universal property of strict monos.

{docstring CategoryTheory.Triangulated.interval_pullback_cokernel_bot_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_pullback_cokernel_bot_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_pullback_cokernel_bot_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_pullback\_cokernel\_ne\_top\_of\_ne\_top

If $`B` is a proper strict subobject of $`\mathrm{coker}(M)` (i.e., $`B \ne \top`), then the pullback $`\pi^*B` is a proper subobject of $`X`: $`\pi^*B \ne \top`. This is a contrapositive: if $`\pi^*B = \top`, we can invert its arrow and factor the cokernel projection through $`B`, forcing $`B.\mathrm{arrow}` to be epi, hence (being a strict mono) an iso, giving $`B = \top`.

Proof: If $`\pi^*B = \top`, then $`\pi^*B.\mathrm{arrow}` is an isomorphism. The retraction $`r = (\pi^*B.\mathrm{arrow})^{-1} \circ (\pi^*\pi)\colon X \to B` satisfies $`r \circ B.\mathrm{arrow} = q` (the cokernel projection), which forces $`B.\mathrm{arrow}` to be epi. Since $`B.\mathrm{arrow}` is also a strict mono, it is an isomorphism, so `Subobject.eq_top_of_isIso_arrow` gives $`B = \top`.

{docstring CategoryTheory.Triangulated.interval_pullback_cokernel_ne_top_of_ne_top}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_pullback_cokernel_ne_top_of_ne_top&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_pullback_cokernel_ne_top_of_ne_top%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_pullback\_ofLE\_comm

For subobjects $`A' \le B'` of $`\mathrm{coker}(M)`, the pullbacks satisfy the naturality square: the canonical map $`\pi^*A' \to \pi^*B'` followed by the pullback projection $`\pi^*B' \to B'` equals the pullback projection $`\pi^*A' \to A'` followed by the inclusion $`A' \le B'`. In short, the pullback functor $`\pi^*(-)` commutes with the `ofLE` inclusion morphisms.

Proof: The proof cancels the monomorphism $`B'.\mathrm{arrow}` and then traces the square through the pullback equations and `Subobject.ofLE_arrow`, using the two pullback square commutativity identities $`(\pi^*B').\mathrm{arrow} \circ q = (\pi^*\pi_B) \circ B'.\mathrm{arrow}` and analogously for $`A'`.

{docstring CategoryTheory.Triangulated.interval_pullback_ofLE_comm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_pullback_ofLE_comm&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_pullback_ofLE_comm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_interval\_inclusion

W-semistability transfers across an arbitrary interval inclusion $`\mathcal{P}((a_1, b_1)) \hookrightarrow \mathcal{P}((a_2, b_2))` satisfying the thinness and enveloping constraints.

Proof: Compose `semistable_of_lower_inclusion` with interval monotonicity.

{docstring CategoryTheory.Triangulated.semistable_of_interval_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_interval_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.semistable_of_interval_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_lower\_inclusion

W-semistability is preserved under inclusion into a wider interval $`\mathcal{P}((a', b'))` with $`a' \le a` and $`b' \ge b`, provided the wider interval still satisfies the thinness constraint.

Proof: The W-semistability data (interval membership, phase equality, and the subobject phase inequality) all transfer to the wider interval since distinguished triangles with vertices in the narrower interval remain in the wider one.

{docstring CategoryTheory.Triangulated.semistable_of_lower_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_lower_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.semistable_of_lower_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_target\_envelope

W-semistability transfers under the enveloping condition: if the W-phase $`\psi` satisfies $`a' + \varepsilon_0 \le \psi \le b' - \varepsilon_0` for a new interval $`(a', b')`.

Proof: Combine the interval transfer lemmas with verification of the enveloping constraints.

{docstring CategoryTheory.Triangulated.semistable_of_target_envelope}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_target_envelope&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.semistable_of_target_envelope%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_target\_subinterval

W-semistability transfers to a target subinterval: if $`E` is W-semistable in $`\mathcal{P}((a, b))` and $`E \in \mathcal{P}((a', b'))` with $`a \le a'` and $`b' \le b`, then $`E` is W-semistable in $`\mathcal{P}((a', b'))`.

Proof: Subobject triangles with vertices in the narrower interval remain in the wider one, so the W-semistability condition is preserved.

{docstring CategoryTheory.Triangulated.semistable_of_target_subinterval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_target_subinterval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.semistable_of_target_subinterval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.StrictShortExactSequence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
