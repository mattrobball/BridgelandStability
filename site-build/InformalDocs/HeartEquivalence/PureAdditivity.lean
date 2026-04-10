import BridgelandStability.HeartEquivalence.PureAdditivity
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "HeartEquivalence: PureAdditivity" =>
%%%
htmlSplit := .never
%%%

# ZOnHeartK0\_heartCohClass

$`Z_{K_0}(\texttt{heartCohClass}(n, E)) = (-1)^{|n|} \cdot Z(H^n_t(E))`.

Proof: Unfolds the definition of $`\texttt{heartCohClass}`, applies $`\texttt{map\_zsmul}`, and uses $`Z_{K_0}([H]) = Z(H)`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.ZOnHeartK0_heartCohClass}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ZOnHeartK0_heartCohClass&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.ZOnHeartK0_heartCohClass%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ZOnHeartK0\_heartCohClassSum\_eq\_top\_of\_pure

For a pure object $`X` concentrated in degree $`n`, the heart central charge applied to the alternating sum of heart cohomology classes equals $`Z(X)`.

Proof: The cohomology class sum has only the degree-$`n` term nonzero (all other $`\texttt{heartCohClass}` vanish outside the support). Simplifies using $`\texttt{ZOnHeartK0\_heartCohClassSum\_of\_pure}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.ZOnHeartK0_heartCohClassSum_eq_top_of_pure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ZOnHeartK0_heartCohClassSum_eq_top_of_pure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.ZOnHeartK0_heartCohClassSum_eq_top_of_pure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ZOnHeartK0\_heartCohClassSum\_of\_pure

For a pure object of degree $`n`, the Euler-form-weighted central charge sum $`Z_{K_0}(\texttt{heartCohClassSum}(b, m, X))` simplifies to a single term.

Proof: All heart cohomology classes outside degree $`n` vanish; the single remaining term is computed from $`\texttt{ZOnHeartK0\_heartCohClass}` and purity.

{docstring CategoryTheory.Triangulated.HeartStabilityData.ZOnHeartK0_heartCohClassSum_of_pure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ZOnHeartK0_heartCohClassSum_of_pure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.ZOnHeartK0_heartCohClassSum_of_pure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ambientZ

If the Euler lift is triangle-additive, the heart central charge extends to an ambient homomorphism $`K_0(\mathcal{C}) \to \mathbb{C}`.

Construction: Lifts $`E \mapsto \texttt{eulerZObj}(E)` through the universal property of $`K_0(\mathcal{C})`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.ambientZ}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ambientZ&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.ambientZ%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ambientZ\_comp\_heartK0ToK0

$`\texttt{ambientZ} \circ \texttt{heartK0ToK0} = Z_{K_0}`.

Proof: On heart generators $`[E]`, both sides evaluate to $`Z(E)`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.ambientZ_comp_heartK0ToK0}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ambientZ_comp_heartK0ToK0&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.ambientZ_comp_heartK0ToK0%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ambientZ\_eq\_ZOnHeartK0\_comp\_heartK0FromK0

$`\texttt{ambientZ} = Z_{K_0} \circ \texttt{heartK0FromK0}`.

Proof: Both sides agree on generators by definition.

{docstring CategoryTheory.Triangulated.HeartStabilityData.ambientZ_eq_ZOnHeartK0_comp_heartK0FromK0}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ambientZ_eq_ZOnHeartK0_comp_heartK0FromK0&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.ambientZ_eq_ZOnHeartK0_comp_heartK0FromK0%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ambientZ\_of

$`\texttt{ambientZ}([E]) = \texttt{eulerZObj}(E)`.

Proof: Immediate from the lifting construction.

{docstring CategoryTheory.Triangulated.HeartStabilityData.ambientZ_of}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ambientZ_of&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.ambientZ_of%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj

The object-level central charge candidate: $`\texttt{eulerZObj}(E) = Z_{K_0}(\texttt{heartEulerClassObj}(E)) \in \mathbb{C}`.

Construction: Composes the Euler class lift to $`K_0(\operatorname{heart})` with the descended heart central charge $`Z_{K_0}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_additive\_of\_heart\_shortExact

The Euler-form central charge $`\texttt{eulerZObj}` is additive over short exact sequences in the heart: for $`0 \to A \to B \to Q \to 0`, $`\texttt{eulerZObj}(B) = \texttt{eulerZObj}(A) + \texttt{eulerZObj}(Q)`.

Proof: Reduces to the linearity of $`Z_{K_0}` over the heart Grothendieck group, using that $`\texttt{heartEulerClassObj}` maps short exact sequences to the $`K_0` relation.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_additive_of_heart_shortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_additive_of_heart_shortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_additive_of_heart_shortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_eq\_truncLT\_add\_heartCohClass

The Euler class satisfies the peeling formula: $`\texttt{eulerZObj}(E) = \texttt{eulerZObj}(\tau^{<a} E) + Z_{K_0}(\texttt{heartCohClass}(a, E))`.

Proof: Applies $`Z_{K_0}` to the peeling identity $`\texttt{heartEulerClassObj\_eq\_truncLT\_add\_heartCohClass}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_eq_truncLT_add_heartCohClass}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_eq_truncLT_add_heartCohClass&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_eq_truncLT_add_heartCohClass%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_eq\_truncLT\_add\_truncGE

The Euler-form central charge satisfies: $`\texttt{eulerZObj}(E) = \texttt{eulerZObj}(\tau^{<a} E) + \texttt{eulerZObj}(\tau^{\ge a} E)`.

Proof: Uses $`\texttt{eulerZObj\_eq\_truncLT\_add\_heartCohClass}` and the identification of the heart cohomology class with the Euler class of the pure truncation.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_eq_truncLT_add_truncGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_eq_truncLT_add_truncGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_eq_truncLT_add_truncGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_eq\_zero\_of\_isZero

If $`E` is zero, then $`\texttt{eulerZObj}(E) = 0`.

Proof: All heart cohomology objects of the zero object are zero, so the Euler class is $`0` and $`Z_{K_0}(0) = 0`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_eq_zero_of_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_eq_zero_of_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_eq_zero_of_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_isTriangleAdditive

If the Euler class lift is triangle-additive, then so is the object-level central charge $`\texttt{eulerZObj}`.

Proof: Applies the group homomorphism $`Z_{K_0}` to the triangle-additivity relation for $`\texttt{heartEulerClassObj}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_isTriangleAdditive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_isTriangleAdditive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_isTriangleAdditive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_of\_heart

For a heart object $`E`, $`\texttt{eulerZObj}(E) = Z(E)`.

Proof: Follows from $`\texttt{heartEulerClassObj\_of\_heart}` and the definition of $`Z_{K_0}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_of_heart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_of_heart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_of_heart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_of\_heart\_shift

For a heart object $`E` and integer $`n`, $`\texttt{eulerZObj}(E[-n]) = (-1)^{|n|} \cdot Z(E)`.

Proof: Uses $`\texttt{heartEulerClassObj\_of\_heart\_shift}` and the definition of $`Z_{K_0}` on $`\texttt{HeartK0}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_of_heart_shift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_of_heart_shift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_of_heart_shift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_of\_pure

For a pure object $`X` concentrated in degree $`n`, $`\texttt{eulerZObj}(X) = (-1)^{|n|} \cdot Z(\texttt{heartShiftOfPure}(X, n))`.

Proof: Applies $`Z_{K_0}` to $`\texttt{heartEulerClassObj\_of\_pure}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_of_pure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_of_pure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_of_pure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_triangle\_of\_pure\_distTriang

For a distinguished triangle concentrated in a single degree $`n`, the Euler-form central charge satisfies the triangle relation: $`\texttt{eulerZObj}(X_2) = \texttt{eulerZObj}(X_1) + \texttt{eulerZObj}(X_3)`.

Proof: Applies $`Z_{K_0}` to the heart-$`K_0` relation $`\texttt{heartK0\_relation\_of\_pure\_distTriang}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_triangle_of_pure_distTriang}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_triangle_of_pure_distTriang&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_triangle_of_pure_distTriang%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_eq\_of\_bounds

The alternating heart cohomology class sum is independent of the choice of bounds, as long as the bounds contain the amplitude of $`X`.

Proof: Uses $`\texttt{heartCohClass\_eq\_zero\_of\_lt\_bound}` and $`\texttt{heartCohClass\_eq\_zero\_of\_gt\_bound}` to show the extra terms vanish outside the amplitude.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_of_bounds}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_eq_of_bounds&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_of_bounds%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_eq\_single\_of\_pure

For a pure object concentrated in degree $`n`, the alternating heart cohomology class sum $`\texttt{heartCohClassSum}(b, m, X)` (with $`b \le n \le b+m`) equals the single term $`\texttt{heartCohClass}(n, X)`.

Proof: All terms except index $`n` vanish by $`\texttt{heartCohClass\_eq\_zero\_of\_gt\_pure}` and $`\texttt{heartCohClass\_eq\_zero\_of\_lt\_pure}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_single_of_pure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_eq_single_of_pure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_single_of_pure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_eq\_top\_of\_pure

For a pure object concentrated in degree $`n`, the alternating sum $`\texttt{heartCohClassSum}(b, m, X)` (with $`b \le n \le b+m`) equals the parity-weighted class: $`(-1)^{|n|} \cdot [\texttt{heartShiftOfPure}(X, n)]`.

Proof: Uses $`\texttt{heartCohClassSum\_eq\_single\_of\_pure}` and then the definition of $`\texttt{heartCohClass}` and $`\texttt{heartCoh}` for a pure object.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_top_of_pure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_eq_top_of_pure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_top_of_pure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_eq\_zero\_of\_gt\_bound

If $`n < b` (i.e., the entire range $`[b, b+m]` is above the support), then $`\texttt{heartCohClassSum}(b, m, X) = 0` for $`X \in \mathcal{C}^{\le n}`.

Proof: Each summand $`\texttt{heartCohClass}(b+j, X)` vanishes by $`\texttt{heartCohClass\_eq\_zero\_of\_gt\_bound}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_zero_of_gt_bound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_eq_zero_of_gt_bound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_zero_of_gt_bound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_eq\_zero\_of\_isZero

If $`E` is zero, then $`\texttt{heartCohClassSum}(b, n, E) = 0`.

Proof: Each summand $`\texttt{heartCohClass}(b+j, E)` vanishes since the zero object has all heart cohomology zero.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_zero_of_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_eq_zero_of_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_zero_of_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_eq\_zero\_of\_lt\_bound

If $`b + n < m` (i.e., the entire range $`[b, b+n]` is below the support), then $`\texttt{heartCohClassSum}(b, n, X) = 0` for $`X \in \mathcal{C}^{\ge m}`.

Proof: Each summand vanishes by $`\texttt{heartCohClass\_eq\_zero\_of\_lt\_bound}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_zero_of_lt_bound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_eq_zero_of_lt_bound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_eq_zero_of_lt_bound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_of\_truncLT

For $`n < a`, $`\texttt{heartCohClassSum}(b, n, \tau^{<a} E) = \texttt{heartCohClassSum}(b, n, E)`.

Proof: Each summand satisfies $`\texttt{heartCohClass}(b+j, \tau^{<a} E) = \texttt{heartCohClass}(b+j, E)` for $`b+j \le n < a` by $`\texttt{heartCohClass\_of\_truncLT}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_of_truncLT}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_of_truncLT&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_of_truncLT%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_pred\_upper

The alternating sum from $`b` to $`b+n` equals the sum from $`b` to $`b+n-1` plus the $`(b+n)`th cohomology class.

Proof: Peels off the top term using $`\texttt{heartCohClassSum\_succ}` shifted by one.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_pred_upper}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_pred_upper&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_pred_upper%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_shrink\_lower

The alternating sum $`\texttt{heartCohClassSum}(b, n, E)` for $`E \in \mathcal{C}^{\ge b}` equals the sum starting at $`b+1`, if the $`b`th cohomology class vanishes.

Proof: The first term $`\texttt{heartCohClass}(b, E) = 0` by the lower bound hypothesis; the remaining sum is $`\texttt{heartCohClassSum}(b+1, n-1, E)`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_shrink_lower}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_shrink_lower&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_shrink_lower%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_shrink\_upper

The alternating sum $`\texttt{heartCohClassSum}(b, n, E)` for $`E \in \mathcal{C}^{\le b+n}` equals the sum ending at $`b+n-1`, if the $`(b+n)`th cohomology class vanishes.

Proof: The last term $`\texttt{heartCohClass}(b+n, E) = 0` by the upper bound hypothesis; the remaining sum is $`\texttt{heartCohClassSum}(b, n-1, E)`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_shrink_upper}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_shrink_upper&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_shrink_upper%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_eq\_pureClass

The heart cohomology class $`\texttt{heartCohClass}(n, E)` equals the purity-weighted class $`\texttt{pureClass}(n, E)`.

Proof: Follows from the definition of $`\texttt{pureClass}` and $`\texttt{heartCohClass}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_pureClass}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_eq_pureClass&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_pureClass%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_eq\_zero\_of\_gt\_bound

If $`n < m` and $`X \in \mathcal{C}^{\le n}`, then $`\texttt{heartCohClass}(m, X) = 0`.

Proof: The pure truncation $`\tau^{[m,m]} X` vanishes because $`\tau^{\ge m}` of $`\tau^{\le m} X \cong X` is zero for $`m > n`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_gt_bound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_eq_zero_of_gt_bound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_gt_bound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_eq\_zero\_of\_gt\_pure

If $`X` is a pure object of degree $`n` and $`m > n`, then $`\texttt{heartCohClass}(m, X) = 0`.

Proof: The pure truncation $`\tau^{[m,m]} X` vanishes since $`X \in \mathcal{C}^{\le n}` and $`m > n`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_gt_pure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_eq_zero_of_gt_pure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_gt_pure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_eq\_zero\_of\_isZero

If $`E` is zero, then $`\texttt{heartCohClass}(n, E) = 0` for all $`n`.

Proof: All truncations of the zero object are zero, so $`H^n_t(0) = 0` and $`[0] = 0` in $`K_0`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_eq_zero_of_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_eq\_zero\_of\_lt\_bound

If $`m < n` and $`X \in \mathcal{C}^{\ge n}`, then $`\texttt{heartCohClass}(m, X) = 0`.

Proof: The pure truncation $`\tau^{[m,m]} X` vanishes because $`\tau^{\le m} X = 0`, so the heart cohomology is zero and its $`K_0`-class vanishes.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_lt_bound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_eq_zero_of_lt_bound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_lt_bound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_eq\_zero\_of\_lt\_pure

If $`X` is a pure object of degree $`n` and $`m < n`, then $`\texttt{heartCohClass}(m, X) = 0`.

Proof: The pure truncation $`\tau^{[m,m]} X` vanishes since $`X \in \mathcal{C}^{\ge n}` and $`m < n`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_lt_pure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_eq_zero_of_lt_pure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_zero_of_lt_pure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_of\_heart\_shift

For a heart object $`E` and integer $`n`, $`\texttt{heartCohClass}(n, E[-n]) = (-1)^{|n|} \cdot [E]` in $`K_0(\operatorname{heart})`.

Proof: The heart cohomology of a pure object concentrated in degree $`n` is isomorphic to $`E` itself after shifting back. The result follows from $`\texttt{heartCohObjIsoOfHeartShift}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_of_heart_shift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_of_heart_shift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_of_heart_shift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_of\_truncGE\_of\_isLE

For $`X \in \mathcal{C}^{\le a}`, $`\texttt{heartCohClass}(a, \tau^{\ge a} X) = \texttt{heartCohClass}(a, X)`.

Proof: Uses the isomorphism $`\texttt{heartCohIso\_of\_truncGE\_of\_isLE}` and invariance of $`K_0`-classes under isomorphism.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_of_truncGE_of_isLE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_of_truncGE_of_isLE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_of_truncGE_of_isLE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_of\_truncLT

For $`n < a`, $`\texttt{heartCohClass}(n, \tau^{<a} E) = \texttt{heartCohClass}(n, E)`.

Proof: Follows from the isomorphism $`\texttt{heartCohIso\_of\_truncLT}` and invariance of $`K_0`-classes under isomorphism.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_of_truncLT}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_of_truncLT&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_of_truncLT%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohIso\_of\_pure

For a pure object concentrated in degree $`n`, $`H^n_t(X) \cong \texttt{heartShiftOfPure}(X, n)`.

Construction: The pure truncation $`\tau^{[n,n]} X \cong X` (since $`X` is already concentrated in degree $`n`), and shifting by $`n` gives the heart object $`\texttt{heartShiftOfPure}(X, n)`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohIso_of_pure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohIso_of_pure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohIso_of_pure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohIso\_of\_truncGE\_of\_isLE

Truncating below degree $`a` does not change the degree-$`a` heart cohomology object when the original object is $`t`-nonpositive in degree $`a`: $`H^a_t(\tau^{\ge a} X) \cong H^a_t(X)` for $`X \in \mathcal{C}^{\le a}`.

Construction: The $`\tau^{\ge a}`-projection $`X \to \tau^{\ge a} X` induces an isomorphism on $`\tau^{[a,a]}` when $`X \in \mathcal{C}^{\le a}`, which after shifting by $`a` gives the heart isomorphism.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohIso_of_truncGE_of_isLE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohIso_of_truncGE_of_isLE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohIso_of_truncGE_of_isLE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohIso\_of\_truncLT

Truncating above degree $`a` does not change the $`n`th heart cohomology when $`n < a`: $`H^n_t(\tau^{<a} E) \cong H^n_t(E)`.

Construction: The truncation map $`\tau^{<a} E \hookrightarrow E` induces an isomorphism on $`\tau^{[n,n]}` for $`n < a` because $`\tau^{\le n}` commutes with the inclusion.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohIso_of_truncLT}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohIso_of_truncLT&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohIso_of_truncLT%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_eq\_heartCohClassSum

The Euler class lift equals the heart cohomology class sum for any choice of bounds $`[b, a]` containing the amplitude of $`X`.

Proof: Uses the bound-independence lemma $`\texttt{heartCohClassSum\_eq\_of\_bounds}` to equate the sum for the chosen classical bounds with the sum for the given bounds.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_eq_heartCohClassSum}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_eq_heartCohClassSum&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_eq_heartCohClassSum%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_eq\_truncLT\_add\_heartCohClass

The Euler class satisfies a peeling formula: $`\texttt{heartEulerClassObj}(E) = \texttt{heartEulerClassObj}(\tau^{<a} E) + \texttt{heartCohClass}(a, E)`.

Proof: Writes the sum from $`b` to $`a` as the sum from $`b` to $`a-1` plus the $`a`-th term, then identifies the partial sum with the Euler class of the truncation using $`\texttt{heartCohClass\_of\_truncLT}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_eq_truncLT_add_heartCohClass}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_eq_truncLT_add_heartCohClass&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_eq_truncLT_add_heartCohClass%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_eq\_truncLT\_add\_truncGE

The Euler class satisfies: $`\texttt{heartEulerClassObj}(E) = \texttt{heartEulerClassObj}(\tau^{<a} E) + \texttt{heartEulerClassObj}(\tau^{\ge a} E) - \texttt{heartEulerClassObj}(\tau^{<a}(\tau^{\ge a} E))`.

Proof: Combines $`\texttt{heartEulerClassObj\_eq\_truncLT\_add\_heartCohClass}` with the identification of the heart cohomology class of $`E` at degree $`a` with that of $`\tau^{\ge a} E` via $`\texttt{heartCohClass\_of\_truncGE\_of\_isLE}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_eq_truncLT_add_truncGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_eq_truncLT_add_truncGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_eq_truncLT_add_truncGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_eq\_zero\_of\_isZero

If $`E` is zero, then $`\texttt{heartEulerClassObj}(E) = 0`.

Proof: The alternating sum is empty or all terms are zero since $`H^n_t(0) = 0`; alternatively, uses $`\texttt{heartCohClassSum\_eq\_zero\_of\_isZero}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_eq_zero_of_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_eq_zero_of_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_eq_zero_of_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_of\_heart

For a heart object $`E`, the Euler lift is $`[E]` itself: $`\texttt{heartEulerClassObj}(E) = [E] \in K_0(\operatorname{heart})`.

Proof: A heart object is concentrated in degree $`0`, so the alternating sum reduces to the single term $`[H^0_t(E)] = [E]`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_heart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_of_heart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_heart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_of\_heart\_shift

For a heart object $`E` and integer $`n`, $`\texttt{heartEulerClassObj}(E[-n]) = (-1)^{|n|} \cdot [E]` in $`K_0(\operatorname{heart})`.

Proof: The object $`E[-n]` is pure of degree $`n`, so the alternating sum reduces to a single term $`\texttt{heartCohClass}(n, E[-n]) = (-1)^{|n|} \cdot [E]` by $`\texttt{heartCohClass\_of\_heart\_shift}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_heart_shift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_of_heart_shift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_heart_shift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_of\_pure

For a pure object $`X` concentrated in degree $`n`, $`\texttt{heartEulerClassObj}(X) = (-1)^{|n|} \cdot [\texttt{heartShiftOfPure}(X, n)]`.

Proof: Reduces to a single-term sum by $`\texttt{heartCohClassSum\_eq\_single\_of\_pure}` and then uses $`\texttt{heartCohClass}` for the single term.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_pure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_of_pure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_pure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_of\_truncGE\_of\_isLE

For $`X \in \mathcal{C}^{\le a}`, $`\texttt{heartEulerClassObj}(\tau^{\ge a} X) = \texttt{heartCohClass}(a, X)`.

Proof: The truncation $`\tau^{\ge a} X` is pure of degree $`a` when $`X \in \mathcal{C}^{\le a}`, so the sum reduces to the single degree-$`a` term.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_truncGE_of_isLE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_of_truncGE_of_isLE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_truncGE_of_isLE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_triangle\_of\_pure\_distTriang

For a pure distinguished triangle concentrated in degree $`n`, $`\texttt{heartEulerClassObj}(X_2) = \texttt{heartEulerClassObj}(X_1) + \texttt{heartEulerClassObj}(X_3)`.

Proof: All three objects are pure of degree $`n`; the sum reduces to a single-term identity using $`\texttt{heartK0\_relation\_of\_pure\_distTriang}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_triangle_of_pure_distTriang}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_triangle_of_pure_distTriang&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_triangle_of_pure_distTriang%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0EquivK0

If the Euler lift is triangle-additive, the canonical map $`K_0(\operatorname{heart}(t)) \to K_0(\mathcal{C})` is an isomorphism of abelian groups.

Construction: An $`\texttt{AddEquiv}` built from $`\texttt{heartK0ToK0}` and $`\texttt{heartK0FromK0}`, with the two round-trip identities as proofs.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0EquivK0}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0EquivK0&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0EquivK0%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0FromK0

The canonical map $`K_0(\mathcal{C}) \to K_0(\operatorname{heart})` induced by the Euler-class lift, assuming triangle additivity.

Construction: Lifts $`E \mapsto \texttt{heartEulerClassObj}(E)` through the universal property of $`K_0(\mathcal{C})`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0FromK0}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0FromK0&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0FromK0%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0FromK0\_comp\_heartK0ToK0

The composition $`\texttt{heartK0FromK0} \circ \texttt{heartK0ToK0} = \operatorname{id}_{K_0(\operatorname{heart})}`.

Proof: On generators $`[E]` for heart objects, the round-trip gives $`[E]` by $`\texttt{heartEulerClassObj\_of\_heart}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0FromK0_comp_heartK0ToK0}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0FromK0_comp_heartK0ToK0&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0FromK0_comp_heartK0ToK0%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0FromK0\_of

$`\texttt{heartK0FromK0}([E]) = \texttt{heartEulerClassObj}(E)`.

Proof: Immediate from the lifting construction.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0FromK0_of}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0FromK0_of&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0FromK0_of%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0ToK0\_comp\_heartK0FromK0

The composition $`\texttt{heartK0ToK0} \circ \texttt{heartK0FromK0} = \operatorname{id}_{K_0(\mathcal{C})}`.

Proof: On generators $`[E]`, the round-trip gives $`[E]` by $`\texttt{heartK0ToK0\_heartEulerClassObj}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_comp_heartK0FromK0}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0ToK0_comp_heartK0FromK0&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_comp_heartK0FromK0%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0\_relation\_of\_pure\_distTriang

A distinguished triangle concentrated in a single $`t`-degree $`n` yields the expected short exact relation in the heart Grothendieck group after shifting by $`n`.

Proof: Shifting the triangle by $`n` places all three vertices in the heart. The shifted triangle is then a short exact sequence in the heart, and the $`K_0` relation follows from $`\texttt{HeartK0.of\_shortExact}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0_relation_of_pure_distTriang}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0_relation_of_pure_distTriang&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0_relation_of_pure_distTriang%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.PureAdditivity%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
