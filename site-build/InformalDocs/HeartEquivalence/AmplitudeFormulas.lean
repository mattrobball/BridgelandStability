import BridgelandStability.HeartEquivalence.AmplitudeFormulas
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "HeartEquivalence: AmplitudeFormulas" =>
%%%
htmlSplit := .never
%%%

# ZOnHeartK0\_heartCohClassSum\_of\_amp\_negOne\_zero

For $`X` of amplitude $`(-1, 0)`, $`Z_{K_0}(\sum (-1)^{|j|} [H^j_t(X)]) = -Z(K) + Z(Q)`.

Proof: Applies the group homomorphism $`Z_{K_0}` to $`\texttt{heartCohClassSum\_of\_amp\_negOne\_zero}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.ZOnHeartK0_heartCohClassSum_of_amp_negOne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ZOnHeartK0_heartCohClassSum_of_amp_negOne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.ZOnHeartK0_heartCohClassSum_of_amp_negOne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_of\_amp\_negOne\_zero

For $`X` of amplitude $`(-1, 0)`, $`\texttt{eulerZObj}(X) = -Z(K) + Z(Q)`.

Proof: Composes $`\texttt{heartEulerClassObj\_of\_amp\_negOne\_zero}` with $`Z_{K_0}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_of_amp_negOne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_of_amp_negOne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_of_amp_negOne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerZObj\_triangle\_of\_amp\_negOne\_zero

Triangle additivity of $`\texttt{eulerZObj}` for objects of amplitude $`(-1, 0)`: $`\texttt{eulerZObj}(X) = \texttt{eulerZObj}(K[1]) + \texttt{eulerZObj}(Q)`.

Proof: Analogous to $`\texttt{heartEulerClassObj\_triangle\_of\_amp\_negOne\_zero}`, applying $`Z_{K_0}` throughout.

{docstring CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_triangle_of_amp_negOne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerZObj_triangle_of_amp_negOne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.eulerZObj_triangle_of_amp_negOne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_of\_amp\_negOne\_zero

For $`X` of amplitude $`(-1, 0)` in a triangle $`K[1] \to X \to Q \to K[2]`, $`\sum_{j=-1}^{0} (-1)^{|j|} [H^j_t(X)] = -[K] + [Q]` in $`K_0(\operatorname{heart})`.

Proof: Evaluates the two-term sum using the cohomology isomorphisms $`H^{-1}_t(X) \cong K` and $`H^0_t(X) \cong Q`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_of_amp_negOne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_of_amp_negOne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_of_amp_negOne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCoh\_negOne\_iso\_of\_amp\_negOne\_zero

For an object of amplitude $`(-1, 0)` presented by a triangle $`K[1] \to X \to Q \to K[2]` with $`K, Q` in the heart, the $`(-1)`-st heart cohomology of $`X` is canonically isomorphic to $`K`.

Construction: Chains three isomorphisms: (1) $`\tau^{[-1,-1]} X \cong \tau^{[-1,0)} X` via the truncation comparison, (2) $`\tau^{[-1,0)} X \cong \tau^{<0} X` since $`X \in \mathcal{C}^{\ge -1}`, (3) $`\tau^{<0} X \cong K[1]` from the triangle isomorphism. Shifting by $`-1` recovers $`K`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCoh_negOne_iso_of_amp_negOne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCoh_negOne_iso_of_amp_negOne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCoh_negOne_iso_of_amp_negOne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCoh\_zero\_iso\_of\_amp\_negOne\_zero

For an object of amplitude $`(-1, 0)` presented by a triangle $`K[1] \to X \to Q \to K[2]` with $`K, Q` in the heart, the $`0`-th heart cohomology of $`X` is canonically isomorphic to $`Q`.

Construction: Chains isomorphisms: $`\tau^{[0,0]} X \cong \tau^{\ge 0} X` since $`X \in \mathcal{C}^{\le 0}`, then $`\tau^{\ge 0} X \cong Q` from the triangle isomorphism.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCoh_zero_iso_of_amp_negOne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCoh_zero_iso_of_amp_negOne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCoh_zero_iso_of_amp_negOne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_isTriangleAdditive

The Euler class lift $`E \mapsto \texttt{heartEulerClassObj}(E)` is additive on distinguished triangles (assuming $`H^0_t` is homological).

Proof: For an arbitrary distinguished triangle, chooses compatible bounds containing the amplitude of all three vertices (shifted appropriately), then delegates to $`\texttt{heartEulerClassObj\_triangle\_of\_bounds}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_isTriangleAdditive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_isTriangleAdditive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_isTriangleAdditive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_of\_amp\_negOne\_zero

For $`X` of amplitude $`(-1, 0)`, $`\texttt{heartEulerClassObj}(X) = -[K] + [Q]`.

Proof: Identifies the Euler class with the heart cohomology class sum via $`\texttt{heartEulerClassObj\_eq\_heartCohClassSum}`, then applies the amplitude formula.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_amp_negOne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_of_amp_negOne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_of_amp_negOne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_triangle\_of\_amp\_negOne\_zero

Triangle additivity of the Euler class for objects of amplitude $`(-1, 0)`: $`\texttt{heartEulerClassObj}(X) = \texttt{heartEulerClassObj}(K[1]) + \texttt{heartEulerClassObj}(Q)`.

Proof: Rewrites the Euler classes of $`K[1]` and $`Q` using the heart and heart-shift formulas, then matches with the amplitude formula.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_triangle_of_amp_negOne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_triangle_of_amp_negOne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_triangle_of_amp_negOne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj\_triangle\_of\_bounds

Full bounded triangle additivity: for a distinguished triangle $`X_1 \to X_2 \to X_3 \to X_1[1]` with compatible amplitude bounds, $`\texttt{heartEulerClassObj}(X_2) = \texttt{heartEulerClassObj}(X_1) + \texttt{heartEulerClassObj}(X_3)`.

Proof: Uses the five-term relation and a telescoping argument. The image terms vanish at the boundary degrees because the $`H^0` functor kills objects outside their amplitude range. The telescoping sum collapses by the standard Finset identity $`\sum_{j=0}^{m} (f(j) - f(j+1)) = f(0) - f(m+1)`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_triangle_of_bounds}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj_triangle_of_bounds&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj_triangle_of_bounds%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# triangleLTGE\_iso\_of\_amp\_negOne\_zero

For an object $`X` of amplitude $`(-1, 0)` presented by a distinguished triangle $`K[1] \to X \to Q \to K[2]` with $`K, Q` in the heart, the canonical truncation triangle $`\tau^{<0} X \to X \to \tau^{\ge 0} X` is isomorphic to this triangle via a triangle isomorphism fixing $`X`.

Proof: The amplitude hypothesis forces $`K[1] \in \mathcal{C}^{\le -1}` and $`Q \in \mathcal{C}^{\ge 0}`, so the given triangle satisfies the universal property of the truncation triangle. Uniqueness yields the isomorphism.

{docstring CategoryTheory.Triangulated.TStructure.triangleLTGE_iso_of_amp_negOne_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20triangleLTGE_iso_of_amp_negOne_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.triangleLTGE_iso_of_amp_negOne_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.AmplitudeFormulas%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
