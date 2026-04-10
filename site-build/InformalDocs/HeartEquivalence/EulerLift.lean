import BridgelandStability.HeartEquivalence.EulerLift
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "HeartEquivalence: EulerLift" =>
%%%
htmlSplit := .never
%%%

# H0FunctorObjIsoOfHeart

On objects already in the heart, the $`H^0` functor restricts to the identity: $`H^0_t(E) \cong E` for $`E \in \operatorname{heart}(t)`.

Construction: Composes the isomorphisms from $`\tau^{\le 0} E \cong E` and $`E \cong \tau^{\ge 0} E` (both isomorphisms because $`E` is in the heart) with the shift-by-zero identification.


{docstring CategoryTheory.Triangulated.HeartStabilityData.H0FunctorObjIsoOfHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0FunctorObjIsoOfHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0FunctorObjIsoOfHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0Functor\_isHomological\_of\_eval\_of\_heartSourceH0primeShortComplex

If the heart-source $`H^0{}'` short complex is exact for every heart source and every representable, then $`H^0_t` is a homological functor.

Proof: Reduces to the heart-case exactness criterion for the $`H^0{}'` functor by the comparison isomorphism between $`H^0` and $`H^0{}'`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_eval_of_heartSourceH0primeShortComplex}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor_isHomological_of_eval_of_heartSourceH0primeShortComplex&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_eval_of_heartSourceH0primeShortComplex%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0Functor\_isHomological\_of\_heartSourceH0primeShortComplex\_distTriang

If for every distinguished triangle with heart source the induced $`H^0{}'` short complex admits a compatible distinguished triangle, then $`H^0_t` is a homological functor.

Proof: Produces the required kernel witness from the distinguished triangle assumption via $`\texttt{heartSourceH0primeShortComplex\_f\_is\_kernel\_of\_distTriang}`, then applies $`\texttt{H0Functor\_isHomological\_of\_heartSourceH0primeShortComplex\_f\_is\_kernel}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_heartSourceH0primeShortComplex_distTriang}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor_isHomological_of_heartSourceH0primeShortComplex_distTriang&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_heartSourceH0primeShortComplex_distTriang%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0Functor\_isHomological\_of\_heartSourceH0primeShortComplex\_f\_is\_kernel

If for every distinguished triangle with heart source the first map of the heart-source $`H^0{}'` short complex is a kernel, then $`H^0_t` is a homological functor.

Proof: Applies $`\texttt{heartSourceH0primeShortComplex\_preadditiveCoyoneda\_exact\_of\_f\_is\_kernel}` to each representable and then uses $`\texttt{H0Functor\_isHomological\_of\_eval\_of\_heartSourceH0primeShortComplex}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_heartSourceH0primeShortComplex_f_is_kernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor_isHomological_of_heartSourceH0primeShortComplex_f_is_kernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_heartSourceH0primeShortComplex_f_is_kernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeObjIsoOfHeart

The primed $`H^0{}'` restricts to the identity on heart objects.

Construction: Composes the inverse of $`\texttt{H0ObjIsoH0prime}` with $`\texttt{H0FunctorObjIsoOfHeart}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoOfHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeObjIsoOfHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoOfHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeObjIsoOfHeart\_inv\_hom\_comp\_truncLEι

The composite of the inverse of $`\texttt{H0primeObjIsoOfHeart}` with the $`\tau^{\le 0}`-inclusion equals the $`\tau^{\ge 0}`-projection.

Proof: A direct computation using the definition of $`\texttt{H0primeObjIsoOfHeart}` and the $`\texttt{H0ObjIsoH0prime}` composition rules.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoOfHeart_inv_hom_comp_truncLEι}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeObjIsoOfHeart_inv_hom_comp_truncLE%CE%B9&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoOfHeart_inv_hom_comp_truncLE%CE%B9%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeObjIsoOfHeart\_inv\_hom\_comp\_truncLEι\_assoc

Associativity-reassociated form of $`\texttt{H0primeObjIsoOfHeart\_inv\_hom\_comp\_truncLE\iota}`.

Proof: Obtained from the non-assoc version by $`\texttt{reassoc}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoOfHeart_inv_hom_comp_truncLEι_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeObjIsoOfHeart_inv_hom_comp_truncLE%CE%B9_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoOfHeart_inv_hom_comp_truncLE%CE%B9_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_comp\_heartSourceNegOneToAShiftHom\_eq\_of\_comp\_truncGEπ\_zero

If $`m \circ \pi_{\ge 0} = 0`, then there exists $`u : E \to \tau^{(-1,0)}(X_3)` such that $`u \circ \texttt{heartSourceNegOneToAShiftHom} = m \circ \delta`.

Proof: Lifts $`m` through the $`\tau^{<0}`-truncation triangle using $`\texttt{Triangle.coyoneda\_exact}`, then computes the composite with $`\texttt{truncGE}(-1)`-projection using $`\texttt{truncLT\_map\_truncGEπ\_comp\_heartSourceNegOneToAShiftHom}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.exists_comp_heartSourceNegOneToAShiftHom_eq_of_comp_truncGEπ_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_comp_heartSourceNegOneToAShiftHom_eq_of_comp_truncGE%CF%80_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.exists_comp_heartSourceNegOneToAShiftHom_eq_of_comp_truncGE%CF%80_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_comp\_heartSourceNegOneToAShiftHom\_eq\_of\_toH0prime\_comp\_kernel

If the canonical lift $`\texttt{toH0prime}(f) \circ H^0{}'(g) = 0`, then there exists $`u` such that $`u \circ \texttt{heartSourceNegOneToAShiftHom} = f \circ g \circ \delta`.

Proof: Reduces to $`\texttt{exists\_comp\_heartSourceNegOneToAShiftHom\_eq\_of\_comp\_truncGEπ\_zero}` by converting the vanishing condition via $`\texttt{toH0primeHom\_eq\_zero\_iff}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.exists_comp_heartSourceNegOneToAShiftHom_eq_of_toH0prime_comp_kernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_comp_heartSourceNegOneToAShiftHom_eq_of_toH0prime_comp_kernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.exists_comp_heartSourceNegOneToAShiftHom_eq_of_toH0prime_comp_kernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_heartSourceNegOneToAShiftHom\_comp\_shift\_map\_factor

The composite $`\texttt{heartSourceNegOneToAShiftHom}(\delta) \circ f[1]` factors through the connecting morphism of the $`(-1,0)`-truncation triangle.

Proof: Checks the vanishing condition using the triangle relation $`\delta \circ f = 0` and $`\texttt{truncLT\_map\_truncGEπ\_comp\_heartSourceNegOneToAShiftHom}`, then applies the Yoneda exactness of the truncation triangle.

{docstring CategoryTheory.Triangulated.HeartStabilityData.exists_heartSourceNegOneToAShiftHom_comp_shift_map_factor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_heartSourceNegOneToAShiftHom_comp_shift_map_factor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.exists_heartSourceNegOneToAShiftHom_comp_shift_map_factor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass

The $`n`th heart cohomology class of $`E`, weighted by the parity sign: $`(-1)^{|n|} \cdot [H^n_t(E)] \in K_0(\operatorname{heart})`.

Construction: Defined as the integer scalar $`(-1)^{|n|}` applied to $`\texttt{HeartK0.of}(\texttt{heartCoh}(n, E))`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum

The finite alternating sum $`\sum_{j=0}^{n} \texttt{heartCohClass}(b+j, E)` of heart cohomology classes from degrees $`b` to $`b+n`.

Construction: A Finset sum over $`\texttt{Finset.range}(n+1)`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClassSum\_succ

The sum from $`b` to $`b+n+1` equals the sum from $`b` to $`b+n` plus the $`(b+n+1)`th class.

Proof: Immediate from $`\texttt{Finset.sum\_range\_succ}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_succ}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClassSum_succ&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClassSum_succ%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_eq\_H0FunctorShift

The heart cohomology class can equivalently be written using the shifted $`H^0` functor: $`\texttt{heartCohClass}(n, X) = (-1)^{|n|} \cdot [(H^0_t[n])(X)]`.

Proof: Follows from the isomorphism $`\texttt{H0FunctorShiftObjIsoHeartCoh}` and invariance of $`K_0`-classes under isomorphism.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_H0FunctorShift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_eq_H0FunctorShift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_eq_H0FunctorShift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_five\_term\_relation

The five-term relation for heart cohomology classes: for a distinguished triangle $`X_1 \to X_2 \to X_3 \to X_1[1]`, $`\texttt{heartCohClass}(n, X_2) - \texttt{heartCohClass}(n, X_3) - \texttt{heartCohClass}(n+1, X_1)` equals a sum of two image terms.

Proof: Multiplies the $`H^0`-functor five-term relation by $`(-1)^{|n|}`, then distributes the sign using $`\texttt{negOnePow\_natAbs\_succ}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_five_term_relation}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_five_term_relation&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_five_term_relation%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohClass\_zero\_of\_heart

For a heart object $`E`, the degree-$`0` heart cohomology class equals the class $`[E]`: $`\texttt{heartCohClass}(0, E) = [E]`.

Proof: Simplifies using $`\texttt{heartCohClass}`, $`\texttt{heartCoh}`, and the isomorphism $`\texttt{H0FunctorObjIsoOfHeart}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_zero_of_heart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohClass_zero_of_heart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohClass_zero_of_heart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohObjIsoOfHeartShift

For a heart object $`E` and integer $`n`, the underlying object of $`H^n_t(E[-n])` is canonically isomorphic to $`E`.

Construction: Uses the isomorphisms $`\tau^{\le n}(E[-n]) \cong E[-n]` and $`E[-n] \cong \tau^{\ge n}(E[-n])` (since $`E[-n]` is concentrated in degree $`n`), composed with a shift isomorphism.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohObjIsoOfHeartShift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohObjIsoOfHeartShift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohObjIsoOfHeartShift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartEulerClassObj

The canonical object-level lift of $`[E]` to $`K_0(\operatorname{heart})`, given by the alternating sum of the chosen bounded heart cohomology classes.

Construction: Computes $`\texttt{heartCohClassSum}(b, \mathrm{toNat}(a - b), E)` where $`a = \texttt{upperBound}(E)` and $`b = \texttt{lowerBound}(E)`, or $`0` if the bounds are reversed.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartEulerClassObj&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartEulerClassObj%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0ToK0\_heartCohClass

The ambient image of the signed heart cohomology class is the class of the pure truncation: $`\texttt{heartK0ToK0}(\texttt{heartCohClass}(n, E)) = [\tau^{[n,n]} E]` in $`K_0(\mathcal{C})`.

Proof: Unfolds the definition, uses $`\texttt{map\_zsmul}`, and identifies the heart object class with the shifted pure truncation class via the $`K_0`-shift-parity formula.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_heartCohClass}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0ToK0_heartCohClass&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_heartCohClass%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0ToK0\_heartCohClassSum

The canonical bounded interval sum maps to $`[E]` in ambient $`K_0`: $`\texttt{heartK0ToK0}(\sum_{j=b}^{a} (-1)^{|j|} [H^j_t(E)]) = [E]`. This is the usual formula $`[E] = \sum_n (-1)^n [H^n_t(E)]`.

Proof: Applies the telescoping formula $`\texttt{heartK0ToK0\_heartCohClassSum\_truncLE}` up to degree $`a`, then uses the fact that $`\tau^{\le a} E \cong E` for $`E \in \mathcal{C}^{\le a}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_heartCohClassSum}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0ToK0_heartCohClassSum&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_heartCohClassSum%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0ToK0\_heartCohClassSum\_truncLE

Telescoping formula: if $`E \in \mathcal{C}^{\ge b}`, then $`\texttt{heartK0ToK0}(\texttt{heartCohClassSum}(b, n, E)) = [\tau^{\le(b+n)} E]`.

Proof: Induction on $`n`. The base case uses the vanishing of $`\tau^{\le(b-1)} E` for $`E \in \mathcal{C}^{\ge b}`. The inductive step applies $`\texttt{k0\_truncLE\_step}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_heartCohClassSum_truncLE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0ToK0_heartCohClassSum_truncLE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_heartCohClassSum_truncLE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartK0ToK0\_heartEulerClassObj

The canonical object-level lift maps to the ambient Grothendieck-group class: $`\texttt{heartK0ToK0}(\texttt{heartEulerClassObj}(E)) = [E]`.

Proof: Delegates to $`\texttt{heartK0ToK0\_heartCohClassSum}` with the chosen bounds, or handles the degenerate zero case.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_heartEulerClassObj}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartK0ToK0_heartEulerClassObj&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartK0ToK0_heartEulerClassObj%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceH0primeShortComplex

The short complex in the heart obtained by applying $`H^0{}'` to the first two morphisms of a distinguished triangle whose source lies in the heart.

Construction: Built as the $`\texttt{ShortComplex.mk}` of the maps $`\texttt{toH0primeHom}(A, f)` and $`(H^0{}'(g))`, with the zero-composite verified from the triangle relation $`f \circ g = 0`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceH0primeShortComplex&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceH0primeShortComplexIso

Comparison isomorphism between the heart-source $`H^0{}'` short complex and the image of the ambient distinguished-triangle short complex under $`H^0{}'`.

Construction: A $`\texttt{ShortComplex.isoMk}` whose first component is $`(\texttt{H0primeObjIsoOfHeart}(A))^{-1}` and second is the identity, with commutativity checked using $`\texttt{H0primeObjIsoOfHeart\_inv\_comp\_H0primeFunctor\_map}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplexIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceH0primeShortComplexIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplexIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceH0primeShortComplex\_cokernelDesc

The canonical map from the cokernel of the heart-source $`H^0{}'` short complex to $`H^0{}'(X_3)`, given by the descent of the second map $`g` through the cokernel.

Construction: Defined as $`\texttt{cokernel.desc}` applied to the second map $`g` of the heart-source short complex.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_cokernelDesc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceH0primeShortComplex_cokernelDesc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_cokernelDesc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceH0primeShortComplex\_cokernelπ\_comp\_cokernelDesc

The cokernel projection followed by the canonical descent map equals the second map of the heart-source short complex.

Proof: This is the defining property $`\pi \circ \texttt{desc} = g` of the cokernel universal property.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_cokernelπ_comp_cokernelDesc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceH0primeShortComplex_cokernel%CF%80_comp_cokernelDesc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_cokernel%CF%80_comp_cokernelDesc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceH0primeShortComplex\_cokernelπ\_comp\_cokernelDesc\_assoc

Associativity-reassociated form of $`\texttt{heartSourceH0primeShortComplex\_cokernelπ\_comp\_cokernelDesc}`.

Proof: Obtained by $`\texttt{reassoc}` from the non-assoc version.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_cokernelπ_comp_cokernelDesc_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceH0primeShortComplex_cokernel%CF%80_comp_cokernelDesc_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_cokernel%CF%80_comp_cokernelDesc_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceH0primeShortComplex\_f\_eq\_toH0primeHom

The first map of the heart-source $`H^0{}'` short complex equals the canonical lift $`\texttt{toH0primeHom}(A, f)`.

Proof: Follows from the private lemma $`\texttt{H0primeObjIsoOfHeart\_inv\_comp\_H0primeFunctor\_map}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_f_eq_toH0primeHom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceH0primeShortComplex_f_eq_toH0primeHom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_f_eq_toH0primeHom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceH0primeShortComplex\_f\_is\_kernel\_of\_distTriang

In the heart-source $`H^0{}'` short complex induced by a distinguished triangle, the first map is a kernel.

Construction: Uses $`\texttt{TStructure.heartFullSubcategory\_shortExact\_of\_distTriang}` to obtain a short exact sequence in the heart, then reads off the kernel property from $`\texttt{ShortExact.fIsKernel}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_f_is_kernel_of_distTriang}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceH0primeShortComplex_f_is_kernel_of_distTriang&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_f_is_kernel_of_distTriang%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceH0primeShortComplex\_preadditiveCoyoneda\_exact\_iff

For a distinguished triangle with heart source and a heart object $`E`, exactness of the ambient short complex after applying $`H^0{}'` and the preadditive coyoneda is equivalent to exactness of the heart-source short complex after applying coyoneda.

Proof: Uses the comparison isomorphism $`\texttt{heartSourceH0primeShortComplexIso}` and $`\texttt{ShortComplex.exact\_iff\_of\_iso}` to transfer exactness.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceH0primeShortComplex\_preadditiveCoyoneda\_exact\_of\_f\_is\_kernel

If the first map of the heart-source short complex is a kernel, then the short complex is exact after applying the preadditive coyoneda.

Proof: Delegates directly to $`\texttt{ShortComplex.preadditiveCoyoneda\_exact\_of\_f\_is\_kernel}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_of_f_is_kernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_of_f_is_kernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_of_f_is_kernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceNegOneToAHom

After shifting back by $`-1`, the morphism $`\texttt{heartSourceNegOneToAShiftHom}` becomes a morphism $`H^{-1}_t(X_3) \to A` in the heart.

Construction: Composes the shift-by-$`(-1)` of $`\texttt{heartSourceNegOneToAShiftHom}` with the isomorphism $`\texttt{truncGELEIsoTruncGELT}` and the canonical $`A[1][-1] \cong A` isomorphism.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceNegOneToAHom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceNegOneToAHom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceNegOneToAHom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartSourceNegOneToAShiftHom

The morphism from the $`(-1,0)`-truncation of $`X_3` to $`A[1]` induced by a morphism $`\delta : X_3 \to A[1]` with $`A` in the heart.

Construction: Lifts $`(\iota_{<0})_{X_3} \circ \delta` through the truncation triangle $`\tau^{(-1,0)}(X_3)` using the Yoneda exactness $`\texttt{Triangle.yoneda\_exact}` after checking the vanishing condition.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartSourceNegOneToAShiftHom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartSourceNegOneToAShiftHom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartSourceNegOneToAShiftHom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isGE\_lowerBound

$`E \in \mathcal{C}^{\ge \texttt{lowerBound}(E)}`.

Proof: Analogous to $`\texttt{isLE\_upperBound}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.isGE_lowerBound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isGE_lowerBound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.isGE_lowerBound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isLE\_upperBound

$`E \in \mathcal{C}^{\le \texttt{upperBound}(E)}`.

Proof: Case split on whether $`E` is in the heart; in each case the bound is witnessed by the heart membership or the classical choice.

{docstring CategoryTheory.Triangulated.HeartStabilityData.isLE_upperBound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isLE_upperBound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.isLE_upperBound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# k0\_truncLE\_step

One-step telescoping: $`[\tau^{\le n} E] = [\tau^{\le(n-1)} E] + \texttt{heartK0ToK0}(\texttt{heartCohClass}(n, E))` in $`K_0(\mathcal{C})`.

Proof: The truncation triangle $`\tau^{<n} E \to \tau^{\le n} E \to \tau^{[n,n+1)} E` gives a $`K_0` relation, and the right-hand term is identified with the heart cohomology class via $`\texttt{heartK0ToK0\_heartCohClass}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.k0_truncLE_step}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20k0_truncLE_step&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.k0_truncLE_step%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# lowerBound

A classical choice of a lower bound $`b` such that $`E \in \mathcal{C}^{\ge b}`, for the bounded $`t`-structure.

Construction: If $`E` is in the heart, returns $`0`; otherwise applies $`\texttt{Classical.choose}` twice to the boundedness hypothesis.


{docstring CategoryTheory.Triangulated.HeartStabilityData.lowerBound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20lowerBound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.lowerBound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# lowerBound\_le\_upperBound

$`\texttt{lowerBound}(E) \le \texttt{upperBound}(E)` for every object $`E`.

Proof: If the inequality fails, $`E` would be zero, hence in the heart with both bounds equal to $`0`, contradicting the assumption.

{docstring CategoryTheory.Triangulated.HeartStabilityData.lowerBound_le_upperBound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20lowerBound_le_upperBound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.lowerBound_le_upperBound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# truncLT\_map\_truncGEπ\_comp\_heartSourceNegOneToAShiftHom

The $`\tau^{\ge(-1)}`-projection on $`\tau^{<0}(X_3)` followed by $`\texttt{heartSourceNegOneToAShiftHom}` equals $`(\iota_{<0})_{X_3} \circ \delta`.

Proof: Reads off the defining property of the chosen lift from the Yoneda exactness calculation.

{docstring CategoryTheory.Triangulated.HeartStabilityData.truncLT_map_truncGEπ_comp_heartSourceNegOneToAShiftHom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20truncLT_map_truncGE%CF%80_comp_heartSourceNegOneToAShiftHom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.truncLT_map_truncGE%CF%80_comp_heartSourceNegOneToAShiftHom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# truncLT\_map\_truncGEπ\_comp\_heartSourceNegOneToAShiftHom\_assoc

Associativity-reassociated form of $`\texttt{truncLT\_map\_truncGEπ\_comp\_heartSourceNegOneToAShiftHom}`.

Proof: Obtained by $`\texttt{reassoc}` from the non-assoc version.

{docstring CategoryTheory.Triangulated.HeartStabilityData.truncLT_map_truncGEπ_comp_heartSourceNegOneToAShiftHom_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20truncLT_map_truncGE%CF%80_comp_heartSourceNegOneToAShiftHom_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.truncLT_map_truncGE%CF%80_comp_heartSourceNegOneToAShiftHom_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# upperBound

A classical choice of an upper bound $`a` such that $`E \in \mathcal{C}^{\le a}`, for the bounded $`t`-structure.

Construction: If $`E` is in the heart, returns $`0`; otherwise applies $`\texttt{Classical.choose}` to the boundedness hypothesis.


{docstring CategoryTheory.Triangulated.HeartStabilityData.upperBound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20upperBound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.upperBound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# comp\_shift\_truncGEπ\_zero\_of\_truncLT\_negOne

For any morphism $`\phi : (\tau^{<(-1)}(X_3))[1] \to X_2[1]`, the composite $`\phi \circ (\pi_{\ge 0})_{X_2}[1]` vanishes.

Proof: The source lies in $`\mathcal{C}^{\le -2}` (after shifting) while the target lies in $`\mathcal{C}^{\ge -1}`, so the morphism vanishes by t-structure orthogonality.

{docstring CategoryTheory.Triangulated.TStructure.comp_shift_truncGEπ_zero_of_truncLT_negOne}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20comp_shift_truncGE%CF%80_zero_of_truncLT_negOne&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.comp_shift_truncGE%CF%80_zero_of_truncLT_negOne%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# negOnePow\_natAbs\_succ

$`(-1)^{|n+1|} = -(-1)^{|n|}` for all $`n \in \mathbb{Z}`.

Proof: Uses the standard identity $`(-1)^{n+1} = -(-1)^n` from $`\texttt{Int.negOnePow\_succ}`.

{docstring CategoryTheory.Triangulated.negOnePow_natAbs_succ}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20negOnePow_natAbs_succ&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.negOnePow_natAbs_succ%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.EulerLift%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
