import BridgelandStability.HeartEquivalence.H0Homological
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "HeartEquivalence: H0Homological" =>
%%%
htmlSplit := .never
%%%

# H0FunctorShiftObjIsoHeartCoh

The shifted $`H^0_t` object of $`X` agrees with the degree-$`n` heart cohomology object $`\texttt{heartCoh}(n, X)`.

Construction: Composes the tautological shift-sequence isomorphism with the shift-by-zero and pure-truncation-shift identifications.


{docstring CategoryTheory.Triangulated.HeartStabilityData.H0FunctorShiftObjIsoHeartCoh}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0FunctorShiftObjIsoHeartCoh&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0FunctorShiftObjIsoHeartCoh%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0Functor\_five\_term\_relation

The five-term exact segment in the long exact sequence of the homological $`H^0_t` yields: $`[H^n(X_2)] - [H^n(X_3)] + [H^{n+1}(X_1)] = [\operatorname{im}(H^n(f))] + [\operatorname{im}(H^{n+1}(f))]` in $`K_0(\operatorname{heart})`.

Proof: Applies $`\texttt{HeartK0.of\_exact\_five}` to the five consecutive terms $`H^n(X_1) \to H^n(X_2) \to H^n(X_3) \to H^{n+1}(X_1) \to H^{n+1}(X_2)` from the long exact cohomology sequence of the distinguished triangle.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor_five_term_relation}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor_five_term_relation&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor_five_term_relation%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0Functor\_isHomological\_of\_H0primeFunctor

If $`H^0{}'` is a homological functor, then so is $`H^0_t` (via the natural isomorphism $`H^0_t \cong H^0{}'`).

Proof: Applies $`\texttt{Functor.IsHomological.of\_iso}` to the inverse of $`\texttt{H0FunctorIsoH0primeFunctor}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_H0primeFunctor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor_isHomological_of_H0primeFunctor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_H0primeFunctor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0Functor\_isHomological\_of\_eval

If the preadditive-coyoneda evaluations of $`H^0{}'` are all exact on distinguished triangles, then $`H^0_t` is a homological functor.

Proof: Assembles the argument: first shows $`H^0{}'` composed with the preadditive Yoneda is homological (via $`\texttt{H0primeFunctor\_preadditiveYoneda\_isHomological\_of\_eval}`), then applies $`\texttt{H0primeFunctor\_isHomological\_of\_preadditiveYoneda}` and $`\texttt{H0Functor\_isHomological\_of\_H0primeFunctor}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_eval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor_isHomological_of_eval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_eval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0Functor\_isHomological\_of\_eval\_of\_heart\_case

It suffices to verify exactness only for distinguished triangles whose first vertex lies in the heart: if those cases hold, then $`H^0_t` is a homological functor.

Proof: Uses $`\texttt{H0primeFunctor\_preadditiveCoyoneda\_exact\_iff\_octahedral\_split}` to reduce the general case to the heart-source case via the octahedral split, then applies $`\texttt{H0Functor\_isHomological\_of\_eval}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_eval_of_heart_case}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor_isHomological_of_eval_of_heart_case&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_of_eval_of_heart_case%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_comp\_preadditiveYoneda\_eval

The composite $`H^0{}'` followed by the preadditive Yoneda, evaluated at a heart object $`E`, is the same as $`H^0{}'` followed by the preadditive coyoneda at $`E`.

Proof: This is a definitional equality ($`\texttt{rfl}`).

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_comp_preadditiveYoneda_eval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_comp_preadditiveYoneda_eval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_comp_preadditiveYoneda_eval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_isHomological\_of\_preadditiveYoneda

If $`H^0{}'` composed with the preadditive Yoneda is a homological functor, then $`H^0{}'` itself is homological.

Proof: The preadditive Yoneda is faithful, so exact sequences are reflected; applies $`\texttt{Functor.reflects\_exact\_of\_faithful}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_isHomological_of_preadditiveYoneda}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_isHomological_of_preadditiveYoneda&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_isHomological_of_preadditiveYoneda%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_preadditiveCoyoneda\_exact\_iff\_octahedral\_split

For any distinguished triangle $`T` and heart object $`E`, exactness of $`H^0{}'`-coyoneda on $`T` is equivalent to exactness on the octahedral-split triangle; the octahedral split data exists for any $`T`.

Proof: Applies $`\texttt{exists\_truncLT\_octahedral\_split}` at level $`0` to produce the split, checks that $`\tau^{\ge 0}(v)` is an isomorphism (making the split exact condition transferable), and translates between the two exactness conditions via $`\texttt{H0primeFunctor\_preadditiveCoyoneda\_exact\_iff\_truncGE}` and $`\texttt{truncGE\_preadditiveCoyoneda\_exact\_iff\_of\_split}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_iff_octahedral_split}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_preadditiveCoyoneda_exact_iff_octahedral_split&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_iff_octahedral_split%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_preadditiveCoyoneda\_exact\_of\_isGE\_one

For a distinguished triangle with first vertex $`A \in \mathcal{C}^{\ge 1}`, the short complex obtained by applying $`H^0{}'` and the preadditive coyoneda is exact.

Proof: The map $`\tau^{<0}(m_3)` is an isomorphism because $`A[1] \in \mathcal{C}^{\ge 0}` forces the rotated-triangle first vertex to be in $`\mathcal{C}^{\ge 0}`. The result follows from $`\texttt{H0primeFunctor\_preadditiveCoyoneda\_exact\_of\_isIso\_truncLT\_map}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_preadditiveCoyoneda\_exact\_of\_isGE\_zero\_of\_heart\_case

For a distinguished triangle with first vertex $`A \in \mathcal{C}^{\ge 0}`, if exactness holds for all heart-source triangles, then the $`H^0{}'`-coyoneda short complex is exact.

Proof: Applies the octahedral split at level $`1` to reduce to a heart-source triangle (via $`\tau^{<1}(A) \in \operatorname{heart}`) and a triangle with first vertex $`\tau^{\ge 1}(A) \in \mathcal{C}^{\ge 1}`, then combines via $`\texttt{H0primeFunctor\_preadditiveCoyoneda\_exact\_of\_split\_one}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_zero_of_heart_case}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_zero_of_heart_case&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_zero_of_heart_case%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_preadditiveCoyoneda\_exact\_of\_isIso\_truncLT\_map

If $`\tau^{<0}(m_3)` is an isomorphism in a distinguished triangle $`A \to Z \to X_3`, then the $`H^0{}'`-coyoneda short complex on the triangle is exact.

Proof: Using the isomorphism of $`\tau^{<0}(m_3)`, lifts a kernel element $`\beta` (with $`\beta \circ H^0{}'(m_3) = 0`) to a morphism $`f : E \to Z` via the obstruction-zero lifting lemma $`\texttt{exists\_toH0primeHom\_eq\_of\_obstruction\_zero}`, then constructs a preimage via $`\texttt{Triangle.coyoneda\_exact}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_isIso_truncLT_map}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_preadditiveCoyoneda_exact_of_isIso_truncLT_map&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_isIso_truncLT_map%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_preadditiveCoyoneda\_exact\_of\_split\_one

Given an octahedral split of a distinguished triangle at level $`1`, if the short triangle from $`\tau^{<1}(A)` gives an exact $`H^0{}'`-coyoneda complex, then so does the original triangle.

Proof: The split triangle with first vertex $`\tau^{\ge 1}(A)` is exact by $`\texttt{H0primeFunctor\_preadditiveCoyoneda\_exact\_of\_isGE\_one}`. Combines both exactness statements to lift kernel elements in the original complex.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_split_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_preadditiveCoyoneda_exact_of_split_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_split_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_preadditiveYoneda\_isHomological\_of\_eval

If for every distinguished triangle and every heart object the $`H^0{}'`-coyoneda complex is exact, then $`H^0{}'` composed with the preadditive Yoneda is a homological functor.

Proof: Reduces to checking exactness on each evaluation functor $`\mathcal{C} \to \mathbf{Ab}` via $`\texttt{ShortComplex.exact\_of\_eval}` and the provided hypothesis.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveYoneda_isHomological_of_eval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_preadditiveYoneda_isHomological_of_eval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveYoneda_isHomological_of_eval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# comp\_H0primeFunctor\_map\_eq\_zero\_iff

A morphism $`\beta \circ H^0{}'(g) = 0` in the heart if and only if $`\beta.\mathrm{hom} \circ \iota_{\le 0} \circ \tau^{\ge 0}(g) = 0` in $`\mathcal{C}`.

Proof: Both directions use naturality of $`\iota_{\le 0}` and $`\texttt{hom\_ext\_toH0prime}` to pass between the heart and ambient-category conditions.

{docstring CategoryTheory.Triangulated.HeartStabilityData.comp_H0primeFunctor_map_eq_zero_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20comp_H0primeFunctor_map_eq_zero_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.comp_H0primeFunctor_map_eq_zero_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_toH0primeHom\_eq\_of\_obstruction\_zero

If $`\beta.\mathrm{hom} \circ \iota_{\le 0} \circ (\tau^{\ge 0} \to X)_{\mathrm{conn}} = 0` (the obstruction vanishes), then $`\beta = \texttt{toH0primeHom}(f)` for some $`f : E_{\mathrm{obj}} \to X`.

Proof: Lifts $`\beta.\mathrm{hom} \circ \iota_{\le 0}` to a morphism into $`X` via the exactness of the $`\tau^{\ge 0}`-triangle and the vanishing obstruction, then identifies the lift with $`\texttt{toH0primeHom}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.exists_toH0primeHom_eq_of_obstruction_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_toH0primeHom_eq_of_obstruction_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.exists_toH0primeHom_eq_of_obstruction_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isZero\_H0Functor\_shift\_obj\_of\_gt\_bound

$`H^m_t(X) = 0` when $`m > n` and $`X \in \mathcal{C}^{\le n}`.

Proof: The pure truncation $`\tau^{[m,m]} X` vanishes because $`\tau^{\ge m}` of $`\tau^{\le m} X \cong X` is zero for $`m > n` when $`X \in \mathcal{C}^{\le n}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.isZero_H0Functor_shift_obj_of_gt_bound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isZero_H0Functor_shift_obj_of_gt_bound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.isZero_H0Functor_shift_obj_of_gt_bound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isZero\_H0Functor\_shift\_obj\_of\_lt\_bound

$`H^m_t(X) = 0` when $`m < n` and $`X \in \mathcal{C}^{\ge n}`.

Proof: The pure truncation $`\tau^{[m,m]} X` vanishes because $`\tau^{\le m} X = 0` for $`m < n` when $`X \in \mathcal{C}^{\ge n}`. The heart cohomology object, being a shift of this zero object, is also zero.

{docstring CategoryTheory.Triangulated.HeartStabilityData.isZero_H0Functor_shift_obj_of_lt_bound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isZero_H0Functor_shift_obj_of_lt_bound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.isZero_H0Functor_shift_obj_of_lt_bound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isZero\_H0prime\_of\_isGE\_one

For $`X \in \mathcal{C}^{\ge 1}`, the object $`H^0{}'(X)` is zero.

Proof: The underlying object $`\tau^{\le 0}(\tau^{\ge 0}(X))` vanishes because $`\tau^{\ge 0}(X) \in \mathcal{C}^{\ge 0}` and $`\tau^{\le 0}` of an object in $`\mathcal{C}^{\ge 1}` is zero.

{docstring CategoryTheory.Triangulated.HeartStabilityData.isZero_H0prime_of_isGE_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isZero_H0prime_of_isGE_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.isZero_H0prime_of_isGE_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom\_eq\_zero\_iff

The canonical lift $`\texttt{toH0primeHom}(f) = 0` if and only if $`f \circ \pi_{\ge 0} = 0`.

Proof: Both directions use $`\texttt{hom\_ext\_toH0prime}` together with $`\texttt{toH0primeHom\_hom}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_eq_zero_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom_eq_zero_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_eq_zero_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# truncGE\_preadditiveCoyoneda\_exact\_iff\_of\_split

For an octahedral splitting of a distinguished triangle, exactness of the $`\tau^{\ge 0}`-coyoneda complex on the original triangle is equivalent to exactness on the split triangle.

Proof: Applies $`\texttt{shortComplexOfDistTriangle\_map\_truncGEIsoOfSplit}` to get a comparison isomorphism, then uses $`\texttt{ShortComplex.exact\_iff\_of\_iso}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.truncGE_preadditiveCoyoneda_exact_iff_of_split}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20truncGE_preadditiveCoyoneda_exact_iff_of_split&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.truncGE_preadditiveCoyoneda_exact_iff_of_split%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exact\_of\_eval

A short complex $`S` of functors $`J \to A` (with $`A` abelian) is exact if and only if for every object $`j \in J` the evaluation $`S_j` is exact.

Proof: Reduces to checking that the kernel lift is epi on each evaluation using $`\texttt{NatTrans.epi\_iff\_epi\_app}`, the kernel comparison isomorphism, and the given evaluation exactness.

{docstring CategoryTheory.Triangulated.ShortComplex.exact_of_eval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exact_of_eval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.ShortComplex.exact_of_eval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# preadditiveCoyoneda\_exact\_of\_f\_is\_kernel

If the first map of a short complex $`S` in a preadditive category is a kernel, then the complex is exact after applying the preadditive coyoneda functor.

Proof: Given a kernel element $`\beta` with $`\beta \circ S.g = 0`, lifts $`\beta` through the kernel universal property and checks the factorization.

{docstring CategoryTheory.Triangulated.ShortComplex.preadditiveCoyoneda_exact_of_f_is_kernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20preadditiveCoyoneda_exact_of_f_is_kernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.ShortComplex.preadditiveCoyoneda_exact_of_f_is_kernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mapHomologicalFunctor

A homological functor $`F` on a triangulated category $`\mathcal{C}` maps a spectral object indexed by $`\iota` to an abelian spectral object by applying the long exact cohomology sequence.

Construction: Sets $`H_n := \omega_1 \circ F[n]` and the connecting maps from $`F`'s homology-sequence morphisms; exactness at each position follows from the three exactness axioms of a homological functor.


{docstring CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mapHomologicalFunctor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_truncLT\_octahedral\_split

For any distinguished triangle $`X_1 \to X_2 \to X_3 \to X_1[1]` and integer $`a`, the octahedral axiom produces a factorization through the truncation $`\tau^{\ge a} X_1`.

Proof: Applies the octahedral axiom to the composition $`\tau^{<a} X_1 \hookrightarrow X_1 \to X_2`, yielding an intermediate object $`Z` and two new distinguished triangles relating $`Z` to $`\tau^{\ge a} X_1` and $`X_3`.

{docstring CategoryTheory.Triangulated.TStructure.exists_truncLT_octahedral_split}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_truncLT_octahedral_split&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.exists_truncLT_octahedral_split%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isIso\_truncLT\_negOne\_map\_of\_heart\_source

For a distinguished triangle $`A \to X_2 \to X_3` with $`A` in the heart, the map $`\tau^{<(-1)}(g)` is an isomorphism.

Proof: The connecting morphism in the rotated triangle lies in $`\mathcal{C}^{\ge -1}` (since $`A[1] \in \mathcal{C}^{\ge -1}`), so $`\texttt{isIso₁\_truncLT\_map\_of\_isGE}` applies to give the isomorphism.

{docstring CategoryTheory.Triangulated.TStructure.isIso_truncLT_negOne_map_of_heart_source}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isIso_truncLT_negOne_map_of_heart_source&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.isIso_truncLT_negOne_map_of_heart_source%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isIso\_truncLT\_pred\_map\_of\_isGE

If $`A \in \mathcal{C}^{\ge a}` and $`A \to Z \to X_3 \to A[1]` is distinguished, then $`\tau^{<a-1}(m_3)` is an isomorphism.

Proof: The rotated triangle places $`A[1] \in \mathcal{C}^{\ge a-1}`, so the $`\tau^{<a-1}` functor kills the first vertex and the isomorphism follows from the induced two-term exact sequence.

{docstring CategoryTheory.Triangulated.TStructure.isIso_truncLT_pred_map_of_isGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isIso_truncLT_pred_map_of_isGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.isIso_truncLT_pred_map_of_isGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shortComplexOfDistTriangle\_map\_truncGEIsoOfSplit

Given an octahedral splitting with $`\tau^{\ge 0}(v)` an isomorphism, the $`\tau^{\ge 0}`-images of the two short complexes (original and split) are isomorphic.

Construction: Builds a $`\texttt{ShortComplex.isoMk}` from the isomorphism $`\tau^{\ge 0}(X_1) \cong \tau^{\ge 0}(\tau^{\ge 0}(X_1))` (idempotency) and $`\tau^{\ge 0}(v)` (hypothesis), with commutativity checked from $`\texttt{hm_1}` and $`\texttt{hm_3}`.


{docstring CategoryTheory.Triangulated.TStructure.shortComplexOfDistTriangle_map_truncGEIsoOfSplit}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shortComplexOfDistTriangle_map_truncGEIsoOfSplit&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.shortComplexOfDistTriangle_map_truncGEIsoOfSplit%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# truncGELEObjShiftIso

Shifting the pure truncation $`\tau^{[n,n]} X` by $`n` identifies it with $`\tau^{[0,0]}(X[n])`.

Construction: Composes the $`\ge`-shift isomorphism applied to $`\tau^{\le n} X` with the functorial image of the $`\le`-shift isomorphism under $`\tau^{\ge 0}`.


{docstring CategoryTheory.Triangulated.TStructure.truncGELEObjShiftIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20truncGELEObjShiftIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.truncGELEObjShiftIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# truncGEObjShiftIso

Shifting $`\tau^{\ge n} X` by $`n` identifies it with $`\tau^{\ge 0}(X[n])`.

Construction: Constructed by comparing the shifted truncation triangle of $`X` at level $`n` with the truncation triangle of $`X[n]` at level $`0`, using the uniqueness of the truncation up to a triangle isomorphism.


{docstring CategoryTheory.Triangulated.TStructure.truncGEObjShiftIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20truncGEObjShiftIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.truncGEObjShiftIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# truncLEObjShiftIso

Shifting $`\tau^{\le n} X` by $`n` identifies it with $`\tau^{\le 0}(X[n])`.

Construction: Analogous to $`\texttt{truncGEObjShiftIso}`: compares the shifted $`\le`-truncation triangle with the $`\le 0`-truncation of $`X[n]`.


{docstring CategoryTheory.Triangulated.TStructure.truncLEObjShiftIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20truncLEObjShiftIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.truncLEObjShiftIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eq\_zero\_congr\_hasZeroMorphisms

The vanishing of a morphism $`f = 0` is independent of the choice of $`\texttt{HasZeroMorphisms}` instance, since there is at most one such instance.

Proof: Uses $`\texttt{Subsingleton.elim}` to unify the two zero-morphism structures.

{docstring CategoryTheory.Triangulated.eq_zero_congr_hasZeroMorphisms}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eq_zero_congr_hasZeroMorphisms&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eq_zero_congr_hasZeroMorphisms%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shortComplex\_exact\_congr\_hasZeroMorphisms

Exactness of a short complex is independent of the choice of $`\texttt{HasZeroMorphisms}` instance.

Proof: Uses $`\texttt{Subsingleton.elim}` to unify the two instances, then the zero-composite witnesses.

{docstring CategoryTheory.Triangulated.shortComplex_exact_congr_hasZeroMorphisms}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shortComplex_exact_congr_hasZeroMorphisms&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.shortComplex_exact_congr_hasZeroMorphisms%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Homological%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
