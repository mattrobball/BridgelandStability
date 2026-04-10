import BridgelandStability.HeartEquivalence.H0Functor
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "HeartEquivalence: H0Functor" =>
%%%
htmlSplit := .never
%%%

# H0Functor

Degree-zero heart cohomology $`H^0_t : \mathcal{C} \to \operatorname{heart}(t)`.

Construction: An abbreviation: $`\texttt{heartCohFunctor}` at index $`n = 0`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0FunctorIsoH0primeFunctor

The normal forms $`\tau^{\ge 0} \circ \tau^{\le 0}` and $`\tau^{\le 0} \circ \tau^{\ge 0}` assemble into a natural isomorphism of functors $`\mathcal{C} \to \operatorname{heart}(t)`.

Construction: Built from $`\texttt{H0ObjIsoH0prime}` as components, with naturality from $`\texttt{H0ObjIsoH0prime\_hom\_naturality}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.H0FunctorIsoH0primeFunctor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0FunctorIsoH0primeFunctor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0FunctorIsoH0primeFunctor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0Functor\_additive

The $`H^0_t` functor is additive.

Proof: Inherits from $`\texttt{heartCohFunctor\_additive}` at $`n = 0`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor_additive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor_additive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor_additive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0Functor\_shiftSequence

The tautological shift-sequence structure on $`H^0_t`, used to compare the generic homological-functor API with the explicit $`\texttt{heartCoh}` objects.

Proof: Applies $`\texttt{Functor.ShiftSequence.tautological}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0Functor_shiftSequence}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0Functor_shiftSequence&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0Functor_shiftSequence%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0ObjIsoH0prime

The two standard normal forms $`\tau^{\ge 0}(\tau^{\le 0} X)` and $`\tau^{\le 0}(\tau^{\ge 0} X)` for $`H^0(X)` are canonically isomorphic.

Construction: Constructed via the shift-by-zero isomorphism composed with the canonical comparison $`\texttt{truncGELEIsoLEGE}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.H0ObjIsoH0prime}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0ObjIsoH0prime&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0ObjIsoH0prime%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0ObjIsoH0prime\_hom\_naturality

The isomorphism $`H^0(X) \cong H^0{}'(X)` is natural in $`X`.

Proof: Verified by checking that both paths around the naturality square agree after composing with the faithful truncation inclusion.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0ObjIsoH0prime_hom_naturality}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0ObjIsoH0prime_hom_naturality&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0ObjIsoH0prime_hom_naturality%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0ObjIsoH0prime\_hom\_naturality\_assoc

Associativity-reassociated form of the naturality of the isomorphism $`H^0(X) \cong H^0{}'(X)`.

Proof: Obtained by $`\texttt{reassoc}` from $`\texttt{H0ObjIsoH0prime\_hom\_naturality}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0ObjIsoH0prime_hom_naturality_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0ObjIsoH0prime_hom_naturality_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0ObjIsoH0prime_hom_naturality_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0prime

The degree-zero cohomology object in the alternative normal form $`\tau^{\le 0}(\tau^{\ge 0} X)`.

Construction: Packages $`(\tau^{\le 0} \circ \tau^{\ge 0})(X)` as a heart object, with the heart membership proof assembled from the truncation bounds.


{docstring CategoryTheory.Triangulated.HeartStabilityData.H0prime}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0prime&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0prime%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor

The alternative $`H^0` in the normal form $`\tau^{\le 0} \circ \tau^{\ge 0}`, assembled as a functor $`\mathcal{C} \to \operatorname{heart}(t)`.

Construction: Object map: $`\texttt{H0prime}`. Morphism map: the composite truncation applied to $`f`, wrapped in $`\texttt{ObjectProperty.homMk}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_additive

The $`H^0{}'` functor is additive.

Proof: Follows from additivity of the two truncation functors.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_additive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_additive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_additive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeFunctor\_preadditiveCoyoneda\_exact\_iff\_truncGE

Exactness of the short complex after applying $`H^0{}'` and the preadditive coyoneda is equivalent to exactness after applying $`\tau^{\ge 0}` and the preadditive coyoneda.

Proof: Uses the natural isomorphism $`\texttt{toH0primeNatIsoViaTruncGE}` and $`\texttt{ShortComplex.exact\_iff\_of\_iso}` to transfer exactness between the two functors.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_iff_truncGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeFunctor_preadditiveCoyoneda_exact_iff_truncGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_iff_truncGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeObjIsoTruncGE

$`H^0{}'(X)` is canonically isomorphic to $`H^0{}'(\tau^{\ge 0} X)`: replacing $`X` by its $`\tau^{\ge 0}`-truncation does not change $`H^0{}'`.

Construction: Applies $`\tau^{\le 0}` to the isomorphism $`(\tau^{\ge 0})^2(X) \cong \tau^{\ge 0}(X)` (idempotency) to get an isomorphism of the $`\tau^{\le 0} \circ \tau^{\ge 0}` outputs.


{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeObjIsoTruncGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeObjIsoTruncGE\_hom\_naturality

Naturality of the isomorphism $`H^0{}'(X) \cong H^0{}'(\tau^{\ge 0} X)` with respect to morphisms in $`\mathcal{C}`.

Proof: Checks that both paths around the naturality square agree after using $`\texttt{truncGEπ\_naturality}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE_hom_naturality}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeObjIsoTruncGE_hom_naturality&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE_hom_naturality%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeObjIsoTruncGE\_hom\_naturality\_assoc

Associativity-reassociated form of $`\texttt{H0primeObjIsoTruncGE\_hom\_naturality}`.

Proof: Obtained by $`\texttt{reassoc}` from the non-assoc version.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE_hom_naturality_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeObjIsoTruncGE_hom_naturality_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE_hom_naturality_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeObjIsoTruncGE\_inv\_naturality

Naturality of the inverse isomorphism $`H^0{}'(\tau^{\ge 0} X) \cong H^0{}'(X)` with respect to morphisms in $`\mathcal{C}`.

Proof: Deduced from the hom-naturality by inverting and using $`\texttt{Iso.eq\_comp\_inv}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE_inv_naturality}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeObjIsoTruncGE_inv_naturality&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE_inv_naturality%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# H0primeObjIsoTruncGE\_inv\_naturality\_assoc

Associativity-reassociated form of $`\texttt{H0primeObjIsoTruncGE\_inv\_naturality}`.

Proof: Obtained by $`\texttt{reassoc}` from the non-assoc version.

{docstring CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE_inv_naturality_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20H0primeObjIsoTruncGE_inv_naturality_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGE_inv_naturality_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# fromH0primeHom\_of\_isGE

If $`X \in \mathcal{C}^{\ge 0}`, a morphism $`E \to H^0{}'(X)` in the heart can be read as a morphism $`E_{\mathrm{obj}} \to X` in $`\mathcal{C}`.

Construction: Composes the underlying morphism with $`\iota_{\le 0}` and then with the inverse of $`\pi_{\ge 0}` (which is an isomorphism since $`X \in \mathcal{C}^{\ge 0}`).


{docstring CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20fromH0primeHom_of_isGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# fromH0primeHom\_of\_isGE\_add

The map $`\texttt{fromH0primeHom\_of\_isGE}` is additive: $`\texttt{from}(\beta_1 + \beta_2) = \texttt{from}(\beta_1) + \texttt{from}(\beta_2)`.

Proof: Distributes addition through composition with the fixed maps $`\iota_{\le 0}` and $`(\pi_{\ge 0})^{-1}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_add}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20fromH0primeHom_of_isGE_add&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_add%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# fromH0primeHom\_of\_isGE\_hom

The underlying morphism of $`\texttt{fromH0primeHom\_of\_isGE}(\beta)` composed with $`\pi_{\ge 0}` equals $`\beta.\mathrm{hom} \circ \iota_{\le 0}`.

Proof: Follows from $`\texttt{asIso}` applied to the isomorphism $`\pi_{\ge 0}` and the definition of $`\texttt{fromH0primeHom}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20fromH0primeHom_of_isGE_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# fromH0primeHom\_of\_isGE\_hom\_assoc

Associativity-reassociated form of $`\texttt{fromH0primeHom\_of\_isGE\_hom}`.

Proof: Obtained by $`\texttt{reassoc}` from the non-assoc version.

{docstring CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_hom_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20fromH0primeHom_of_isGE_hom_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_hom_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# fromH0primeHom\_of\_isGE\_toH0primeHom

The right-inverse identity: $`\texttt{fromH0primeHom}(\texttt{toH0primeHom}(f)) = f`.

Proof: Cancels the round-trip using $`\texttt{fromH0primeHom\_hom}` and $`\texttt{toH0primeHom\_hom}` together with monicity of $`\pi_{\ge 0}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_toH0primeHom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20fromH0primeHom_of_isGE_toH0primeHom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_toH0primeHom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# fromH0primeHom\_of\_isGE\_zero

The map $`\texttt{fromH0primeHom\_of\_isGE}` sends the zero morphism to zero.

Proof: Follows by $`\texttt{simp}` from the definition involving composition with zero.

{docstring CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20fromH0primeHom_of_isGE_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isGE_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCoh

The degree-$`n` heart cohomology object $`H^n_t(E)`, realized as the pure truncation $`\tau^{[n,n]} E` shifted into the heart.

Construction: Defined as $`\texttt{heartShiftOfPure}` applied to $`(\tau^{\ge n} \circ \tau^{\le n})(E)` with shift index $`n`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCoh}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCoh&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCoh%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohFunctor

The degree-$`n` heart cohomology assembled into a functor $`\mathcal{C} \to \operatorname{heart}(t)`.

Construction: Lifts the composite $`\tau^{[n,n]} \circ [-n]` to the heart full subcategory via $`\texttt{ObjectProperty.lift}`, verifying that each output satisfies both the $`\le 0` and $`\ge 0` bounds of the heart.


{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohFunctor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohFunctor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohFunctor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohFunctor\_additive

The heart cohomology functor $`H^n_t` is additive.

Proof: Follows from additivity of the truncation functors and the shift functor.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohFunctor_additive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohFunctor_additive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohFunctor_additive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartCohFunctor\_obj

$`H^n_t(E) = \texttt{heartCoh}(n, E)` as objects.

Proof: True by definition.

{docstring CategoryTheory.Triangulated.HeartStabilityData.heartCohFunctor_obj}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartCohFunctor_obj&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.heartCohFunctor_obj%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_ext\_toH0prime

Two morphisms into $`H^0{}'(X)` from a heart object are equal if they agree after composing with the truncation inclusion $`\iota_{\le 0}`.

Proof: Uses the universal property of $`\tau^{\le 0}`: the inclusion is a monomorphism on morphisms from objects in $`\mathcal{C}^{\le 0}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.hom_ext_toH0prime}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_ext_toH0prime&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.hom_ext_toH0prime%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom

A morphism $`f : E_{\mathrm{obj}} \to X` from a heart object factors canonically through $`H^0{}'(X) = \tau^{\le 0}(\tau^{\ge 0} X)`.

Construction: Lifts $`f \circ \pi_{\ge 0}` through the truncation-$`\le 0` inclusion using the $`\texttt{liftTruncLE}` universal property.


{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom\_add

The canonical lift is additive: $`\texttt{toH0prime}(f + g) = \texttt{toH0prime}(f) + \texttt{toH0prime}(g)`.

Proof: Follows from $`\texttt{hom\_ext\_toH0prime}` and linearity of composition.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_add}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom_add&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_add%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom\_comp\_H0primeFunctor\_map

The canonical lift is compatible with post-composition: $`\texttt{toH0prime}(f) \circ H^0{}'(g) = \texttt{toH0prime}(f \circ g)`.

Proof: Both sides agree after composing with the truncation inclusion, by naturality of $`\iota_{\le 0}` and the defining property of the lift.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_comp_H0primeFunctor_map}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom_comp_H0primeFunctor_map&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_comp_H0primeFunctor_map%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom\_comp\_H0primeFunctor\_map\_assoc

Associativity-reassociated form of $`\texttt{toH0primeHom\_comp\_H0primeFunctor\_map}`.

Proof: Obtained by $`\texttt{reassoc}` from the non-assoc version.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_comp_H0primeFunctor_map_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom_comp_H0primeFunctor_map_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_comp_H0primeFunctor_map_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom\_eq

Characterization of when a morphism $`\beta : E \to H^0{}'(X)` equals the canonical lift: $`\beta = \texttt{toH0primeHom}(f)` iff $`\beta.\mathrm{hom} \circ \iota_{\le 0} = f \circ \pi_{\ge 0}`.

Proof: Immediate from $`\texttt{hom\_ext\_toH0prime}` and $`\texttt{toH0primeHom\_hom}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom\_fromH0primeHom\_of\_isGE

The left-inverse identity: $`\texttt{toH0primeHom}(\texttt{fromH0primeHom}(\beta)) = \beta`.

Proof: Uses $`\texttt{toH0primeHom\_eq}` with the equality $`\texttt{fromH0primeHom\_hom}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_fromH0primeHom_of_isGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom_fromH0primeHom_of_isGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_fromH0primeHom_of_isGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom\_hom

The underlying morphism of the canonical lift satisfies $`\beta \circ \iota_{\le 0} = f \circ \pi_{\ge 0}`.

Proof: Immediate from the lifting construction.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom\_hom\_assoc

Associativity-reassociated form of $`\texttt{toH0primeHom\_hom}`.

Proof: Obtained by $`\texttt{reassoc}` from the non-assoc version.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_hom_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom_hom_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_hom_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeHom\_zero

The canonical lift of the zero morphism is zero.

Proof: Follows from $`\texttt{hom\_ext\_toH0prime}` and the vanishing of $`0 \circ \pi_{\ge 0}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeHom_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeIsoOfIsGE

For $`X \in \mathcal{C}^{\ge 0}`, morphisms $`E_{\mathrm{obj}} \to X` are in natural additive bijection with morphisms $`E \to H^0{}'(X)` in the heart.

Construction: Packages $`\texttt{toH0primeHom}` and $`\texttt{fromH0primeHom\_of\_isGE}` as mutually inverse additive maps, with the two round-trip identities from $`\texttt{toH0primeHom\_fromH0primeHom\_of\_isGE}` and $`\texttt{fromH0primeHom\_of\_isGE\_toH0primeHom}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeIsoOfIsGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeIsoOfIsGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeIsoOfIsGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeIsoViaTruncGE

For any $`X`, morphisms $`E_{\mathrm{obj}} \to \tau^{\ge 0} X` are in natural additive bijection with morphisms $`E \to H^0{}'(X)` in the heart.

Construction: Composes $`\texttt{toH0primeIsoOfIsGE}` for $`\tau^{\ge 0} X` with postcomposition by $`(\texttt{H0primeObjIsoTruncGE}(X))^{-1}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeIsoViaTruncGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeIsoViaTruncGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeIsoViaTruncGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeIsoViaTruncGE\_naturality

The bijection $`\texttt{toH0primeIsoViaTruncGE}` is natural in $`X`: it commutes with post-composition by a morphism $`g : X \to Y`.

Proof: Reduces to $`\texttt{toH0primeHom\_comp\_H0primeFunctor\_map}` and $`\texttt{H0primeObjIsoTruncGE\_inv\_naturality}`.

{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeIsoViaTruncGE_naturality}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeIsoViaTruncGE_naturality&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeIsoViaTruncGE_naturality%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeNatIsoViaTruncGE

For a heart object $`E`, the $`H^0{}'`-evaluation functor $`\mathcal{C} \to \mathbf{Ab}` is naturally isomorphic to evaluation of the ambient $`\tau^{\ge 0}`-truncation functor at $`E_{\mathrm{obj}}`.

Construction: Assembles the component isomorphisms $`\texttt{toH0primeIsoViaTruncGE}` into a $`\texttt{NatIso}` using $`\texttt{toH0primeIsoViaTruncGE\_naturality}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeNatIsoViaTruncGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeNatIsoViaTruncGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeNatIsoViaTruncGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toH0primeNatTrans

For a heart object $`E`, maps $`E_{\mathrm{obj}} \to X` in $`\mathcal{C}` induce maps $`E \to H^0{}'(X)` in the heart, naturally in $`X`.

Construction: Packages $`\texttt{toH0primeHom}` into a natural transformation between preadditive-coyoneda functors.


{docstring CategoryTheory.Triangulated.HeartStabilityData.toH0primeNatTrans}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toH0primeNatTrans&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toH0primeNatTrans%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# descTruncGE\_add

The descent map $`\texttt{descTruncGE}` is additive.

Proof: Follows from uniqueness of the lift and additivity of composition.

{docstring CategoryTheory.Triangulated.TStructure.descTruncGE_add}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20descTruncGE_add&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.descTruncGE_add%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# descTruncGE\_zero

The descent of the zero morphism through $`\tau^{\ge n}` is zero.

Proof: Follows from the universal property: the zero morphism composed with the projection is zero.

{docstring CategoryTheory.Triangulated.TStructure.descTruncGE_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20descTruncGE_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.descTruncGE_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# truncGE\_map\_comp\_descTruncGE

Composition of $`\tau^{\ge n}(g)` with the descent map $`\texttt{descTruncGE}(f)` equals $`\texttt{descTruncGE}(g \circ f)`.

Proof: Both sides lift to the same morphism after composing with the truncation projection, so they agree by the universal property of $`\tau^{\ge n}`.

{docstring CategoryTheory.Triangulated.TStructure.truncGE_map_comp_descTruncGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20truncGE_map_comp_descTruncGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.truncGE_map_comp_descTruncGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# truncGE\_map\_comp\_descTruncGE\_assoc

Associativity-reassociated form of $`\texttt{truncGE\_map\_comp\_descTruncGE}`.

Proof: Obtained by $`\texttt{reassoc}` from the non-assoc version.

{docstring CategoryTheory.Triangulated.TStructure.truncGE_map_comp_descTruncGE_assoc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20truncGE_map_comp_descTruncGE_assoc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.truncGE_map_comp_descTruncGE_assoc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.H0Functor%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
