import BridgelandStability.EulerForm.Basic
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "EulerForm" =>
%%%
htmlSplit := .never
%%%

# NumericalComponent

A connected component of the space of numerical stability conditions, i.e., a connected component of $`\operatorname{Stab}_N(\mathcal{C})` where the central charge factors through $`N(\mathcal{C}) = K_0 / \operatorname{rad}(\chi)`.

Construction: An abbreviation for the component type of `StabilityCondition.WithClassMap` indexed by a component index, instantiated to the numerical quotient map $`K_0(\mathcal{C}) \to N(\mathcal{C})`.


{docstring CategoryTheory.Triangulated.NumericalComponent}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20NumericalComponent&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.NumericalComponent%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# NumericalK₀

The numerical Grothendieck group $`N(\mathcal{C})`, defined as the quotient $`K_0(\mathcal{C}) / \operatorname{rad}(\chi)` where $`\operatorname{rad}(\chi)` is the left radical of the Euler form $`\chi(E,F) = \sum_i (-1)^i \dim_k \operatorname{Ext}^i(E,F)`.

Construction: The quotient of $`K_0(\mathcal{C})` by the kernel of the map $`e \mapsto (f \mapsto \chi(e, f))`, i.e., by `eulerFormRad`.


{docstring CategoryTheory.Triangulated.NumericalK₀}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20NumericalK%E2%82%80&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.NumericalK%E2%82%80%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# instAddCommGroup

The numerical Grothendieck group $`N(\mathcal{C})` inherits an abelian group structure from the quotient $`K_0(\mathcal{C}) / \operatorname{rad}(\chi)`.

Construction: Derived by `inferInstanceAs` from the `AddCommGroup` instance on a quotient of an abelian group.


{docstring CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20instAddCommGroup&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.NumericalK%E2%82%80.instAddCommGroup%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# NumericalStabilityCondition

A numerical stability condition on $`\mathcal{C}`: a stability condition whose central charge $`Z : K_0(\mathcal{C}) \to \mathbb{C}` factors through the numerical quotient $`N(\mathcal{C}) = K_0(\mathcal{C}) / \operatorname{rad}(\chi)`.

Construction: An abbreviation for `StabilityCondition.WithClassMap C (numericalQuotientMap k C)`, packaging the requirement that the central charge respects the Euler-form radical.


{docstring CategoryTheory.Triangulated.NumericalStabilityCondition}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20NumericalStabilityCondition&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.NumericalStabilityCondition%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# CentralChargeIsLocalHomeomorphOnConnectedComponents

The proposition that on each connected component of $`\operatorname{Stab}_N(\mathcal{C})`, the map sending a numerical stability condition to its central charge $`Z : N(\mathcal{C}) \to \mathbb{C}` is a local homeomorphism. This is the content of Bridgeland's Corollary 1.3.

Construction: An abbreviation for `StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents` instantiated to the numerical quotient $`N(\mathcal{C})`.


{docstring CategoryTheory.Triangulated.NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20CentralChargeIsLocalHomeomorphOnConnectedComponents&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# NumericallyFinite

A $`k`-linear triangulated category $`\mathcal{T}` is numerically finite if for all objects $`E, F \in \mathcal{T}`, the graded vector space $`\bigoplus_n \operatorname{Hom}(E, F[n])` is finite-dimensional over $`k`.

Construction: The typeclass packages the finiteness hypothesis as a `Module.Finite` instance on the direct sum of shifted Hom spaces, parameterized by the base field and the shift functor.


{docstring CategoryTheory.Triangulated.NumericallyFinite}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20NumericallyFinite&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.NumericallyFinite%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerForm

The Euler form $`\chi : K_0(\mathcal{C}) \times K_0(\mathcal{C}) \to \mathbb{Z}`, obtained by applying the universal property of $`K_0` twice to the function $`(E, F) \mapsto \sum_n (-1)^n \dim_k \operatorname{Hom}(E, F[n])`.

Construction: Defined by lifting `eulerFormInner k C` (which is itself the lift of the contravariant Euler form) along $`K_0` via `K₀.lift`.


{docstring CategoryTheory.Triangulated.eulerForm}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerForm&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eulerForm%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerFormInner

The Euler form $`\chi(E, F) = \sum_{n} (-1)^n \dim_k \operatorname{Hom}(E, F[n])` is the signed alternating sum of dimensions of shifted Hom spaces. It defines a bilinear pairing on objects of a numerically finite triangulated category.

Construction: Defined as the integer-valued function that sums `(-1)^n * finrank k Hom(E, F[n])` over the finitely many nonzero shifts, using the `NumericallyFinite` hypothesis to ensure the sum is well-defined.


{docstring CategoryTheory.Triangulated.eulerFormInner}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerFormInner&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eulerFormInner%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerFormInner\_isTriangleAdditive

The assignment $`E \mapsto \chi(E, -)` (as a group homomorphism $`K_0 \to \mathbb{Z}`) is triangle-additive in $`E`, so the Euler form descends to a bilinear form on $`K_0`.

{docstring CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerFormInner_isTriangleAdditive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerFormObj\_contravariant\_triangleAdditive

The contravariant Euler form $`F \mapsto \chi(E, F)` is additive on distinguished triangles: if $`A \to B \to C \to A[1]` is distinguished, then $`\chi(E, A) - \chi(E, B) + \chi(E, C) = 0`.

Proof: Follows from the long exact sequence of Hom spaces induced by the distinguished triangle and the alternating-sum telescoping that results from rank-nullity applied to each connecting map.

{docstring CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerFormObj_contravariant_triangleAdditive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerFormObj\_covariant\_triangleAdditive

For fixed $`F`, the function $`E \mapsto \chi(E, F) = \sum_n (-1)^n \dim_k \operatorname{Hom}(E, F[n])` is triangle-additive: for any distinguished triangle $`A \to B \to C \to A[1]` one has $`\chi(B, F) = \chi(A, F) + \chi(C, F)`.

Proof: Apply the long exact sequence in $`\operatorname{Hom}(-, F[n])` from the preadditiveYoneda functor, extract rank-nullity data for each degree, and use `eulerSum_of_rank_identity_int` to telescope the alternating sum.

{docstring CategoryTheory.Triangulated.eulerFormObj_covariant_triangleAdditive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerFormObj_covariant_triangleAdditive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eulerFormObj_covariant_triangleAdditive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerFormRad

The left radical of the Euler form: the additive subgroup of $`K_0(\mathcal{C})` consisting of classes $`e` such that $`\chi(e, f) = 0` for all $`f \in K_0(\mathcal{C})`.

Construction: Defined as the kernel of the group homomorphism `eulerForm k C : K₀ C →+ K₀ C →+ ℤ`.


{docstring CategoryTheory.Triangulated.eulerFormRad}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerFormRad&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eulerFormRad%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerSum\_of\_rank\_identity

If the Hom-space dimensions satisfy $`\dim(E \to b_n) = \dim(E \to a_n) + \dim(E \to c_n) - r_{n-1} - r_n` for a finitely-supported correction $`r`, then the alternating Euler sums satisfy $`\sum_n (-1)^n \dim(E \to b_n) = \sum_n (-1)^n \dim(E \to a_n) + \sum_n (-1)^n \dim(E \to c_n)`.

Proof: The correction terms $`(-1)^n r_{n-1}` and $`(-1)^n r_n` cancel by `finsum_alternating_shift_cancel`.

{docstring CategoryTheory.Triangulated.eulerSum_of_rank_identity}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerSum_of_rank_identity&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eulerSum_of_rank_identity%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerSum\_of\_rank\_identity\_int

An integer-valued version of `eulerSum_of_rank_identity`: if integer sequences $`a, b, c, r` satisfy $`b(n) = a(n) + c(n) - r(n-1) - r(n)` with $`a, c, r` finitely supported, then $`\sum_n (-1)^n b(n) = \sum_n (-1)^n a(n) + \sum_n (-1)^n c(n)`.

Proof: Same telescoping cancellation as `eulerSum_of_rank_identity`, applied to abstract integer sequences rather than Hom-space dimensions.

{docstring CategoryTheory.Triangulated.eulerSum_of_rank_identity_int}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerSum_of_rank_identity_int&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eulerSum_of_rank_identity_int%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# finrank\_mid\_of\_exact

For a middle-exact sequence $`K \xrightarrow{f} M \xrightarrow{g} N` of finite-dimensional $`k`-vector spaces (i.e., $`\operatorname{im} f = \ker g`), we have $`\dim M = \dim(\operatorname{im} f) + \dim(\operatorname{im} g)`.

Proof: Apply rank-nullity to $`g` (giving $`\dim M = \dim(\ker g) + \dim(\operatorname{im} g)`) and substitute $`\ker g = \operatorname{im} f`.

{docstring CategoryTheory.Triangulated.finrank_mid_of_exact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20finrank_mid_of_exact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.finrank_mid_of_exact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# finsum\_alternating\_shift\_cancel

The sum $`\sum_{n \in \mathbb{Z}} (-1)^n r(n-1) + \sum_{n \in \mathbb{Z}} (-1)^n r(n) = 0` for any finitely-supported integer sequence $`r`.

Proof: Shift the index in the first sum ($`n \mapsto n+1`) to get $`\sum_m (-1)^{m+1} r(m)`; since $`(-1)^{m+1} = -(-1)^m`, the two sums cancel.

{docstring CategoryTheory.Triangulated.finsum_alternating_shift_cancel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20finsum_alternating_shift_cancel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.finsum_alternating_shift_cancel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# instFGNumericalK₀OfNumericallyFinite

If $`\mathcal{C}` is numerically finite, the numerical Grothendieck group $`N(\mathcal{C})` is a finitely generated abelian group.

Construction: Synthesized from `NumericallyFinite.fg`.


{docstring CategoryTheory.Triangulated.instFGNumericalK₀OfNumericallyFinite}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20instFGNumericalK%E2%82%80OfNumericallyFinite&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.instFGNumericalK%E2%82%80OfNumericallyFinite%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# linearCoyonedaObjIsHomological

For any object $`E` in a $`k`-linear triangulated category, the $`k`-linear Yoneda functor $`\operatorname{Hom}(E, -)` (viewed as a functor to $`k`-modules) is homological, i.e., it sends distinguished triangles to long exact sequences.

Construction: Reduced to exactness of the preadditive Yoneda functor via `preadditiveYoneda.map_distinguished_exact` and `ShortComplex.exact_iff_exact_map_forget₂`.


{docstring CategoryTheory.Triangulated.linearCoyonedaObjIsHomological}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20linearCoyonedaObjIsHomological&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.linearCoyonedaObjIsHomological%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# linearMap\_range\_eq\_ker\_of\_addMonoidHom

If two $`k`-linear maps $`f : V \to W` and $`g : W \to X` satisfy $`\operatorname{im}(f^{\mathrm{AbGrp}}) = \ker(g^{\mathrm{AbGrp}})` as subgroups, then $`\operatorname{im} f = \ker g` as $`k`-submodules.

Proof: Directly from the pointwise equivalence between module membership and group membership.

{docstring CategoryTheory.Triangulated.linearMap_range_eq_ker_of_addMonoidHom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20linearMap_range_eq_ker_of_addMonoidHom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.linearMap_range_eq_ker_of_addMonoidHom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# linearRange\_eq\_linearKer\_of\_ab\_exact

If a composable pair $`f : A \to B`, $`g : B \to C` in a $`k`-linear category satisfies $`f \circ g = 0` and abelian-group exactness at $`\operatorname{Hom}(E, B)`, then $`\operatorname{im}(f \circ -) = \ker(g \circ -)` as $`k`-linear subspaces.

Proof: Straightforward from the exactness hypothesis.

{docstring CategoryTheory.Triangulated.linearRange_eq_linearKer_of_ab_exact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20linearRange_eq_linearKer_of_ab_exact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.linearRange_eq_linearKer_of_ab_exact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# numericalQuotientMap

The canonical surjection $`K_0(\mathcal{C}) \twoheadrightarrow N(\mathcal{C})` sending each class $`[E]` to its image in the numerical Grothendieck group $`N(\mathcal{C}) = K_0 / \operatorname{rad}(\chi)`.

Construction: The quotient map `QuotientAddGroup.mk' (eulerFormRad k C)`.


{docstring CategoryTheory.Triangulated.numericalQuotientMap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20numericalQuotientMap&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.numericalQuotientMap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.EulerForm.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
