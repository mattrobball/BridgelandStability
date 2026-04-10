import BridgelandStability.GrothendieckGroup.Basic
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "GrothendieckGroup: Basic" =>
%%%
htmlSplit := .never
%%%

# IsTriangleAdditive

A function $`f : \mathcal{C} \to A` to an additive group is triangle-additive if $`f(B) = f(A) + f(C)` for every distinguished triangle $`A \to B \to C \to A[1]`. This is the universal property hypothesis for lifting through $`K_0`.

Construction: A `Prop`-valued typeclass with a single field `additive` quantifying over all distinguished triangles.


{docstring CategoryTheory.Triangulated.IsTriangleAdditive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsTriangleAdditive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsTriangleAdditive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# K₀

The Grothendieck group $`K_0(\mathcal{C})` of a pretriangulated category $`\mathcal{C}`, defined as the quotient of the free abelian group on objects of $`\mathcal{C}` by the relations $`[B] = [A] + [C]` for each distinguished triangle $`A \to B \to C \to A[1]`.

Construction: Defined as `(trianglePresentation C).K0`, the Grothendieck group of the triangle presentation.


{docstring CategoryTheory.Triangulated.K₀}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20K%E2%82%80&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_ext

Extensionality for $`K_0(\mathcal{C})`: two group homomorphisms from $`K_0(\mathcal{C})` that agree on all object classes $`[X]` are equal.

Proof: Delegates to `K0Presentation.hom_ext`.

{docstring CategoryTheory.Triangulated.K₀.hom_ext}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_ext&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.hom_ext%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_ext\_iff

Two group homomorphisms $`f, g : K_0(\mathcal{C}) \to A` are equal if and only if they agree on all object classes $`[X]` for $`X \in \mathcal{C}`.

Proof: The forward direction is trivial; the reverse direction is `K₀.hom_ext`.

{docstring CategoryTheory.Triangulated.K₀.hom_ext_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_ext_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.hom_ext_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# instAddCommGroup

The Grothendieck group $`K_0(\mathcal{C})` carries a canonical additive commutative group structure inherited from the quotient of the free abelian group.

Proof: Inferred from the `AddCommGroup` instance on the quotient `(trianglePresentation C).K0`.

{docstring CategoryTheory.Triangulated.K₀.instAddCommGroup}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20instAddCommGroup&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.instAddCommGroup%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# lift

The universal property of $`K_0(\mathcal{C})`: any triangle-additive function $`f : \mathcal{C} \to A` lifts uniquely to a group homomorphism $`K_0(\mathcal{C}) \to A`.

Construction: Defined as `(trianglePresentation C).lift f`, delegating to the algebraic universal property of the $`K_0`-presentation.


{docstring CategoryTheory.Triangulated.K₀.lift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20lift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.lift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# lift\_of

The lift agrees with the original function on generators: $`\operatorname{lift}(f)([X]) = f(X)`.

Proof: Immediate from `K0Presentation.lift_of`.

{docstring CategoryTheory.Triangulated.K₀.lift_of}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20lift_of&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.lift_of%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of

The class map $`[\cdot] : \mathcal{C} \to K_0(\mathcal{C})` sending an object $`X` to its class $`[X]` in the Grothendieck group.

Construction: Defined as `QuotientAddGroup.mk (FreeAbelianGroup.of X)` through the triangle presentation.


{docstring CategoryTheory.Triangulated.K₀.of}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.of%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_isZero

The class of any zero object vanishes: if $`\operatorname{IsZero}(X)` then $`[X] = 0`.

Proof: Transport via the isomorphism to the explicit zero object and apply `of_zero`.

{docstring CategoryTheory.Triangulated.K₀.of_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.of_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_iso

Isomorphic objects have the same class in $`K_0`: if $`X \cong Y` then $`[X] = [Y]`.

Proof: Construct a distinguished triangle $`X \xrightarrow{e} Y \to 0 \to X[1]` from the isomorphism $`e`, apply `of_triangle`, and use `of_zero`.

{docstring CategoryTheory.Triangulated.K₀.of_iso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_iso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.of_iso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_postnikovTower\_eq\_sum

$`K_0` additivity for Postnikov towers: if $`P` is a Postnikov tower of $`E` with factors $`F_0, \ldots, F_{n-1}`, then $`[E] = \sum_{i=0}^{n-1} [F_i]` in $`K_0(\mathcal{C})`. This is the key algebraic identity used in the sector bound (Lemma 6.2 of Bridgeland).

Proof: Induction on the chain length via the auxiliary lemma `of_chain_eq_partial_sum`, which telescopes using `of_triangle` at each step. The base case uses `of_isZero` on the zero base object, and the top isomorphism identifies the final chain object with $`E`.

{docstring CategoryTheory.Triangulated.K₀.of_postnikovTower_eq_sum}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_postnikovTower_eq_sum&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.of_postnikovTower_eq_sum%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_shift\_neg\_one

Shifting by $`[-1]` negates the class: $`[X[-1]] = -[X]` in $`K_0(\mathcal{C})`.

Proof: Apply `of_shift_one` to $`X[-1]`, use the natural isomorphism $`(X[-1])[1] \cong X`, and solve for $`[X[-1]]`.

{docstring CategoryTheory.Triangulated.K₀.of_shift_neg_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_shift_neg_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.of_shift_neg_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_shift\_one

Shifting by $`[1]` negates the class: $`[X[1]] = -[X]` in $`K_0(\mathcal{C})`.

Proof: Rotate the contractible triangle of $`X` to obtain a distinguished triangle $`X \to 0 \to X[1] \to X[1]`, apply `of_triangle` to get $`0 = [X] + [X[1]]`, and rearrange.

{docstring CategoryTheory.Triangulated.K₀.of_shift_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_shift_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.of_shift_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_triangle

Additivity on triangles: for a distinguished triangle $`A \to B \to C \to A[1]`, one has $`[B] = [A] + [C]` in $`K_0(\mathcal{C})`.

Proof: Immediate from the fundamental relation `of_rel` of the triangle presentation.

{docstring CategoryTheory.Triangulated.K₀.of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_zero

The class of the zero object vanishes in $`K_0`: $`[0] = 0`.

Proof: Apply `of_triangle` to the contractible triangle $`0 \to 0 \to 0 \to 0[1]`, yielding $`[0] = [0] + [0]`, then cancel.

{docstring CategoryTheory.Triangulated.K₀.of_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.K%E2%82%80.of_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cl

The class of an object $`E` in a target lattice $`\Lambda`, via a group homomorphism $`v : K_0(\mathcal{C}) \to \Lambda`. This is $`v([E])` in the notation of Bridgeland.

Construction: An abbreviation for `v (K_0.of C E)`, composing the class map with the lattice homomorphism.


{docstring CategoryTheory.Triangulated.cl}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cl&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.cl%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cl\_id

When $`v = \operatorname{id}`, the class map reduces to $`K_0.\operatorname{of}`.

Proof: Definitional equality (`rfl`).

{docstring CategoryTheory.Triangulated.cl_id}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cl_id&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.cl_id%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cl\_isZero

The class of a zero object vanishes in the target lattice.

Proof: Follows from $`[E] = 0` in $`K_0` (`of_isZero`) and `map_zero`.

{docstring CategoryTheory.Triangulated.cl_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cl_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.cl_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cl\_iso

The class map respects isomorphisms: if $`X \cong Y` then $`v([X]) = v([Y])`.

Proof: Immediate from `of_iso`.

{docstring CategoryTheory.Triangulated.cl_iso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cl_iso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.cl_iso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cl\_postnikovTower\_eq\_sum

The class of a Postnikov tower total object equals the sum of the classes of the factors in the target lattice: $`v([E]) = \sum_i v([F_i])`.

Proof: Follows from `of_postnikovTower_eq_sum` and `map_sum`.

{docstring CategoryTheory.Triangulated.cl_postnikovTower_eq_sum}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cl_postnikovTower_eq_sum&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.cl_postnikovTower_eq_sum%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cl\_shift\_neg\_one

Shifting by $`[-1]` negates the class in the target lattice: $`v([E[-1]]) = -v([E])`.

Proof: Follows from `of_shift_neg_one` and `map_neg`.

{docstring CategoryTheory.Triangulated.cl_shift_neg_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cl_shift_neg_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.cl_shift_neg_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cl\_shift\_one

Shifting by $`[1]` negates the class in the target lattice: $`v([E[1]]) = -v([E])`.

Proof: Follows from `of_shift_one` and `map_neg`.

{docstring CategoryTheory.Triangulated.cl_shift_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cl_shift_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.cl_shift_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cl\_triangle

The class map respects distinguished triangles: $`v([B]) = v([A]) + v([C])`.

Proof: Follows from `of_triangle` and the additivity of $`v` (`map_add`).

{docstring CategoryTheory.Triangulated.cl_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cl_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.cl_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive

Any triangle-additive function $`f : \mathcal{C} \to A` is additive for the triangle presentation of $`K_0`, i.e., satisfies the $`K_0`-presentation's additivity condition.

Construction: Unwraps the subtype: the `K0Presentation.IsAdditive` instance for `trianglePresentation C` is given by `IsTriangleAdditive.additive T hT` applied to the underlying triangle and membership proof.


{docstring CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTrianglePresentationOfIsTriangleAdditive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# trianglePresentation

The triangle presentation of a pretriangulated category $`\mathcal{C}`: a `K0Presentation` whose objects are objects of $`\mathcal{C}` and whose relations are distinguished triangles $`A \to B \to C \to A[1]`, with $`\operatorname{obj}_1 = A`, $`\operatorname{obj}_2 = B`, $`\operatorname{obj}_3 = C`.

Construction: An abbreviation instantiating `K0Presentation C {T : Triangle C // T \in distTriang C}` with the three vertex projections.


{docstring CategoryTheory.Triangulated.trianglePresentation}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20trianglePresentation&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.trianglePresentation%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# trianglePresentation\_of

The class map of the triangle presentation agrees with $`K_0.\operatorname{of}`.

Proof: Definitional equality (`rfl`).

{docstring CategoryTheory.Triangulated.trianglePresentation_of}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20trianglePresentation_of&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.trianglePresentation_of%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
