import BridgelandStability.GrothendieckGroup.Defs
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "GrothendieckGroup: Defs" =>
%%%
htmlSplit := .never
%%%

# K0Presentation

A $`K_0`-presentation is a purely algebraic specification of a Grothendieck-style group quotient. Given a type of objects $`\operatorname{Obj}` and a type of relations $`\operatorname{Rel}`, a presentation consists of three projections $`\operatorname{obj}_1, \operatorname{obj}_2, \operatorname{obj}_3 : \operatorname{Rel} \to \operatorname{Obj}` encoding the pattern $`[\operatorname{obj}_2(r)] = [\operatorname{obj}_1(r)] + [\operatorname{obj}_3(r)]`. This factors out the identical quotient plumbing shared by the triangulated $`K_0` (relations from distinguished triangles) and the heart $`K_0` (relations from short exact sequences).

Construction: A structure with three fields `obj_1`, `obj_2`, `obj_3 : Rel \to Obj` parameterized by universe-polymorphic types `Obj` and `Rel`.


{docstring K0Presentation}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20K0Presentation&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsAdditive

A function $`f : \operatorname{Obj} \to A` to an additive group is additive for a presentation $`P` if $`f(\operatorname{obj}_2(r)) = f(\operatorname{obj}_1(r)) + f(\operatorname{obj}_3(r))` for every relation $`r`.

Construction: A single-field `Prop`-valued class carrying the additivity hypothesis for each relation.


{docstring K0Presentation.IsAdditive}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsAdditive&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.IsAdditive%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_relMap

A compatible map on relations implies additivity of the induced object map. If $`f_{\operatorname{Obj}} : \operatorname{Obj} \to \operatorname{QObj}` and $`f_{\operatorname{Rel}} : \operatorname{Rel} \to \operatorname{QRel}` satisfy $`f_{\operatorname{Obj}}(P.\operatorname{obj}_i(r)) = Q.\operatorname{obj}_i(f_{\operatorname{Rel}}(r))` for $`i = 1, 2, 3`, then $`Q.\operatorname{of} \circ f_{\operatorname{Obj}}` is additive for $`P`.

Proof: Rewrite using the compatibility hypotheses and apply `Q.of_rel`.

{docstring K0Presentation.IsAdditive.of_relMap}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_relMap&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.IsAdditive.of_relMap%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# K0

The Grothendieck group $`K_0(P)` of a presentation $`P` is the quotient $`\operatorname{FreeAbelianGroup}(\operatorname{Obj}) \,/\, P.\operatorname{subgroup}`. This is the universal abelian group receiving a map from $`\operatorname{Obj}` that respects the three-term relations.

Construction: An abbreviation for the quotient `FreeAbelianGroup Obj / P.subgroup`.


{docstring K0Presentation.K0}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20K0&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.K0%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_ext

Extensionality for $`K_0`: two group homomorphisms $`f, g : K_0(P) \to A` that agree on all generators $`[X]` are equal.

Proof: By induction on the quotient and then on the free abelian group (generators, zero, negation, addition), reducing to the generator case.

{docstring K0Presentation.hom_ext}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_ext&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.hom_ext%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# induction\_on

Induction principle for $`K_0(P)`: to prove a property of all elements of $`K_0(P)`, it suffices to check generators $`[X]`, zero, negation, and addition.

Proof: Combines `QuotientAddGroup.induction_on` with `FreeAbelianGroup.induction_on`.

{docstring K0Presentation.induction_on}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20induction_on&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.induction_on%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# instAddCommGroupK0

The Grothendieck group $`K_0(P)` of a $`K_0`-presentation $`P` carries an abelian group structure, inherited from the quotient of a free abelian group.

Construction: Derived by `inferInstanceAs` from the `AddCommGroup` instance on `FreeAbelianGroup Obj ⧸ P.subgroup`.


{docstring K0Presentation.instAddCommGroupK0}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20instAddCommGroupK0&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.instAddCommGroupK0%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isAdditive\_of

The class map $`P.\operatorname{of}` is additive for its own presentation.

Proof: Immediate from the fundamental relation `P.of_rel`.

{docstring K0Presentation.isAdditive_of}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isAdditive_of&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.isAdditive_of%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# lift

The universal property of $`K_0`: any additive function $`f : \operatorname{Obj} \to A` lifts uniquely to a group homomorphism $`K_0(P) \to A`.

Construction: Constructed via `QuotientAddGroup.lift` applied to `FreeAbelianGroup.lift f`, after verifying that the relation subgroup maps to zero using the additivity hypothesis.


{docstring K0Presentation.lift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20lift&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.lift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# lift\_of

The lift of an additive function $`f` agrees with $`f` on generators: $`\operatorname{lift}(f)([X]) = f(X)`.

Proof: Immediate from `FreeAbelianGroup.lift_apply_of`.

{docstring K0Presentation.lift_of}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20lift_of&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.lift_of%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# map

The induced map on Grothendieck groups from a function $`f : \operatorname{Obj} \to \operatorname{QObj}` that respects relations. Given presentations $`P` and $`Q` and an additivity proof for $`Q.\operatorname{of} \circ f`, this yields a group homomorphism $`K_0(P) \to K_0(Q)`.

Construction: Defined as `P.lift (Q.of \circ f)` using the supplied additivity instance.


{docstring K0Presentation.map}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20map&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.map%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# map\_comp

Functoriality: the induced map of a composition $`g \circ f` equals the composition of the induced maps.

Proof: By extensionality on generators, where both sides evaluate to $`[g(f(X))]`.

{docstring K0Presentation.map_comp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20map_comp&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.map_comp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# map\_id

The identity map on objects induces the identity homomorphism on $`K_0`.

Proof: By extensionality (`hom_ext`), checking on generators where both sides equal $`[X]`.

{docstring K0Presentation.map_id}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20map_id&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.map_id%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# map\_of

The induced map sends generators to generators: $`\operatorname{map}(f)([X]_P) = [f(X)]_Q`.

Proof: Immediate from `lift_of`.

{docstring K0Presentation.map_of}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20map_of&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.map_of%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of

The class map $`[\cdot] : \operatorname{Obj} \to K_0(P)` sends an object $`X` to its equivalence class in the Grothendieck group.

Construction: Defined as `QuotientAddGroup.mk (FreeAbelianGroup.of X)`.


{docstring K0Presentation.of}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.of%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_rel

The fundamental relation: for each relation $`r`, one has $`[\operatorname{obj}_2(r)] = [\operatorname{obj}_1(r)] + [\operatorname{obj}_3(r)]` in $`K_0(P)`.

Proof: The difference $`\operatorname{of}(\operatorname{obj}_2) - \operatorname{of}(\operatorname{obj}_1) - \operatorname{of}(\operatorname{obj}_3)` lies in the relation subgroup by definition of the closure, so the quotient identifies the two sides.

{docstring K0Presentation.of_rel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_rel&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.of_rel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# subgroup

The relation subgroup of a $`K_0`-presentation $`P` is the additive subgroup of $`\operatorname{FreeAbelianGroup}(\operatorname{Obj})` generated by the elements $`[\operatorname{obj}_2(r)] - [\operatorname{obj}_1(r)] - [\operatorname{obj}_3(r)]` for each relation $`r`.

Construction: Defined as the additive closure of the set $`\{\operatorname{of}(P.\operatorname{obj}_2\, r) - \operatorname{of}(P.\operatorname{obj}_1\, r) - \operatorname{of}(P.\operatorname{obj}_3\, r) \mid r : \operatorname{Rel}\}` inside `FreeAbelianGroup Obj`.


{docstring K0Presentation.subgroup}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20subgroup&body=%2A%2ADeclaration%3A%2A%2A%20%60K0Presentation.subgroup%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.GrothendieckGroup.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
