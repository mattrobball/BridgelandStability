import BridgelandStability.QuasiAbelian.Basic
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "QuasiAbelian" =>
%%%
htmlSplit := .never
%%%

# subobject\_of\_faithful\_preservesMono

A faithful functor $`F : \mathcal{A} \to \mathcal{C}` that preserves monomorphisms induces an injection on subobject lattices. If `Finite (Subobject (F.obj E))` in $`\mathcal{C}`, then `Finite (Subobject E)` in $`\mathcal{A}`. The key use case is the full subcategory inclusion $`\iota : \mathcal{P}(\phi) \hookrightarrow \mathcal{C}`, transferring local finiteness of the slicing.

Proof: Construct an injective map `Subobject E \to Subobject (F.obj E)` by applying $`F` to representative arrows, verify injectivity using faithfulness and `preimageIso`, and apply `Finite.of_injective`.

{docstring CategoryTheory.Finite.subobject_of_faithful_preservesMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20subobject_of_faithful_preservesMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Finite.subobject_of_faithful_preservesMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsStrict

A morphism $`f : X \to Y` in a category with kernels and cokernels is strict if the canonical comparison morphism from the (abelian) coimage to the (abelian) image is an isomorphism. In an abelian category every morphism is strict, so strictness is a nontrivial condition only in the pre-abelian setting.

Construction: Defined as `IsIso (Abelian.coimageImageComparison f)`, using the comparison morphism from Mathlib that is defined without assuming the ambient category is abelian.


{docstring CategoryTheory.IsStrict}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsStrict&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrict%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsStrictArtinianObject

The proposition that $`X` is strict-Artinian.

Construction: An abbreviation for `isStrictArtinianObject.Is X`.


{docstring CategoryTheory.IsStrictArtinianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsStrictArtinianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictArtinianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsStrictEpi

A morphism $`f` is a strict epimorphism if it is both an epimorphism and strict: $`f` is epi and the coimage-to-image comparison is an isomorphism.

Construction: A `Prop`-valued structure with two fields: `epi : Epi f` and `strict : IsStrict f`.


{docstring CategoryTheory.IsStrictEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsStrictEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isColimitCokernelCofork

A strict epimorphism is the cokernel of its kernel: the cofork $`\operatorname{ker}(f) \xrightarrow{\iota} X \xrightarrow{f} Y` is a colimit.

Construction: Constructs an `IsColimit` witness for the cokernel cofork of $`f` at its kernel, using the isomorphism $`\operatorname{Coim}(f) \cong Y` that results from strictness and the epi hypothesis.


{docstring CategoryTheory.IsStrictEpi.isColimitCokernelCofork}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isColimitCokernelCofork&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictEpi.isColimitCokernelCofork%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsStrictEpi.isIso

A strict epimorphism that is also mono is an isomorphism.

Proof: The kernel is zero since $`f` is mono. Descend through the cokernel colimit to construct a section, making $`f` a split mono. A split mono that is also epi is an isomorphism.

{docstring CategoryTheory.IsStrictEpi.isIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictEpi.isIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# normalEpi

A strict epimorphism is a normal epimorphism: it is the cokernel of some morphism (namely, its own kernel).

Construction: Constructs a `NormalEpi` instance from the cokernel colimit witness.


{docstring CategoryTheory.IsStrictEpi.normalEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20normalEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictEpi.normalEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# regularEpi

A strict epimorphism is a regular epimorphism.

Construction: Obtained from the normal epi structure via `NormalEpi.regularEpi`.


{docstring CategoryTheory.IsStrictEpi.regularEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20regularEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictEpi.regularEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strongEpi

A strict epimorphism is a strong epimorphism.

Proof: A regular epi is a strong epi in any category.

{docstring CategoryTheory.IsStrictEpi.strongEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strongEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictEpi.strongEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsStrictMono

A morphism $`f` is a strict monomorphism if it is both a monomorphism and strict: $`f` is mono and the coimage-to-image comparison is an isomorphism.

Construction: A `Prop`-valued structure with two fields: `mono : Mono f` and `strict : IsStrict f`.


{docstring CategoryTheory.IsStrictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsStrictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsStrictMono.isIso

A strict monomorphism that is also epi is an isomorphism.

Proof: The cokernel is zero since $`f` is epi. Lift through the kernel limit to construct a retraction, making $`f` a split epi. A split epi that is also mono is an isomorphism.

{docstring CategoryTheory.IsStrictMono.isIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictMono.isIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isLimitKernelFork

A strict monomorphism is the kernel of its cokernel: the fork $`X \xrightarrow{f} Y \xrightarrow{\pi} \operatorname{coker}(f)` is a limit.

Construction: Constructs an `IsLimit` witness for the kernel fork of $`f` at its cokernel, using the isomorphism $`X \cong \operatorname{Im}(f)` that results from strictness and the mono hypothesis.


{docstring CategoryTheory.IsStrictMono.isLimitKernelFork}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isLimitKernelFork&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictMono.isLimitKernelFork%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# normalMono

A strict monomorphism is a normal monomorphism: it is the kernel of some morphism (namely, its own cokernel).

Construction: Constructs a `NormalMono` instance from the kernel limit witness.


{docstring CategoryTheory.IsStrictMono.normalMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20normalMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictMono.normalMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsStrictNoetherianObject

The proposition that $`X` is strict-Noetherian.

Construction: An abbreviation for `isStrictNoetherianObject.Is X`.


{docstring CategoryTheory.IsStrictNoetherianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsStrictNoetherianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsStrictNoetherianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# QuasiAbelian

**\[Definition 4.1\]**

A preadditive category with kernels, cokernels, pullbacks, and pushouts is quasi-abelian if pullbacks of strict epimorphisms are strict epimorphisms and pushouts of strict monomorphisms are strict monomorphisms. This is the definition from Schneiders (1999), used in Bridgeland's treatment of hearts of $`t`-structures.

Construction: A `Prop`-valued typeclass with two fields: `pullback_strictEpi` (stability of strict epis under pullback) and `pushout_strictMono` (stability of strict monos under pushout).


{docstring CategoryTheory.QuasiAbelian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20QuasiAbelian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.QuasiAbelian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%204.1%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# StrictShortExact

A strict short exact sequence is a `ShortComplex` that is short exact (mono left, epi right, exact in the middle) and where both morphisms $`f` and $`g` are strict. In a quasi-abelian category, kernels of strict epis are strict monos and cokernels of strict monos are strict epis.

Construction: A `Prop`-valued structure carrying `shortExact : S.ShortExact`, `strict_f : IsStrict S.f`, and `strict_g : IsStrict S.g`.


{docstring CategoryTheory.StrictShortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20StrictShortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StrictShortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# StrictSubobject

The ordered type of strict subobjects of $`X`: subobjects whose arrows are strict monomorphisms.

Construction: An abbreviation for `\{ P : Subobject X // P.IsStrict \}`.


{docstring CategoryTheory.StrictSubobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20StrictSubobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StrictSubobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Subobject.IsStrict

A subobject is strict if its arrow is a strict monomorphism. This is the quasi-abelian notion of admissible/exact subobject used in Bridgeland's finite-length thin interval categories.

Construction: Defined as `IsStrictMono P.arrow`.


{docstring CategoryTheory.Subobject.IsStrict}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsStrict&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Subobject.IsStrict%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrict\_iff

A subobject $`P` is strict if and only if its arrow is a strict monomorphism.

Proof: Definitional unfolding (`Iff.rfl`).

{docstring CategoryTheory.Subobject.isStrict_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrict_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Subobject.isStrict_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# instWellFoundedGTStrictSubobjectOfIsStrictNoetherianObject

If $`X` is strictly Noetherian (i.e., its strict subobjects satisfy the ascending chain condition), then the poset of strict subobjects of $`X` is well-founded for $`>`.

Construction: Extracted from the `isStrictNoetherianObject` property via `prop_of_is`.


{docstring CategoryTheory.instWellFoundedGTStrictSubobjectOfIsStrictNoetherianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20instWellFoundedGTStrictSubobjectOfIsStrictNoetherianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.instWellFoundedGTStrictSubobjectOfIsStrictNoetherianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# instWellFoundedLTStrictSubobjectOfIsStrictArtinianObject

If $`X` is strictly Artinian (i.e., its strict subobjects satisfy the descending chain condition), then the poset of strict subobjects of $`X` is well-founded for $`<`.

Construction: Extracted from the `isStrictArtinianObject` property via `prop_of_is`.


{docstring CategoryTheory.instWellFoundedLTStrictSubobjectOfIsStrictArtinianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20instWellFoundedLTStrictSubobjectOfIsStrictArtinianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.instWellFoundedLTStrictSubobjectOfIsStrictArtinianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isArtinianObject\_of\_faithful\_preservesMono

Artinian objects transfer across full faithful functors that preserve monomorphisms.

Proof: Map descending chains of subobjects in $`\mathcal{A}` to descending chains in $`\mathcal{C}` via the injective monotone subobject image map. Stabilization in $`\mathcal{C}` pulls back to stabilization in $`\mathcal{A}` by injectivity.

{docstring CategoryTheory.isArtinianObject_of_faithful_preservesMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isArtinianObject_of_faithful_preservesMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isArtinianObject_of_faithful_preservesMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isArtinianObject\_of\_isStrictArtinianObject

In an abelian category, strict-Artinian and Artinian coincide, because every mono is strict.

Proof: Every subobject is strict (since every mono is strict in an abelian category), so descending chains of subobjects are descending chains of strict subobjects. Apply the antitone chain condition.

{docstring CategoryTheory.isArtinianObject_of_isStrictArtinianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isArtinianObject_of_isStrictArtinianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isArtinianObject_of_isStrictArtinianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isNoetherianObject\_of\_faithful\_preservesMono

Noetherian objects transfer across full faithful functors that preserve monomorphisms.

Proof: Map ascending chains of subobjects in $`\mathcal{A}` to ascending chains in $`\mathcal{C}` via the injective monotone subobject image map. Stabilization in $`\mathcal{C}` pulls back to stabilization in $`\mathcal{A}` by injectivity.

{docstring CategoryTheory.isNoetherianObject_of_faithful_preservesMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isNoetherianObject_of_faithful_preservesMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isNoetherianObject_of_faithful_preservesMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isNoetherianObject\_of\_isStrictNoetherianObject

In an abelian category, strict-Noetherian and Noetherian coincide, because every mono is strict.

Proof: Every subobject is strict (since every mono is strict in an abelian category), so ascending chains of subobjects are ascending chains of strict subobjects. Apply the monotone chain condition.

{docstring CategoryTheory.isNoetherianObject_of_isStrictNoetherianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isNoetherianObject_of_isStrictNoetherianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isNoetherianObject_of_isStrictNoetherianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictArtinianObject

An object $`X` is strict-Artinian if the strict subobjects of $`X` satisfy the descending chain condition. This is the finite-length notion relevant to quasi-abelian categories.

Construction: Defined as an `ObjectProperty` asserting `WellFoundedLT (StrictSubobject X)`.


{docstring CategoryTheory.isStrictArtinianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictArtinianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictArtinianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictArtinianObject\_of\_faithful\_map\_strictMono

Strict-Artinian objects transfer across full faithful functors that send strict monomorphisms to strict monomorphisms.

Proof: Map descending chains of strict subobjects in $`\mathcal{A}` to descending chains of subobjects in $`\mathcal{C}` via the injective monotone strict-subobject image map, then use the Artinian hypothesis in $`\mathcal{C}` and injectivity.

{docstring CategoryTheory.isStrictArtinianObject_of_faithful_map_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictArtinianObject_of_faithful_map_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictArtinianObject_of_faithful_map_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictArtinianObject\_of\_isArtinianObject

Ordinary Artinian objects are strict-Artinian, since strict subobjects form a subtype of all subobjects and descending chains in the subtype lift to descending chains in the full subobject lattice.

Proof: The inclusion `StrictSubobject X \hookrightarrow Subobject X` is order-preserving, so `InvImage.wf` transfers the well-foundedness.

{docstring CategoryTheory.isStrictArtinianObject_of_isArtinianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictArtinianObject_of_isArtinianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictArtinianObject_of_isArtinianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictEpi\_cokernel

The cokernel of any morphism is a strict epimorphism. The coimage-to-image comparison for $`Y \twoheadrightarrow \operatorname{coker}(g)` is an isomorphism because $`\operatorname{coker}(g)` is epi (making the image trivial) and an explicit inverse pair of `cokernel.desc` morphisms establishes $`\operatorname{Coim}(\operatorname{coker.\pi}(g)) \cong \operatorname{coker}(g)`.

Proof: Dual to `isStrictMono_kernel`: since $`\operatorname{coker.\pi}(g)` is epi, its cokernel is zero, making $`\operatorname{ker.\iota}(\operatorname{coker.\pi}( \operatorname{coker.\pi}(g)))` an iso. An explicit inverse pair of `cokernel.desc` morphisms completes the argument.

{docstring CategoryTheory.isStrictEpi_cokernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictEpi_cokernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictEpi_cokernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictEpi\_of\_epi

In an abelian category, every epimorphism is a strict epimorphism.

Proof: Combine the epi hypothesis with `isStrict_of_abelian`.

{docstring CategoryTheory.isStrictEpi_of_epi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictEpi_of_epi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictEpi_of_epi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictEpi\_of\_isColimitCokernelCofork

If $`f` is the cokernel of its kernel, then $`f` is a strict epimorphism.

Proof: The colimit hypothesis makes $`f` epi. The coimage-to-image comparison is shown to be an isomorphism by factoring it as $`\operatorname{inv}(\operatorname{image.\iota}) \circ e` where $`e : \operatorname{Coim}(f) \cong Y` comes from the colimit comparison.

{docstring CategoryTheory.isStrictEpi_of_isColimitCokernelCofork}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictEpi_of_isColimitCokernelCofork&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictEpi_of_isColimitCokernelCofork%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictEpi\_of\_isIso

An isomorphism is a strict epimorphism.

Proof: Apply `isStrictEpi_of_isColimitCokernelCofork`: the kernel of an iso is zero, so $`f` is trivially the cokernel of its zero kernel.

{docstring CategoryTheory.isStrictEpi_of_isIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictEpi_of_isIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictEpi_of_isIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictEpi\_of\_normalEpi

A normal epimorphism in a preadditive category with kernels and cokernels is strict.

Proof: Factor the normal epi's colimit through the kernel inclusion to obtain a colimit for the cokernel cofork, then apply `isStrictEpi_of_isColimitCokernelCofork`.

{docstring CategoryTheory.isStrictEpi_of_normalEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictEpi_of_normalEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictEpi_of_normalEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictMono\_kernel

The kernel of any morphism is a strict monomorphism. The coimage-to-image comparison for $`\operatorname{ker}(g) \hookrightarrow X` is an isomorphism because $`\operatorname{ker}(g)` is mono (making the coimage trivial) and an explicit inverse pair of `kernel.lift` morphisms establishes $`\operatorname{ker}(g) \cong \operatorname{Im}(\operatorname{ker}(g))`.

Proof: Since $`\operatorname{ker.\iota}(g)` is mono, its kernel is zero, so $`\operatorname{cokernel.\pi}(\operatorname{ker.\iota}(\operatorname{ker.\iota}(g)))` is an iso. An explicit inverse pair of `kernel.lift` morphisms shows $`\operatorname{ker}(g) \cong \operatorname{ker}(\operatorname{cokernel.\pi}( \operatorname{ker.\iota}(g)))`, and the comparison factors through these isos.

{docstring CategoryTheory.isStrictMono_kernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictMono_kernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictMono_kernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictMono\_of\_isIso

An isomorphism is a strict monomorphism.

Proof: Apply `isStrictMono_of_isLimitKernelFork`: the cokernel of an iso is zero, so $`f` is trivially the kernel of its zero cokernel.

{docstring CategoryTheory.isStrictMono_of_isIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictMono_of_isIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictMono_of_isIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictMono\_of\_isLimitKernelFork

If $`f` is the kernel of its cokernel, then $`f` is a strict monomorphism.

Proof: The limit hypothesis makes $`f` mono. An explicit inverse pair of `kernel.lift` morphisms establishes $`X \cong \operatorname{Im}(f)`, and the coimage-to-image comparison is expressed as a composition of isomorphisms.

{docstring CategoryTheory.isStrictMono_of_isLimitKernelFork}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictMono_of_isLimitKernelFork&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictMono_of_isLimitKernelFork%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictMono\_of\_mono

In an abelian category, every monomorphism is a strict monomorphism.

Proof: Combine the mono hypothesis with `isStrict_of_abelian`.

{docstring CategoryTheory.isStrictMono_of_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictMono_of_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictMono_of_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictMono\_of\_normalMono

A normal monomorphism in a preadditive category with kernels and cokernels is strict.

Proof: Factor the normal mono's limit through the cokernel projection to obtain a limit for the kernel fork, then apply `isStrictMono_of_isLimitKernelFork`.

{docstring CategoryTheory.isStrictMono_of_normalMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictMono_of_normalMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictMono_of_normalMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictNoetherianObject

An object $`X` is strict-Noetherian if the strict subobjects of $`X` satisfy the ascending chain condition.

Construction: Defined as an `ObjectProperty` asserting `WellFoundedGT (StrictSubobject X)`.


{docstring CategoryTheory.isStrictNoetherianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictNoetherianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictNoetherianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictNoetherianObject\_of\_faithful\_map\_strictMono

Strict-Noetherian objects transfer across full faithful functors that send strict monomorphisms to strict monomorphisms.

Proof: Map ascending chains of strict subobjects in $`\mathcal{A}` to ascending chains of subobjects in $`\mathcal{C}` via the injective monotone strict-subobject image map, then use the Noetherian hypothesis in $`\mathcal{C}` and injectivity.

{docstring CategoryTheory.isStrictNoetherianObject_of_faithful_map_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictNoetherianObject_of_faithful_map_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictNoetherianObject_of_faithful_map_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictNoetherianObject\_of\_isNoetherianObject

Ordinary Noetherian objects are strict-Noetherian, since strict subobjects form a subtype of all subobjects and ascending chains in the subtype lift to ascending chains in the full subobject lattice.

Proof: The inclusion `StrictSubobject X \hookrightarrow Subobject X` is order-preserving, so `InvImage.wf` transfers the well-foundedness.

{docstring CategoryTheory.isStrictNoetherianObject_of_isNoetherianObject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictNoetherianObject_of_isNoetherianObject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrictNoetherianObject_of_isNoetherianObject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrict\_of\_abelian

In an abelian category, every morphism is strict.

Proof: In an abelian category, `Abelian.coimageImageComparison` is an isomorphism by definition.

{docstring CategoryTheory.isStrict_of_abelian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrict_of_abelian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isStrict_of_abelian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# strictShortExact\_of\_shortExact

In an abelian category, every short exact sequence is a strict short exact sequence.

Proof: Apply `isStrict_of_abelian` to both morphisms of the short complex.

{docstring CategoryTheory.strictShortExact_of_shortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20strictShortExact_of_shortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.strictShortExact_of_shortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.QuasiAbelian.Basic%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
