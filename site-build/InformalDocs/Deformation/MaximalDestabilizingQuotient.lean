import BridgelandStability.Deformation.MaximalDestabilizingQuotient
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: MaximalDestabilizingQuotient" =>
%%%
htmlSplit := .never
%%%

# IsStrictMDQ

A strict maximally destabilizing quotient in a thin interval category: a morphism $`q : X \twoheadrightarrow B` such that $`q` is strict epi, $`B` is nonzero and $`W`-semistable, and $`q` has minimal $`W`-phase among all $`W`-semistable strict quotients (with equality forcing factorization). This is the quasi-abelian analogue of `StabilityFunction.IsMDQ`.

Construction: A structure with four fields: `strictEpi` (the quotient map is a strict epimorphism), `nonzero` ($`B` is nonzero), `semistable` ($`B` is $`\operatorname{ssf}`-semistable at its $`W`-phase), and `minimal` (for any other semistable strict quotient $`B'`, $`\psi(B) \le \psi(B')` with equality giving a factorization $`q' = q \circ t`).


{docstring CategoryTheory.Triangulated.IsStrictMDQ}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsStrictMDQ&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# comp\_of\_destabilizing\_semistable\_subobject

If $`A \hookrightarrow X` is a destabilizing $`W`-semistable strict subobject with $`\psi(A) > \psi(X)` and $`A \ne \top`, and $`q : \operatorname{coker}(A) \to B` is a strict MDQ on the cokernel, then $`\operatorname{coker\_proj}(A) \circ q : X \to B` is a strict MDQ on $`X`.

Proof: Strict epi follows from composition. Minimality: for a competitor $`q' : X \to B'` with $`\psi(B') \le \psi(B)`, the Hom vanishing $`\operatorname{Hom}(A, B') = 0` (from the phase gap) implies $`q'` factors through $`\operatorname{coker}(A)`, reducing to the MDQ minimality on the cokernel.

{docstring CategoryTheory.Triangulated.IsStrictMDQ.comp_of_destabilizing_semistable_subobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20comp_of_destabilizing_semistable_subobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ.comp_of_destabilizing_semistable_subobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# factor\_of\_phase\_eq\_of\_strictQuotient

If a nonzero strict quotient $`Q` of the MDQ source has the same $`W`-phase as the MDQ target $`B`, then the MDQ factors through $`Q`: there exists $`t : B \to Q` with $`q' = q \circ t`.

Proof: By `isSemistable_of_strictQuotient_phase_eq`, $`Q` is semistable at the common phase. The MDQ minimality then yields the factorization.

{docstring CategoryTheory.Triangulated.IsStrictMDQ.factor_of_phase_eq_of_strictQuotient}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20factor_of_phase_eq_of_strictQuotient&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ.factor_of_phase_eq_of_strictQuotient%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# id\_of\_semistable

A semistable interval object is its own strict MDQ: $`\operatorname{id}_X : X \to X` is a strict MDQ when $`X` is $`W`-semistable.

Proof: The identity is trivially strict epi, $`X` is nonzero and semistable by hypothesis, and minimality follows from `phase_le_of_strictQuotient_of_window` with factorization via $`q' = \operatorname{id} \circ q'`.

{docstring CategoryTheory.Triangulated.IsStrictMDQ.id_of_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20id_of_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ.id_of_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isSemistable\_of\_strictQuotient\_phase\_eq

If a nonzero strict quotient of the source has the same phase as a strict MDQ, then it is already semistable. Otherwise a destabilizing strict subobject would produce a smaller-phase strict quotient, contradicting MDQ minimality.

Proof: By contradiction: if the quotient is not semistable, the first strict SES (strict-Artinian descent) produces a proper subobject of larger phase. The composition through the cokernel gives a strict quotient of $`X` with phase $`< \psi(B)`, which is then below the MDQ quotient with phase equal to $`\psi(B)`, contradicting minimality.

{docstring CategoryTheory.Triangulated.IsStrictMDQ.isSemistable_of_strictQuotient_phase_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isSemistable_of_strictQuotient_phase_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ.isSemistable_of_strictQuotient_phase_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# kernelSubobject\_ne\_bot\_of\_not\_semistable

If $`X` is not $`W`-semistable and $`q : X \to B` is a strict MDQ, then $`\ker(q) \ne \bot`. If it were, $`q` would be an isomorphism, forcing $`X \cong B` to be semistable.

Proof: If $`\ker(q) = \bot` then $`q` is mono and epi, hence iso. But $`B` is semistable, contradicting $`X` not being semistable.

{docstring CategoryTheory.Triangulated.IsStrictMDQ.kernelSubobject_ne_bot_of_not_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20kernelSubobject_ne_bot_of_not_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ.kernelSubobject_ne_bot_of_not_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_strictEpi\_factor

If a strict MDQ $`q : X \twoheadrightarrow B` factors as $`q = p \circ \pi_Q` through a strict epi $`p : X \twoheadrightarrow Q`, then $`\pi_Q : Q \to B` is also a strict MDQ.

Proof: Strict epi property of $`\pi_Q` follows from `interval_strictEpi_of_strictEpi_comp`. Minimality: for any competitor $`q' : Q \to B'`, the composite $`p \circ q'` is a competitor for $`q`, so the original minimality applies.

{docstring CategoryTheory.Triangulated.IsStrictMDQ.of_strictEpi_factor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_strictEpi_factor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ.of_strictEpi_factor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_le\_of\_strictQuotient

The phase of a strict MDQ is bounded above by the phase of any nonzero strict quotient of its source: if $`q : X \twoheadrightarrow B` is a strict MDQ and $`p : X \twoheadrightarrow Q` is any strict epi with $`Q \ne 0`, then $`\psi(B) \le \psi(Q)`.

Proof: Find a semistable strict quotient of $`Q` with phase $`\le \psi(Q)` (by `exists_semistable_strictQuotient_le_phase_of_finiteLength`), compose to get a semistable strict quotient of $`X`, then apply the MDQ minimality.

{docstring CategoryTheory.Triangulated.IsStrictMDQ.phase_le_of_strictQuotient}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_le_of_strictQuotient&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ.phase_le_of_strictQuotient%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_lt\_of\_strictQuotient\_of\_kernel

For a strict MDQ $`q : X \twoheadrightarrow B`, every proper strict quotient of $`\ker(q)` has $`W`-phase strictly greater than $`\psi(B)`.

Proof: A strict quotient of $`\ker(q)` gives a strictly larger kernel subobject of $`X`. The cokernel of this larger kernel has phase $`< \psi(\operatorname{coker}(\ker(q))) = \psi(B)` by the seesaw, but $`\psi(B) \le` that phase by MDQ minimality. The resolution gives the strict inequality.

{docstring CategoryTheory.Triangulated.IsStrictMDQ.phase_lt_of_strictQuotient_of_kernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_lt_of_strictQuotient_of_kernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ.phase_lt_of_strictQuotient_of_kernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# precomposeIso

Precomposing a strict MDQ with an isomorphism of sources preserves the strict MDQ property: if $`q : X \to B` is a strict MDQ and $`e : X' \cong X`, then $`e \circ q : X' \to B` is a strict MDQ.

Proof: Strict epi is preserved by precomposing with an isomorphism. Minimality: given a competitor $`q' : X' \to B'`, compose with $`e^{-1}` to get a competitor for $`q`, apply the original minimality, then re-compose.

{docstring CategoryTheory.Triangulated.IsStrictMDQ.precomposeIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20precomposeIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQ.precomposeIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_semistable\_strictQuotient\_le\_phase\_of\_finiteLength

Quotient selection for thin interval categories: every nonzero interval object $`X` admits a proper strict kernel $`M` whose cokernel is $`W`-semistable with $`W`-phase at most that of $`X`. This is the strict-kernel analogue of Proposition 2.4's first quotient-selection step.

Proof: Noetherian induction on the strict-subobject poset. At each step, test whether the cokernel of the current kernel is semistable. If yes, stop. If not, find a destabilizing strict subobject of the cokernel, pull it back to get a strictly larger kernel, and note the phase decreases. Terminate by well-foundedness.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_semistable_strictQuotient_le_phase_of_finiteLength}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_semistable_strictQuotient_le_phase_of_finiteLength&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_semistable_strictQuotient_le_phase_of_finiteLength%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_strictMDQ\_of\_finiteLength

MDQ existence in thin finite-length interval categories: every nonzero interval object admits a strict MDQ. This is the foundational MDQ existence theorem using the strict-Noetherian descent.

Proof: Noetherian induction. If the cokernel of the current kernel is semistable, its identity is an MDQ. Otherwise, find a destabilizing strict subobject, pull back to get a larger kernel, recurse on the cokernel, then compose via `comp_of_destabilizing_semistable_subobject`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_strictMDQ_of_finiteLength}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_strictMDQ_of_finiteLength&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_strictMDQ_of_finiteLength%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mapSubIso

For an object $`E`, a subobject $`K \leq E`, and a subobject $`S \leq K`, there is a canonical isomorphism $`(\mathrm{map}(K.\mathrm{arrow})(S) : D) \cong (S : D)` between the image of $`S` under the pushforward along $`K.\mathrm{arrow}` and $`S` itself as objects of $`D`.

Construction: Constructed as `Subobject.isoOfEqMk` applied to the equality `Subobject.map_eq_mk K S`, which identifies `(Subobject.map K.arrow).obj S` with `Subobject.mk (S.arrow ≫ K.arrow)`, followed by the underlying isomorphism.


{docstring CategoryTheory.Triangulated.Subobject.mapSubIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mapSubIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.mapSubIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# map\_eq\_mk

For a subobject $`K \leq E` and a subobject $`S \leq K`, the pushforward $`(\mathrm{map}(K.\mathrm{arrow}))(S)` equals $`\mathrm{mk}(S.\mathrm{arrow} \circ K.\mathrm{arrow})` as a subobject of $`E`.

Proof: Rewrite $`S` as $`\mathrm{mk}(S.\mathrm{arrow})` and apply the functoriality formula `Subobject.map_mk`.

{docstring CategoryTheory.Triangulated.Subobject.map_eq_mk}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20map_eq_mk&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.map_eq_mk%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ThinFiniteLengthInInterval

The thin interval category $`\mathcal{P}((a,b))` has strict finite length when every interval object is both strict-Artinian and strict-Noetherian. This is the finite-length hypothesis used in the MDQ construction.

Construction: Defined as a universal quantification: for every $`Y` in the interval category, $`Y` is strict-Artinian and strict-Noetherian.


{docstring CategoryTheory.Triangulated.ThinFiniteLengthInInterval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ThinFiniteLengthInInterval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.ThinFiniteLengthInInterval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_ambient

Derive thin finite length for a sub-interval from artinian/noetherian data on an ambient interval via inclusion.

Proof: Immediate from `interval_thinFiniteLength_of_inclusion` applied to the inclusion of interval predicates.

{docstring CategoryTheory.Triangulated.ThinFiniteLengthInInterval.of_ambient}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_ambient&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.ThinFiniteLengthInInterval.of_ambient%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# of\_wide

Derive thin finite length for $`\mathcal{P}((a,b))` from wide-sector finite length at center $`t` with radius $`4\varepsilon_0`: if $`t - 4\varepsilon_0 \le a` and $`b \le t + 4\varepsilon_0`, then the interval inclusion monotonicity gives the result.

Proof: The interval $`(a,b)` is contained in $`(t - 4\varepsilon_0, t + 4\varepsilon_0)`. Apply interval inclusion and transport the strict finite-length property from the wider interval.

{docstring CategoryTheory.Triangulated.ThinFiniteLengthInInterval.of_wide}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_wide&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.ThinFiniteLengthInInterval.of_wide%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_kernelSubobject\_isLimitKernelFork

For a morphism $`q : X \to Y` in a thin interval category $`\mathcal{P}((a,b))` with $`b - a \leq 1`, the canonical fork $`\ker(q) \hookrightarrow X \xrightarrow{q} Y` with the kernel subobject arrow is a limit kernel fork.

Proof: Any morphism $`g : W \to X` with $`g \circ q = 0` factors through $`\ker(q)` via `kernel.lift`; composing with the isomorphism `kernelSubobjectIso` gives the unique factorization through the kernel subobject arrow.

{docstring CategoryTheory.Triangulated.interval_kernelSubobject_isLimitKernelFork}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_kernelSubobject_isLimitKernelFork&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_kernelSubobject_isLimitKernelFork%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_kernelSubobject\_ne\_top\_of\_strictEpi\_nonzero

The kernel subobject of a strict epi with nonzero target is not $`\top`. If it were, the strict epi would factor through zero, contradicting the nonzero target.

Proof: If $`\ker(q) = \top` then $`q` factors through the zero object, but $`q` is epi with nonzero target, contradiction.

{docstring CategoryTheory.Triangulated.interval_kernelSubobject_ne_top_of_strictEpi_nonzero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_kernelSubobject_ne_top_of_strictEpi_nonzero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_kernelSubobject_ne_top_of_strictEpi_nonzero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictEpi\_of\_strictEpi\_comp

If $`p \circ q` is a strict epimorphism in a thin interval category, then $`q` is a strict epimorphism.

Proof: Map to the left heart. The image of $`p \circ q` is epi, so the image of $`q` is epi. Transport back.

{docstring CategoryTheory.Triangulated.interval_strictEpi_of_strictEpi_comp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictEpi_of_strictEpi_comp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictEpi_of_strictEpi_comp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictShortExact\_of\_kernelSubobject\_strictEpi

If $`q : X \twoheadrightarrow Y` is a strict epimorphism in a thin interval category $`\mathcal{P}((a,b))` with $`b - a \leq 1`, then the sequence $`\ker(q) \hookrightarrow X \twoheadrightarrow Y` with the kernel subobject inclusion is a strict short exact sequence.

Proof: The kernel subobject arrow forms a limit kernel fork by `interval_kernelSubobject_isLimitKernelFork`; with the strict epi hypothesis on $`q`, `interval_strictShortExact_of_kernel_strictEpi` then yields strict short exactness.

{docstring CategoryTheory.Triangulated.interval_strictShortExact_of_kernelSubobject_strictEpi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictShortExact_of_kernelSubobject_strictEpi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictShortExact_of_kernelSubobject_strictEpi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# thinFiniteLength\_of\_node78\_window

The Node 7.8 window $`\mathcal{P}((t - 3\varepsilon_0, t + 5\varepsilon_0))` has thin finite length, derived from wide-sector finite length centered at $`t + \varepsilon_0`.

Proof: Apply `ThinFiniteLengthInInterval.of_wide` with center $`t + \varepsilon_0` and verify the containment bounds.

{docstring CategoryTheory.Triangulated.thinFiniteLength_of_node78_window}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20thinFiniteLength_of_node78_window&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.thinFiniteLength_of_node78_window%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_gt\_of\_strictQuotient\_of\_inner\_strip

For an object $`X` in the inner strip $`\mathcal{P}((a + 2\varepsilon, b - 4\varepsilon))` of a thin interval $`\mathcal{P}((a,b))`, every nonzero strict quotient has $`W`-phase strictly greater than $`a + \varepsilon`.

Proof: The inner strip containment gives tight phase bounds. The $`W`-phase of any interval object is $`> a - \varepsilon` by perturbation bounds, and $`a + \varepsilon` is obtained by monotonicity from the tighter inner strip.

{docstring CategoryTheory.Triangulated.wPhaseOf_gt_of_strictQuotient_of_inner_strip}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_gt_of_strictQuotient_of_inner_strip&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_gt_of_strictQuotient_of_inner_strip%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotient%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
