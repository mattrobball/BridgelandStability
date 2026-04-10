import BridgelandStability.Deformation.IntervalSelection
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: IntervalSelection" =>
%%%
htmlSplit := .never
%%%

# of\_wide

The thin-sector finite length hypothesis follows from the wide-sector one: $`\operatorname{WideSectorFiniteLength}(\sigma, \varepsilon_0) \Rightarrow \operatorname{SectorFiniteLength}(\sigma, 2\varepsilon_0)`.

Proof: A $`2\varepsilon_0`-interval is contained in a $`4\varepsilon_0`-interval, so apply `interval_thinFiniteLength_of_inclusion`.

{docstring CategoryTheory.Triangulated.SectorFiniteLength.of_wide}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20of_wide&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SectorFiniteLength.of_wide%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_maxPhase\_maximal\_strictSubobject

For a nonzero object $`X` in a thin interval subcategory $`\mathcal{P}((a,b))` with finite subobject lattice, there exists a nonzero strict subobject $`M` of $`X` with maximal $`W`-phase among all nonzero strict subobjects, and maximal for inclusion among those with the same $`W`-phase.

Proof: Delegates to `exists_maxPhase_maximal_strictSubobject_of_finite` using `Set.toFinite` to convert the `Finite (Subobject X)` instance to finiteness of the set of nonzero strict subobjects.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_maxPhase_maximal_strictSubobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_maxPhase_maximal_strictSubobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_maxPhase_maximal_strictSubobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_maxPhase\_maximal\_strictSubobject\_of\_finite

Given a non-zero object $`X` in a thin interval category $`\mathcal{P}((a,b))` whose set of nonzero strict subobjects is finite, there exists a nonzero strict subobject $`M \hookrightarrow X` whose $`W`-phase is maximal among all nonzero strict subobjects, and which is maximal for inclusion among all strict subobjects realizing that maximal $`W`-phase. Moreover, any strict subobject strictly containing $`M` has strictly smaller $`W`-phase.

Proof: Among the nonempty finite set of nonzero strict subobjects, choose $`M_0` maximizing $`W`-phase. Among all subobjects realizing phase equal to $`\phi(M_0)`, take a maximal one $`M` by inclusion; finiteness ensures such a maximum exists. The strict phase-drop property for $`M` then follows from the maximality of $`M` within the equal-phase class.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_maxPhase_maximal_strictSubobject_of_finite}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_maxPhase_maximal_strictSubobject_of_finite&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_maxPhase_maximal_strictSubobject_of_finite%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_minPhase\_maximal\_strictKernel

Given a non-semistable non-zero object $`X` in a thin interval category $`\mathcal{P}((a,b))` with finitely many subobjects, there exists a proper strict kernel $`M \subsetneq X` whose strict quotient $`X/M` has minimal $`W`-phase among all proper strict kernels, and which is maximal for inclusion among all proper strict kernels realizing that minimum quotient $`W`-phase. Any proper strict kernel strictly contained in $`M` has strictly larger quotient phase.

Proof: Non-semistability of $`X` supplies an initial proper strict kernel. Among all proper strict kernels, the finite set has a minimum quotient phase realized by some $`M_0`. Among kernels with the same minimal quotient phase, a maximal one $`M` is chosen by inclusion; finiteness guarantees existence. Strict phase increase for subobjects of $`M` follows from the maximality of $`M` in that equal-phase class.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_minPhase_maximal_strictKernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_minPhase_maximal_strictKernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_minPhase_maximal_strictKernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_minPhase\_minimal\_strictKernel

Given a non-semistable non-zero object $`X` in a thin interval category $`\mathcal{P}((a,b))` with finitely many subobjects, there exists a proper strict kernel $`M \subsetneq X` whose strict quotient has minimal $`W`-phase among all proper strict kernels, and which is minimal for inclusion among all proper strict kernels realizing that minimum quotient $`W`-phase. Any proper strict kernel strictly smaller than $`M` has strictly larger quotient $`W`-phase.

Proof: Apply `exists_minPhase_maximal_strictKernel` to get a minimal-phase kernel $`M_0`, then among all proper strict kernels with the same minimal quotient phase take a minimal one $`M` by inclusion. The strict phase increase for sub-kernels of $`M` follows from the minimality of $`M` in the equal-phase class.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_minPhase_minimal_strictKernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_minPhase_minimal_strictKernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_minPhase_minimal_strictKernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_phase\_gt\_strictSubobject\_of\_not\_semistable

If an interval object $`X` is not W-semistable at its own W-phase, then there exists a nonzero strict subobject whose W-phase strictly exceeds that of $`X`.

Proof: The failure of W-semistability provides a distinguished triangle $`K \to X \to Q` with $`\operatorname{wPhaseOf}(W(K)) > \operatorname{wPhaseOf}(W(X))`. The strict mono $`K \hookrightarrow X` gives the desired subobject.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.exists_phase_gt_strictSubobject_of_not_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_phase_gt_strictSubobject_of_not_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.exists_phase_gt_strictSubobject_of_not_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_maxPhase\_strictSubobject

The maximal strict subobject from `exists_maxPhase_maximal_strictSubobject` is W-semistable: any further strict subobject has W-phase at most equal.

Proof: By maximality of the W-phase among strict subobjects, any subobject of the maximal one cannot have strictly larger phase.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_of_maxPhase_strictSubobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_maxPhase_strictSubobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_of_maxPhase_strictSubobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalInclusion\_map\_strictMono

The inclusion functor between nested interval subcategories preserves strict monomorphisms.

Proof: A strict mono $`f` in $`\mathcal{P}((a_1, b_1))` gives a strict short exact sequence. Map through the inclusion to get a distinguished triangle in $`\mathcal{P}((a_2, b_2))`, which yields strict mono/epi.

{docstring CategoryTheory.Triangulated.intervalInclusion_map_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalInclusion_map_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalInclusion_map_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalLiftSub

Given a strict subobject $`B` of the cokernel $`\operatorname{coker}(M.\operatorname{arrow})` in an interval subcategory, lift it to a subobject of $`X` containing $`M` via pullback along the cokernel projection.

Construction: Defined as the pullback $`(\operatorname{cokernel}.\pi \circ M.\operatorname{arrow})^*(B)`.


{docstring CategoryTheory.Triangulated.intervalLiftSub}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalLiftSub&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalLiftSub%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalLiftSubCokernelIso

For subobjects $`A \leq B` of an interval subobject $`M \leq X` in $`\mathcal{P}((a,b))`, the cokernel of the inclusion $`\widetilde{A} \hookrightarrow \widetilde{B}` of their lifts to $`X` is canonically isomorphic to the cokernel of the original inclusion $`A \hookrightarrow B` inside $`M`.

Construction: The isomorphism is constructed via the canonical identifications $`\widetilde{A} \cong A` and $`\widetilde{B} \cong B` given by `Subobject.underlyingIso`, together with a compatibility check that the lift of the inclusion equals the composition with these isomorphisms, then applying `cokernel.mapIso`.


{docstring CategoryTheory.Triangulated.intervalLiftSubCokernelIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalLiftSubCokernelIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalLiftSubCokernelIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalLiftSub\_arrow\_strictMono\_of\_strictMono

If $`M \hookrightarrow X` and $`A \hookrightarrow M` are both strict monomorphisms in a thin interval category $`\mathcal{P}((a,b))`, then the arrow of the lifted subobject $`\widetilde{A} \hookrightarrow X` is also a strict monomorphism.

Proof: The composite $`A \to M \to X` is strict mono by the interval composition lemma; the arrow of the corresponding subobject of $`X` is then strict mono by `intervalSubobject_arrow_strictMono_of_strictMono`.

{docstring CategoryTheory.Triangulated.intervalLiftSub_arrow_strictMono_of_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalLiftSub_arrow_strictMono_of_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalLiftSub_arrow_strictMono_of_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalLiftSub\_bot

Lifting the bottom subobject $`\bot \leq M` to a subobject of $`X` gives the bottom subobject $`\bot \leq X`.

Proof: The composite arrow $`0 \circ M.\mathrm{arrow}` is zero, so the corresponding subobject is $`\bot` by `Subobject.mk_eq_bot_iff_zero`.

{docstring CategoryTheory.Triangulated.intervalLiftSub_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalLiftSub_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalLiftSub_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalLiftSub\_le

For any subobject $`A \leq M` in the interval category, the lifted subobject $`\widetilde{A} \leq X` satisfies $`\widetilde{A} \leq M` as a subobject of $`X`.

Proof: The composite $`A.\mathrm{arrow} \circ M.\mathrm{arrow}` factors through $`M.\mathrm{arrow}` via $`A.\mathrm{arrow}`, giving the required inequality by `Subobject.mk_le_mk_of_comm`.

{docstring CategoryTheory.Triangulated.intervalLiftSub_le}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalLiftSub_le&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalLiftSub_le%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalLiftSub\_lt

If $`A` is a proper subobject of $`M` (i.e., $`A \neq \top` in $`\mathrm{Sub}(M)`), then the lifted subobject $`\widetilde{A}` is strictly smaller than $`M` as a subobject of $`X`.

Proof: Since $`\widetilde{A} \leq M` by `intervalLiftSub_le`, it suffices to show $`\widetilde{A} \neq M`. Equality would force $`A = \top` via the injectivity of the map $`\mathrm{Sub}(M) \to \mathrm{Sub}(X)` sending a subobject to its composition with $`M.\mathrm{arrow}`, contradicting the hypothesis.

{docstring CategoryTheory.Triangulated.intervalLiftSub_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalLiftSub_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalLiftSub_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalLiftSub\_mono

The operation of lifting subobjects of $`M` to subobjects of $`X` is monotone: if $`A \leq B` in $`\mathrm{Sub}(M)`, then $`\widetilde{A} \leq \widetilde{B}` in $`\mathrm{Sub}(X)`.

Proof: The morphism `Subobject.ofLE A B h` witnesses the inequality at the level of arrows, and `Subobject.mk_le_mk_of_comm` with this morphism gives the desired inequality of lifted subobjects.

{docstring CategoryTheory.Triangulated.intervalLiftSub_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalLiftSub_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalLiftSub_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalLiftSub\_ne\_bot

If $`A \neq \bot` in $`\mathrm{Sub}(M)`, then the lifted subobject $`\widetilde{A}` is also nonzero, i.e., $`\widetilde{A} \neq \bot` in $`\mathrm{Sub}(X)`.

Proof: If $`\widetilde{A} = \bot`, then $`A.\mathrm{arrow} \circ M.\mathrm{arrow} = 0`; since $`M.\mathrm{arrow}` is a monomorphism, $`A.\mathrm{arrow} = 0`, forcing $`A = \bot`, contradicting the hypothesis.

{docstring CategoryTheory.Triangulated.intervalLiftSub_ne_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalLiftSub_ne_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalLiftSub_ne_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalLiftSub\_wPhase\_eq

The $`W`-phase of the lifted subobject $`\widetilde{A} \leq X` in the interval category equals the $`W`-phase of $`A \leq M`: $`\phi_W(\widetilde{A}) = \phi_W(A)`.

Proof: The underlying interval object of $`\widetilde{A}` is canonically isomorphic to that of $`A` via `Subobject.underlyingIso`, so the $`W`-phase is preserved by `wPhase_iso`.

{docstring CategoryTheory.Triangulated.intervalLiftSub_wPhase_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalLiftSub_wPhase_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalLiftSub_wPhase_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalSubobject\_arrow\_strictMono\_of\_strictMono

If $`f : Y \to X` is a strict monomorphism in a thin interval category $`\mathcal{P}((a,b))` with $`b - a \leq 1`, then the arrow of the subobject $`\mathrm{mk}(f) \hookrightarrow X` is also a strict monomorphism.

Proof: The arrow of $`\mathrm{mk}(f)` is the composition of the underlying isomorphism $`e.\mathrm{hom}` with $`f`. Both factors are strict mono (the first by `isStrictMono_of_isIso`, the second by hypothesis), and their composition is strict mono by the interval composition lemma.

{docstring CategoryTheory.Triangulated.intervalSubobject_arrow_strictMono_of_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalSubobject_arrow_strictMono_of_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalSubobject_arrow_strictMono_of_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalSubobject\_bot\_arrow\_strictMono

The arrow of the bottom subobject $`\bot \hookrightarrow X` in a thin interval category $`\mathcal{P}((a,b))` with $`b - a \leq 1` is a strict monomorphism.

Proof: The bottom arrow is the zero morphism $`0 \colon 0 \to X`. Its cokernel map $`X \to X` is an isomorphism, so the zero morphism is a strict mono by the kernel fork limit characterization applied to the fact that the source is a zero object.

{docstring CategoryTheory.Triangulated.intervalSubobject_bot_arrow_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalSubobject_bot_arrow_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalSubobject_bot_arrow_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalSubobject\_isZero\_iff\_eq\_bot

For an object $`X` in an interval subcategory $`\mathcal{P}((a,b))`, a subobject $`B \leq X` is a zero object if and only if $`B = \bot` in $`\mathrm{Sub}(X)`.

Proof: If $`B` is zero, its defining arrow is zero, hence $`B = \mathrm{mk}(0) = \bot` by `Subobject.mk_eq_bot_iff_zero`. Conversely, $`\bot` coerces to the zero object in $`\mathcal{P}((a,b))` via the canonical isomorphism `Subobject.botCoeIsoZero`.

{docstring CategoryTheory.Triangulated.intervalSubobject_isZero_iff_eq_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalSubobject_isZero_iff_eq_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalSubobject_isZero_iff_eq_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalSubobject\_not\_isZero\_of\_ne\_bot

If $`B \neq \bot` as a subobject of $`X` in an interval category, then $`B` is not a zero object.

Proof: This is the contrapositive of `intervalSubobject_isZero_iff_eq_bot`: being zero implies being $`\bot`.

{docstring CategoryTheory.Triangulated.intervalSubobject_not_isZero_of_ne_bot}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalSubobject_not_isZero_of_ne_bot&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalSubobject_not_isZero_of_ne_bot%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalSubobject\_top\_ne\_bot\_of\_not\_isZero

If $`X` is a nonzero object in an interval category $`\mathcal{P}((a,b))`, then the top subobject $`\top \in \mathrm{Sub}(X)` is not equal to $`\bot`.

Proof: If $`\top = \bot`, then by `intervalSubobject_isZero_iff_eq_bot` the top subobject is zero, and since the top subobject arrow is an isomorphism, $`X` itself would be zero, contradicting the hypothesis.

{docstring CategoryTheory.Triangulated.intervalSubobject_top_ne_bot_of_not_isZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalSubobject_top_ne_bot_of_not_isZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalSubobject_top_ne_bot_of_not_isZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_K0\_of\_strictMono

If $`f : Y \hookrightarrow X` is a strict monomorphism in a thin interval category $`\mathcal{P}((a,b))` with $`b - a \leq 1`, then $`[X] = [Y] + [\mathrm{coker}(f)]` in $`K_0(\mathcal{C})` after applying the class map $`v`.

Proof: The strict mono $`f` fits into a strict short exact sequence $`Y \to X \to \mathrm{coker}(f)` by `interval_strictShortExact_cokernel_of_strictMono`; additivity of the $`K_0` class map on strict short exact sequences then gives the formula.

{docstring CategoryTheory.Triangulated.interval_K0_of_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_K0_of_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_K0_of_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_card\_subobject\_lt\_of\_ne\_top

If $`M \subsetneq X` is a proper subobject in an interval category with finitely many subobjects, then the number of subobjects of $`M` is strictly less than the number of subobjects of $`X`.

Proof: The map sending $`A \in \mathrm{Sub}(M)` to $`\mathrm{map}(M.\mathrm{arrow})(A) \in \mathrm{Sub}(X)` is injective. The top subobject $`\top \in \mathrm{Sub}(X)` is not in its image, since being in the image would force $`M = \top`; `Fintype.card_lt_of_injective_of_notMem` then gives strict inequality.

{docstring CategoryTheory.Triangulated.interval_card_subobject_lt_of_ne_top}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_card_subobject_lt_of_ne_top&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_card_subobject_lt_of_ne_top%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictArtinianObject\_of\_inclusion

If $`X` in $`\mathcal{P}((a_1, b_1))` has Artinian image in the wider $`\mathcal{P}((a_2, b_2))`, then $`X` is strict Artinian.

Proof: Since the inclusion is faithful and preserves strict monos, any descending chain of strict subobjects in the source maps injectively to one in the target.

{docstring CategoryTheory.Triangulated.interval_strictArtinianObject_of_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictArtinianObject_of_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictArtinianObject_of_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictArtinianObject\_of\_inclusion\_strict

If the inclusion $`\mathcal{P}((a_1,b_1)) \hookrightarrow \mathcal{P}((a_2,b_2))` holds and $`X` viewed in the larger interval category is strictly Artinian, then $`X` is strictly Artinian in $`\mathcal{P}((a_1,b_1))`.

Proof: The inclusion functor $`I` sends strict subobjects of $`X` to strict subobjects of $`I(X)` injectively and monotonically (via `intervalInclusion_map_strictMono`). Any descending chain in strict subobjects of $`X` gives a descending chain for $`I(X)`, which terminates by strict Artinian hypothesis; injectivity then implies the original chain terminates.

{docstring CategoryTheory.Triangulated.interval_strictArtinianObject_of_inclusion_strict}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictArtinianObject_of_inclusion_strict&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictArtinianObject_of_inclusion_strict%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictFiniteLength\_of\_inclusion

If $`X` in $`\mathcal{P}((a_1, b_1))` has Artinian and Noetherian image in the wider interval, then $`X` has strict finite length.

Proof: Combines `interval_strictArtinianObject_of_inclusion` and `interval_strictNoetherianObject_of_inclusion`.

{docstring CategoryTheory.Triangulated.interval_strictFiniteLength_of_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictFiniteLength_of_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictFiniteLength_of_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictFiniteLength\_of\_inclusion\_strict

If $`X` in the smaller interval category $`\mathcal{P}((a_1,b_1))` maps into $`\mathcal{P}((a_2,b_2))` and is both strictly Artinian and strictly Noetherian there, then $`X` is both strictly Artinian and strictly Noetherian in $`\mathcal{P}((a_1,b_1))`.

Proof: This combines `interval_strictArtinianObject_of_inclusion_strict` and `interval_strictNoetherianObject_of_inclusion_strict` into a single conjunction.

{docstring CategoryTheory.Triangulated.interval_strictFiniteLength_of_inclusion_strict}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictFiniteLength_of_inclusion_strict&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictFiniteLength_of_inclusion_strict%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictNoetherianObject\_of\_inclusion

If $`X` in $`\mathcal{P}((a_1, b_1))` has Noetherian image in the wider $`\mathcal{P}((a_2, b_2))`, then $`X` is strict Noetherian.

Proof: Dual of `interval_strictArtinianObject_of_inclusion` for ascending chains.

{docstring CategoryTheory.Triangulated.interval_strictNoetherianObject_of_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictNoetherianObject_of_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictNoetherianObject_of_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictNoetherianObject\_of\_inclusion\_strict

If the inclusion $`\mathcal{P}((a_1,b_1)) \hookrightarrow \mathcal{P}((a_2,b_2))` holds and $`X` viewed in the larger interval category is strictly Noetherian, then $`X` is strictly Noetherian in $`\mathcal{P}((a_1,b_1))`.

Proof: Dual to the Artinian case: the inclusion functor $`I` transports ascending chains of strict subobjects of $`X` to ascending chains for $`I(X)` injectively and monotonically, and these terminate by the strictly Noetherian hypothesis; injectivity then yields termination in the original category.

{docstring CategoryTheory.Triangulated.interval_strictNoetherianObject_of_inclusion_strict}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictNoetherianObject_of_inclusion_strict&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictNoetherianObject_of_inclusion_strict%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_strictShortExact\_cokernel\_of\_strictMono

A strict monomorphism $`f : Y \hookrightarrow X` in the interval subcategory $`\mathcal{P}((a, b))` with $`b - a \le 1` gives rise to a strict short exact sequence $`Y \hookrightarrow X \twoheadrightarrow \operatorname{coker}(f)`.

Proof: Embed into the abelian left heart via the functor $`\mathcal{P}((a,b)) \to \mathcal{P}((a, a+1])`. The strict mono maps to a mono with epi cokernel projection. Extract the short exact sequence in the heart, lift to a distinguished triangle, and pull back strict short exactness.

{docstring CategoryTheory.Triangulated.interval_strictShortExact_cokernel_of_strictMono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_strictShortExact_cokernel_of_strictMono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_strictShortExact_cokernel_of_strictMono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_thinFiniteLength\_of\_inclusion

If every object in $`\mathcal{P}((a_2, b_2))` has finite length, then every object in the narrower $`\mathcal{P}((a_1, b_1))` has strict finite length.

Proof: Apply `interval_strictFiniteLength_of_inclusion` to each object, using the ambient finite length hypothesis.

{docstring CategoryTheory.Triangulated.interval_thinFiniteLength_of_inclusion}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_thinFiniteLength_of_inclusion&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_thinFiniteLength_of_inclusion%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_thinFiniteLength\_of\_inclusion\_strict

If every object of the larger interval category $`\mathcal{P}((a_2,b_2))` is strictly Artinian and strictly Noetherian, and $`\mathcal{P}((a_1,b_1)) \hookrightarrow \mathcal{P}((a_2,b_2))`, then every object of $`\mathcal{P}((a_1,b_1))` is also strictly Artinian and strictly Noetherian.

Proof: For each $`X \in \mathcal{P}((a_1,b_1))`, apply the finite-length hypothesis to $`I(X)` in the larger category, then use `interval_strictFiniteLength_of_inclusion_strict` to transport the conclusion back.

{docstring CategoryTheory.Triangulated.interval_thinFiniteLength_of_inclusion_strict}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_thinFiniteLength_of_inclusion_strict&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_thinFiniteLength_of_inclusion_strict%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalSelection%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
