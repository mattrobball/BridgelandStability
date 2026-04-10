import BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: MaximalDestabilizingQuotientKernel" =>
%%%
htmlSplit := .never
%%%

# IsStrictMDQKernel

A minimal-phase strict kernel: a proper strict subobject $`M` of an interval object $`X` whose cokernel is $`W`-semistable and has minimal $`W`-phase among all proper strict kernels. This is the dual of the MDQ construction, used in the thin-interval HN recursion.

Construction: A structure with four fields: `ne_top` ($`M \ne \top`), `strict` ($`M.\mathrm{arrow}` is strict mono), `semistable` ($`\operatorname{coker}(M)` is $`W`-semistable), and `minimal` (for any other proper strict kernel $`B`, $`\psi(\operatorname{coker}(M)) \le \psi(\operatorname{coker}(B))`).


{docstring CategoryTheory.Triangulated.IsStrictMDQKernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsStrictMDQKernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsStrictMDQKernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hn\_exists\_in\_thin\_interval\_of\_finiteSubobjects

HN existence in thin intervals with finite subobjects: every nonzero interval object admits an HN filtration with $`\operatorname{ssf}`-semistable factors whose phases lie in $`(L, U)`. This is the legacy version using global Hom vanishing and destabilizing phase bounds.

Proof: Delegates to `hn_exists_in_thin_interval` after packaging the finite-subobject hypothesis into the required form.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.hn_exists_in_thin_interval_of_finiteSubobjects}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hn_exists_in_thin_interval_of_finiteSubobjects&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.hn_exists_in_thin_interval_of_finiteSubobjects%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictMDQKernel\_of\_minPhase\_strictKernel

A proper strict kernel with semistable quotient of minimal quotient phase packages into the strict-kernel MDQ structure used in the faithful Node 7.7 refactor.

Proof: Direct constructor application: assemble the four fields from the given hypotheses.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictMDQKernel_of_minPhase_strictKernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictMDQKernel\_of\_minPhase\_strictKernel\_of\_finiteLength

The finite-length version: packages a minimal-phase strict kernel into the MDQ-kernel structure when the ambient interval has thin finite length.

Proof: Extract strict-Artinian and strict-Noetherian instances from `ThinFiniteLengthInInterval`, then delegate to `isStrictMDQKernel_of_minPhase_strictKernel_of_strictArtinian`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel_of_finiteLength}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictMDQKernel_of_minPhase_strictKernel_of_finiteLength&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel_of_finiteLength%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isStrictMDQKernel\_of\_minPhase\_strictKernel\_of\_strictArtinian

Packages a minimal-phase strict kernel with strict-Artinian cokernel into the MDQ-kernel structure, combining `semistable_cokernel_of_minPhase_strictKernel_of_minimal_of_strictArtinian` with the constructor.

Proof: First establish semistability via the strict-Artinian version, then apply the constructor.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel_of_strictArtinian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isStrictMDQKernel_of_minPhase_strictKernel_of_strictArtinian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel_of_strictArtinian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_lt\_of\_strictQuotient\_of\_minPhase\_strictKernel

Every proper strict quotient of a minimal-phase minimal strict kernel $`M` has phase strictly larger than the phase of the ambient minimal quotient $`\operatorname{coker}(M)`. This is the kernel-recursion step for thin-interval HN existence.

Proof: Lift the subobject $`A \hookrightarrow M` to a subobject of $`X` via the composition $`A \hookrightarrow M \hookrightarrow X`. This lift is strictly smaller than $`M`, so the minimality of $`M` gives $`\psi(\operatorname{coker}(M)) < \psi(\operatorname{coker}(\mathrm{lift}))`. The seesaw decomposition $`W(\operatorname{coker}(\mathrm{lift})) = W(\operatorname{coker}(A)) + W(\operatorname{coker}(M))` then forces $`\psi(\operatorname{coker}(A)) > \psi(\operatorname{coker}(\mathrm{lift})) > \psi(\operatorname{coker}(M))`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.phase_lt_of_strictQuotient_of_minPhase_strictKernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_lt_of_strictQuotient_of_minPhase_strictKernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.phase_lt_of_strictQuotient_of_minPhase_strictKernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_cokernel\_of\_minPhase\_strictKernel\_of\_minimal

If a proper strict kernel $`M` has minimal quotient phase among all proper strict kernels (with finite subobjects), then its cokernel $`X/M` is $`W`-semistable. Any destabilizing strict subobject of $`X/M` would pull back to a strictly larger kernel with smaller cokernel phase, contradicting minimality.

Proof: By contradiction: if $`X/M` is not semistable, find a maximal-phase strict subobject $`B` of $`X/M` with $`\psi(B) > \psi(X/M)`. Pull $`B` back to a proper strict kernel of $`X`. The seesaw gives $`\psi(\operatorname{coker}(\mathrm{pullback})) < \psi(X/M)`, contradicting minimality.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel_of_minimal}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_cokernel_of_minPhase_strictKernel_of_minimal&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel_of_minimal%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_cokernel\_of\_minPhase\_strictKernel\_of\_minimal\_of\_strictArtinian

The strict-Artinian version of the quotient-semistability step: if a proper strict kernel $`M` has minimal quotient phase and the cokernel is strict-Artinian, then the cokernel is $`W`-semistable. Uses strict-Artinian descent (first strict SES) instead of finite enumeration.

Proof: Same pullback contradiction as the finite-subobject version, but the destabilizing strict subobject of the quotient is chosen by strict-Artinian descent rather than finite enumeration.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel_of_minimal_of_strictArtinian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_cokernel_of_minPhase_strictKernel_of_minimal_of_strictArtinian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel_of_minimal_of_strictArtinian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cokernelMapMonoIso

For nested subobjects $`S \leq T` of $`X` and a monomorphism $`f : X \to Y`, there is a canonical isomorphism $`\mathrm{coker}(\mathrm{map}(f)(S) \hookrightarrow \mathrm{map}(f)(T)) \cong \mathrm{coker}(S \hookrightarrow T)`.

Construction: Constructed via `cokernel.mapIso` using the canonical isomorphisms `Subobject.mapMonoIso f S` and `Subobject.mapMonoIso f T`, with the compatibility condition provided by `Subobject.ofLE_map_comp_mapMonoIso_hom`.


{docstring CategoryTheory.Triangulated.Subobject.cokernelMapMonoIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernelMapMonoIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.cokernelMapMonoIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mapMonoIso

For a monomorphism $`f : X \to Y` and a subobject $`S \leq X`, there is a canonical isomorphism $`(\mathrm{map}(f)(S) : D) \cong (S : D)` between the image of $`S` under the pushforward along $`f` and $`S` itself as objects of $`D`.

Construction: Constructed as `Subobject.isoOfEqMk` applied to the equality `Subobject.map_eq_mk_mono f S`, which identifies `(Subobject.map f).obj S` with `Subobject.mk (S.arrow ≫ f)`.


{docstring CategoryTheory.Triangulated.Subobject.mapMonoIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mapMonoIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.mapMonoIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# map\_eq\_mk\_mono

For a monomorphism $`f : X \to Y` and a subobject $`S \leq X`, the pushforward $`(\mathrm{map}(f))(S)` equals $`\mathrm{mk}(S.\mathrm{arrow} \circ f)` as a subobject of $`Y`.

Proof: Rewrite $`S` as $`\mathrm{mk}(S.\mathrm{arrow})` and apply the functoriality formula `Subobject.map_mk`.

{docstring CategoryTheory.Triangulated.Subobject.map_eq_mk_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20map_eq_mk_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.map_eq_mk_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ofLE\_map\_comp\_mapMonoIso\_hom

For nested subobjects $`S \leq T` of $`X` and a monomorphism $`f : X \to Y`, the natural square $`\mathrm{ofLE}(\mathrm{map}(f)(S), \mathrm{map}(f)(T)) \circ (\mathrm{mapMonoIso}(f,T)).\mathrm{hom} = (\mathrm{mapMonoIso}(f,S)).\mathrm{hom} \circ \mathrm{ofLE}(S,T)` commutes.

Proof: Both composites are equal after postcomposing with the arrow of $`T` and then $`f`: this reduces to associativity and the definition of `Subobject.mapMonoIso` and `Subobject.ofLE`.

{docstring CategoryTheory.Triangulated.Subobject.ofLE_map_comp_mapMonoIso_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ofLE_map_comp_mapMonoIso_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.ofLE_map_comp_mapMonoIso_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interval\_cokernelTopIso

For a subobject $`A \leq X` in a thin interval category $`\mathcal{P}((a,b))`, the cokernel of the inclusion $`A \hookrightarrow \top` is canonically isomorphic to the cokernel of $`A.\mathrm{arrow} : A \to X`.

Construction: Constructed by composing the isomorphism `cokernelCompIsIso` (which uses that the top subobject arrow is an isomorphism) with `cokernelIsoOfEq` applied to the identity `\mathrm{ofLE}(A,\top).\mathrm{arrow} = A.\mathrm{arrow}`.


{docstring CategoryTheory.Triangulated.interval_cokernelTopIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interval_cokernelTopIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interval_cokernelTopIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# thinFiniteLength\_cokernel

Every cokernel of a subobject arrow in a thin finite-length interval inherits strict finite length.

Proof: Immediate: the cokernel is an object of the interval category, so `ThinFiniteLengthInInterval` applies.

{docstring CategoryTheory.Triangulated.thinFiniteLength_cokernel}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20thinFiniteLength_cokernel&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.thinFiniteLength_cokernel%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_cokernel\_kernelSubobject\_eq

The $`W`-phase of the cokernel of a kernel subobject equals the $`W`-phase of the original quotient target: $`\psi(\operatorname{coker}(\ker(q))) = \psi(B)` when $`q : X \twoheadrightarrow B` is a strict epi.

Proof: The cokernel of $`\ker(q)` is isomorphic to $`B` via the canonical comparison. Transport the $`W`-phase through this isomorphism using `cl_iso`.

{docstring CategoryTheory.Triangulated.wPhaseOf_cokernel_kernelSubobject_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_cokernel_kernelSubobject_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_cokernel_kernelSubobject_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_cokernel\_mapMono\_eq

For nested subobjects $`S \leq T` of $`X` in an interval category and a monomorphism $`f : X \to Y`, the $`W`-phase of $`\mathrm{coker}(\mathrm{map}(f)(S) \hookrightarrow \mathrm{map}(f)(T))` equals the $`W`-phase of $`\mathrm{coker}(S \hookrightarrow T)`.

Proof: The canonical isomorphism `Subobject.cokernelMapMonoIso f h` between the two cokernels gives an isomorphism after applying the interval inclusion functor, so the $`W`-phase is preserved by `wPhase_iso`.

{docstring CategoryTheory.Triangulated.wPhaseOf_cokernel_mapMono_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_cokernel_mapMono_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_cokernel_mapMono_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_cokernel\_ofLE\_top\_eq

For a subobject $`A \leq X` in an interval category, the $`W`-phase of $`\mathrm{coker}(A \hookrightarrow \top)` equals the $`W`-phase of $`\mathrm{coker}(A.\mathrm{arrow})`.

Proof: The canonical isomorphism `interval_cokernelTopIso A` gives an isomorphism of underlying objects, so their classes in $`K_0` agree and hence $`W` takes the same value; the $`W`-phase is then equal.

{docstring CategoryTheory.Triangulated.wPhaseOf_cokernel_ofLE_top_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_cokernel_ofLE_top_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_cokernel_ofLE_top_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.MaximalDestabilizingQuotientKernel%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
