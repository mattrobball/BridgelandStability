import BridgelandStability.HeartEquivalence.Forward
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "HeartEquivalence: Forward" =>
%%%
htmlSplit := .never
%%%

# stabilityFunctionOnHeart

Restrict a Bridgeland stability condition $`\sigma` to the heart of its associated $`t`-structure, producing the induced stability function on that abelian heart $`\mathcal{P}((0,1])`.

Construction: The $`Z_{\mathrm{obj}}` field sends $`E` in the heart to $`\sigma.Z([E])` via the inclusion. Additivity follows from the $`K_0`-relation for short exact sequences lifted from the heart to distinguished triangles. The upper half-plane condition uses the HN filtration: each HN factor lies in some $`\mathcal{P}(\varphi)` with $`\varphi \in (0,1]`, so its central charge is in the upper half-plane; the sum of upper half-plane vectors remains in the upper half-plane.


{docstring CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabilityFunctionOnHeart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabilityFunctionOnHeart\_isSemistable\_of\_mem\_P\_phi

For $`\varphi \in (0,1]`, every nonzero $`E \in \mathcal{P}(\varphi)` is semistable with respect to the heart stability function.

Proof: For any subobject $`B \hookrightarrow E` in the heart, the Hom-vanishing property of the slicing forces $`\varphi^+(B) \le \varphi` (otherwise a nonzero map from the top HN factor of $`B` into $`E` would exist, contradicting Hom vanishing from higher to lower phase). Since the heart phase of $`B` is at most $`\varphi^+(B)`, we get $`\operatorname{phase}(B) \le \varphi = \operatorname{phase}(E)`.

{docstring CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart_isSemistable_of_mem_P_phi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabilityFunctionOnHeart_isSemistable_of_mem_P_phi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart_isSemistable_of_mem_P_phi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabilityFunctionOnHeart\_phase\_eq\_of\_mem\_P\_phi

For $`E \in \mathcal{P}(\varphi)` nonzero and $`\varphi \in (0,1]`, the heart stability-function phase of $`E` equals $`\varphi`.

Proof: The compatibility axiom gives $`Z(E) = m \, e^{i\pi\varphi}` with $`m > 0`. Dividing $`\arg(Z(E)) = \pi\varphi` by $`\pi` yields $`\varphi`.

{docstring CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabilityFunctionOnHeart_phase_eq_of_mem_P_phi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabilityFunctionOnHeart\_phase\_le\_phiPlus

For a nonzero heart object $`E`, the heart stability-function phase is at most $`\varphi^+(E)`, the maximal HN phase.

Proof: Decomposes $`Z(E)` as a sum over HN factors. Each factor's argument is at most $`\pi \varphi^+(E)`. The argument of a sum of upper half-plane vectors is at most the supremum of the individual arguments, so $`\arg(Z(E)) / \pi \le \varphi^+(E)`.

{docstring CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart_phase_le_phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabilityFunctionOnHeart_phase_le_phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart_phase_le_phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# append\_hn\_filtration\_of\_mono\_local

Given a monomorphism $`i : X \hookrightarrow Y` with semistable cokernel $`B` of phase strictly less than the last HN phase of $`X`, one can append $`B` to obtain an HN filtration of $`Y`.

Proof: Delegates to $`\texttt{append\_hn\_filtration\_of\_mono}`.

{docstring CategoryTheory.Triangulated.StabilityFunction.append_hn_filtration_of_mono_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20append_hn_filtration_of_mono_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityFunction.append_hn_filtration_of_mono_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_hn\_with\_last\_phase\_of\_semistable\_local

A semistable object admits an HN filtration whose last phase equals the object's stability-function phase.

Proof: Delegates to the general existence result $`\texttt{exists\_hn\_with\_last\_phase\_of\_semistable}`.

{docstring CategoryTheory.Triangulated.StabilityFunction.exists_hn_with_last_phase_of_semistable_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_hn_with_last_phase_of_semistable_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityFunction.exists_hn_with_last_phase_of_semistable_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cokernelMapMonoIso\_local

Taking cokernels after mapping a subobject inclusion along a monomorphism does not change the resulting quotient object.

Construction: Uses $`\texttt{cokernel.mapIso}` with the two $`\texttt{mapMonoIso}` isomorphisms.


{docstring CategoryTheory.Triangulated.Subobject.cokernelMapMonoIso_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernelMapMonoIso_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.cokernelMapMonoIso_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mapMonoIso\_local

The image of a subobject along a monomorphism is canonically isomorphic to the original subobject (as objects in the ambient category).

Construction: Constructs the isomorphism using $`\texttt{Subobject.isoOfEqMk}` from the identity $`\texttt{map\_eq\_mk\_mono}`.


{docstring CategoryTheory.Triangulated.Subobject.mapMonoIso_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mapMonoIso_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.mapMonoIso_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# map\_eq\_mk\_mono\_local

For a monomorphism $`f : X \to Y` and a subobject $`S \le X`, the image subobject $`f_*(S)` equals $`\operatorname{mk}(S.\mathrm{arrow} \circ f)`.

Proof: Rewrites using $`\texttt{Subobject.mk\_arrow}` and $`\texttt{Subobject.map\_mk}`.

{docstring CategoryTheory.Triangulated.Subobject.map_eq_mk_mono_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20map_eq_mk_mono_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.map_eq_mk_mono_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ofLE\_map\_comp\_mapMonoIso\_hom\_local

The canonical comparison between the image of an inclusion $`S \le T` under a monomorphism $`f` and the image of $`T`, composed with the $`\texttt{mapMonoIso}` isomorphism, equals the composition of $`\texttt{mapMonoIso}(S)` and the original inclusion.

Proof: Checks equality after composing with the arrow of $`T`, using monicity of $`f` and the definition of $`\texttt{mapMonoIso}`.

{docstring CategoryTheory.Triangulated.Subobject.ofLE_map_comp_mapMonoIso_hom_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ofLE_map_comp_mapMonoIso_hom_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Subobject.ofLE_map_comp_mapMonoIso_hom_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isSemistable\_cokernel\_mapMono\_iff\_local

Semistability of the cokernel of a subobject inclusion is preserved under pushing forward by a monomorphism: $`Z.\texttt{IsSemistable}(\operatorname{coker}(f_*(S) \to f_*(T)))` iff $`Z.\texttt{IsSemistable}(\operatorname{coker}(S \to T))`.

Proof: In both directions, uses $`\texttt{cokernelMapMonoIso\_local}` (and its symmetric) to transfer semistability via $`\texttt{isSemistable\_of\_iso}`.

{docstring CategoryTheory.Triangulated.isSemistable_cokernel_mapMono_iff_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isSemistable_cokernel_mapMono_iff_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.isSemistable_cokernel_mapMono_iff_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isSemistable\_cokernel\_ofLE\_congr\_local

Semistability of the cokernel of a subobject inclusion is invariant under propositionally equal subobjects.

Proof: Substitution on the subobject equalities.

{docstring CategoryTheory.Triangulated.isSemistable_cokernel_ofLE_congr_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isSemistable_cokernel_ofLE_congr_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.isSemistable_cokernel_ofLE_congr_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_cokernel\_mapMono\_eq\_local

The stability phase of the cokernel of a subobject inclusion is preserved under pushing forward by a monomorphism.

Proof: Uses $`\texttt{phase\_eq\_of\_iso}` applied to $`\texttt{cokernelMapMonoIso\_local}`.

{docstring CategoryTheory.Triangulated.phase_cokernel_mapMono_eq_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_cokernel_mapMono_eq_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phase_cokernel_mapMono_eq_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_cokernel\_ofLE\_congr\_local

The phase of the cokernel of a subobject inclusion is invariant under propositionally equal subobjects.

Proof: Substitution on the subobject equalities.

{docstring CategoryTheory.Triangulated.phase_cokernel_ofLE_congr_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_cokernel_ofLE_congr_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phase_cokernel_ofLE_congr_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Forward%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
