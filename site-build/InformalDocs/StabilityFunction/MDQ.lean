import BridgelandStability.StabilityFunction.MDQ
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "StabilityFunction: MDQ" =>
%%%
htmlSplit := .never
%%%

# ofIso

An HN filtration can be transported along an isomorphism $`E \cong E'`.

Construction: Push the chain forward via `Subobject.map(e.hom)` and transfer phases and semistability via `phase_cokernel_mapMono_eq` and `isSemistable_cokernel_mapMono_iff`.


{docstring CategoryTheory.AbelianHNFiltration.ofIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ofIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.AbelianHNFiltration.ofIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsMDQ

A quotient $`q \colon E \twoheadrightarrow B` is a maximally destabilizing quotient (MDQ) if $`q` is epi, $`B` is a nonzero semistable object of minimal phase among all semistable quotients of $`E`, and whenever another semistable quotient $`B'` has the same phase as $`B`, the map $`q'` factors through $`q`.

Construction: The structure carries `Epi q`, non-zeroness and semistability of $`B`, and a universal property: for every epi $`q' \colon E \twoheadrightarrow B'` with $`B'` nonzero semistable, $`\phi(B) \le \phi(B')`, and equality implies factorisation $`q' = q \circ t`.


{docstring CategoryTheory.IsMDQ}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsMDQ&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsMDQ%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# lt\_phase\_of\_kernel\_mdq

Kernel-step inequality (Bridgeland, Proposition 2.4e). If $`q \colon E \twoheadrightarrow B` is an MDQ and $`q_K \colon \ker(q) \twoheadrightarrow B'` is an MDQ of the kernel, then $`\phi(B) < \phi(B')`.

Proof: Let $`K = \ker(q)`, $`K' = \ker(q_K)`, $`T = K'` pushed into $`E`, and $`Q = E/T`. The map $`Q \twoheadrightarrow B` factors through $`q` but $`K \to Q` is nonzero (since $`T \ne K`), so $`\phi(Q) \ne \phi(B)` by the MDQ factorisation property. The MDQ bound gives $`\phi(B) \le \phi(Q)`, and the $`Z`-value decomposition $`Z(Q) = Z(B') + Z(B)` with the arg convexity bound shows $`\phi(Q) \le \max(\phi(B'), \phi(B)) = \phi(B)` would hold if $`\phi(B') \le \phi(B)`, contradicting $`\phi(B) < \phi(Q)`.

{docstring CategoryTheory.IsMDQ.lt_phase_of_kernel_mdq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20lt_phase_of_kernel_mdq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.IsMDQ.lt_phase_of_kernel_mdq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hasHN\_of\_artinian\_noetherian

Proposition 2.4 (Bridgeland, Artinian--Noetherian form). If every object of $`\mathcal{A}` is both Artinian and Noetherian, then any stability function on $`\mathcal{A}` has the HN property.

Proof: Reduce to the subobject case via the canonical isomorphism $`\operatorname{Subobject.mk}(\mathrm{id}_E) \cong E`. The recursive construction uses maximally destabilizing quotients (MDQ): for a non-semistable object, find a destabilizing semistable subobject, pass to the quotient, recurse to get an MDQ there, and pull back. The kernel-step inequality (`IsMDQ.lt_phase_of_kernel_mdq`) ensures the phases decrease, and `append_hn_filtration_of_mono` concatenates the pieces.

{docstring CategoryTheory.StabilityFunction.hasHN_of_artinian_noetherian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hasHN_of_artinian_noetherian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.StabilityFunction.hasHN_of_artinian_noetherian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# append\_hn\_filtration\_of\_mono

Given a monomorphism $`i \colon X \hookrightarrow Y`, an HN filtration $`F` of $`X`, a semistable quotient $`B \cong \operatorname{coker}(i)` with $`\phi(B) < \phi_{n-1}(F)`, one can append $`B` to produce an HN filtration of $`Y`.

Proof: Push the chain of $`F` forward via $`\operatorname{Subobject.map}(i)` and append $`\top`. The last factor is $`B`, and the phase bound ensures strict anti-monotonicity is preserved.

{docstring CategoryTheory.append_hn_filtration_of_mono}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20append_hn_filtration_of_mono&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.append_hn_filtration_of_mono%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# cokernelKernelSubobjectIsoTarget

For an epimorphism $`q \colon E \twoheadrightarrow B`, the quotient $`E / \ker(q)` is canonically isomorphic to $`B`.

Construction: Constructed by composing the cokernel-of-kernel-subobject isomorphism with the coimage--image isomorphism and the image-subobject isomorphism.


{docstring CategoryTheory.cokernelKernelSubobjectIsoTarget}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20cokernelKernelSubobjectIsoTarget&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.cokernelKernelSubobjectIsoTarget%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_hn\_of\_semistable

A semistable object admits an HN filtration.

Proof: Immediate from `exists_hn_with_last_phase_of_semistable`.

{docstring CategoryTheory.exists_hn_of_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_hn_of_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.exists_hn_of_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_hn\_with\_last\_phase\_of\_semistable

A semistable object has an HN filtration whose last (and only) phase equals $`\phi(E)`.

Proof: Construct the trivial single-factor filtration $`\bot < \top` with phase $`\phi(E)`.

{docstring CategoryTheory.exists_hn_with_last_phase_of_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_hn_with_last_phase_of_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.exists_hn_with_last_phase_of_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_mdq\_of\_artinian\_noetherian

Existence of MDQ. Every nonzero Artinian--Noetherian object admits a maximally destabilizing quotient.

Proof: Well-founded induction on the subobject lattice (via `WellFoundedGT`). If $`E` is semistable, the identity is an MDQ. Otherwise, find a destabilizing semistable subobject $`A'`, pass to $`\operatorname{coker}(A')` (which is Artinian--Noetherian by `isArtinianObject_of_epi` and `isNoetherianObject_of_epi`), recurse to get an MDQ there, and pull it back to $`E` via `IsMDQ.comp_of_destabilizing_semistable_subobject`.

{docstring CategoryTheory.exists_mdq_of_artinian_noetherian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_mdq_of_artinian_noetherian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.exists_mdq_of_artinian_noetherian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isSemistable\_cokernel\_mapMono\_iff

Semistability of $`\operatorname{coker}(f_*(S) \hookrightarrow f_*(T))` is equivalent to semistability of $`\operatorname{coker}(S \hookrightarrow T)`, for a mono $`f`.

Proof: Transport via `isSemistable_of_iso` in both directions using `Subobject.cokernelMapMonoIso`.

{docstring CategoryTheory.isSemistable_cokernel_mapMono_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isSemistable_cokernel_mapMono_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.isSemistable_cokernel_mapMono_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_cokernel\_mapMono\_eq

For a monomorphism $`f \colon X \hookrightarrow Y` and subobjects $`S \le T` of $`X`, the phase of $`\operatorname{coker}(f_*(S) \hookrightarrow f_*(T))` equals $`\phi(\operatorname{coker}(S \hookrightarrow T))`.

Proof: The two cokernels are isomorphic via the natural map induced by $`f`.

{docstring CategoryTheory.phase_cokernel_mapMono_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_cokernel_mapMono_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.phase_cokernel_mapMono_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.StabilityFunction.MDQ%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
