import BridgelandStability.HeartEquivalence.Reverse
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "HeartEquivalence: Reverse" =>
%%%
htmlSplit := .never
%%%

# HeartPhase

The phase of a heart object measured by the heart stability function.

Construction: An abbreviation: $`\texttt{StabilityFunction.phase}` applied to $`h.Z` and a heart object $`E`.


{docstring CategoryTheory.Triangulated.HeartPhase}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20HeartPhase&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartPhase%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# HeartSemistable

Semistability in the heart with respect to the heart stability function.

Construction: An abbreviation: $`\texttt{StabilityFunction.IsSemistable}` applied to $`h.Z` and a heart object $`E`.


{docstring CategoryTheory.Triangulated.HeartSemistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20HeartSemistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartSemistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# HeartStabilityData.roundtrip

Proposition 5.3c / right inverse. Forgetting the phase package back to heart data recovers the original input: $`(h.\mathrm{toPhasePackage}).\mathrm{toHeartStabilityData} = h`.

Proof: Definitional equality ($`\texttt{rfl}`).

{docstring CategoryTheory.Triangulated.HeartStabilityData.roundtrip}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20roundtrip&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.roundtrip%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# HeartStabilityData.toPhasePackage

**\[Proposition 5.3\]** reverse: partial, missing central charge construction + HN existence

Proposition 5.3b / reverse direction. Heart stability data determines the ambient phase family $`P(\varphi)` with the isomorphism, shift, and Hom-vanishing axioms.

Construction: Packages $`\texttt{phasePredicate}` together with the proofs $`\texttt{phasePredicate\_closedUnderIso}`, $`\texttt{phasePredicate\_shift\_iff}`, and $`\texttt{phasePredicate\_hom\_zero}`.


{docstring CategoryTheory.Triangulated.HeartStabilityData.toPhasePackage}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toPhasePackage&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HeartStabilityData.toPhasePackage%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Proposition%205.3%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# PhasePackage

A local reverse-direction package: the induced phase family from heart stability data, together with the isomorphism, shift, and Hom-vanishing axioms of a Bridgeland slicing.

Construction: Fields: the heart stability data, the phase predicate $`P : \mathbb{R} \to \texttt{ObjectProperty}\; \mathcal{C}`, closure under isomorphism, zero membership, shift compatibility $`P(\varphi)(X) \Leftrightarrow P(\varphi+1)(X[1])`, and Hom vanishing $`\varphi_2 < \varphi_1 \Rightarrow \operatorname{Hom}(P(\varphi_1), P(\varphi_2)) = 0`.


{docstring CategoryTheory.Triangulated.PhasePackage}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20PhasePackage&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.PhasePackage%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# PhasePackage.toHeartStabilityData

Forget the reverse-direction phase package back to the original heart data.

Construction: Projects the $`\texttt{heartData}` field.


{docstring CategoryTheory.Triangulated.PhasePackage.toHeartStabilityData}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toHeartStabilityData&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.PhasePackage.toHeartStabilityData%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# StabilityCondition.roundtrip

Proposition 5.3c / left inverse. Starting from $`\sigma`, extracting heart data, and reconstructing the phase package agrees with the direct construction: $`(\sigma.\mathrm{toHeartStabilityData}).\mathrm{toPhasePackage} = \sigma.\mathrm{toPhasePackage}`.

Proof: Definitional equality ($`\texttt{rfl}`).

{docstring CategoryTheory.Triangulated.StabilityCondition.roundtrip}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20roundtrip&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.roundtrip%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# stabilityFunctionOnHeart\_hasHN\_local

The heart stability function induced by a stability condition $`\sigma` has the Harder--Narasimhan property: every nonzero heart object admits an HN filtration.

Proof: By strong induction on the length of the slicing HN filtration $`F` of $`E` in $`\mathcal{C}`. If $`F` has a single factor, $`E \in \mathcal{P}(\varphi)` and is already semistable in the heart. Otherwise, split $`F` into the prefix (an object with fewer HN factors) and the last semistable factor. The prefix lies in the heart by the phase bounds, and has an abelian HN filtration by the inductive hypothesis. The last factor is semistable in the heart by $`\texttt{stabilityFunctionOnHeart\_isSemistable\_of\_mem\_P\_phi}`. Appending via $`\texttt{append\_hn\_filtration\_of\_mono}` gives the desired filtration of $`E`.

{docstring CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart_hasHN_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20stabilityFunctionOnHeart_hasHN_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.stabilityFunctionOnHeart_hasHN_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# StabilityCondition.toHeartStabilityData

**\[Proposition 5.3\]** forward: stability condition → heart stability data

Proposition 5.3a / forward direction. Every stability condition $`\sigma` determines heart stability data: the $`t`-structure is $`\sigma.\mathrm{slicing}.\mathrm{toTStructure}`, boundedness follows from the HN filtration axiom, the stability function is $`Z` restricted to the heart, and the HN property comes from $`\texttt{stabilityFunctionOnHeart\_hasHN\_local}`.

Construction: Packages the four fields: $`t`-structure, boundedness proof, restricted stability function, and HN property proof.


{docstring CategoryTheory.Triangulated.StabilityCondition.toHeartStabilityData}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toHeartStabilityData&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.toHeartStabilityData%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Proposition%205.3%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# StabilityCondition.toPhasePackage

The reverse-direction phase package extracted from a stability condition.

Construction: Composes $`\texttt{toHeartStabilityData}` with $`\texttt{toPhasePackage}`.


{docstring CategoryTheory.Triangulated.StabilityCondition.toPhasePackage}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toPhasePackage&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.toPhasePackage%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_shortExact\_triangle

Given a short exact sequence $`0 \to A \to B \to Q \to 0` with $`A, B, Q` in the heart (as objects and morphisms in the ambient category), there exists a distinguished triangle $`A \to B \to Q \to A[1]`.

Proof: Lifts the given data to the heart full subcategory, applies $`\texttt{heartFullSubcategory\_shortExact\_triangle}`, then transports the connecting morphism back to the ambient category.

{docstring CategoryTheory.Triangulated.TStructure.heart_shortExact_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_shortExact_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heart_shortExact_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# arg\_add\_lt\_max\_local

For two complex numbers $`z_1, z_2` in the upper half-plane union with distinct arguments, the argument of their sum is strictly less than the maximum of their arguments.

Proof: Delegates directly to the general $`\texttt{arg\_add\_lt\_max}` lemma.

{docstring CategoryTheory.Triangulated.arg_add_lt_max_local}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20arg_add_lt_max_local&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.arg_add_lt_max_local%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_hom\_zero\_of\_semistable\_phase\_gt

If $`E` and $`F` are heart-semistable with $`\mathrm{phase}(F) < \mathrm{phase}(E)`, then every morphism $`f : E \to F` in the heart is zero.

Proof: Delegates to the general stability-function result $`\texttt{hom\_zero\_of\_semistable\_phase\_gt}` applied to the heart stability function $`h.Z`.

{docstring CategoryTheory.Triangulated.heart_hom_zero_of_semistable_phase_gt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_hom_zero_of_semistable_phase_gt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.heart_hom_zero_of_semistable_phase_gt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_phase\_le\_of\_epi

If $`p : E \to Q` is an epimorphism in the heart with $`E` semistable and $`Q` nonzero, then $`\mathrm{phase}(E) \le \mathrm{phase}(Q)`.

Proof: Delegates to the general result $`\texttt{phase\_le\_of\_epi}` applied to $`h.Z`.

{docstring CategoryTheory.Triangulated.heart_phase_le_of_epi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_phase_le_of_epi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.heart_phase_le_of_epi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseBase

Normalize a real phase $`\varphi` into the standard Bridgeland interval $`(0, 1]`.

Construction: Defined as $`\texttt{toIocMod}` with period $`1` and base point $`0`.


{docstring CategoryTheory.Triangulated.phaseBase}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseBase&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseBase%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseBase\_add\_one

$`\texttt{phaseBase}(\varphi + 1) = \texttt{phaseBase}(\varphi)`.

Proof: Adding the period does not change the mod-representative.

{docstring CategoryTheory.Triangulated.phaseBase_add_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseBase_add_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseBase_add_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseBase\_add\_phaseIndex

$`\texttt{phaseBase}(\varphi) + \texttt{phaseIndex}(\varphi) = \varphi`.

Proof: The defining identity of the floor-mod decomposition.

{docstring CategoryTheory.Triangulated.phaseBase_add_phaseIndex}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseBase_add_phaseIndex&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseBase_add_phaseIndex%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseBase\_eq\_of\_mem\_Ioc

If $`\varphi \in (0, 1]`, then $`\texttt{phaseBase}(\varphi) = \varphi`.

Proof: The mod operation fixes elements already in the fundamental domain.

{docstring CategoryTheory.Triangulated.phaseBase_eq_of_mem_Ioc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseBase_eq_of_mem_Ioc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseBase_eq_of_mem_Ioc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseBase\_mem

$`\texttt{phaseBase}(\varphi) \in (0, 1]` for all $`\varphi \in \mathbb{R}`.

Proof: Immediate from the modular arithmetic property of $`\texttt{toIocMod}`.

{docstring CategoryTheory.Triangulated.phaseBase_mem}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseBase_mem&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseBase_mem%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseIndex

The integral shift needed to move a phase into $`(0, 1]`: $`\varphi = \texttt{phaseBase}(\varphi) + \texttt{phaseIndex}(\varphi)`.

Construction: Defined as $`\texttt{toIocDiv}` with period $`1` and base point $`0`.


{docstring CategoryTheory.Triangulated.phaseIndex}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseIndex&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseIndex%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseIndex\_add\_one

$`\texttt{phaseIndex}(\varphi + 1) = \texttt{phaseIndex}(\varphi) + 1`.

Proof: Adding the period increments the floor by one.

{docstring CategoryTheory.Triangulated.phaseIndex_add_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseIndex_add_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseIndex_add_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseIndex\_eq\_zero\_of\_mem\_Ioc

If $`\varphi \in (0, 1]`, then $`\texttt{phaseIndex}(\varphi) = 0`.

Proof: If $`\varphi` is already in the fundamental domain, no shift is needed.

{docstring CategoryTheory.Triangulated.phaseIndex_eq_zero_of_mem_Ioc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseIndex_eq_zero_of_mem_Ioc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseIndex_eq_zero_of_mem_Ioc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseIndex\_le\_of\_lt

If $`\varphi_2 < \varphi_1`, then $`\texttt{phaseIndex}(\varphi_2) \le \texttt{phaseIndex}(\varphi_1)`.

Proof: If the index were strictly larger, then $`\texttt{phaseIndex}(\varphi_1) + 1 \le \texttt{phaseIndex}(\varphi_2)`, giving $`\varphi_1 \ge \texttt{phaseIndex}(\varphi_1) + 1 > \varphi_2`, a contradiction with $`\texttt{phaseIndex\_lt\_phase}` and $`\texttt{phase\_le\_phaseIndex\_add\_one}`.

{docstring CategoryTheory.Triangulated.phaseIndex_le_of_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseIndex_le_of_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseIndex_le_of_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseIndex\_lt\_phase

$`\texttt{phaseIndex}(\varphi) < \varphi` for all $`\varphi \in \mathbb{R}`.

Proof: Since $`\texttt{phaseBase}(\varphi) > 0` and $`\varphi = \texttt{phaseBase}(\varphi) + \texttt{phaseIndex}(\varphi)`, the strict positivity gives the inequality.

{docstring CategoryTheory.Triangulated.phaseIndex_lt_phase}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseIndex_lt_phase&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phaseIndex_lt_phase%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phasePredicate

The ambient phase predicate attached to heart stability data: normalize the phase into $`(0, 1]`, then shift the object back by the corresponding integer.

Construction: Defined as $`\texttt{shiftedHeartSemistable}(\texttt{phaseBase}(\varphi), \texttt{phaseIndex}(\varphi))`.


{docstring CategoryTheory.Triangulated.phasePredicate}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phasePredicate&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phasePredicate%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phasePredicate\_closedUnderIso

The phase predicate $`P(\varphi)` is closed under isomorphism.

Proof: Follows from $`\texttt{shiftedHeartSemistable\_closedUnderIso}`.

{docstring CategoryTheory.Triangulated.phasePredicate_closedUnderIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phasePredicate_closedUnderIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phasePredicate_closedUnderIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phasePredicate\_hom\_zero

For arbitrary phases $`\varphi_1 > \varphi_2`, every morphism $`f : E \to F` with $`E \in P(\varphi_1)` and $`F \in P(\varphi_2)` is zero.

Proof: If $`\texttt{phaseIndex}(\varphi_2) = \texttt{phaseIndex}(\varphi_1)`, both objects shift to the same heart and the result follows from heart Hom vanishing. Otherwise the index gap forces a nonzero $`t`-amplitude mismatch between the shifted objects, and the morphism vanishes by the $`t`-structure orthogonality $`\texttt{zero\_of\_isLE\_of\_isGE}`.

{docstring CategoryTheory.Triangulated.phasePredicate_hom_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phasePredicate_hom_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phasePredicate_hom_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phasePredicate\_hom\_zero\_of\_mem\_Ioc

For $`\varphi_1, \varphi_2 \in (0, 1]` with $`\varphi_2 < \varphi_1`, every morphism $`f : E \to F` with $`E \in P(\varphi_1)` and $`F \in P(\varphi_2)` is zero.

Proof: Reduces to Hom vanishing between heart-semistable objects of decreasing phase via $`\texttt{heart\_hom\_zero\_of\_semistable\_phase\_gt}`.

{docstring CategoryTheory.Triangulated.phasePredicate_hom_zero_of_mem_Ioc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phasePredicate_hom_zero_of_mem_Ioc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phasePredicate_hom_zero_of_mem_Ioc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phasePredicate\_iff\_of\_mem\_Ioc

For $`\varphi \in (0, 1]`, $`\texttt{phasePredicate}(\varphi, X)` iff $`X` is zero or $`X` lies in the heart with heart-semistable phase $`\varphi`.

Proof: Since $`\texttt{phaseBase}(\varphi) = \varphi` and $`\texttt{phaseIndex}(\varphi) = 0`, the shifted heart condition reduces to the unshifted one.

{docstring CategoryTheory.Triangulated.phasePredicate_iff_of_mem_Ioc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phasePredicate_iff_of_mem_Ioc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phasePredicate_iff_of_mem_Ioc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phasePredicate\_instClosedUnderIso

Instance: $`P(\varphi)` is closed under isomorphism.

Proof: Delegates to $`\texttt{phasePredicate\_closedUnderIso}`.

{docstring CategoryTheory.Triangulated.phasePredicate_instClosedUnderIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phasePredicate_instClosedUnderIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phasePredicate_instClosedUnderIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phasePredicate\_shift\_iff

Shifting by $`[1]` raises the phase by $`1`: $`X \in P(\varphi)` iff $`X[1] \in P(\varphi + 1)`.

Proof: Uses $`\texttt{phaseBase\_add\_one}` and $`\texttt{phaseIndex\_add\_one}` to reduce to $`\texttt{shiftedHeartSemistable\_shift\_iff}`.

{docstring CategoryTheory.Triangulated.phasePredicate_shift_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phasePredicate_shift_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phasePredicate_shift_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phasePredicate\_shift\_int

Shifting by $`[n]` raises the phase by $`n`: $`X \in P(\varphi)` iff $`X[n] \in P(\varphi + n)`.

Proof: Induction on $`n` (positive and negative cases), using $`\texttt{phasePredicate\_shift\_iff}` for each step.

{docstring CategoryTheory.Triangulated.phasePredicate_shift_int}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phasePredicate_shift_int&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phasePredicate_shift_int%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_le\_phaseIndex\_add\_one

$`\varphi \le \texttt{phaseIndex}(\varphi) + 1` for all $`\varphi \in \mathbb{R}`.

Proof: Since $`\texttt{phaseBase}(\varphi) \le 1` and $`\varphi = \texttt{phaseBase}(\varphi) + \texttt{phaseIndex}(\varphi)`, the upper bound on the base gives the inequality.

{docstring CategoryTheory.Triangulated.phase_le_phaseIndex_add_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_le_phaseIndex_add_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phase_le_phaseIndex_add_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shiftedHeartSemistable

Bridgeland's reverse-direction phase slices: objects whose $`[-n]`-shift lies in the heart and is semistable there of phase $`\psi`, together with zero objects.

Construction: An $`\texttt{ObjectProperty}` on $`\mathcal{C}`: $`X` satisfies $`\texttt{shiftedHeartSemistable}(\psi, n)` iff $`X` is zero, or $`X[-n] \in \operatorname{heart}(t)` with heart-semistable phase $`\psi`.


{docstring CategoryTheory.Triangulated.shiftedHeartSemistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shiftedHeartSemistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.shiftedHeartSemistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shiftedHeartSemistable\_closedUnderIso

The shifted heart semistability predicate is closed under isomorphism.

Proof: An isomorphism $`X \cong Y` induces an isomorphism $`X[-n] \cong Y[-n]` in the heart, preserving semistability and phase.

{docstring CategoryTheory.Triangulated.shiftedHeartSemistable_closedUnderIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shiftedHeartSemistable_closedUnderIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.shiftedHeartSemistable_closedUnderIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shiftedHeartSemistable\_shift\_iff

$`X` belongs to $`\texttt{shiftedHeartSemistable}(h, \psi, n)` if and only if $`X[1]` belongs to $`\texttt{shiftedHeartSemistable}(h, \psi, n+1)`.

Proof: Both directions transfer data along the canonical isomorphism $`(X[1])[-(n+1)] \cong X[-n]` given by the shift-addition law, using $`\texttt{prop\_of\_iso}` and $`\texttt{isSemistable\_of\_iso}`.

{docstring CategoryTheory.Triangulated.shiftedHeartSemistable_shift_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shiftedHeartSemistable_shift_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.shiftedHeartSemistable_shift_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shiftedHeartSemistable\_zero\_iff

$`X` belongs to $`\texttt{shiftedHeartSemistable}(h, \psi, 0)` if and only if $`X` is zero or $`X` itself (without any shift) is a heart object that is semistable of phase $`\psi`.

Proof: Both directions transfer the heart-membership and stability data along the canonical isomorphism $`X[0] \cong X` using $`\texttt{prop\_of\_iso}` and $`\texttt{isSemistable\_of\_iso}`.

{docstring CategoryTheory.Triangulated.shiftedHeartSemistable_zero_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shiftedHeartSemistable_zero_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.shiftedHeartSemistable_zero_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.HeartEquivalence.Reverse%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
