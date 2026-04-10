import BridgelandStability.Deformation.DeformedSlicingHN
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: DeformedSlicingHN" =>
%%%
htmlSplit := .never
%%%

# deformedGtPred\_shift\_one

$`Q(>t)[1] \subseteq Q(>t+1)`: the forward shift sends $`Q(>t)`-objects to $`Q(>t+1)`.

Proof: Induction on the extension closure defining $`Q(>t)`: zero objects shift to zero, semistable objects shift by `deformedPred_shift_one`, and extensions shift by shifting the distinguished triangle.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtPred_shift_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedGtPred_shift_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtPred_shift_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedLePred\_shift\_neg\_one

$`Q(\le t)[-1] \subseteq Q(\le t-1)`: the backward shift sends $`Q(\le t)`-objects to $`Q(\le t-1)`.

Proof: For semistable objects, use `deformedPred_of_shift_one` applied to $`Y = E[-1]` with $`Y[1] \cong E`. For extensions, shift the triangle by $`-1`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_shift_neg_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedLePred_shift_neg_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_shift_neg_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedLePred\_shift\_one

$`Q(\le t)[1] \subseteq Q(\le t+1)`: the forward shift sends $`Q(\le t)`-objects to $`Q(\le t+1)`.

Proof: Same induction as `deformedGtPred_shift_one`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_shift_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedLePred_shift_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_shift_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedGtPred\_of\_triangle\_obj₃

Third-vertex closure for $`Q(>t)`: if $`X \to S \to Y` is distinguished with $`X, S \in Q(>t)`, then $`Y \in Q(>t)`.

Proof: Rotate the triangle: $`S \to Y \to X[1]` is distinguished. Since $`X[1] \in Q(>t+1) \subseteq Q(>t)`, the extension closure gives $`Y \in Q(>t)`.

{docstring CategoryTheory.Triangulated.deformedGtPred_of_triangle_obj₃}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedGtPred_of_triangle_obj%E2%82%83&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.deformedGtPred_of_triangle_obj%E2%82%83%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedLePred\_of\_triangle\_obj₁

First-vertex closure for $`Q(\le t)`: if $`X \to R_0 \to R_1` is distinguished with $`R_0, R_1 \in Q(\le t)`, then $`X \in Q(\le t)`.

Proof: Inverse-rotate: $`R_1[-1] \to X \to R_0` is distinguished. Since $`R_1[-1] \in Q(\le t-1) \subseteq Q(\le t)`, extension closure gives $`X \in Q(\le t)`.

{docstring CategoryTheory.Triangulated.deformedLePred_of_triangle_obj₁}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedLePred_of_triangle_obj%E2%82%81&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.deformedLePred_of_triangle_obj%E2%82%81%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedPred\_of\_shift\_one

Backward shift for $`Q`. If $`E[1]` is Q-semistable of phase $`\phi + 1`, then $`E` is Q-semistable of phase $`\phi`.

Proof: Reverse the shift transport: shift the interval by $`-1`, invert the W-phase shift, and transfer semistability by shifting triangles by $`-1`.

{docstring CategoryTheory.Triangulated.deformedPred_of_shift_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedPred_of_shift_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.deformedPred_of_shift_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedPred\_shift\_one

Forward shift for $`Q`. If $`E` is Q-semistable of phase $`\phi`, then $`E[1]` is Q-semistable of phase $`\phi + 1`.

Proof: Transport the deformed predicate through the shift: the interval shifts by $`+1`, the W-phase shifts by $`+1` (via `wPhaseOf_neg` and negation $`W(E[1]) = -W(E)`), and semistability transfers by shifting all triangles.

{docstring CategoryTheory.Triangulated.deformedPred_shift_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedPred_shift_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.deformedPred_shift_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# deformedSlicing\_hn\_exists

Q-HN existence (Bridgeland p.24, Steps 1+2). Every object admits a Q-HN filtration.

Proof: For zero objects, use the trivial filtration. For nonzero $`E`, decompose via the $`\sigma`-HN filtration. Each $`\sigma`-factor admits a Q-HN via `sigmaSemistable_hasDeformedHN`. Combine `deformedGtLe_triangle` (Step 2: $`Q(>t)/Q(\le t)` truncation) with `exists_hn_of_deformedGt_deformedLe_triangle` (Step 1: recursive refinement of truncation triangles into a full HN filtration).

{docstring CategoryTheory.Triangulated.deformedSlicing_hn_exists}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20deformedSlicing_hn_exists&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.deformedSlicing_hn_exists%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isZero\_deformedGt\_of\_deformedLe\_triangle

Dual: if $`S \in Q(\le t)` and distinguished triangle $`X \to S \to Y` with $`X \in Q(>t)` and $`Y \in Q(\le t)`, then $`X = 0`.

Proof: First-vertex closure gives $`X \in Q(\le t)`. Combined with $`X \in Q(>t)`, apply `isZero_of_deformedGtPred_deformedLePred`.

{docstring CategoryTheory.Triangulated.isZero_deformedGt_of_deformedLe_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isZero_deformedGt_of_deformedLe_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.isZero_deformedGt_of_deformedLe_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isZero\_deformedLe\_of\_deformedGt\_triangle

If $`S \in Q(>t)` and distinguished triangle $`X \to S \to Y` with $`X \in Q(>t)` and $`Y \in Q(\le t)`, then $`Y = 0`.

Proof: Third-vertex closure gives $`Y \in Q(>t)`. Combined with $`Y \in Q(\le t)`, apply `isZero_of_deformedGtPred_deformedLePred`.

{docstring CategoryTheory.Triangulated.isZero_deformedLe_of_deformedGt_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isZero_deformedLe_of_deformedGt_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.isZero_deformedLe_of_deformedGt_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isZero\_of\_deformedGtPred\_deformedLePred

If $`X \in Q(>t) \cap Q(\le t)`, then $`X = 0`.

Proof: The identity $`\operatorname{id}_X : X \to X` is a morphism from a $`Q(>t)`-object to a $`Q(\le t)`-object, which is zero by hom-vanishing.

{docstring CategoryTheory.Triangulated.isZero_of_deformedGtPred_deformedLePred}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isZero_of_deformedGtPred_deformedLePred&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.isZero_of_deformedGtPred_deformedLePred%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.DeformedSlicingHN%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
