import BridgelandStability.Deformation.IntervalAbelian
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: IntervalAbelian" =>
%%%
htmlSplit := .never
%%%

# P\_phi\_of\_heart\_triangle

If a distinguished triangle $`K \to E \to Q` has $`E \in \mathcal{P}(\phi)` and $`K, Q` in the heart $`\mathcal{P}((\phi - 1, \phi])`, then $`K, Q \in \mathcal{P}(\phi)`.

Proof: From $`Z(E) = Z(K) + Z(Q)` and $`\operatorname{Im}(Z(E) \cdot e^{-i\pi\phi}) = 0` (since $`E \in \mathcal{P}(\phi)`), combined with $`\operatorname{Im}(Z(K) \cdot e^{-i\pi\phi}) \le 0` and $`\operatorname{Im}(Z(Q) \cdot e^{-i\pi\phi}) \le 0`, both imaginary parts must be zero. Apply `P_phi_of_im_zero_heart`.

{docstring CategoryTheory.Triangulated.P_phi_of_heart_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_of_heart_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.P_phi_of_heart_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_of\_im\_zero\_above

If $`X` is a nonzero object with all $`\sigma`-phases in $`[\phi, \phi+1)` and $`\mathrm{Im}(Z([X]) \cdot e^{-i\pi\phi}) = 0`, then $`X \in \mathcal{P}(\phi)`.

Proof: Decompose $`X` via its HN filtration; each factor $`F_i` has phase $`\phi_i \in [\phi, \phi+1)`, so $`Z([F_i]) = m_i e^{i\pi\phi_i}` and the imaginary part contribution $`m_i \sin(\pi(\phi_i - \phi)) \geq 0`. Since the sum of nonneg terms vanishes, each is zero, forcing $`\sin(\pi(\phi_i - \phi)) = 0`, i.e., $`\phi_i = \phi`.

{docstring CategoryTheory.Triangulated.P_phi_of_im_zero_above}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_of_im_zero_above&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.P_phi_of_im_zero_above%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_of\_im\_zero\_heart

From $`\operatorname{Im} = 0` to $`\mathcal{P}(\phi)`. If $`X` is nonzero with all $`\sigma`-phases in $`(\phi - 1, \phi]` and $`\operatorname{Im}(Z(X) \cdot e^{-i\pi\phi}) = 0`, then $`X \in \mathcal{P}(\phi)`.

Proof: Each HN factor contributes $`\le 0` to the imaginary sum, and the total is $`0`, so each contribution is $`0`. For nonzero factors, $`\sin(\pi(\psi - \phi)) = 0` with $`\psi \in (\phi - 1, \phi]` forces $`\psi = \phi`. Strict antitone of HN phases forces exactly one factor.

{docstring CategoryTheory.Triangulated.P_phi_of_im_zero_heart}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_of_im_zero_heart&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.P_phi_of_im_zero_heart%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_of\_truncation\_of\_P\_phi\_cone

Given a distinguished triangle $`A \to B \to X_3 \to A[1]` with $`A, B \in \mathcal{P}(\phi)`, both t-structure truncations of $`X_3` (with respect to the heart $`\mathcal{P}((\phi-1,\phi])`) lie in $`\mathcal{P}(\phi)`.

Proof: From $`A, B \in \mathcal{P}(\phi)` one gets $`\mathrm{Im}(Z([X_3]) \cdot e^{-i\pi\phi}) = 0` by $`K_0`-additivity. The truncation triangle decomposes this into the heart piece $`Q` (with $`\mathrm{Im} \leq 0`) and the co-heart piece $`L` shifted (with $`\mathrm{Im} \geq 0`); since they sum to zero, both imaginary parts vanish, and `P_phi_of_im_zero_heart` resp. `P_phi_of_im_zero_above` promote each to $`\mathcal{P}(\phi)`.

{docstring CategoryTheory.Triangulated.P_phi_of_truncation_of_P_phi_cone}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_of_truncation_of_P_phi_cone&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.P_phi_of_truncation_of_P_phi_cone%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_hasFiniteProducts

For any stability condition $`\sigma` and phase $`\phi \in \mathbb{R}`, the full subcategory $`\mathcal{P}(\phi)` has finite products.

Construction: Constructs the `HasFiniteProducts` instance on $`\mathcal{P}(\phi)` from the existing binary products and terminal object instances, via `hasFiniteProducts_of_has_binary_and_terminal`.


{docstring CategoryTheory.Triangulated.StabilityCondition.P_phi_hasFiniteProducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_hasFiniteProducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.P_phi_hasFiniteProducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_abelian

**\[Lemma 5.2\]**

Bridgeland's Lemma 5.2. Each $`\mathcal{P}(\phi)` is an abelian category.

Construction: Defined as the abelian subcategory structure obtained from $`\mathcal{P}(\phi)` being admissible in the abelian heart $`\mathcal{P}((\phi - 1, \phi])`.


{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_abelian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_abelian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_abelian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Lemma%205.2%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_admissible

$`\mathcal{P}(\phi)` is admissible in the heart $`\mathcal{P}((\phi - 1, \phi])`: it is closed under subobjects, quotients, and extensions in the heart.

Proof: For subobjects/quotients: a short exact sequence $`0 \to K \to E \to Q \to 0` in the heart with $`E \in \mathcal{P}(\phi)` gives $`Z(E) = Z(K) + Z(Q)`. The imaginary-part argument forces both $`K, Q \in \mathcal{P}(\phi)`. Extension closure is similar.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_admissible}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_admissible&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_admissible%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_biprod

$`\mathcal{P}(\phi)` is closed under binary biproducts.

Proof: The biproduct triangle is distinguished; both factors in $`\mathcal{P}(\phi)` means the biproduct has all phases equal to $`\phi`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_biprod}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_biprod&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_biprod%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_closedUnderBinaryProducts

$`\mathcal{P}(\phi)` is closed under binary products.

Proof: Follows from closure under biproducts.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_closedUnderBinaryProducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_closedUnderBinaryProducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_closedUnderBinaryProducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_closedUnderFiniteProducts

$`\mathcal{P}(\phi)` is closed under finite products.

Proof: Induction from binary products and the zero object.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_closedUnderFiniteProducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_closedUnderFiniteProducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_closedUnderFiniteProducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# P\_phi\_hom\_vanishing

Negative-degree Hom vanishing in $`\mathcal{P}(\varphi)`. For $`X, Y \in \mathcal{P}(\varphi)` and $`n < 0`, every morphism $`\iota(X) \to \iota(Y)\llbracket n \rrbracket` is zero.

Proof: The shift axiom gives $`Y\llbracket n \rrbracket \in \mathcal{P}(\varphi + n)`. Since $`n < 0`, we have $`\varphi > \varphi + n`, so the slicing's Hom-vanishing axiom applies directly.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_hom_vanishing}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20P_phi_hom_vanishing&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_phi_hom_vanishing%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_Z\_nonneg\_of\_phases\_above

If $`E` is a nonzero object with all $`\sigma`-phases in $`[\phi, \phi+1)`, then $`\mathrm{Im}(Z([E]) \cdot e^{-i\pi\phi}) \geq 0`.

Proof: Decompose $`E` via its HN filtration with phases $`\phi_i \in [\phi, \phi+1)`; write $`Z([F_i]) = m_i e^{i\pi\phi_i}` with $`m_i > 0`. Each summand contributes $`m_i \sin(\pi(\phi_i - \phi)) \geq 0` since $`\phi_i - \phi \in [0,1)`, so the sum is nonneg.

{docstring CategoryTheory.Triangulated.im_Z_nonneg_of_phases_above}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_Z_nonneg_of_phases_above&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_Z_nonneg_of_phases_above%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# im\_Z\_nonpos\_of\_heart\_phases

Im non-positivity for heart objects. If $`E` is nonzero with $`\phi^+(E) \le \phi` and $`\phi^-(E) > \phi - 1` (so all HN phases lie in $`(\phi - 1, \phi]`), then $`\operatorname{Im}(Z(E) \cdot e^{-i\pi\phi}) \le 0`.

Proof: Decompose $`Z(E) = \sum Z(F_j)` via $`K_0`. Each factor $`F_j` has $`Z(F_j) = m_j e^{i\pi\phi_j}` with $`\phi_j \in (\phi - 1, \phi]`, so $`\operatorname{Im}(Z(F_j) \cdot e^{-i\pi\phi}) = m_j \sin(\pi(\phi_j - \phi)) \le 0` since $`\sin \le 0` on $`(-\pi, 0]`.

{docstring CategoryTheory.Triangulated.im_Z_nonpos_of_heart_phases}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20im_Z_nonpos_of_heart_phases&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.im_Z_nonpos_of_heart_phases%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.IntervalAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
