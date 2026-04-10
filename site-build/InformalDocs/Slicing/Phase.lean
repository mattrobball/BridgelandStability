import BridgelandStability.Slicing.Phase
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Slicing: Phase" =>
%%%
htmlSplit := .never
%%%

# exists\_both\_nonzero

For any nonzero object $`E`, there exists an HN filtration with both a nonzero first factor and a nonzero last factor.

Proof: Start from a filtration with nonzero first factor (from `exists_nonzero_first`). If the last factor is zero, drop it (preserving the nonzero first factor). Iterate until the last factor is also nonzero; termination is guaranteed by the decreasing filtration length.

{docstring CategoryTheory.Triangulated.HNFiltration.exists_both_nonzero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_both_nonzero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.exists_both_nonzero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isZero\_factor\_last\_of\_hom\_eq\_zero

If all morphisms from $`E` to the last HN factor $`A_n` are zero, then $`A_n = 0`. Dual of `isZero_factor_zero_of_hom_eq_zero`.

Proof: Since $`T.\mathrm{mor}_2 = 0` (because it factors through $`E`), the Yoneda exact sequence gives $`\mathrm{id}_{A_n} = T.\mathrm{mor}_3 \circ \gamma` for some $`\gamma : E_1[1] \to A_n`. Hom-vanishing on the shifted prefix filtration shows $`\gamma = 0`, so $`\mathrm{id}_{A_n} = 0` and $`A_n` is zero.

{docstring CategoryTheory.Triangulated.HNFiltration.isZero_factor_last_of_hom_eq_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isZero_factor_last_of_hom_eq_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.isZero_factor_last_of_hom_eq_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# isZero\_factor\_zero\_of\_hom\_eq\_zero

If all morphisms from the first HN factor $`A_1` to $`E` are zero, then $`A_1 = 0`. More precisely, the first triangle's third vertex is a zero object.

Proof: By `chain_hom_eq_zero_of_factor_zero`, all maps from $`A_1` to the chain object $`E_1` are zero. Since $`E_0 = 0`, the first triangle gives $`E_1 \cong A_1`, so the identity $`\mathrm{id}_{A_1} = 0`, whence $`A_1` is zero.

{docstring CategoryTheory.Triangulated.HNFiltration.isZero_factor_zero_of_hom_eq_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20isZero_factor_zero_of_hom_eq_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.isZero_factor_zero_of_hom_eq_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_eq\_of\_nonzero\_last\_factors

For any two HN filtrations of the same nonzero object with nonzero last factors, the lowest phases agree: $`\phi^-(F_1) = \phi^-(F_2)`.

Proof: Antisymmetry from two applications of `phiMinus_ge_of_nonzero_last_factor`.

{docstring CategoryTheory.Triangulated.HNFiltration.phiMinus_eq_of_nonzero_last_factors}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_eq_of_nonzero_last_factors&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.phiMinus_eq_of_nonzero_last_factors%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_ge\_of\_nonzero\_last\_factor

The lowest phase of one HN filtration is bounded below by the lowest phase of any other, provided the second has a nonzero last factor. Dual of `phiPlus_le_of_nonzero_factor`.

Proof: By contradiction: if $`\phi^-(F_1) > \phi^-(F_2)`, then all $`F_1`-phases exceed the last $`F_2`-phase, so $`\operatorname{Hom}(E, A_n^{(2)}) = 0` by `hom_eq_zero_of_lt_phases`, and `isZero_factor_last_of_hom_eq_zero` gives $`A_n^{(2)} = 0`, a contradiction.

{docstring CategoryTheory.Triangulated.HNFiltration.phiMinus_ge_of_nonzero_last_factor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_ge_of_nonzero_last_factor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.phiMinus_ge_of_nonzero_last_factor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_eq\_of\_nonzero\_factors

For any two HN filtrations of the same nonzero object, if both have nonzero first factors, then their highest phases agree: $`\phi^+(F_1) = \phi^+(F_2)`.

Proof: Antisymmetry from two applications of `phiPlus_le_of_nonzero_factor`.

{docstring CategoryTheory.Triangulated.HNFiltration.phiPlus_eq_of_nonzero_factors}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_eq_of_nonzero_factors&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.phiPlus_eq_of_nonzero_factors%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_le\_of\_nonzero\_factor

The highest phase $`\phi^+(F_1)` of one HN filtration cannot exceed $`\phi^+(F_2)` of another, provided $`F_1` has a nonzero first factor.

Proof: By contradiction: if $`\phi^+(F_1) > \phi^+(F_2)`, then all $`F_2`-phases lie below $`\phi_1(F_1)`, so $`\operatorname{Hom}(A_1^{(1)}, E) = 0` by `hom_eq_zero_of_gt_phases`. Then `isZero_factor_zero_of_hom_eq_zero` gives $`A_1^{(1)} = 0`, contradicting the hypothesis.

{docstring CategoryTheory.Triangulated.HNFiltration.phiPlus_le_of_nonzero_factor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_le_of_nonzero_factor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.phiPlus_le_of_nonzero_factor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_HN\_intrinsic\_width

For any nonzero object $`E`, there exists an HN filtration whose extreme phases match the intrinsic $`\phi^+(E)` and $`\phi^-(E)`.

Proof: Take a filtration with both nonzero boundary factors (from `exists_both_nonzero`); then `phiPlus_eq` and `phiMinus_eq` identify the extreme phases.

{docstring CategoryTheory.Triangulated.Slicing.exists_HN_intrinsic_width}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_HN_intrinsic_width&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.exists_HN_intrinsic_width%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# geProp\_of\_phiMinus\_ge

If $`t \le \phi^-(E)`, then $`E \in \mathcal{P}(\ge t)`.

Proof: Take a filtration from `exists_both_nonzero`; its lowest phase equals $`\phi^-(E) \ge t`.

{docstring CategoryTheory.Triangulated.Slicing.geProp_of_phiMinus_ge}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20geProp_of_phiMinus_ge&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.geProp_of_phiMinus_ge%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# geProp\_shift

If $`E \in \mathcal{P}(\ge t)`, then $`E[a] \in \mathcal{P}(\ge t + a)` for any integer shift $`a`.

Proof: Shift the HN filtration by $`a`; the shifted lowest phase becomes $`\phi^- + a \ge t + a`.

{docstring CategoryTheory.Triangulated.Slicing.geProp_shift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20geProp_shift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.geProp_shift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_of\_phiMinus\_gt

If $`t < \phi^-(E)`, then $`E \in \mathcal{P}(> t)`.

Proof: Take a filtration from `exists_both_nonzero`; its lowest phase equals the intrinsic $`\phi^-(E) > t`.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_of_phiMinus_gt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_of_phiMinus_gt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_of_phiMinus_gt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_shift

If $`E \in \mathcal{P}(> t)`, then $`E[a] \in \mathcal{P}(> t + a)` for any integer shift $`a`.

Proof: Shift the HN filtration by $`a` using `shiftHN`; the shifted lowest phase becomes $`\phi^- + a > t + a`.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_shift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_shift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_shift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_intrinsic\_phases

If $`a < \phi^-(E)` and $`\phi^+(E) < b`, then $`E \in \mathcal{P}((a, b))`. Converse of the interval-to-phase-bound lemmas.

Proof: Take a filtration from `exists_both_nonzero` whose extreme phases match the intrinsic values. Then every phase $`\phi_i` satisfies $`a < \phi^- \le \phi_i \le \phi^+ < b`.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_of_intrinsic_phases}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_intrinsic_phases&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_of_intrinsic_phases%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_of\_phiPlus\_le

If $`\phi^+(E) \le t`, then $`E \in \mathcal{P}(\le t)`.

Proof: Take a filtration from `exists_both_nonzero`; its highest phase equals the intrinsic $`\phi^+(E) \le t`.

{docstring CategoryTheory.Triangulated.Slicing.leProp_of_phiPlus_le}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_of_phiPlus_le&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_of_phiPlus_le%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_shift

If $`E \in \mathcal{P}(\le t)`, then $`E[a] \in \mathcal{P}(\le t + a)` for any integer shift $`a`.

Proof: Shift the HN filtration by $`a`; the shifted highest phase becomes $`\phi^+ + a \le t + a`.

{docstring CategoryTheory.Triangulated.Slicing.leProp_shift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_shift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_shift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_of\_phiPlus\_lt

If $`\phi^+(E) < t`, then $`E \in \mathcal{P}(< t)`.

Proof: Take a filtration from `exists_both_nonzero`; its highest phase equals $`\phi^+(E) < t`.

{docstring CategoryTheory.Triangulated.Slicing.ltProp_of_phiPlus_lt}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_of_phiPlus_lt&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ltProp_of_phiPlus_lt%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_shift

If $`E \in \mathcal{P}(< t)`, then $`E[a] \in \mathcal{P}(< t + a)` for any integer shift $`a`.

Proof: Shift the HN filtration by $`a`; the shifted highest phase becomes $`\phi^+ + a < t + a`.

{docstring CategoryTheory.Triangulated.Slicing.ltProp_shift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_shift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ltProp_shift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_le\_phiPlus\_of\_nonzero\_hom

If a semistable object $`A \in \mathcal{P}(\phi)` maps nonzero to $`X`, then $`\phi \le \phi^+(X)`. Contrapositive of `hom_eq_zero_of_gt_phases`.

Proof: By contradiction: if $`\phi > \phi^+(X)`, then all phases of any filtration of $`X` lie below $`\phi`, so `hom_eq_zero_of_gt_phases` kills the morphism.

{docstring CategoryTheory.Triangulated.Slicing.phase_le_phiPlus_of_nonzero_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_le_phiPlus_of_nonzero_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phase_le_phiPlus_of_nonzero_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_eq

The intrinsic $`\phi^-(E)` equals $`\phi_n` of any HN filtration of $`E` with nonzero last factor.

Proof: By `phiMinus_eq_of_nonzero_last_factors`, applied to the chosen representative filtration and the given one.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_ge\_of\_geProp

If $`E \in \mathcal{P}(\ge t)` and $`E` is nonzero, then $`t \le \phi^-(E)`.

Proof: The $`\mathcal{P}(\ge t)` condition gives a filtration with $`\phi^- \ge t`.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_ge_of_geProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_ge_of_geProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_ge_of_geProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_ge\_phiMinus\_of\_hn

The intrinsic $`\phi^-(E)` is bounded below by the lowest phase of any HN filtration of $`E`. Dual of `phiPlus_le_phiPlus_of_hn`.

Proof: By `phiMinus_ge_of_nonzero_last_factor` applied to a filtration with nonzero last factor.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_ge_phiMinus_of_hn}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_ge_phiMinus_of_hn&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_ge_phiMinus_of_hn%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_gt\_of\_gtProp

If $`E \in \mathcal{P}(> t)` and $`E` is nonzero, then $`t < \phi^-(E)`.

Proof: The $`\mathcal{P}(> t)` condition gives a filtration with $`\phi^- > t`; the intrinsic $`\phi^-` is bounded below by this.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_gtProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_gt_of_gtProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_gtProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_gt\_of\_intervalProp

If $`E \in \mathcal{P}((a, b))` and $`E` is nonzero, then $`a < \phi^-(E)`.

Proof: The interval filtration has lowest phase $`> a`; the intrinsic $`\phi^-` is bounded below by this filtration's lowest phase.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_gt_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_le\_phase\_of\_nonzero\_hom

If $`X` maps nonzero to a semistable object $`B \in \mathcal{P}(\psi)`, then $`\phi^-(X) \le \psi`. Contrapositive of `hom_eq_zero_of_lt_phases`.

Proof: By contradiction: if $`\phi^-(X) > \psi`, then all phases of $`X` exceed $`\psi`, so `hom_eq_zero_of_lt_phases` kills the morphism.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_le_phase_of_nonzero_hom}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_le_phase_of_nonzero_hom&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_le_phase_of_nonzero_hom%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_le\_phiPlus

For any nonzero object $`E`, $`\phi^-(E) \le \phi^+(E)`.

Proof: By contradiction: if $`\phi^- > \phi^+`, then all phases of one filtration exceed all phases of another, creating a phase gap. Then $`\operatorname{Hom}(E, E) = 0`, so $`\mathrm{id}_E = 0`, contradicting $`E \ne 0`.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_le_phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_le_phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_le_phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_lt\_of\_intervalProp

If $`E \in \mathcal{P}((a, b))` and $`E` is nonzero, then $`\phi^-(E) < b`.

Proof: Follows from $`\phi^-(E) \le \phi^+(E) < b`.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_lt_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_lt_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_lt_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_eq

The intrinsic $`\phi^+(E)` equals $`\phi_1` of any HN filtration of $`E` with nonzero first factor.

Proof: By `phiPlus_eq_of_nonzero_factors`, applied to the chosen representative filtration and the given one.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_gt\_of\_intervalProp

If $`E \in \mathcal{P}((a, b))` and $`E` is nonzero, then $`a < \phi^+(E)`.

Proof: By contradiction: if $`\phi^+(E) \le a`, then all phases of one filtration are $`\le a` while the interval filtration has all phases $`> a`, creating a phase gap that forces $`\mathrm{id}_E = 0`.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_gt_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_gt_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_gt_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_le\_of\_leProp

If $`E \in \mathcal{P}(\le t)` and $`E` is nonzero, then $`\phi^+(E) \le t`.

Proof: The $`\mathcal{P}(\le t)` condition gives a filtration with $`\phi^+ \le t`; the intrinsic $`\phi^+` is bounded above by this.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_le_of_leProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_le_of_leProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_le_of_leProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_le\_phiPlus\_of\_hn

The intrinsic $`\phi^+(E)` is bounded above by the highest phase of any HN filtration of $`E`.

Proof: By `phiPlus_le_of_nonzero_factor` applied to a filtration with nonzero first factor.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_le_phiPlus_of_hn}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_le_phiPlus_of_hn&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_le_phiPlus_of_hn%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_lt\_of\_intervalProp

If $`E \in \mathcal{P}((a, b))` and $`E` is nonzero, then $`\phi^+(E) < b`.

Proof: The interval property provides a filtration with all phases $`< b`; the intrinsic $`\phi^+` is bounded by the highest phase of this filtration.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_lt_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_lt\_of\_ltProp

If $`E \in \mathcal{P}(< t)` and $`E` is nonzero, then $`\phi^+(E) < t`.

Proof: The $`\mathcal{P}(< t)` condition gives a filtration with $`\phi^+ < t`.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_ltProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_lt_of_ltProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_ltProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# chain\_hom\_eq\_zero\_of\_factor\_zero

If all morphisms from the first semistable factor $`A_1` of an HN filtration to $`E` are zero, then all morphisms from $`A_1` to any chain object $`E_k` are zero.

Proof: Downward induction starting from $`k = n` (where $`E_n \cong E` and the hypothesis applies directly). At each step, the coYoneda exact sequence on the inverse rotation of the $`k`-th triangle, combined with Hom-vanishing on the shifted factor $`A_k[-1]`, extends the vanishing to $`E_k`.

{docstring CategoryTheory.Triangulated.chain_hom_eq_zero_of_factor_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20chain_hom_eq_zero_of_factor_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.chain_hom_eq_zero_of_factor_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Phase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
