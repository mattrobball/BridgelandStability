import BridgelandStability.Slicing.TStructure
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Slicing: TStructure" =>
%%%
htmlSplit := .never
%%%

# HNFiltration.phaseShift

Convert an HN filtration with respect to $`\mathcal{P}` into one with respect to the shifted predicate $`\psi \mapsto \mathcal{P}(\psi + t)`, by subtracting $`t` from all phases.

Construction: Preserves the chain, triangles, and semistability data. The new phase assignment is $`\phi_i - t`, and strict antitonicity is preserved since subtracting a constant preserves order.


{docstring CategoryTheory.Triangulated.HNFiltration.phaseShift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.phaseShift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# single

A $`1`-factor HN filtration for a semistable object $`S \in \mathcal{P}(\phi)`: the chain is $`0 \to S` with the unique distinguished triangle $`0 \to S \xrightarrow{\mathrm{id}} S \to 0`.

Construction: Sets $`n = 1`, the chain to the composable arrow $`0 \to S`, the single phase to $`\phi`, and the single triangle to the contractible distinguished triangle on $`S`. Strict antitonicity is vacuous for a singleton.


{docstring CategoryTheory.Triangulated.HNFiltration.single}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20single&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.single%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# unphaseShift

Convert an HN filtration with respect to the shifted slicing $`(\mathcal{P}_t)` back to one with respect to $`\mathcal{P}`, by adding $`t` to all phases. Inverse of `phaseShift`.

Construction: Preserves the chain and triangle data. The new phase assignment is $`\phi_i + t`.


{docstring CategoryTheory.Triangulated.HNFiltration.unphaseShift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20unphaseShift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.unphaseShift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# unphaseShift\_n

The filtration length is preserved by `unphaseShift`.

Proof: By definition (`rfl`).

{docstring CategoryTheory.Triangulated.HNFiltration.unphaseShift_n}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20unphaseShift_n&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.unphaseShift_n%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# unphaseShift\_phiPlus

The highest phase of the unshifted filtration equals the shifted highest phase plus $`t`: $`\phi^+(\mathrm{unphaseShift}(G)) = \phi^+(G) + t`.

Proof: By definition (`rfl`).

{docstring CategoryTheory.Triangulated.HNFiltration.unphaseShift_phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20unphaseShift_phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.unphaseShift_phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# zero

A $`0`-factor HN filtration on a zero object: the chain is the single-vertex composable arrow $`0 \to 0`, with no triangles and no phases.

Construction: Sets $`n = 0`, the chain to the constant $`E`, and all triangle/phase data to vacuous matches. The base and top isomorphisms are both the identity on $`E`.


{docstring CategoryTheory.Triangulated.HNFiltration.zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# gtProp\_of\_semistable

A semistable object $`S \in \mathcal{P}(\phi)` with $`\phi > t` satisfies $`\mathcal{P}(> t)`.

Proof: Use the single-factor filtration; then $`\phi^- = \phi > t`.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_of_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_of_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_of_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_of\_semistable

A semistable object $`S \in \mathcal{P}(\phi)` with $`\phi \le t` satisfies $`\mathcal{P}(\le t)`.

Proof: Use the single-factor filtration; then $`\phi^+ = \phi \le t`.

{docstring CategoryTheory.Triangulated.Slicing.leProp_of_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_of_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_of_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Slicing.phaseShift

The phase-shifted slicing $`\mathcal{P}_t` defined by $`\mathcal{P}_t(\psi) = \mathcal{P}(\psi + t)`. This shifts all phases down by $`t`.

Construction: Constructs a new `Slicing` by composing the predicate with addition by $`t`. Shift compatibility, Hom-vanishing, and HN existence are verified by reducing to the corresponding properties of the original slicing.


{docstring CategoryTheory.Triangulated.Slicing.phaseShift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phaseShift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseShift\_geProp

$`\mathcal{P}_t(\ge u)` coincides with $`\mathcal{P}(\ge u + t)`.

Proof: Generalization of `phaseShift_geProp_zero` with parameter $`u`.

{docstring CategoryTheory.Triangulated.Slicing.phaseShift_geProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift_geProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phaseShift_geProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseShift\_geProp\_zero

$`\mathcal{P}_t(\ge 0)` coincides with $`\mathcal{P}(\ge t)`.

Proof: Both directions convert between shifted and unshifted filtrations.

{docstring CategoryTheory.Triangulated.Slicing.phaseShift_geProp_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift_geProp_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phaseShift_geProp_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseShift\_gtProp

$`\mathcal{P}_t(> u)` coincides with $`\mathcal{P}(> u + t)`.

Proof: Generalization of `phaseShift_gtProp_zero` with parameter $`u`.

{docstring CategoryTheory.Triangulated.Slicing.phaseShift_gtProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift_gtProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phaseShift_gtProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseShift\_gtProp\_zero

$`\mathcal{P}_t(> 0)` coincides with $`\mathcal{P}(> t)`: an object has all shifted phases $`> 0` iff all original phases are $`> t`.

Proof: Both directions convert between HN filtrations with shifted and unshifted phases by adding or subtracting $`t`.

{docstring CategoryTheory.Triangulated.Slicing.phaseShift_gtProp_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift_gtProp_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phaseShift_gtProp_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseShift\_leProp

$`\mathcal{P}_t(\le u)` coincides with $`\mathcal{P}(\le u + t)`.

Proof: Generalization of `phaseShift_leProp_zero` with parameter $`u`.

{docstring CategoryTheory.Triangulated.Slicing.phaseShift_leProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift_leProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phaseShift_leProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseShift\_leProp\_zero

$`\mathcal{P}_t(\le 0)` coincides with $`\mathcal{P}(\le t)`.

Proof: Both directions convert between shifted and unshifted filtrations.

{docstring CategoryTheory.Triangulated.Slicing.phaseShift_leProp_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift_leProp_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phaseShift_leProp_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseShift\_ltProp

$`\mathcal{P}_t(< u)` coincides with $`\mathcal{P}(< u + t)`.

Proof: Generalization of `phaseShift_ltProp_zero` with parameter $`u`.

{docstring CategoryTheory.Triangulated.Slicing.phaseShift_ltProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift_ltProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phaseShift_ltProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phaseShift\_ltProp\_zero

$`\mathcal{P}_t(< 0)` coincides with $`\mathcal{P}(< t)`.

Proof: Both directions convert between shifted and unshifted filtrations.

{docstring CategoryTheory.Triangulated.Slicing.phaseShift_ltProp_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phaseShift_ltProp_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phaseShift_ltProp_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_eq\_phiMinus\_of\_semistable

For a semistable nonzero object $`E \in \mathcal{P}(\phi)`, $`\phi^+(E) = \phi^-(E) = \phi`.

Proof: The single-factor filtration has $`\phi^+ = \phi^- = \phi`, and the uniqueness theorems `phiPlus_eq` and `phiMinus_eq` identify the intrinsic values.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_eq_phiMinus_of_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_eq_phiMinus_of_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_eq_phiMinus_of_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_HN\_all\_eq

If all factors in an HN filtration have the same phase $`\phi`, then $`E` is $`\mathcal{P}(\phi)`-semistable.

Proof: Induction along the chain: at each step, the triangle has first vertex $`\mathcal{P}(\phi)`-semistable (by the inductive hypothesis) and third vertex $`\mathcal{P}(\phi)`-semistable (by hypothesis), so the middle vertex is $`\mathcal{P}(\phi)`-semistable by `semistable_of_triangle`.

{docstring CategoryTheory.Triangulated.Slicing.semistable_of_HN_all_eq}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_HN_all_eq&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.semistable_of_HN_all_eq%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_phiPlus\_eq\_phiMinus

Converse. If $`\phi^+(E) = \phi^-(E)` for a nonzero object $`E`, then $`E` is semistable of phase $`\phi^+(E)`.

Proof: Equal extreme phases combined with strict antitonicity of the phase sequence forces the filtration length $`n = 1`. The single triangle then has a zero first vertex, making $`\mathrm{mor}_2` an isomorphism. Thus $`E` is isomorphic to the unique factor, which is semistable of the claimed phase.

{docstring CategoryTheory.Triangulated.Slicing.semistable_of_phiPlus_eq_phiMinus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_phiPlus_eq_phiMinus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.semistable_of_phiPlus_eq_phiMinus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# semistable\_of\_triangle

Extension-closure of $`\mathcal{P}(\phi)`. If $`A, B \in \mathcal{P}(\phi)` and $`A \to E \to B \to A[1]` is distinguished, then $`E \in \mathcal{P}(\phi)`.

Proof: Uses `phiPlus_lt_of_triangle` and `phiMinus_gt_of_triangle` to pin $`\phi^+(E) = \phi^-(E) = \phi`, then invokes `semistable_of_phiPlus_eq_phiMinus`.

{docstring CategoryTheory.Triangulated.Slicing.semistable_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20semistable_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.semistable_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# zero\_of\_geProp\_ltProp

Any morphism from an object in $`\mathcal{P}(\ge 0)` to an object in $`\mathcal{P}(< 0)` is zero.

Proof: Both objects have HN filtrations with a phase gap (source phases $`\ge 0 >` target phases), so `hom_eq_zero_of_phase_gap` applies.

{docstring CategoryTheory.Triangulated.Slicing.zero_of_geProp_ltProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20zero_of_geProp_ltProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.zero_of_geProp_ltProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# zero\_of\_geProp\_ltProp\_general

For any cutoff $`t \in \mathbb{R}`, any morphism from $`\mathcal{P}(\ge t)` to $`\mathcal{P}(< t)` is zero.

Proof: Reduce to the $`t = 0` case via `phaseShift`: apply `zero_of_geProp_ltProp` to the phase-shifted slicing.

{docstring CategoryTheory.Triangulated.Slicing.zero_of_geProp_ltProp_general}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20zero_of_geProp_ltProp_general&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.zero_of_geProp_ltProp_general%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# zero\_of\_gtProp\_leProp

Any morphism from an object in $`\mathcal{P}(> 0)` to an object in $`\mathcal{P}(\le 0)` is zero.

Proof: Both objects have HN filtrations; the phase ranges create a gap (all source phases $`> 0 \ge` all target phases), so `hom_eq_zero_of_phase_gap` applies.

{docstring CategoryTheory.Triangulated.Slicing.zero_of_gtProp_leProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20zero_of_gtProp_leProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.zero_of_gtProp_leProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# zero\_of\_gtProp\_leProp\_general

For any cutoff $`t \in \mathbb{R}`, any morphism from $`\mathcal{P}(> t)` to $`\mathcal{P}(\le t)` is zero.

Proof: Reduce to the $`t = 0` case via `phaseShift`: apply `zero_of_gtProp_leProp` to the phase-shifted slicing.

{docstring CategoryTheory.Triangulated.Slicing.zero_of_gtProp_leProp_general}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20zero_of_gtProp_leProp_general&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.zero_of_gtProp_leProp_general%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# IsBounded

A t-structure on a triangulated category is bounded if every object $`E` lies between some integer levels: there exist $`a, b \in \mathbb{Z}` with $`E \in \mathcal{D}^{\le a} \cap \mathcal{D}^{\ge b}`.

Construction: A proposition asserting that for every object $`E`, there exist integers $`a, b` such that `t.le a E` and `t.ge b E` both hold.


{docstring CategoryTheory.Triangulated.TStructure.IsBounded}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsBounded&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.IsBounded%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
