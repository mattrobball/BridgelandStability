import BridgelandStability.Slicing.Defs
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Slicing: Defs" =>
%%%
htmlSplit := .never
%%%

# HNFiltration

**\[Definition 3.3\]** axiom (c): HN decomposition data for triangulated categories

A Harder–Narasimhan filtration of an object $`E` in a triangulated category equipped with a slicing $`\mathcal{P}` is a sequence of distinguished triangles $`0 = E_0 \to E_1 \to \cdots \to E_n = E` such that each successive quotient $`A_i = E_i / E_{i-1}` lies in $`\mathcal{P}(\phi_i)` for a strictly decreasing sequence of phases $`\phi_1 > \phi_2 > \cdots > \phi_n`.

Construction: The structure carries the filtration length, the sequence of objects, the phase assignments, the distinguished triangle witnesses, and the strict monotonicity proof on the phases.


{docstring CategoryTheory.Triangulated.HNFiltration}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20HNFiltration&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%203.3%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# dropFirst

Given an HN filtration whose first factor $`A_0 = \mathrm{cone}(E_0 \to E_1)[-1]` is zero, produces a new HN filtration of the same object $`E` with the first factor removed, having $`n-1` factors with phases $`\phi_1 > \cdots > \phi_{n-1}`. The zero first factor forces $`E_1 \cong 0`, so the shortened chain still starts at zero.

Construction: The construction uses the fact that a zero factor forces $`E_1 \cong 0` (via the distinguished triangle), making the new chain (starting at $`E_1`) a valid HN filtration with the same top object $`E`.


{docstring CategoryTheory.Triangulated.HNFiltration.dropFirst}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20dropFirst&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.dropFirst%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# dropLast

Given an HN filtration whose last factor $`A_{n-1}` is zero, produces a new HN filtration of the same object $`E` with the last factor removed, having $`n-1` factors with phases $`\phi_0 > \cdots > \phi_{n-2}`. A zero last factor implies $`E_{n-1} \cong E_n = E` via the distinguished triangle, so the prefix already filtrates $`E`.

Construction: The construction reuses `HNFiltration.prefix` for the first $`n-1` steps and adjusts `top_iso` using the isomorphism $`E_{n-1} \cong E` that results from the zero last factor.


{docstring CategoryTheory.Triangulated.HNFiltration.dropLast}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20dropLast&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.dropLast%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_nonzero\_factor

For any HN filtration of a nonzero object $`E`, at least one semistable factor is nonzero. If all factors were zero, a straightforward induction on the chain would show $`E \cong 0`, a contradiction.

Proof: By induction on the chain length: if every factor $`A_i` is zero then each $`E_i \cong E_{i-1}` (since the triangle $`E_{i-1} \to E_i \to A_i` with $`A_i = 0` gives an isomorphism on the first map), so $`E = E_n \cong E_0 = 0`, contradicting $`E \neq 0`.

{docstring CategoryTheory.Triangulated.HNFiltration.exists_nonzero_factor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_nonzero_factor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.exists_nonzero_factor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_nonzero\_first

For any nonzero object $`E`, there exists an HN filtration whose first factor is nonzero. This is obtained by repeatedly applying `dropFirst` to eliminate zero leading factors; the process terminates since each step strictly decreases the length $`n`, and at least one factor must be nonzero by `exists_nonzero_factor`.

Proof: By well-founded induction on the length $`n`: if the first factor of the current filtration is zero, invoke `dropFirst` (which decreases $`n` by 1) and recurse; otherwise the current filtration witnesses the claim.

{docstring CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_nonzero_first&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_nonzero\_last

For any nonzero object $`E`, there exists an HN filtration whose last factor is nonzero. This is the analogue of `exists_nonzero_first`, obtained by repeatedly applying `dropLast`.

Proof: By well-founded induction on $`n`: if the last factor is zero, apply `dropLast` (decreasing $`n`) and recurse; otherwise stop.

{docstring CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_nonzero_last&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# n\_pos

If $`E` is nonzero then any HN filtration of $`E` has at least one factor, i.e., $`n \geq 1`. If $`n = 0` the empty filtration would give $`E \cong 0`, contradicting the hypothesis.

Proof: If $`n = 0` then `zero_isZero` (applied with the inequality $`n \leq 0`) yields $`E \cong 0`, contradicting $`\neg\mathrm{IsZero}(E)`.

{docstring CategoryTheory.Triangulated.HNFiltration.n_pos}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20n_pos&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.n_pos%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ofIso

Transports an HN filtration of $`E` along an isomorphism $`E \cong E'`, producing an HN filtration of $`E'` with the same length, chain, phases, and semistable factors.

Construction: All fields are copied unchanged from the original filtration; `top_iso` is updated by composing the old isomorphism with $`e : E \xrightarrow{\sim} E'`, and `zero_isZero` is transported along $`e^{-1}`.


{docstring CategoryTheory.Triangulated.HNFiltration.ofIso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ofIso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.ofIso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# HNFiltration.phiMinus

The lowest HN phase $`\phi^-(E) = \phi_{n-1}` extracted from a given filtration, defined as the phase of the last (lowest-phase) semistable factor.

Construction: Defined as $`F.\phi\langle n-1, \cdot\rangle`, the value of the phase function at the last index.


{docstring CategoryTheory.Triangulated.HNFiltration.phiMinus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.phiMinus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# HNFiltration.phiPlus

The highest HN phase $`\phi^+(E) = \phi_0` extracted from a given filtration, defined as the phase of the first (highest-phase) semistable factor.

Construction: Defined as $`F.\phi\langle 0, h\rangle`, the value of the phase function at the first index.


{docstring CategoryTheory.Triangulated.HNFiltration.phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# prefix

Extracts the first $`k` factors of an HN filtration, yielding an HN filtration of the intermediate object $`E_k` with phases $`\phi_0 > \cdots > \phi_{k-1}`.

Construction: The prefix filtration restricts the chain, triangles, and phase data to indices $`0, \ldots, k-1`; `top_iso` is the identity since $`E_k` is by definition the $`k`-th chain object.


{docstring CategoryTheory.Triangulated.HNFiltration.prefix}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20prefix&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.prefix%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# prefix\_φ

The phases of the prefix filtration agree with those of the original: $`(F.\mathrm{prefix}\, k).\phi_j = F.\phi_j` for all $`j < k`.

Proof: This holds by reflexivity from the definition of `prefix`.

{docstring CategoryTheory.Triangulated.HNFiltration.prefix_φ}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20prefix_%CF%86&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.prefix_%CF%86%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shiftHN

Shifts an HN filtration of $`E` by an integer $`a \in \mathbb{Z}`, producing an HN filtration of $`E[a]` with shifted phases $`\phi_i + a`. The semistability of each shifted factor follows from the axiom $`\mathcal{P}(\phi)[a] = \mathcal{P}(\phi + a)`.

Construction: The chain is precomposed with the shift functor $`[a]`; each phase is increased by $`a` (cast to $`\mathbb{R}`); semistability is verified using `Slicing.shift_int`.


{docstring CategoryTheory.Triangulated.HNFiltration.shiftHN}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shiftHN&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.shiftHN%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shiftHN\_phiMinus

Shifting an HN filtration by $`a` increases $`\phi^-` by $`a`: $`(F.\mathrm{shiftHN}\, a).\phi^- = F.\phi^- + a`.

Proof: This holds by `rfl` from the definition of `shiftHN` and `phiMinus`.

{docstring CategoryTheory.Triangulated.HNFiltration.shiftHN_phiMinus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shiftHN_phiMinus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.shiftHN_phiMinus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shiftHN\_phiPlus

Shifting an HN filtration by $`a` increases $`\phi^+` by $`a`: $`(F.\mathrm{shiftHN}\, a).\phi^+ = F.\phi^+ + a`.

Proof: This holds by `rfl` from the definition of `shiftHN` and `phiPlus`.

{docstring CategoryTheory.Triangulated.HNFiltration.shiftHN_phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shiftHN_phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.HNFiltration.shiftHN_phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Slicing

**\[Definition 3.3\]**

A slicing $`\mathcal{P}` of a triangulated category $`\mathcal{T}` assigns to each $`\phi \in \mathbb{R}` a full additive subcategory $`\mathcal{P}(\phi) \subseteq \mathcal{T}` satisfying: (1) $`\mathcal{P}(\phi + 1) = \mathcal{P}(\phi)[1]`, (2) if $`\phi_1 > \phi_2` and $`A_i \in \mathcal{P}(\phi_i)` then $`\operatorname{Hom}(A_1, A_2) = 0`, and (3) every nonzero object admits a Harder–Narasimhan filtration. This is Definition 3.3 of Bridgeland (2007).

Construction: The structure bundles a predicate `mem : ℝ → C → Prop` with proofs of the shift compatibility, Hom-vanishing, and HN existence axioms.


{docstring CategoryTheory.Triangulated.Slicing}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20Slicing&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Definition%203.3%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ext

Two slicings are equal if and only if their underlying phase predicates $`\mathcal{P}` agree.

Proof: All fields of `Slicing` other than `P` are propositions or data determined by `P`, so equality of `P` implies equality of the whole structure by `cases` and `simp`.

{docstring CategoryTheory.Triangulated.Slicing.ext}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ext&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ext%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp

The interval subcategory predicate $`\mathcal{P}((a,b))`: an object $`E` belongs to $`\mathcal{P}((a,b))` if it is zero or admits an HN filtration all of whose phases lie in the open interval $`(a, b)`.

Construction: Defined as the `ObjectProperty` sending $`E` to $`\mathrm{IsZero}(E) \lor \exists F : \mathrm{HNFiltration}, \forall i,\; a < F.\phi_i \wedge F.\phi_i < b`.


{docstring CategoryTheory.Triangulated.Slicing.intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Slicing.phiMinus

The intrinsic lowest phase $`\phi^-(E)` of a nonzero object $`E` with respect to a slicing $`\mathcal{P}`, defined as the phase of the last factor in an HN filtration chosen to have nonzero last factor.

Construction: Defined using `exists_nonzero_last` to choose an HN filtration $`F` with nonzero last factor, then taking $`F.\phi_{n-1}`; well-definedness (independence of the choice) is proved separately.


{docstring CategoryTheory.Triangulated.Slicing.phiMinus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# Slicing.phiPlus

The intrinsic highest phase $`\phi^+(E)` of a nonzero object $`E` with respect to a slicing $`\mathcal{P}`, defined as the phase of the first factor in an HN filtration chosen to have nonzero first factor.

Construction: Defined using `exists_nonzero_first` to choose an HN filtration $`F` with nonzero first factor, then taking $`F.\phi_0`; well-definedness is proved separately.


{docstring CategoryTheory.Triangulated.Slicing.phiPlus}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shift

If $`X \in \mathcal{P}(\phi)` then $`X[1] \in \mathcal{P}(\phi + 1)`; this is the forward direction of the shift axiom.

Proof: Immediate from the `mp` direction of `shift_iff`.

{docstring CategoryTheory.Triangulated.Slicing.shift}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shift&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.shift%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shift\_int

The generalized shift: for any integer $`n`, $`X \in \mathcal{P}(\phi)` if and only if $`X[n] \in \mathcal{P}(\phi + n)`.

Proof: For $`n \geq 0` this follows from iterated application of `shift_nat`/`unshift_nat`; for $`n < 0` one uses `shiftFunctorAdd'` to rewrite the negative shift as a composite and reduces to the positive case.

{docstring CategoryTheory.Triangulated.Slicing.shift_int}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shift_int&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.shift_int%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shift\_inv

If $`X[1] \in \mathcal{P}(\phi + 1)` then $`X \in \mathcal{P}(\phi)`; this is the backward direction of the shift axiom.

Proof: Immediate from the `mpr` direction of `shift_iff`.

{docstring CategoryTheory.Triangulated.Slicing.shift_inv}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shift_inv&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.shift_inv%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# shift\_nat

If $`X \in \mathcal{P}(\phi)` then $`X[n] \in \mathcal{P}(\phi + n)` for any natural number $`n`; obtained by iterating the basic shift axiom.

Proof: By induction on $`n`: the base case $`n = 0` uses the shift-by-zero isomorphism; the inductive step applies `shift_iff` once more and uses `shiftFunctorAdd'` to combine the shifts.

{docstring CategoryTheory.Triangulated.Slicing.shift_nat}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20shift_nat&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.shift_nat%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# unshift\_nat

If $`X[n] \in \mathcal{P}(\phi + n)` for a natural number $`n` then $`X \in \mathcal{P}(\phi)`; the inverse of `shift_nat`.

Proof: By induction on $`n`, using the `mpr` direction of `shift_iff` and `shiftFunctorAdd'` to decompose the shift.

{docstring CategoryTheory.Triangulated.Slicing.unshift_nat}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20unshift_nat&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.unshift_nat%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# zero\_mem'

Any object isomorphic to zero belongs to every phase slice $`\mathcal{P}(\phi)`.

Proof: The zero object lies in $`\mathcal{P}(\phi)` by `Slicing.zero_mem`; any object isomorphic to zero is therefore in $`\mathcal{P}(\phi)` since each slice is closed under isomorphisms.

{docstring CategoryTheory.Triangulated.Slicing.zero_mem'}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20zero_mem%27&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.zero_mem%27%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# instContainsZeroP

Each phase slice $`\mathcal{P}(\phi)` of a slicing contains the zero object, as required by the `ContainsZero` typeclass.

Construction: The witness is $`0 \in \mathcal{C}` together with `isZero_zero` and `Slicing.zero_mem`.


{docstring CategoryTheory.Triangulated.instContainsZeroP}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20instContainsZeroP&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.instContainsZeroP%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
