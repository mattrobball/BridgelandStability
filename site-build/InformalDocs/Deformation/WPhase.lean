import BridgelandStability.Deformation.WPhase
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: WPhase" =>
%%%
htmlSplit := .never
%%%

# Semistable

W-semistability. An object $`E` in $`\mathcal{P}((a, b))` is W-semistable of W-phase $`\psi` if: (1) $`E \in \mathcal{P}((a,b))` and $`E \ne 0`, (2) $`W([E]) \ne 0`, (3) $`\operatorname{wPhaseOf}(W([E]), \alpha) = \psi`, and (4) for every distinguished triangle $`K \to E \to Q \to K[1]` with $`K, Q \in \mathcal{P}((a,b))` and $`K \ne 0`, we have $`\operatorname{wPhaseOf}(W([K]), \alpha) \le \psi`.

Construction: A structure bundling the interval membership, nonzero witness, W-nonvanishing, phase equality, and the subobject phase inequality.


{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.Semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20Semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.Semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phase\_mem\_Ioc

The W-phase of a W-semistable object lies in $`(\alpha - 1, \alpha + 1]`.

Proof: Substitute the phase equality into `wPhaseOf_mem_Ioc`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.Semistable.phase_mem_Ioc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phase_mem_Ioc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.Semistable.phase_mem_Ioc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# polar

The W-value of a W-semistable object satisfies the polar decomposition $`W([E]) = \|W([E])\| \cdot e^{i\pi\psi}`.

Proof: Substitute the phase equality into `wPhaseOf_compat`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.Semistable.polar}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20polar&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.Semistable.polar%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wNe

The nonvanishing condition for the deformed central charge: $`\mathrm{wNe}(E)` holds when $`W([E]) \ne 0` in $`\mathbb{C}`. This ensures that the W-phase $`\mathrm{wPhaseOf}(W([E]), \alpha)` is well-defined (for zero input $`\mathrm{wPhaseOf}` returns $`\alpha` by convention, so the phase is only geometrically meaningful when $`W([E]) \ne 0`).

Construction: An abbreviation for $`W(\mathrm{cl}(E)) \ne 0`, where $`\mathrm{cl}(E) \in K_0` is the class of $`E`.


{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.wNe}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wNe&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.wNe%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wNe\_def

Unfolds the definition of `wNe`: `ssf.wNe E` is definitionally equal to the proposition $`W([E]) \ne 0`. This lemma is used to convert between the abstract predicate and the explicit nonvanishing condition.

Proof: This is a `rfl` proof: both sides are definitionally equal by the abbreviation `wNe`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.wNe_def}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wNe_def&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.wNe_def%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhase

The W-phase of an object $`E` with respect to a skewed stability function $`\mathtt{ssf}`, defined as $`\mathrm{wPhaseOf}(W([E]), \alpha)`. This is the unique real number $`\psi \in (\alpha - 1, \alpha + 1]` satisfying $`W([E]) = \|W([E])\| \cdot e^{i\pi\psi}` (when $`W([E]) \ne 0`; otherwise it equals $`\alpha` by convention). The parameter $`\alpha \in (a, b)` is the skewing center of $`\mathtt{ssf}`.

Construction: An abbreviation for $`\mathrm{wPhaseOf}(\mathtt{ssf}.W(\mathrm{cl}(E)),\ \mathtt{ssf}.\alpha)`, the W-phase of the deformed charge $`W([E])` computed relative to the skewing parameter $`\alpha`.


{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhase&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhase\_congr

If two objects $`E` and $`E'` have the same deformed charge, $`W([E]) = W([E'])`, then they have the same W-phase, $`\mathrm{wPhase}(E) = \mathrm{wPhase}(E')`. This is the congruence lemma for the W-phase under equality of charges.

Proof: Immediate from unfolding `wPhase` and rewriting with the hypothesis $`W([E]) = W([E'])`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase_congr}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhase_congr&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase_congr%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhase\_def

The $`W`-phase of $`E` unfolds as $`\mathrm{wPhaseOf}(W([E]), \alpha)`, where $`\alpha` is the reference phase of the skewed stability function.

Proof: This is true by reflexivity (definitional unfolding).

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase_def}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhase_def&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase_def%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhase\_iso

Isomorphic objects have equal $`W`-phases: if $`E \cong E'`, then $`\psi_W(E) = \psi_W(E')`.

Proof: Since the central charge $`W` factors through $`K_0`, an isomorphism $`E \cong E'` implies $`[E] = [E']` in $`K_0`, hence $`W([E]) = W([E'])`, and the $`W`-phases agree by `wPhase_congr`.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase_iso}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhase_iso&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase_iso%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhase\_seesaw

A phase seesaw inequality: if $`W([E_1]) + W([E_2]) = W([E])`, the $`W`-phase of $`E` equals $`\psi`, the $`W`-phase of $`E_1` lies in $`(\psi-1, \psi]`, $`W([E_2]) \neq 0`, and the $`W`-phase of $`E_2` lies in $`(\psi-1, \psi+1)`, then $`\psi \leq \psi_W(E_2)`.

Proof: By contradiction, assume $`\psi_W(E_2) < \psi`. Rotating by $`e^{-i\pi\psi}` and taking imaginary parts, $`\mathrm{Im}(W([E]) \cdot e^{-i\pi\psi}) = 0` (since $`\psi_W(E) = \psi`), $`\mathrm{Im}(W([E_1]) \cdot e^{-i\pi\psi}) \geq 0` (since $`\psi_W(E_1) \leq \psi`), and $`\mathrm{Im}(W([E_2]) \cdot e^{-i\pi\psi}) < 0` (since $`\psi_W(E_2) < \psi`). The additivity $`W([E_1]) + W([E_2]) = W([E])` then yields a sign contradiction.

{docstring CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase_seesaw}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhase_seesaw&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.SkewedStabilityFunction.wPhase_seesaw%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# W\_ne\_zero\_of\_intervalProp

W-nonvanishing for interval objects. If $`\|W - Z\|_\sigma < \cos(\pi(b-a)/2)` and $`E` is nonzero in $`\mathcal{P}((a, b))` with $`b - a < 1`, then $`W([E]) \ne 0`.

Proof: Combine the Z-nonvanishing bound with the sector bound on $`W - Z`: the ratio $`M/\cos(\pi(b-a)/2) < 1`, so $`\|(W-Z)(E)\| < \|Z(E)\|`, and if $`W(E) = 0` we get $`\|Z(E)\| \le \|(W-Z)(E)\|`, a contradiction.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.W_ne_zero_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20W_ne_zero_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.W_ne_zero_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# W\_ne\_zero\_of\_seminorm\_lt\_one

W-nonvanishing. If the seminorm $`\|W - Z\|_\sigma < 1`, then $`W([E]) \ne 0` for every nonzero $`\sigma`-semistable object $`E`.

Proof: By the triangle inequality, $`\|W([E])\| \ge \|Z([E])\| - \|(W-Z)([E])\| \ge (1 - M)\|Z([E])\| > 0` where $`M = \|W - Z\|_\sigma < 1` and $`\|Z([E])\| > 0` from compatibility.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.W_ne_zero_of_seminorm_lt_one}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20W_ne_zero_of_seminorm_lt_one&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.W_ne_zero_of_seminorm_lt_one%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# norm\_Z\_pos\_of\_intervalProp

Z-nonvanishing for interval objects. For a nonzero object $`E \in \mathcal{P}((a, b))` with $`b - a < 1`, the central charge satisfies $`\|Z([E])\| > 0`.

Proof: Decompose $`E` via its HN filtration and apply the sector estimate: $`\cos(\pi(b-a)/2) \cdot \sum \|Z(F_j)\| \le \|Z(E)\|`. Since $`b - a < 1`, the cosine is positive, and at least one factor has $`\|Z(F_j)\| > 0`.

{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.norm_Z_pos_of_intervalProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20norm_Z_pos_of_intervalProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.norm_Z_pos_of_intervalProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# skewedStabilityFunction\_of\_near

Node 7.2a. Given a stability condition $`\sigma` and a group homomorphism $`W` with $`\|W - Z\|_\sigma < 1`, $`W` restricts to a skewed stability function on any interval $`(a, b)` with skewing parameter $`\alpha = (a+b)/2`.

Construction: Constructs a `SkewedStabilityFunction` by setting $`\alpha = (a+b)/2` and using `W_ne_zero_of_seminorm_lt_one` for the nonvanishing condition.


{docstring CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedStabilityFunction_of_near}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20skewedStabilityFunction_of_near&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedStabilityFunction_of_near%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf

The W-phase of a complex number $`w \ne 0` relative to a skewing parameter $`\alpha`. Defined as $`\alpha + \arg(w \cdot e^{-i\pi\alpha}) / \pi`, giving $`\psi \in (\alpha - 1, \alpha + 1]` satisfying $`w = \|w\| \cdot e^{i\pi\psi}`.

Construction: Computed by rotating $`w` by $`e^{-i\pi\alpha}` to center the branch cut, taking the standard argument in $`(-\pi, \pi]`, then rescaling by $`1/\pi` and shifting by $`\alpha`.


{docstring CategoryTheory.Triangulated.wPhaseOf}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_add\_two

Shifting $`\alpha` by 2 shifts wPhaseOf by 2. For nonzero $`w`, $`\operatorname{wPhaseOf}(w, \alpha + 2) = \operatorname{wPhaseOf}(w, \alpha) + 2`.

Proof: Apply `wPhaseOf_neg` twice: once for $`w \mapsto -w` and once for $`-w \mapsto w`.

{docstring CategoryTheory.Triangulated.wPhaseOf_add_two}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_add_two&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_add_two%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_compat

Polar compatibility. A nonzero complex number $`w` equals $`\|w\| \cdot e^{i\pi \cdot \operatorname{wPhaseOf}(w, \alpha)}`.

Proof: Factor $`w = z \cdot e^{i\pi\alpha}` where $`z = w \cdot e^{-i\pi\alpha}`. Apply the standard polar decomposition $`z = \|z\| \cdot e^{i \arg(z)}`, note $`\|z\| = \|w\|`, and reassemble using $`\arg(z) + \pi\alpha = \pi \cdot \operatorname{wPhaseOf}(w, \alpha)`.

{docstring CategoryTheory.Triangulated.wPhaseOf_compat}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_compat&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_compat%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_indep

$`\alpha`-independence of wPhaseOf. For nonzero $`w`, if $`\operatorname{wPhaseOf}(w, \alpha_1) \in (\alpha_2 - 1, \alpha_2 + 1]`, then $`\operatorname{wPhaseOf}(w, \alpha_1) = \operatorname{wPhaseOf}(w, \alpha_2)`. This shows the W-phase is intrinsic, provided the branch cuts are compatible.

Proof: Write $`w = \|w\| \cdot e^{i\pi\phi}` where $`\phi = \operatorname{wPhaseOf}(w, \alpha_1)`. Since $`\phi \in (\alpha_2 - 1, \alpha_2 + 1]`, apply `wPhaseOf_of_exp` with parameter $`\alpha_2` to get $`\operatorname{wPhaseOf}(w, \alpha_2) = \phi`.

{docstring CategoryTheory.Triangulated.wPhaseOf_indep}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_indep&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_indep%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_mem\_Ioc

The W-phase lies in the half-open interval $`(\alpha - 1, \alpha + 1]`.

Proof: Immediate from $`\arg(z) \in (-\pi, \pi]` after dividing by $`\pi` and adding $`\alpha`.

{docstring CategoryTheory.Triangulated.wPhaseOf_mem_Ioc}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_mem_Ioc&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_mem_Ioc%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_neg

Negation shifts W-phase by 1. For nonzero $`w`, $`\operatorname{wPhaseOf}(-w, \alpha + 1) = \operatorname{wPhaseOf}(w, \alpha) + 1`. Since $`e^{i\pi} = -1`, negating $`w` shifts the argument by $`\pi`, hence the phase by $`1`.

Proof: Write $`-w = \|w\| \cdot e^{i\pi(\phi + 1)}` where $`\phi = \operatorname{wPhaseOf}(w, \alpha)`. Since $`\phi + 1 \in (\alpha, \alpha + 2] = ((\alpha+1) - 1, (\alpha+1) + 1]`, apply `wPhaseOf_of_exp` to get $`\operatorname{wPhaseOf}(-w, \alpha + 1) = \phi + 1`.

{docstring CategoryTheory.Triangulated.wPhaseOf_neg}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_neg&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_neg%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_of\_exp

The W-phase of $`m \cdot e^{i\pi\phi}` with $`m > 0` and $`\phi \in (\alpha - 1, \alpha + 1]` equals $`\phi`.

Proof: After rotation by $`e^{-i\pi\alpha}`, the argument of $`m \cdot e^{i\pi(\phi - \alpha)}` is $`\pi(\phi - \alpha) \in (-\pi, \pi]`, so dividing by $`\pi` and adding $`\alpha` recovers $`\phi`.

{docstring CategoryTheory.Triangulated.wPhaseOf_of_exp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_of_exp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_of_exp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_zero

The W-phase of zero is $`\alpha`, since $`\arg(0) = 0`.

Proof: Direct computation: $`\arg(0) = 0`, so $`\alpha + 0/\pi = \alpha`.

{docstring CategoryTheory.Triangulated.wPhaseOf_zero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_zero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_zero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.WPhase%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
