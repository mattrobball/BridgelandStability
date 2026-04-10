import BridgelandStability.Deformation.BoundaryTriangle
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: BoundaryTriangle" =>
%%%
htmlSplit := .never
%%%

# gtProp\_of\_geProp

If $`E \in \mathcal{P}(\ge b)` and $`a < b`, then $`E \in \mathcal{P}(> a)`.

Proof: Immediate from the definitions: all phases $`\ge b > a`.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_of_geProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_of_geProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_of_geProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_lower\_boundary\_strictShortExact

In a finite-length interval subcategory, lower boundary truncation yields a strict short exact sequence.

Proof: Dual of `exists_upper_boundary_strictShortExact` using the lower boundary triangle.

{docstring CategoryTheory.Triangulated.exists_lower_boundary_strictShortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_lower_boundary_strictShortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_lower_boundary_strictShortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_lower\_boundary\_triangle

Dual of `exists_upper_boundary_triangle`: there exists a distinguished triangle $`X \to Q \to Y` with $`Y \in \mathcal{P}(\le a_1)` and $`X \in \mathcal{P}((a_1, b))`.

Proof: Apply the dual t-structure truncation at $`a_1`.

{docstring CategoryTheory.Triangulated.exists_lower_boundary_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_lower_boundary_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_lower_boundary_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_upper\_boundary\_strictShortExact

In a thin interval subcategory $`\mathcal{P}((a, b_2))` (with $`b_2 - a \le 1`), given $`a < b_1 \le b_2` and $`Q \in \mathcal{P}((a, b_2))`, there exists a strict short exact sequence $`0 \to X_1 \to Q \to X_3 \to 0` in $`\mathcal{P}((a, b_2))` with $`X_1 \in \mathcal{P}(\ge b_1)` and $`X_3 \in \mathcal{P}((a, b_1))`.

Proof: Apply `exists_upper_boundary_triangle` to obtain the distinguished triangle, then use `strictShortExact_of_distTriang` to package it as a strict short exact sequence in the thin interval category.

{docstring CategoryTheory.Triangulated.exists_upper_boundary_strictShortExact}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_upper_boundary_strictShortExact&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_upper_boundary_strictShortExact%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_upper\_boundary\_triangle

Given a slicing, a cutoff $`b_1 > a`, and an object $`Q \in \mathcal{P}((a, b_2))`, there exists a distinguished triangle $`X \to Q \to Y \to X[1]` with $`X \in \mathcal{P}(\ge b_1)` and $`Y \in \mathcal{P}((a, b_1))`. This is the upper boundary truncation.

Proof: Apply the t-structure truncation of the phase-shifted slicing at $`b_1` to separate the high-phase part $`X` from the low-phase part $`Y`. The interval bound on $`Y` follows from the triangle and the phase bounds.

{docstring CategoryTheory.Triangulated.exists_upper_boundary_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_upper_boundary_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.exists_upper_boundary_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_lower\_boundary\_triangle

If $`K \in \mathcal{P}((a_2, b))`, $`X \in \mathcal{P}((a_1, b))`, and $`Y \in \mathcal{P}(\leq a_1)` fit into a distinguished triangle $`X \to K \to Y \to X[1]` with $`a_2 \leq a_1 < b`, then $`Y \in \mathcal{P}((a_2, b))`.

Proof: The upper phase bound for $`Y` comes from $`\phi^+(Y) \leq a_1 < b`. The lower bound $`a_2 < \phi^-(Y)` follows from $`\phi^-(K)` being bounded below (using that $`K \in \mathcal{P}((a_2,b))`) and propagation through the triangle via $`X \in \mathcal{P}(\geq a_1)`.

{docstring CategoryTheory.Triangulated.intervalProp_of_lower_boundary_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_lower_boundary_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalProp_of_lower_boundary_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_upper\_boundary\_triangle

The low-phase vertex $`Y` of an upper boundary triangle lies in $`\mathcal{P}((a, b_1))`.

Proof: The lower phase bound comes from the triangle: $`\phi^-(Y) > a` since $`Q \in \mathcal{P}((a, b_2))` and $`X \in \mathcal{P}(\ge b_1)`. The upper bound $`\phi^+(Y) < b_1` comes from the t-structure truncation.

{docstring CategoryTheory.Triangulated.intervalProp_of_upper_boundary_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_upper_boundary_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalProp_of_upper_boundary_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_wSemistable\_lower\_target

If $`E` is W-semistable of phase $`\psi` in $`\mathcal{P}((a, b))`, then $`E \in \mathcal{P}((\psi - \varepsilon_0, b))`.

Proof: Phase confinement gives $`\phi^-(E) > \psi - \varepsilon_0` and $`\phi^+(E) < b`.

{docstring CategoryTheory.Triangulated.intervalProp_of_wSemistable_lower_target}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_wSemistable_lower_target&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalProp_of_wSemistable_lower_target%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_wSemistable\_upper\_target

If $`E` is W-semistable of phase $`\psi` in $`\mathcal{P}((a, b))` and has $`\sigma`-phases confined by Lemma 7.3, then $`E \in \mathcal{P}((a, \psi + \varepsilon_0))`.

Proof: Phase confinement gives $`\phi^+(E) < \psi + \varepsilon_0` and $`\phi^-(E) > a` (from interval membership), so all HN phases lie in $`(a, \psi + \varepsilon_0)`.

{docstring CategoryTheory.Triangulated.intervalProp_of_wSemistable_upper_target}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_wSemistable_upper_target&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.intervalProp_of_wSemistable_upper_target%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_gt\_of\_geProp\_target

If $`E \in \mathcal{P}((a, b))` is nonzero with $`\sigma`-phases $`\ge \psi + \varepsilon_0`, then the W-phase of $`E` exceeds $`\psi`.

Proof: All HN factors have phase $`\ge \psi + \varepsilon_0`, so perturbation gives W-phase $`> \psi + \varepsilon_0 - \varepsilon_0 = \psi`. Apply the $`K_0` imaginary-part summation and sin/Im conversion.

{docstring CategoryTheory.Triangulated.wPhaseOf_gt_of_geProp_target}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_gt_of_geProp_target&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_gt_of_geProp_target%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_gt\_of\_upper\_boundary\_triangle

The W-phase of the high-phase vertex in an upper boundary triangle exceeds $`\psi`.

Proof: The high-phase vertex has all $`\sigma`-phases $`\ge \psi + \varepsilon_0`, so `wPhaseOf_gt_of_geProp_target` applies.

{docstring CategoryTheory.Triangulated.wPhaseOf_gt_of_upper_boundary_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_gt_of_upper_boundary_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_gt_of_upper_boundary_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_gt\_of\_upper\_source\_boundary\_P\_phi

Given a distinguished triangle $`X \to Q \to Y \to X[1]` with $`Q \in \mathcal{P}((\psi-\varepsilon_0, \phi+\varepsilon_0))`, $`X \in \mathcal{P}(\geq \psi+\varepsilon_0)`, and $`Y \in \mathcal{P}(\phi)`, if $`\phi - \varepsilon_0 < \psi \leq \phi` and $`W` is sufficiently close to $`Z`, then the $`W`-phase of $`X` satisfies $`\psi < \mathrm{wPhaseOf}(W([X]), \tfrac{\psi-\varepsilon_0+\phi+\varepsilon_0}{2})`.

Proof: The $`\mathcal{P}(\phi)`-semistability of $`Y` is used to place $`Y` in the thin interval $`\mathcal{P}((\psi-\varepsilon_0, \psi+\varepsilon_0))`, reducing the statement to `wPhaseOf_gt_of_upper_source_boundary_target`.

{docstring CategoryTheory.Triangulated.wPhaseOf_gt_of_upper_source_boundary_P_phi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_gt_of_upper_source_boundary_P_phi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_gt_of_upper_source_boundary_P_phi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_gt\_of\_upper\_source\_boundary\_target

Given a distinguished triangle $`X \to Q \to Y \to X[1]` with $`Q \in \mathcal{P}((\psi-\varepsilon_0, \phi+\varepsilon_0))`, $`X \in \mathcal{P}(\geq \psi+\varepsilon_0)`, $`Y \in \mathcal{P}((\psi-\varepsilon_0, \psi+\varepsilon_0))`, $`\phi - \varepsilon_0 < \psi \leq \phi`, and $`W` sufficiently close to $`Z`, then $`\psi < \mathrm{wPhaseOf}(W([X]), \tfrac{\psi-\varepsilon_0+\phi+\varepsilon_0}{2})`.

Proof: The interval $`\mathcal{P}((\psi-\varepsilon_0, \phi+\varepsilon_0))` is thin (width $`< 1`), and the boundary triangle places $`X` in that interval with $`\phi^-(X) \geq \psi + \varepsilon_0`, so `wPhaseOf_gt_of_upper_boundary_triangle` applies directly.

{docstring CategoryTheory.Triangulated.wPhaseOf_gt_of_upper_source_boundary_target}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_gt_of_upper_source_boundary_target&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_gt_of_upper_source_boundary_target%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_lt\_of\_leProp\_source

If $`E \in \mathcal{P}((a,b))` is nonzero with $`E \in \mathcal{P}(\leq \psi - \varepsilon_0)`, the interval $`(a,b)` is thin ($`b - a + 2\varepsilon_0 < 1`), $`a + \varepsilon_0 \leq \psi \leq b - \varepsilon_0`, and $`W` is sufficiently close to $`Z`, then $`\mathrm{wPhaseOf}(W([E]), \tfrac{a+b}{2}) < \psi`.

Proof: All HN phases of $`E` are bounded above by $`\psi - \varepsilon_0`. After rotating $`W([E])` by $`e^{-i\pi\psi}` and decomposing via the HN filtration, the imaginary part is shown to be negative using the perturbation bounds on each semistable factor, which forces the $`W`-phase below $`\psi`.

{docstring CategoryTheory.Triangulated.wPhaseOf_lt_of_leProp_source}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_lt_of_leProp_source&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_lt_of_leProp_source%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_lt\_of\_lower\_boundary\_triangle

Given a distinguished triangle $`X \to K \to Y \to X[1]` with $`K \in \mathcal{P}((a_2,b))`, $`X \in \mathcal{P}((a_1,b))`, $`Y \in \mathcal{P}(\leq a_1)` (with $`a_2 \leq a_1 < b`), and $`Y` nonzero, if $`W` is sufficiently close to $`Z` and $`a_1 + \varepsilon_0 \leq \psi \leq b - \varepsilon_0`, then $`\mathrm{wPhaseOf}(W([Y]), \tfrac{a_2+b}{2}) < \psi`.

Proof: First $`Y \in \mathcal{P}((a_2,b))` is established by `intervalProp_of_lower_boundary_triangle`, and then $`Y \in \mathcal{P}(\leq \psi - \varepsilon_0)` is inherited from the $`\mathcal{P}(\leq a_1)` bound; finally `wPhaseOf_lt_of_leProp_source` applies.

{docstring CategoryTheory.Triangulated.wPhaseOf_lt_of_lower_boundary_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_lt_of_lower_boundary_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_lt_of_lower_boundary_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_lt\_of\_lower\_source\_boundary\_P\_phi

Given a distinguished triangle $`X \to K \to Y \to X[1]` with $`K \in \mathcal{P}((\phi-\varepsilon_0, \psi+\varepsilon_0))`, $`X \in \mathcal{P}(\phi)` (the semistable slice), $`Y \in \mathcal{P}(\leq \psi-\varepsilon_0)` nonzero, $`\phi \leq \psi < \phi + \varepsilon_0`, and $`W` sufficiently close to $`Z`, then $`\mathrm{wPhaseOf}(W([Y]), \tfrac{\phi-\varepsilon_0+\psi+\varepsilon_0}{2}) < \psi`.

Proof: The $`\mathcal{P}(\phi)`-semistability of $`X` places $`X` in the thin interval $`\mathcal{P}((\psi-\varepsilon_0, \psi+\varepsilon_0))`, then `wPhaseOf_lt_of_lower_source_boundary_target` applies.

{docstring CategoryTheory.Triangulated.wPhaseOf_lt_of_lower_source_boundary_P_phi}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_lt_of_lower_source_boundary_P_phi&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_lt_of_lower_source_boundary_P_phi%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# wPhaseOf\_lt\_of\_lower\_source\_boundary\_target

Given a distinguished triangle $`X \to K \to Y \to X[1]` with $`K \in \mathcal{P}((\phi-\varepsilon_0, \psi+\varepsilon_0))`, $`X \in \mathcal{P}((\psi-\varepsilon_0, \psi+\varepsilon_0))`, $`Y \in \mathcal{P}(\leq \psi-\varepsilon_0)` nonzero, $`\phi \leq \psi < \phi + \varepsilon_0`, and $`W` sufficiently close to $`Z`, then $`\mathrm{wPhaseOf}(W([Y]), \tfrac{\phi-\varepsilon_0+\psi+\varepsilon_0}{2}) < \psi`.

Proof: The interval $`(\phi-\varepsilon_0, \psi+\varepsilon_0)` is thin by the hypothesis $`\varepsilon_0 < 1/8` and $`\psi < \phi + \varepsilon_0`; then `wPhaseOf_lt_of_lower_boundary_triangle` applies with $`a_1 = \psi - \varepsilon_0`, $`a_2 = \phi - \varepsilon_0`, $`b = \psi + \varepsilon_0`.

{docstring CategoryTheory.Triangulated.wPhaseOf_lt_of_lower_source_boundary_target}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20wPhaseOf_lt_of_lower_source_boundary_target&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.wPhaseOf_lt_of_lower_source_boundary_target%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.BoundaryTriangle%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
