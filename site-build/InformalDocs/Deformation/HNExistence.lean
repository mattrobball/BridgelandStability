import BridgelandStability.Deformation.HNExistence
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: HNExistence" =>
%%%
htmlSplit := .never
%%%

# interior\_has\_enveloped\_HN

Lemma 7.7 interior HN (deformedPred version). Derives a `deformedPred`-typed HN filtration from `interior_has_enveloped_HN_ssf` by wrapping each $`\operatorname{ssf}`-semistable factor with the enveloping interval $`(a, b)` as the `deformedPred` witness. Phase bounds are $`(a + \varepsilon, b - \varepsilon)` matching the paper.

Proof: Apply `interior_has_enveloped_HN_ssf` to get an ssf-typed filtration $`G`. Retype each factor: since $`G.\phi(j) \in (a + \varepsilon, b - \varepsilon)`, the interval $`(a, b)` with $`a + \varepsilon \le G.\phi(j) \le b - \varepsilon` witnesses $`\operatorname{deformedPred}`.

{docstring CategoryTheory.Triangulated.interior_has_enveloped_HN}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interior_has_enveloped_HN&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interior_has_enveloped_HN%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HNExistence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# interior\_has\_enveloped\_HN\_ssf

Lemma 7.7 interior HN (ssf version, Bridgeland p.23). Every nonzero object $`E` in the interior $`\mathcal{P}((a + 2\varepsilon, b - 4\varepsilon))` of a thin finite-length interval $`\mathcal{P}((a,b))` admits an HN filtration whose factors are $`\operatorname{ssf}`-semistable in $`\mathcal{P}((a,b))` with phases in $`(a + \varepsilon, b - \varepsilon)`.

Proof: Part A: Apply the $`\varphi^+` reduction recursion (`hn_exists_with_phiPlus_reduction`) to obtain an HN filtration with phases in $`(a+\varepsilon, U)`. Part B: Establish a tight upper bound $`\psi(F_1) < b - 3\varepsilon` on the first (largest-phase) factor by backward induction on the Postnikov chain: $`\varphi^+(\operatorname{chain}(k)) \le \varphi^+(E) < b - 4\varepsilon` combined with phase confinement $`\psi_1 - \varepsilon < \varphi^-(F_1) \le \varphi^+(F_1)` gives $`\psi_1 < b - 3\varepsilon`. Since phases are decreasing, all phases are $`< b - \varepsilon`.

{docstring CategoryTheory.Triangulated.interior_has_enveloped_HN_ssf}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20interior_has_enveloped_HN_ssf&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.interior_has_enveloped_HN_ssf%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HNExistence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# sigmaSemistable\_hasDeformedHN

$`\sigma`-semistable objects have $`Q`-HN filtrations (Bridgeland p.24). For $`E \in \mathcal{P}(\phi)`, embed $`E` in $`\mathcal{P}((\phi - 3\varepsilon, \phi + 5\varepsilon))` and apply `interior_has_enveloped_HN`. The $`Q`-HN phases lie in $`(\phi - 2\varepsilon, \phi + 4\varepsilon)`. Two parameters: $`\varepsilon_0` (local finiteness, $`< 1/10`) and $`\varepsilon` (perturbation, $`\varepsilon < \varepsilon_0`). `ThinFiniteLengthInInterval` is derived from `WideSectorFiniteLength` via `of_wide`.

Proof: Set $`a = \phi - 3\varepsilon`, $`b = \phi + 5\varepsilon`. Derive thin finite length from wide-sector finite length. Embed $`E \in \mathcal{P}(\phi) \subset \mathcal{P}((\phi - \varepsilon, \phi + \varepsilon)) = \mathcal{P}((a + 2\varepsilon, b - 4\varepsilon))`. Apply `interior_has_enveloped_HN` and translate phase bounds.

{docstring CategoryTheory.Triangulated.sigmaSemistable_hasDeformedHN}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20sigmaSemistable_hasDeformedHN&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.sigmaSemistable_hasDeformedHN%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.HNExistence%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
