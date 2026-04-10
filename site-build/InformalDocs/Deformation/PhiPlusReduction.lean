import BridgelandStability.Deformation.PhiPlusReduction
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Deformation: PhiPlusReduction" =>
%%%
htmlSplit := .never
%%%

# comp\_of\_destabilizing\_with\_quotient\_bound

MDQ composition with quotient-bound Hom vanishing (Bridgeland p.23). Same as `comp_of_destabilizing_semistable_subobject` but replaces the universal `hHom` with a quotient lower bound: all $`W`-semistable strict quotients of $`X` have $`\psi > t_{\mathrm{lo}}`. Combined with $`\psi(A) < U_{\mathrm{hom}}`, both objects are in $`[a + \varepsilon, b - \varepsilon]`, enabling `hom_eq_zero_of_deformedPred`.

Proof: For a competitor $`q' : X \to B'` with $`\psi(B') \le \psi(B)`: the quotient lower bound gives $`\psi(B') \ge a + \varepsilon`, the destabilizing subobject has $`\psi(A) < b - \varepsilon`, and the phase gap $`\psi(B') < \psi(A)` enables `hom_eq_zero_of_enveloped_semistable` to show $`A \to B' = 0`. Hence $`q'` factors through $`\operatorname{coker}(A)`, reducing to the MDQ minimality on the cokernel.

{docstring CategoryTheory.Triangulated.comp_of_destabilizing_with_quotient_bound}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20comp_of_destabilizing_with_quotient_bound&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.comp_of_destabilizing_with_quotient_bound%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhiPlusReduction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# hom\_eq\_zero\_of\_enveloped\_semistable

Hom vanishing for two $`\operatorname{ssf}`-semistable objects whose $`W`-phases are both in $`[a + \varepsilon, b - \varepsilon]`. Converts both to `deformedPred` using $`(a, b)` as the witness interval, then applies `hom_eq_zero_of_deformedPred`. This is the localized version of `hHom` that avoids the universal quantifier problem.

Proof: Both objects are semistable with phases in $`[a + \varepsilon, b - \varepsilon]`, so each is a `deformedPred` object witnessed by $`(a, b)`. Apply the sharp Hom vanishing `hom_eq_zero_of_deformedPred` (Lemma 7.6, sorry-free).

{docstring CategoryTheory.Triangulated.hom_eq_zero_of_enveloped_semistable}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20hom_eq_zero_of_enveloped_semistable&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.hom_eq_zero_of_enveloped_semistable%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhiPlusReduction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# mdq\_of\_sigma\_phase\_split

MDQ lifting through $`\sigma`-phase split (Bridgeland p.23). Given a strict SES $`0 \to X_{\mathrm{hi}} \to E \to E_{\mathrm{lo}} \to 0` from the $`\sigma`-phase split at cutoff $`t_{\mathrm{cut}}`, where $`X_{\mathrm{hi}} \in \operatorname{geProp}(t_{\mathrm{cut}})` and an MDQ $`q : E_{\mathrm{lo}} \to B` for $`E_{\mathrm{lo}}`, the composite $`E \twoheadrightarrow E_{\mathrm{lo}} \twoheadrightarrow B` is an MDQ for $`E`.

Proof: For any $`W`-semistable quotient $`p : E \to B'` with $`\psi(B') \le \psi(B)`: phase confinement gives $`\varphi^+(B') < \psi(B') + \varepsilon \le \psi(B) + \varepsilon`. Since $`B` is a quotient of $`E_{\mathrm{lo}}` (all $`\sigma`-phases $`\le t_{\mathrm{cut}}`), the seesaw gives $`\psi(B) \le \psi(E)`, hence $`\varphi^+(B') < t_{\mathrm{cut}}`. So $`B' \in \operatorname{ltProp}(t_{\mathrm{cut}})` while $`X_{\mathrm{hi}} \in \operatorname{geProp}(t_{\mathrm{cut}})`, giving $`\operatorname{Hom}(X_{\mathrm{hi}}, B') = 0`. Hence $`E \to B'` factors through $`E \to E_{\mathrm{lo}} \to B'`.

{docstring CategoryTheory.Triangulated.mdq_of_sigma_phase_split}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20mdq_of_sigma_phase_split&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.mdq_of_sigma_phase_split%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhiPlusReduction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_bound\_of\_destabilizing\_subobject

$`\varphi^+` bound on destabilizing subobjects (Bridgeland p.23). If $`Y \in \operatorname{IntervalCat}(a,b)` with $`\varphi^+(Y) \le \psi(Y) + \varepsilon` and $`\psi(Y) < b - 3\varepsilon`, and $`A` is a $`W`-semistable strict subobject with $`\psi(A) > \psi(Y)`, then $`\psi(A) < b - \varepsilon`.

Proof: `phiPlus_triangle_le` gives $`\varphi^+(A) \le \varphi^+(Y)`. Phase confinement gives $`\psi(A) - \varepsilon < \varphi^-(A) \le \varphi^+(A)`. Combining: $`\psi(A) < \varphi^+(Y) + \varepsilon \le \psi(Y) + 2\varepsilon < b - \varepsilon`.

{docstring CategoryTheory.Triangulated.phiPlus_bound_of_destabilizing_subobject}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_bound_of_destabilizing_subobject&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.phiPlus_bound_of_destabilizing_subobject%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Deformation.PhiPlusReduction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
