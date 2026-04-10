import BridgelandStability.Slicing.ExtensionClosure
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Slicing: ExtensionClosure" =>
%%%
htmlSplit := .never
%%%

# gtProp\_of\_triangle

Extension-closure of $`\mathcal{P}(> t)`. If $`A \to E \to B \to A[1]` is a distinguished triangle and both $`A` and $`B` have all HN phases $`> t`, then $`E` also has all HN phases $`> t`.

Proof: By contradiction: suppose $`\phi^-(E) \le t`. Then the last HN factor $`F^-` of $`E` has phase $`\le t`. By Hom-vanishing, $`\operatorname{Hom}(A, F^-) = 0` and $`\operatorname{Hom}(B, F^-) = 0`. The Yoneda exact sequence on the triangle gives $`\operatorname{Hom}(E, F^-) = 0`, contradicting the non-triviality of $`F^-`.

{docstring CategoryTheory.Triangulated.Slicing.gtProp_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20gtProp_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.gtProp_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.ExtensionClosure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# intervalProp\_of\_triangle

Extension-closure of $`\mathcal{P}((a,b))`. If $`A \to E \to B \to A[1]` is a distinguished triangle and both $`A` and $`B` have all HN phases in the open interval $`(a, b)`, then so does $`E`.

Proof: Combines `phiPlus_lt_of_triangle` to get $`\phi^+(E) < b` and `phiMinus_gt_of_triangle` to get $`\phi^-(E) > a`. Then all phases of $`E` lie in $`(a, b)` by the phase range lemma.

{docstring CategoryTheory.Triangulated.Slicing.intervalProp_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20intervalProp_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.intervalProp_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.ExtensionClosure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# leProp\_of\_triangle

Extension-closure of $`\mathcal{P}(\le t)`. If $`A \to E \to B \to A[1]` is a distinguished triangle and both $`A` and $`B` have all HN phases $`\le t`, then $`E` also has all HN phases $`\le t`.

Proof: By contradiction: suppose $`\phi^+(E) > t`. Then the first HN factor $`F^+` of $`E` has phase $`> t`. By Hom-vanishing, $`\operatorname{Hom}(F^+, A) = 0` and $`\operatorname{Hom}(F^+, B) = 0`. The coYoneda exact sequence on the triangle then gives $`\operatorname{Hom}(F^+, E) = 0`, contradicting the fact that $`F^+` is a nonzero factor of $`E`.

{docstring CategoryTheory.Triangulated.Slicing.leProp_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20leProp_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.leProp_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.ExtensionClosure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# ltProp\_of\_triangle

Extension-closure of $`\mathcal{P}(< t)`. If $`A \to E \to B \to A[1]` is a distinguished triangle and both $`A` and $`B` have all HN phases $`< t`, then $`E` also has all HN phases $`< t`.

Proof: By contradiction: if $`\phi^+(E) \ge t`, then Hom-vanishing kills all maps from the top HN factor of $`E` to both $`A` and $`B`, and coYoneda exactness forces it to map trivially to $`E`, contradicting non-triviality. The argument mirrors `leProp_of_triangle` with strict inequalities.

{docstring CategoryTheory.Triangulated.Slicing.ltProp_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20ltProp_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.ltProp_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.ExtensionClosure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_gt\_of\_triangle

If $`A \to E \to B \to A[1]` is a distinguished triangle and $`\phi^-(A) > t`, $`\phi^-(B) > t` for any nonzero $`A, B`, then $`\phi^-(E) > t` for the nonzero middle term.

Proof: By contradiction: if $`\phi^-(E) \le t`, the last HN factor of $`E` has phase $`\le t`, below both $`\phi^-(A)` and $`\phi^-(B)`. Yoneda exactness forces all maps from $`E` to this factor to vanish, contradicting non-triviality.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_gt_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.ExtensionClosure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_triangle\_le

**\[Lemma 3.4\]** φ⁻(E) ≤ φ⁻(B)

Lemma 3.4 (right inequality). In a distinguished triangle $`A \to E \to B \to A[1]` where the phases of $`A` and $`B` lie in an interval $`(a, b)` with $`b \le a + 1`, one has $`\phi^-(E) \le \phi^-(B)`.

Proof: By contradiction: if $`\phi^-(E) > \phi^-(B)`, then maps $`E \to B^-` vanish by Hom-vanishing. By the Yoneda exact sequence, maps $`B \to B^-` factor through $`A[1]`. The width condition ensures the shifted phases of $`A[1]` are above $`\phi(B^-)`, so $`\operatorname{Hom}(A[1], B^-) = 0`, giving $`B^- = 0`, a contradiction.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_triangle_le}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_triangle_le&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_triangle_le%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.ExtensionClosure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Lemma%203.4%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiMinus\_triangle\_le'

Variant of Lemma 3.4 (`phiMinus_triangle_le`) where the hypothesis $`B \in \mathcal{P}((a,b))` is weakened to $`\phi^+(B) < b`. Under the same width bound $`b \le a + 1` and with $`A \in \mathcal{P}((a,b))`, one still obtains $`\phi^-(E) \le \phi^-(B)`.

Proof: Same proof strategy as `phiMinus_triangle_le`, using the weaker hypothesis $`\phi^+(B) < b` (rather than full interval membership) wherever the upper phase bound of $`B` is needed.

{docstring CategoryTheory.Triangulated.Slicing.phiMinus_triangle_le'}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiMinus_triangle_le%27&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiMinus_triangle_le%27%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.ExtensionClosure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_lt\_of\_triangle

If $`A \to E \to B \to A[1]` is a distinguished triangle and $`\phi^+(A) < t`, $`\phi^+(B) < t` for any nonzero $`A, B`, then $`\phi^+(E) < t` for the nonzero middle term.

Proof: By contradiction: if $`\phi^+(E) \ge t`, then the top HN factor of $`E` has phase $`\ge t`, placing it above both $`\phi^+(A)` and $`\phi^+(B)`. CoYoneda exactness forces all maps from this factor to $`E` to vanish, contradicting non-triviality.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_triangle}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_lt_of_triangle&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_triangle%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.ExtensionClosure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# phiPlus\_triangle\_le

**\[Lemma 3.4\]** φ⁺(A) ≤ φ⁺(E)

Lemma 3.4 (left inequality). In a distinguished triangle $`A \to E \to B \to A[1]` where the phases of $`A` and $`B` lie in an interval $`(a, b)` with $`b \le a + 1`, one has $`\phi^+(A) \le \phi^+(E)`.

Proof: By contradiction: if $`\phi^+(A) > \phi^+(E)`, then the top factor $`A^+` of $`A` has all maps to $`E` vanishing (phase gap). By the coYoneda exact sequence on the inverse rotation, maps $`A^+ \to A` factor through $`B[-1]`. The width condition $`b \le a + 1` ensures that the shifted phases of $`B[-1]` are below $`\phi(A^+)`, so $`\operatorname{Hom}(A^+, B[-1]) = 0` as well, giving $`A^+ = 0`, a contradiction.

{docstring CategoryTheory.Triangulated.Slicing.phiPlus_triangle_le}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20phiPlus_triangle_le&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.phiPlus_triangle_le%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.ExtensionClosure%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A%2A%2APaper%3A%2A%2A%20Lemma%203.4%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
