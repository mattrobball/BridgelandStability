import BridgelandStability.NumericalStability.Defs
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "NumericalStability" =>
%%%
htmlSplit := .never
%%%

# IsFiniteType

A $`k`-linear pretriangulated category $`\mathcal{T}` is of finite type if every Hom space $`\operatorname{Hom}(E, F)` is finite-dimensional over $`k` and, for each pair of objects $`E, F`, only finitely many shifted Hom spaces $`\operatorname{Hom}(E, F[n])` are nontrivial.

Construction: The typeclass bundles two conditions: a `Module.Finite k (E \longrightarrow F)` instance for all pairs $`(E, F)`, and a `Set.Finite` witness that the set $`\{n \in \mathbb{Z} \mid \operatorname{Hom}(E, F[n]) \neq 0\}` is finite.


{docstring CategoryTheory.Triangulated.IsFiniteType}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20IsFiniteType&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.IsFiniteType%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.NumericalStability.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# eulerFormObj

The object-level Euler form is defined by $`\chi(E, F) = \sum_{n \in \mathbb{Z}} (-1)^n \dim_k \operatorname{Hom}(E, F[n])`. It computes the alternating sum of dimensions of shifted Hom spaces between objects of a finite-type triangulated category.

Construction: Defined as a `finsum` over $`\mathbb{Z}`, weighting each shifted Hom dimension by $`(-1)^n` via `Int.negOnePow`. The sum is well-defined because `IsFiniteType` guarantees only finitely many nonzero terms.


{docstring CategoryTheory.Triangulated.eulerFormObj}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20eulerFormObj&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.eulerFormObj%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.NumericalStability.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
