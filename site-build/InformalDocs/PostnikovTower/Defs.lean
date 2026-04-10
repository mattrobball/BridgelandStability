import BridgelandStability.PostnikovTower.Defs
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "PostnikovTower" =>
%%%
htmlSplit := .never
%%%

# PostnikovTower

A Postnikov tower of an object $`E` in a pretriangulated category $`\mathcal{C}` is a finite filtration $$`0 = A_0 \to A_1 \to \cdots \to A_n \cong E` where each step $`A_i \to A_{i+1}` completes to a distinguished triangle $`A_i \to A_{i+1} \to F_i \to A_i[1]`. The factor objects $`F_i` are derived as the third vertices of these triangles. This separates the tower/filtration data from any phase or semistability data that may be layered on top (e.g., for Harder--Narasimhan filtrations).

Construction: A structure carrying: the length $`n`; a `ComposableArrows C n` chain of objects; a family of distinguished triangles indexed by $`\operatorname{Fin}\, n`; isomorphisms identifying each triangle's first and second vertices with consecutive chain objects; a proof that the base $`A_0` is zero; a proof that the top $`A_n \cong E`; and a degeneracy proof that $`E` is zero when $`n = 0`.


{docstring CategoryTheory.Triangulated.PostnikovTower}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20PostnikovTower&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.PostnikovTower%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.PostnikovTower.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# factor

The $`i`-th factor of a Postnikov tower, defined as the third vertex $`(P.\operatorname{triangle}\, i).\operatorname{obj}_3` of the $`i`-th distinguished triangle.

Construction: Defined as `(P.triangle i).obj_3`, extracting the factor directly from the triangle data without a separate stored field.


{docstring CategoryTheory.Triangulated.PostnikovTower.factor}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20factor&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.PostnikovTower.factor%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.PostnikovTower.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# factors

The sequence of all factor objects of a Postnikov tower, as a function $`\operatorname{Fin}\, n \to \mathcal{C}`.

Construction: Defined as `P.factor`, repackaging the factor function.


{docstring CategoryTheory.Triangulated.PostnikovTower.factors}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20factors&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.PostnikovTower.factors%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.PostnikovTower.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# length

The length of a Postnikov tower, equal to the number of factors $`n`.

Construction: Returns the field `P.n`.


{docstring CategoryTheory.Triangulated.PostnikovTower.length}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20length&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.PostnikovTower.length%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.PostnikovTower.Defs%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
