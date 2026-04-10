import BridgelandStability.TStructure.AbelianSubcategoryImageFactorisation
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "TStructure: AbelianSubcategoryImageFactorisation" =>
%%%
htmlSplit := .never
%%%

# exists\_distinguished\_triangle\_of\_image\_factorisation

Image factorisation triangle. Given a distinguished triangle $`\iota(X_1) \xrightarrow{\iota(f_1)} \iota(X_2) \xrightarrow{f_2} X_3 \xrightarrow{f_3} \iota(X_1)[1]` with $`X_1, X_2` in the abelian subcategory, and a decomposition of $`X_3` as $`\iota(K)[1] \xrightarrow{\alpha} X_3 \xrightarrow{\beta} \iota(Q) \xrightarrow{\gamma} \iota(K)[1][1]` (also distinguished), there exist: an object $`I` in the subcategory, morphisms $`i \colon I \to X_2`, $`\delta \colon \iota(Q) \to \iota(I)[1]`, $`m_1 \colon X_1 \to I`, and $`m_3 \colon \iota(I) \to \iota(K)[1]` such that (1) $`\iota(i), \iota(\pi_Q), \delta` form a distinguished triangle, (2) $`\iota(\iota_K), \iota(m_1), -m_3` form a distinguished triangle, and (3) $`m_1 \circ i = f_1`.

Proof: The proof applies the octahedral axiom to the factorisation $`f_2 \circ \beta = \iota(\pi_Q)`. The epi $`\pi_Q` yields the first triangle via `exists_distinguished_triangle_of_epi`. The octahedron produces the second triangle and the factorisation $`m_1 \circ i = f_1`. The key lifting steps use fullness of $`\iota \circ \operatorname{shift}` to extract $`m_1` and $`m_3` as morphisms in the ambient category, and `IsTriangulated` to access the octahedral axiom.

{docstring CategoryTheory.Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_image_factorisation}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_distinguished_triangle_of_image_factorisation&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_image_factorisation%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.AbelianSubcategoryImageFactorisation%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
