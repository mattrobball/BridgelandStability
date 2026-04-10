import BridgelandStability.TStructure.HeartAbelian
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "TStructure: HeartAbelian" =>
%%%
htmlSplit := .never
%%%

# heartAbelian

Heart abelianity. The heart of a t-structure on a triangulated category is abelian, assuming the heart has finite products. This is \cite(Th\'eor\`eme 1.3.6)(bbd-1982).

Construction: Constructed by applying `AbelianSubcategory.abelian` to the heart embedding $`\iota`, using `heart_hι` (no negative Hom spaces) and `heart_admissible` (all morphisms admissible).


{docstring CategoryTheory.Triangulated.TStructure.heartAbelian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartAbelian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heartAbelian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.HeartAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heartFullSubcategoryAbelian

Heart abelianity (canonical form). The full subcategory of heart objects of a t-structure on a triangulated category is abelian.

Construction: Instantiates `heartAbelian` with the canonical heart full subcategory, using `heart_hasFiniteProducts` for the finite products hypothesis.


{docstring CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heartFullSubcategoryAbelian&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.HeartAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_admissible

Admissibility of heart morphisms. Every morphism in the heart is admissible in the sense of `AbelianSubcategory`: given $`f_1 \colon X_1 \to X_2` in the heart, the cone $`X_3` of $`\iota(f_1)` decomposes as $`\iota(K)[1] \to X_3 \to \iota(Q)` with $`K, Q` in the heart.

Proof: The cone $`X_3` satisfies $`\operatorname{IsLE}(0)` and $`\operatorname{IsGE}(-1)` (from the rotated distinguished triangle and the heart conditions on $`X_1, X_2`). The truncation triangle $`\tau_{<0}(X_3) \to X_3 \to \tau_{\ge 0}(X_3)` provides $`Q = \tau_{\ge 0}(X_3)` (which is $`\operatorname{IsLE}(0)` and $`\operatorname{IsGE}(0)`, hence in the heart) and $`K = \tau_{<0}(X_3)[-1]` (which is $`\operatorname{IsLE}(0)` and $`\operatorname{IsGE}(0)` after unshifting, hence in the heart). The essential image of $`\iota` recovers actual heart objects, and the admissible triangle is built from the truncation triangle via explicit isomorphisms.

{docstring CategoryTheory.Triangulated.TStructure.heart_admissible}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_admissible&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heart_admissible%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.HeartAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_biprod

The biproduct of two heart objects lies in the heart.

Proof: The biproduct triangle $`X \oplus Y \to X \to Y \to (X \oplus Y)[1]` is distinguished. Apply `isLE\sb{2}` and `isGE\sb{2}` to the $`\operatorname{IsLE}(0)` and $`\operatorname{IsGE}(0)` conditions of $`X` and $`Y`.

{docstring CategoryTheory.Triangulated.TStructure.heart_biprod}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_biprod&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heart_biprod%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.HeartAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_closedUnderBinaryProducts

The heart of a t-structure is closed under binary products.

Proof: Any binary product $`X \times Y` is isomorphic to $`X \oplus Y` (via the biproduct--product isomorphism in a preadditive category), and `heart_biprod` shows $`X \oplus Y` lies in the heart.

{docstring CategoryTheory.Triangulated.TStructure.heart_closedUnderBinaryProducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_closedUnderBinaryProducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heart_closedUnderBinaryProducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.HeartAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_closedUnderFiniteProducts

The heart of a t-structure is closed under finite products.

Proof: Follows from closure under binary products and the zero object via `ObjectProperty.IsClosedUnderFiniteProducts.mk'`.

{docstring CategoryTheory.Triangulated.TStructure.heart_closedUnderFiniteProducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_closedUnderFiniteProducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heart_closedUnderFiniteProducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.HeartAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_containsZero

The zero object lies in the heart of any t-structure.

Proof: The zero object is both $`\operatorname{IsLE}(0)` and $`\operatorname{IsGE}(0)`.

{docstring CategoryTheory.Triangulated.TStructure.heart_containsZero}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_containsZero&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heart_containsZero%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.HeartAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_hasFiniteProducts

The full subcategory defined by the heart has finite products.

Proof: Combine the terminal object (from `heart_containsZero`) and binary products (from `heart_closedUnderBinaryProducts`) via `hasFiniteProducts_of_has_binary_and_terminal`.

{docstring CategoryTheory.Triangulated.TStructure.heart_hasFiniteProducts}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_hasFiniteProducts&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heart_hasFiniteProducts%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.HeartAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# heart\_hι

No negative Hom spaces in the heart. For objects $`X, Y` in the heart of a t-structure $`t`, every morphism $`\iota(X) \to \iota(Y)[n]` is zero when $`n < 0`.

Proof: Since $`\iota(Y)[n]` is $`\operatorname{IsGE}(-n)` with $`-n > 0` and $`\iota(X)` is $`\operatorname{IsLE}(0)`, the vanishing $`t.\operatorname{zero}` applies.

{docstring CategoryTheory.Triangulated.TStructure.heart_hι}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20heart_h%CE%B9&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.TStructure.heart_h%CE%B9%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.TStructure.HeartAbelian%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
