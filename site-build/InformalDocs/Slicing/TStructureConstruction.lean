import BridgelandStability.Slicing.TStructureConstruction
import VersoManual

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Slicing: TStructureConstruction" =>
%%%
htmlSplit := .never
%%%

# exists\_split\_at\_cutoff

Splitting at an arbitrary cutoff. Given an HN filtration of $`E` with all phases in $`(a, b)` and a cutoff $`t`, there exists a distinguished triangle $`X \to E \to Y \to X[1]` with $`X \in \mathcal{P}(> t)`, $`Y \in \mathcal{P}(\le t)`, and $`\phi^+(X) < b` if $`X \ne 0`.

Proof: Phase-shift by $`t` to reduce to the $`t = 0` case. Apply `exists_triangle_gtProp_leProp` to the shifted filtration. Convert back using `phaseShift_gtProp_zero` and `phaseShift_leProp_zero`. The upper phase bound on $`X` is recovered via `unphaseShift_phiPlus` and the original interval constraint.

{docstring CategoryTheory.Triangulated.Slicing.exists_split_at_cutoff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_split_at_cutoff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.exists_split_at_cutoff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_split\_with\_interval

Special case of `exists_split_at_cutoff` with $`t = a`: split at the lower endpoint of the interval.

Proof: Direct application of `exists_split_at_cutoff` with $`t = a`.

{docstring CategoryTheory.Triangulated.Slicing.exists_split_with_interval}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_split_with_interval&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.exists_split_with_interval%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_triangle\_geProp\_ltProp

Dual decomposition: given an HN filtration of $`A`, there exists a distinguished triangle $`X \to A \to Y \to X[1]` with $`X \in \mathcal{P}(\ge 0)` and $`Y \in \mathcal{P}(< 0)`.

Proof: Same inductive strategy as `exists_triangle_gtProp_leProp`, using the dual half-open predicates $`\mathcal{P}(\ge 0)` and $`\mathcal{P}(< 0)` and splitting at the boundary between non-negative and negative phases.

{docstring CategoryTheory.Triangulated.Slicing.exists_triangle_geProp_ltProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_triangle_geProp_ltProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.exists_triangle_geProp_ltProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# exists\_triangle\_gtProp\_leProp

Given an HN filtration of an object $`A`, there exists a distinguished triangle $`X \to A \to Y \to X[1]` with $`X \in \mathcal{P}(> 0)` and $`Y \in \mathcal{P}(\le 0)`. Moreover, if $`X` is nonzero, its phases are drawn from those of the original filtration with appropriate bounds.

Proof: Induction on the filtration length. If all phases are $`> 0`, take $`X = A` and $`Y = 0`. If all phases are $`\le 0`, take $`X = 0` and $`Y = A`. In the mixed case, split the prefix filtration by the inductive hypothesis, then use the octahedral axiom to incorporate the remaining low-phase factor via `appendFactor`.

{docstring CategoryTheory.Triangulated.Slicing.exists_triangle_gtProp_leProp}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20exists_triangle_gtProp_leProp&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.exists_triangle_gtProp_leProp%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toTStructure

A slicing $`\mathcal{P}` on a triangulated category determines a t-structure with the convention: $`\mathcal{D}^{\le n} = \mathcal{P}(> -n)` and $`\mathcal{D}^{\ge n} = \mathcal{P}(\le 1 - n)`. The heart is $`\mathcal{P}((0, 1])`.

Construction: Constructs a `TStructure` by setting `le n` to `gtProp(-n)` and `ge n` to `leProp(1 - n)`. Shift compatibility follows from `gtProp_shift` and `leProp_shift`. Hom-vanishing at the $`(0, 1)` boundary uses `zero_of_gtProp_leProp`. The existence of the decomposition triangle at level $`(0, 1)` is provided by `exists_triangle_gtProp_leProp`.


{docstring CategoryTheory.Triangulated.Slicing.toTStructure}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toTStructure&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.toTStructure%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toTStructureGE

A slicing $`\mathcal{P}` also determines the dual half-open t-structure with: $`\mathcal{D}^{\le n} = \mathcal{P}(\ge -n)` and $`\mathcal{D}^{\ge n} = \mathcal{P}(< 1 - n)`. The heart is $`\mathcal{P}([0, 1))`.

Construction: Constructs a `TStructure` by setting `le n` to `geProp(-n)` and `ge n` to `ltProp(1 - n)`. The decomposition triangle uses `exists_triangle_geProp_ltProp`.


{docstring CategoryTheory.Triangulated.Slicing.toTStructureGE}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toTStructureGE&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.toTStructureGE%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toTStructureGE\_bounded

Bounded t-structure from the dual half-open convention. The t-structure induced by `toTStructureGE` is bounded.

Proof: Same strategy as `toTStructure_bounded`, using ceiling/floor to convert the finite phase interval into integer bounds for the $`\ge / <` predicates.

{docstring CategoryTheory.Triangulated.Slicing.toTStructureGE_bounded}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toTStructureGE_bounded&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.toTStructureGE_bounded%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toTStructureGE\_heart\_iff

An object $`E` lies in the heart of `toTStructureGE` if and only if $`E \in \mathcal{P}(\ge 0) \cap \mathcal{P}(< 1)`, i.e.\ its HN phases lie in $`[0, 1)`.

Proof: Unfolding the heart definition with the dual conventions.

{docstring CategoryTheory.Triangulated.Slicing.toTStructureGE_heart_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toTStructureGE_heart_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.toTStructureGE_heart_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toTStructure\_bounded

Bounded t-structure from a slicing. The t-structure $`\mathcal{D}^{\le \bullet}` induced by a slicing is bounded: every object lies between $`\mathcal{D}^{\le a}` and $`\mathcal{D}^{\ge b}` for some integers $`a, b`.

Proof: The HN filtration axiom places every nonzero object's phases in a finite interval $`[\phi^-, \phi^+]`. Setting $`a = \lceil -\phi^- \rceil + 1` and $`b = \lfloor 1 - \phi^+ \rfloor` gives the required integer bounds.

{docstring CategoryTheory.Triangulated.Slicing.toTStructure_bounded}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toTStructure_bounded&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.toTStructure_bounded%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)

# toTStructure\_heart\_iff

An object $`E` lies in the heart of the slicing-induced t-structure if and only if $`E \in \mathcal{P}(> 0) \cap \mathcal{P}(\le 1)`, i.e.\ its HN phases lie in the half-open interval $`(0, 1]`.

Proof: Unfolding the heart definition: $`E \in \mathcal{D}^{\le 0} \cap \mathcal{D}^{\ge 0}` becomes $`\mathrm{gtProp}(0)` and $`\mathrm{leProp}(1)` after substituting the t-structure conventions.

{docstring CategoryTheory.Triangulated.Slicing.toTStructure_heart_iff}

Something wrong, better idea? [Suggest a change](https://github.com/mattrobball/BridgelandStability/issues/new?title=Review%3A%20toTStructure_heart_iff&body=%2A%2ADeclaration%3A%2A%2A%20%60CategoryTheory.Triangulated.Slicing.toTStructure_heart_iff%60%0A%2A%2AModule%3A%2A%2A%20%60BridgelandStability.Slicing.TStructureConstruction%60%0A%2A%2ASource%3A%2A%2A%20unavailable%0A---%0A%2A%2ADescribe%20the%20issue%3A%2A%2A&labels=exposition-review)
