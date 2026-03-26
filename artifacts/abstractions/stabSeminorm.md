# Audit: `stabSeminorm` and Bridgeland Topology Infrastructure

## 1. Definition

From `BridgelandStability/StabilityCondition/Defs.lean`:

```lean
def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)
```

Given a stability condition `σ = (Z, P)` and a group homomorphism `U : K₀(C) → ℂ`, this
is `sup { ‖U([E])‖ / ‖Z([E])‖ : E is σ-semistable and nonzero }`.  The codomain is
`ℝ≥0∞` (extended nonneg reals), so the supremum always exists but may be `⊤`.

Companion definitions in the same file:

```lean
def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)

def basisNhd (σ : StabilityCondition C) (ε : ℝ) : Set (StabilityCondition C) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}
```

The Bridgeland topology is `TopologicalSpace.generateFrom` over
`basisNhd C σ ε` for all σ and `ε ∈ (0, 1/8)`.


## 2. Catalogued API

### Properties of `slicingDist` (in `Seminorm.lean`)

| Theorem | Statement |
|---|---|
| `slicingDist_self` | `d(P, P) = 0` |
| `slicingDist_symm` | `d(P, Q) = d(Q, P)` |
| `slicingDist_triangle` | `d(P, R) ≤ d(P, Q) + d(Q, R)` |
| `slicingDist_le_of_phase_bounds` | Converse: pointwise phase bounds imply distance bound |
| `phiPlus_sub_lt_of_slicingDist` | `d < ε ⟹ |φ⁺(E; P) - φ⁺(E; Q)| < ε` |
| `phiMinus_sub_lt_of_slicingDist` | `d < ε ⟹ |φ⁻(E; P) - φ⁻(E; Q)| < ε` |
| `intervalProp_of_semistable_slicingDist` | Lemma 6.1: semistable phase proximity |

**Verdict**: `slicingDist` satisfies all axioms of a `PseudoEMetricSpace` (self = 0,
symmetric, triangle inequality).  It is *not* known to satisfy `d(P,Q) = 0 ⟹ P = Q` in
the formalization (that would require showing HN filtrations are determined by φ± values).

### Properties of `stabSeminorm` (across `Seminorm.lean`, `Deformation.lean`, `ConnectedComponent.lean`)

| Theorem | Statement |
|---|---|
| `stabSeminorm_nonneg` | `0 ≤ ‖U‖_σ` (trivial for `ℝ≥0∞`) |
| `stabSeminorm_zero` | `‖0‖_σ = 0` |
| `stabSeminorm_neg` | `‖-U‖_σ = ‖U‖_σ` |
| `stabSeminorm_add_le` | `‖U + V‖_σ ≤ ‖U‖_σ + ‖V‖_σ` (subadditivity) |
| `stabSeminorm_smul` | `‖t • U‖_σ = |t| · ‖U‖_σ` for `t : ℝ` |
| `stabSeminorm_smul_complex` | `‖t • U‖_σ = ‖t‖ · ‖U‖_σ` for `t : ℂ` |
| `stabSeminorm_bound_real` | Pointwise: `‖U(A)‖ ≤ ‖U‖_σ.toReal · ‖Z(A)‖` for semistable A |
| `eq_zero_of_stabSeminorm_toReal_eq_zero` | Definiteness: finite `‖U‖_σ = 0 ⟹ U = 0` |
| `Z_mem_finiteSeminormSubgroup` | `‖Z(σ)‖_σ ≤ 1`, so `Z(σ) ∈ V(σ)` |

### Seminorm comparison and topology (Lemma 6.2, Proposition 6.3)

| Theorem | Statement |
|---|---|
| `sector_bound` / `sector_bound'` | Sector estimate: extends pointwise bounds to all objects via HN decomposition |
| `norm_Z_le_of_tau_semistable` | Reverse triangle: controls `‖Z(E)‖` by `‖W(E)‖` |
| `stabSeminorm_le_of_near` | Quantitative comparison: `‖U‖_τ ≤ ‖U‖_σ / (cos πε - ‖ΔZ‖_σ)` |
| `stabSeminorm_lt_top_of_same_Z` | Same Z: `V(σ) ⊆ V(τ)` |
| `stabSeminorm_lt_top_of_near` | General: `V(σ) ⊆ V(τ)` when `d < ε` and `‖ΔZ‖_σ < cos πε` |
| `finiteSeminormSubgroup_eq_of_same_Z` | Same Z: `V(σ) = V(τ)` (Prop 6.3 special case) |
| `finiteSeminormSubgroup_eq_of_basisNhd` | Full Prop 6.3: `V(σ) = V(τ)` for `τ ∈ B_ε(σ)`, `ε < 1/8` |
| `stabSeminorm_dominated_of_basisNhd` | Local domination: `‖·‖_σ ≤ K · ‖·‖_τ` on a single neighborhood |
| `stabSeminorm_dominated_of_connected` | Lemma 6.2 on components: equivalence of seminorms |
| `stabSeminorm_center_dominates_of_basisNhd` | Reverse domination: `‖·‖_τ ≤ K · ‖·‖_σ` |

### Deformation interface (Theorem 7.1 usage)

| Theorem | Key hypothesis |
|---|---|
| `StabilityCondition.deformed` | `stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1` |
| `hperturb_of_stabSeminorm` | Bridges global seminorm bound to pointwise W-phase perturbation |
| `W_ne_zero_of_seminorm_lt_one` | `‖W - Z‖_σ < 1 ⟹ W(E) ≠ 0` for semistable E |
| `phase_confinement_from_stabSeminorm` | Seminorm + sector width ⟹ phase confinement |
| `stabSeminorm_lt_cos_of_hsin_hthin` | Upgrades sin bound to cos bound when interval is thin |

### Topology and local homeomorphism

| Construction | Role |
|---|---|
| `finiteSeminormSubgroup` | `V(σ) = { U : ‖U‖_σ < ⊤ }`, an `AddSubgroup` |
| `componentSeminormSubgroup` | `V(Σ)` as a `Submodule ℂ (K₀ C →+ ℂ)` via component rep |
| `componentNormedAddCommGroup` | Norm on `V(Σ)` via `stabSeminorm` + `AddGroupNorm.toNormedAddCommGroup` |
| `componentNormedSpace` | `NormedSpace ℂ V(Σ)` via `stabSeminorm_smul_complex` |
| `centralChargeIsLocalHomeomorphOnConnectedComponents` | Theorem 1.2: Z is a local homeomorphism on each component |


## 3. Mathematical Generalization Analysis

### What `stabSeminorm` really is

The definition `sup_E { ‖U(E)‖ / ‖Z(E)‖ }` over a distinguished subset of generators
(semistable objects) is the **operator seminorm** of `U` relative to `Z`, restricted to
semistable classes.  More precisely, if we think of `Z` as defining a "reference norm"
`‖·‖_Z` on the image of semistable classes, then `stabSeminorm` is the operator norm
of `U` with respect to `‖·‖_Z`.

This is closely analogous to:
- The **operator norm** `‖T‖ = sup { ‖Tx‖ / ‖x‖ }` for a linear map between normed spaces.
- The `seminormFromBounded'` construction in Mathlib (`Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded`), which defines `‖x‖ = sup_y { f(xy)/f(y) }` for a submultiplicatively bounded function on a ring.

### What it does NOT need

The definition `stabSeminorm` as written requires the **full** `StabilityCondition C`,
but it only accesses:

1. **`σ.slicing.P φ`**: to identify the semistable objects and their phases.
2. **`σ.Z`**: to compute the denominator `‖Z(E)‖`.

It does NOT need:
- The `compat` field (central charge compatibility with phases) -- except indirectly:
  `compat` is used in *proofs* (e.g., `stabSeminorm_bound_real` uses it to ensure `‖Z(E)‖ > 0`
  for nonzero semistable `E`).
- The `locallyFinite` field -- not used by the definition at all; only by downstream theorems.
- The triangulated structure -- only needed for HN filtrations in `sector_bound`.

### Could it be defined for general normed group homomorphisms?

**Partially.** The core formula `sup { ‖U(e)‖ / ‖Z(e)‖ : e ∈ S }` makes sense for:
- An additive group `G` with a distinguished subset `S ⊆ G`.
- Two group homomorphisms `Z, U : G → ℂ` (or more generally, to a normed field).
- The requirement that `Z(e) ≠ 0` for `e ∈ S` (otherwise the ratio is `0/0`).

This would give an abstract "relative operator seminorm":

```
relSeminorm (S : Set G) (Z U : G →+ ℂ) : ℝ≥0∞ :=
  ⨆ (e : G) (_ : e ∈ S), ENNReal.ofReal (‖U e‖ / ‖Z e‖)
```

**However**, the proofs that make `stabSeminorm` powerful -- sector bounds, seminorm
comparison, the deformation theorem -- all require deep structure that this abstraction
would not provide:

- **Sector bound** (`sector_bound`): Needs HN filtrations, K₀ additivity, and the
  geometric fact that Z-values of semistable factors lie on rays with nearby angles. This
  is what converts a bound on semistable factors to a bound on arbitrary objects.
- **Seminorm comparison** (`stabSeminorm_le_of_near`): Needs `slicingDist` proximity,
  which is specific to slicings.
- **Definiteness** (`eq_zero_of_stabSeminorm_toReal_eq_zero`): Needs that K₀ is generated
  by classes of objects, and every object has an HN filtration into semistable pieces.

### Does it just need a central charge?

**No.** The slicing `P` is essential. Without knowing which objects are semistable, the
supremum would be taken over all nonzero objects, and the sector bound (which extends the
pointwise bound from semistable objects to all objects) would not apply. The whole point of
the Bridgeland construction is that the supremum over semistable objects (together with the
sector bound) controls the behavior on all objects.

That said, the *definition* of `stabSeminorm` could be weakened to take a `PreStabilityCondition`
(no local finiteness requirement) without changing the formula. The `locallyFinite` field is
only needed for the deformation theorem, not for the seminorm properties.


## 4. Mathlib Comparison

### Existing Mathlib constructions

| Mathlib type | Relationship to `stabSeminorm` |
|---|---|
| `Seminorm 𝕜 E` (`Mathlib.Analysis.Seminorm`) | `stabSeminorm` restricted to `V(σ)` gives a genuine `Seminorm ℂ V(σ)`. The codebase constructs this explicitly as `componentAddGroupNorm` (even a norm, not just a seminorm, since definiteness holds). |
| `AddGroupSeminorm` (`Mathlib.Analysis.Normed.Group.Seminorm`) | `stabSeminorm` on the full `K₀ C →+ ℂ` satisfies subadditivity and negation-invariance, making it an `AddGroupSeminorm`-valued function, except its codomain is `ℝ≥0∞` rather than `ℝ`. |
| `PseudoEMetricSpace` | `slicingDist` satisfies the axioms of a `PseudoEMetricSpace`. The codebase does **not** register this instance; the topology is instead generated by `basisNhd` sets. |
| `seminormFromBounded'` (`Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded`) | Structurally parallel: `sup_y { f(xy)/f(y) }`. But this is for ring seminorms on commutative rings, not for group homomorphism spaces. |

### What is NOT in Mathlib

- **Bridgeland stability conditions**: No Mathlib formalization exists.
- **Stability topology / generalized metric on slicings**: Novel to this project.
- **Extended-real-valued seminorms with sector bounds**: The combination of `ℝ≥0∞`-valued
  seminorms with geometric sector estimates is specific to Bridgeland theory.

### Potential Mathlib contribution paths

1. **`slicingDist` as `PseudoEMetricSpace`**: The three proved properties (`_self`, `_symm`,
   `_triangle`) are exactly the `PseudoEMetricSpace` axioms. Registering this would give
   access to the `EMetricSpace` API (balls, Cauchy sequences, etc.) for free. The topology
   is currently hand-generated rather than derived from the metric.

2. **`ℝ≥0∞`-valued `AddGroupSeminorm`**: The properties (`_zero`, `_neg`, `_add_le`,
   `_smul_complex`) make `stabSeminorm σ` an `AddGroupSeminorm` / `Seminorm` except for
   the codomain being `ℝ≥0∞` instead of `ℝ`. Mathlib does not have extended-real-valued
   seminorms. This gap is worked around by restricting to `V(σ) = { U : ‖U‖_σ < ⊤ }` and
   projecting to `ℝ`.

3. **Relative operator seminorm**: The pattern `sup_S { ‖U(e)‖ / ‖Z(e)‖ }` could be
   abstracted to a general construction on normed abelian groups with a distinguished
   generating subset. The sector bound would require additional hypotheses (convexity of
   the "cone" of Z-values).


## 5. Summary Assessment

`stabSeminorm` is at **maximal usable generality for its mathematical purpose**. The
definition itself is simple and could be stated for a broader class of inputs, but every
non-trivial theorem about it (sector bounds, seminorm comparison, deformation theorem) uses
the full stability condition structure. Abstracting the definition without abstracting the
proofs would produce a definition with no useful API.

The two concrete improvements that would increase usable generality without mathematical
cost:

1. **Weaken to `PreStabilityCondition`**: The definition and all seminorm-algebraic
   properties (`_zero`, `_neg`, `_add_le`, `_smul`, `stabSeminorm_bound_real`) do not use
   `locallyFinite`. They could take a `PreStabilityCondition` instead. The `sector_bound`
   and comparison theorems would still need `IsTriangulated` for HN filtrations.

2. **Register `PseudoEMetricSpace` on `Slicing C`**: The three `slicingDist` axioms are
   proved. Registering the instance would give the `EMetricSpace` API for free, and the
   current `TopologicalSpace.generateFrom` construction for the Bridgeland topology could
   be shown to agree with the product of the `PseudoEMetricSpace` topology on slicings and
   the seminorm topology on central charges.
