# Cross-cutting Analysis: wPhaseOf, K0, stabSeminorm (v2)

## Status: Analysis complete, proposals below

---

## Phase 1: Critical API Catalog

### 1. `wPhaseOf` (Deformation/WPhase.lean)

Definition:
```lean
noncomputable def wPhaseOf (w : ℂ) (α : ℝ) : ℝ :=
  α + Complex.arg (w * Complex.exp (-(↑(Real.pi * α) * Complex.I))) / Real.pi
```

Core API in WPhase.lean (pure-complex, no category dependency):

| Declaration | Statement |
|---|---|
| `wPhaseOf_mem_Ioc` | `wPhaseOf w α ∈ (α - 1, α + 1]` |
| `wPhaseOf_compat` | `w = ‖w‖ * exp(iπ · wPhaseOf w α)` (polar decomposition) |
| `wPhaseOf_of_exp` | `wPhaseOf (m * exp(iπφ), α) = φ` when `m > 0`, `φ ∈ (α-1, α+1]` |
| `wPhaseOf_zero` | `wPhaseOf 0 α = α` (`@[simp]`) |
| `wPhaseOf_neg` | `wPhaseOf (-w) (α+1) = wPhaseOf w α + 1` for `w ≠ 0` |
| `wPhaseOf_add_two` | `wPhaseOf w (α+2) = wPhaseOf w α + 2` for `w ≠ 0` |
| `wPhaseOf_indep` | branch-cut independence: `wPhaseOf w α₁ = wPhaseOf w α₂` when compatible |

Additional pure-complex API in ForMathlib/ files:

| File | Key lemmas |
|---|---|
| `PhasePerturbation.lean` (ForMathlib) | `im_sq_le_norm_sq_mul`, `abs_sin_arg_le_norm_sub_one`, `sin_abs_eq_abs_sin`, `abs_arg_one_add_lt` |
| `SectorBound.lean` (ForMathlib) | `eq_of_pos_mul_exp_eq` (ray rigidity), `re_mul_exp_neg_ge_cos_mul_norm`, `norm_sum_exp_ge_cos_mul_sum` |
| `ArgConvexity.lean` (ForMathlib) | `arg_add_le_max`, `min_arg_le_arg_add` (arg convexity for sums) |

Category-dependent API (PhaseArithmetic.lean, ~30 theorems):

| Declaration | Statement |
|---|---|
| `wPhaseOf_Z_eq` | `wPhaseOf(Z(E), α) = φ` for σ-semistable E of phase φ |
| `wPhaseOf_perturbation` | `|wPhaseOf(W(E), α) - φ| < ε` under seminorm control |
| `wPhaseOf_gt_of_im_pos` | phase lower bound from positive imaginary part |
| `wPhaseOf_lt_of_im_neg` | phase upper bound from negative imaginary part |
| `wPhaseOf_seesaw` / `_strict` / `_dual` | seesaw inequalities for sums |
| `wPhaseOf_lt_of_add_le_lt` / `_gt` | additivity phase bounds |
| `wPhaseOf_gt_of_intervalProp` / `_lt` | Lemma 7.3(b) bounds for interval objects |

### 2. `K₀` (GrothendieckGroup/Defs.lean)

Definition:
```lean
def K₀Subgroup : AddSubgroup (FreeAbelianGroup C) :=
  AddSubgroup.closure
    {x | ∃ (T : Pretriangulated.Triangle C), (T ∈ distTriang C) ∧
        x = FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ -
          FreeAbelianGroup.of T.obj₃}

def K₀ : Type _ := FreeAbelianGroup C ⧸ K₀Subgroup C
```

Core API:

| Declaration | Statement |
|---|---|
| `K₀.instAddCommGroup` | `AddCommGroup (K₀ C)` |
| `K₀.of` | Class map `C → K₀ C` |
| `K₀.of_triangle` | `[T.obj₂] = [T.obj₁] + [T.obj₃]` |
| `K₀.of_zero` / `K₀.of_isZero` | Zero objects vanish |
| `K₀.of_iso` | Isomorphism invariance |
| `K₀.of_shift_one` / `of_shift_neg_one` | `[X⟦1⟧] = -[X]` (`@[simp]`) |
| `IsTriangleAdditive` | Typeclass for triangle-respecting functions |
| `K₀.lift` / `K₀.lift_of` | Universal property |
| `K₀.of_postnikovTower_eq_sum` | `[E] = Σ [Fᵢ]` (Postnikov decomposition) |

### 3. `stabSeminorm` (StabilityCondition/Defs.lean)

Definition:
```lean
def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)
```

Core API (across Seminorm.lean, Deformation.lean, ConnectedComponent.lean):

| Declaration | Statement |
|---|---|
| `stabSeminorm_zero` | `‖0‖_σ = 0` |
| `stabSeminorm_neg` | `‖-U‖_σ = ‖U‖_σ` |
| `stabSeminorm_add_le` | `‖U + V‖_σ ≤ ‖U‖_σ + ‖V‖_σ` |
| `stabSeminorm_smul` | `‖t • U‖_σ = |t| · ‖U‖_σ` for `t : ℝ` |
| `stabSeminorm_smul_complex` | `‖t • U‖_σ = ‖t‖ · ‖U‖_σ` for `t : ℂ` |
| `stabSeminorm_bound_real` | `‖U(A)‖ ≤ ‖U‖_σ.toReal · ‖Z(A)‖` for semistable A |
| `eq_zero_of_stabSeminorm_toReal_eq_zero` | Finite `‖U‖_σ = 0 ⟹ U = 0` |
| `sector_bound` / `sector_bound'` | Extends pointwise bounds via HN |
| `stabSeminorm_lt_top_of_same_Z` | `V(σ) ⊆ V(τ)` for same Z |
| `stabSeminorm_lt_top_of_near` | `V(σ) ⊆ V(τ)` when nearby |
| `finiteSeminormSubgroup` | `AddSubgroup` of finite-seminorm morphisms |

Companion `slicingDist`:

| Declaration | Statement |
|---|---|
| `slicingDist_self` | `d(P, P) = 0` |
| `slicingDist_symm` | `d(P, Q) = d(Q, P)` |
| `slicingDist_triangle` | `d(P, R) ≤ d(P, Q) + d(Q, R)` |

---

## Phase 2: Duplication Analysis

### 2A. K₀ and HeartK0: K0Presentation proposal

The existing proposal at `artifacts/generalizations/k0-presentation.md` remains valid. The
duplicated pattern is confirmed:

**Triangulated K₀** (`GrothendieckGroup/Defs.lean`):
- `K₀Subgroup` = `AddSubgroup.closure {[T.obj₂] - [T.obj₁] - [T.obj₃] | T ∈ distTriang}`
- `K₀` = `FreeAbelianGroup C ⧸ K₀Subgroup C`
- `K₀.of`, `K₀.of_triangle`, `K₀.lift`, `K₀.lift_of`

**Heart K₀** (`HeartEquivalence/Basic.lean`):
- `HeartK0Subgroup` = `AddSubgroup.closure {[S.X₂] - [S.X₁] - [S.X₃] | S.ShortExact}`
- `HeartK0` = `FreeAbelianGroup heart ⧸ HeartK0Subgroup`
- `HeartK0.of`, `HeartK0.of_shortExact`, `ZOnHeartK0` (via `QuotientAddGroup.lift`)

The proposal does not need updating. One minor note: the `HeartK0` in the codebase
does *not* have a standalone `lift` definition -- the universal property is inlined
into `ZOnHeartK0` and `heartK0ToK0` via `QuotientAddGroup.lift` each time. This
makes the factoring more valuable, not less, since a shared `K0Presentation.lift`
would eliminate three copies of the same `(AddSubgroup.closure_le _).mpr` proof
pattern.

**Verdict**: Proposal is still valid, effort is small, and it would deduplicate
~6 shared declarations plus 3 copies of the universal-property proof.

### 2B. wPhaseOf: Overlap with Mathlib's Complex.arg API

`wPhaseOf w α` is defined as `α + arg(w * exp(-iπα)) / π`. This is the
**normalized argument relative to a branch cut at angle πα**, scaled to have
period 2 instead of 2π.

Mathlib's `Complex.arg` API provides:

| Mathlib lemma | Relationship |
|---|---|
| `Complex.arg_le_pi` | Used directly in `wPhaseOf_mem_Ioc` (upper bound) |
| `Complex.neg_pi_lt_arg` | Used directly in `wPhaseOf_mem_Ioc` (lower bound) |
| `Complex.arg_real_mul` | Used in `wPhaseOf_of_exp` and `wPhaseOf_perturbation_generic` |
| `Complex.arg_exp_mul_I` | Used in `wPhaseOf_of_exp` and `wPhaseOf_perturbation_generic` |
| `Complex.arg_mul` | Used in `wPhaseOf_perturbation_generic` (arg of product) |
| `Complex.norm_mul_exp_arg_mul_I` | Used in `wPhaseOf_compat` (polar decomposition) |

The pure-complex lemmas in `wPhaseOf`'s API are:

1. `wPhaseOf_mem_Ioc`: Direct consequence of `arg ∈ (-π, π]`. Not in Mathlib because
   `wPhaseOf` is a project-specific definition, but the underlying bounds *are* Mathlib.
2. `wPhaseOf_compat`: Polar decomposition. Uses `Complex.norm_mul_exp_arg_mul_I` from
   Mathlib but adds the `wPhaseOf` normalization.
3. `wPhaseOf_of_exp`: Inverse direction. Uses `arg_real_mul`, `arg_exp_mul_I`,
   `toIocMod_eq_self` from Mathlib.
4. `wPhaseOf_zero`, `wPhaseOf_neg`, `wPhaseOf_add_two`, `wPhaseOf_indep`: Structural
   lemmas specific to the `wPhaseOf` construction.

The `ForMathlib/` lemmas are genuinely new:
- `abs_sin_arg_le_norm_sub_one` (law-of-sines for arg): Not in Mathlib. This is a
  geometric inequality `|sin(arg z)| ≤ ‖z - 1‖` proved via `im² ≤ ‖z-1‖² · ‖z‖²`.
- `abs_arg_one_add_lt` (near-identity phase bound): Not in Mathlib. Combines the
  law-of-sines bound with monotonicity of sin.
- `norm_sum_exp_ge_cos_mul_sum` (sector norm bound): Not in Mathlib. This is the
  key geometric estimate for Lemma 6.2.
- `eq_of_pos_mul_exp_eq` (ray rigidity): Not in Mathlib.

**Verdict**: The `wPhaseOf` pure-complex lemmas do NOT reimplement `Complex.arg`
API. They correctly *use* the Mathlib API and build genuinely new results on top.
The `ForMathlib/` files are good candidates for Mathlib upstreaming as standalone
contributions to `Analysis.SpecialFunctions.Complex.Arg`.

### 2C. stabSeminorm: Overlap with Mathlib's Seminorm/operator-norm API

The stabSeminorm is `sup { ‖U(E)‖ / ‖Z(E)‖ : E σ-semistable, nonzero }`.

**Mathlib's `Seminorm 𝕜 E`** (`Mathlib.Analysis.Seminorm`):
```lean
structure Seminorm (𝕜 : Type) (E : Type) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    extends AddGroupSeminorm E where
  smul' : ∀ (a : 𝕜) (x : E), toFun (a • x) = ‖a‖ * toFun x
```
Requires: `toFun : E → ℝ` (not `ℝ≥0∞`), `map_zero'`, `add_le'`, `neg'`, `smul'`.

**`AddGroupSeminorm G`** (`Mathlib.Analysis.Normed.Group.Seminorm`):
```lean
structure AddGroupSeminorm (G : Type) [AddGroup G] where
  toFun : G → ℝ
  map_zero' : toFun 0 = 0
  add_le' : ∀ r s, toFun (r + s) ≤ toFun r + toFun s
  neg' : ∀ r, toFun (-r) = toFun r
```

The project already exploits this in `LocalHomeomorphism.lean`:
- `componentAddGroupNorm` constructs an `AddGroupNorm` (not just seminorm) on the
  subspace `V(σ)` by restricting `stabSeminorm` to finite-seminorm elements and
  projecting `.toReal`.
- `componentNormedAddCommGroup` gives `NormedAddCommGroup (V(σ))`.
- `componentNormedSpace` gives `NormedSpace ℂ (V(σ))`.

The gap: `stabSeminorm` on the *full* `K₀ C →+ ℂ` takes values in `ℝ≥0∞`, not `ℝ`.
Mathlib has no extended-real-valued seminorm type. The project works around this by
restricting to the finite-seminorm subspace.

**Verdict**: The project already bridges the gap correctly. `stabSeminorm` restricted
to `V(σ)` is registered as a `NormedAddCommGroup` / `NormedSpace`. There is no
additional Mathlib construction that would help. The `ℝ≥0∞`-valued seminorm on the
full space is a mild generalization that Mathlib could eventually support, but it is
not blocking anything.

---

## Phase 3: Mathematical Identity

### 3A. wPhaseOf: Standard name in complex analysis

`wPhaseOf w α = α + arg(w · exp(-iπα)) / π` is the **winding number / phase function
with branch cut at angle πα**, normalized to period 2.

In complex analysis, this is a variant of the **continuous argument** (or
**continuous log branch**) with branch cut on the ray `{r · exp(iπα) : r < 0}`.
The normalization by `π` converts from radians to "turns/2" (Bridgeland phases),
so that phase 1 corresponds to the negative real axis.

There is no single standard name for this exact construction. The closest standard
terminology:
- **"argument with branch cut at angle πα"**: standard in multi-valued function theory
- **"Bridgeland phase"**: the name used in the stability conditions literature
- **"normalized argument"**: when the division by π is emphasized

The `wPhaseOf_indep` theorem (independence of α when branch cuts are compatible)
is the standard fact that the continuous argument is locally independent of the
branch-cut choice.

**Verdict**: `wPhaseOf` is a standard construction with a domain-specific name.
It does not correspond to any single Mathlib definition. The name `wPhaseOf` is
appropriate for this project.

### 3B. stabSeminorm: Is it a Mathlib Seminorm?

The project proves:
1. `stabSeminorm_zero`: `‖0‖_σ = 0`
2. `stabSeminorm_add_le`: `‖U+V‖_σ ≤ ‖U‖_σ + ‖V‖_σ` (subadditivity)
3. `stabSeminorm_neg`: `‖-U‖_σ = ‖U‖_σ` (symmetry)
4. `stabSeminorm_smul_complex`: `‖t • U‖_σ = ‖t‖ · ‖U‖_σ` (absolute homogeneity)
5. `eq_zero_of_stabSeminorm_toReal_eq_zero`: finite `‖U‖_σ = 0 ⟹ U = 0` (definiteness)

Properties 1-4 are exactly the axioms of `Seminorm ℂ (K₀ C →+ ℂ)`, **except**
the codomain is `ℝ≥0∞` rather than `ℝ`.

On the subspace `V(σ) = {U : ‖U‖_σ < ⊤}`, the `.toReal` projection satisfies
all `Seminorm` axioms with codomain `ℝ`, plus definiteness (property 5), making
it a `Norm` (even stronger). **The project already constructs this**:
`componentAddGroupNorm` in `LocalHomeomorphism.lean` gives `AddGroupNorm` on
`V(σ)`, and `componentNormedSpace` gives `NormedSpace ℂ V(σ)`.

**Verdict**: `stabSeminorm` restricted to `V(σ)` is already registered as a norm.
There is nothing additional to do. Registering the `ℝ≥0∞`-valued version as a
Mathlib `Seminorm` would require extending Mathlib's seminorm theory to `ℝ≥0∞`,
which is a substantial Mathlib contribution orthogonal to this project.

### 3C. slicingDist: Is it a PseudoEMetricSpace?

The project proves:
1. `slicingDist_self`: `d(P, P) = 0`
2. `slicingDist_symm`: `d(P, Q) = d(Q, P)`
3. `slicingDist_triangle`: `d(P, R) ≤ d(P, Q) + d(Q, R)`

These are exactly the axioms of `PseudoEMetricSpace` (with `edist := slicingDist C`).
The codomain is already `ℝ≥0∞`, which is what `PseudoEMetricSpace` wants.

However, registering the instance requires filling the `toUniformSpace` and
`uniformity_edist` fields, which means defining the uniform structure on `Slicing C`
and proving it agrees with the edist-generated one. Currently, the Bridgeland
topology on `StabilityCondition C` is defined via `TopologicalSpace.generateFrom`
(basis neighborhoods), not via `slicingDist`. Registering `PseudoEMetricSpace`
on `Slicing C` alone would give a topology on slicings but not on stability
conditions (which additionally involve the seminorm on central charges).

**Verdict**: `slicingDist` satisfies `PseudoEMetricSpace` axioms. Registering
it is feasible and would unlock the `EMetricSpace` API (balls, Hausdorff distance,
etc.). The main question is whether the induced topology on `Slicing C` agrees with
the product component of the Bridgeland topology. This likely holds but is not
currently proved. Proposal below.

---

## Phase 4: Proposals

### Proposal A: K0Presentation factoring

**Status**: Propose (reaffirm existing proposal).

The proposal at `artifacts/generalizations/k0-presentation.md` is still valid and
needs no updating. It would deduplicate:
- 2x `*Subgroup` definitions
- 2x quotient type definitions
- 2x `AddCommGroup` instances
- 2x `of` maps
- 2x `of_rel` / `of_triangle` / `of_shortExact` proofs
- 3x `QuotientAddGroup.lift` universal-property proofs (K₀.lift, ZOnHeartK0, heartK0ToK0)

The shared `K0Presentation.lift` would also lay groundwork for `K₀.hom_ext`
(extensionality for morphisms out of K₀), which is currently missing and inlined
~5 times via `QuotientAddGroup.addMonoidHom_ext` + `FreeAbelianGroup.lift_ext`.

**Effort**: Small. Proof-copy from existing K₀ into the generic structure, then
rewire downstream consumers through `abbrev` wrappers.

### Proposal B: PseudoEMetricSpace on Slicing C

**Status**: Propose (conditional on topology agreement proof).

```lean
noncomputable instance Slicing.pseudoEMetricSpace :
    PseudoEMetricSpace (Slicing C) where
  edist := slicingDist C
  edist_self := slicingDist_self C
  edist_comm := slicingDist_symm C
  edist_triangle := slicingDist_triangle C
  toUniformSpace := ⟨...⟩  -- generated from edist
  uniformity_edist := ...   -- by definition
```

Using `PseudoEMetricSpace.mk` with the default uniform space (generated from
edist) avoids any topology-agreement question -- the uniform space is simply
*defined* to be the edist-generated one. The question then becomes whether
downstream code that uses the `TopologicalSpace.generateFrom`-based topology
can be migrated.

**Benefit**: Unlocks `EMetric.ball`, `ediam`, Cauchy sequence API, and Lipschitz
continuity framework for slicing maps.

**Risk**: The Bridgeland topology on `StabilityCondition C` is a *product* of
the slicing metric and the central-charge seminorm. Registering a
`PseudoEMetricSpace` on `Slicing C` gives a topology on slicings alone, not on
the full `StabilityCondition C`. The existing `generateFrom` topology couples both
components. A refactor to use a product topology `(Slicing metric) × (charge norm)`
would be cleaner but touches many files.

**Concrete code** (the instance itself is straightforward):

```lean
instance Slicing.instEDist : EDist (Slicing C) where
  edist := slicingDist C

noncomputable instance Slicing.instPseudoEMetricSpace :
    PseudoEMetricSpace (Slicing C) :=
  PseudoEMetricSpace.ofEDist (slicingDist_self C) (slicingDist_symm C)
    (slicingDist_triangle C)
```

Wait -- `PseudoEMetricSpace.ofEDist` does not exist in Mathlib. The actual
construction needs:

```lean
noncomputable instance Slicing.instPseudoEMetricSpace :
    PseudoEMetricSpace (Slicing C) where
  edist := slicingDist C
  edist_self s := slicingDist_self C s
  edist_comm s₁ s₂ := slicingDist_symm C s₁ s₂
  edist_triangle s₁ s₂ s₃ := slicingDist_triangle C s₁ s₂ s₃
  toUniformSpace := .ofDist (fun s₁ s₂ => (slicingDist C s₁ s₂).toReal) sorry sorry sorry
  uniformity_edist := sorry
```

The `toUniformSpace` and `uniformity_edist` fields require non-trivial work. The
simplest path is to use `UniformSpace.ofFun` or to simply not fill them and instead
use `PseudoEMetricSpace.mk'` if available, or to define them via the edist balls.

**Effort**: Medium. The three metric axioms are proved; the uniform-space plumbing
is the remaining work.

**Verdict**: Propose, but flag as medium-effort. The metric axioms are done; the
uniform space boilerplate is mechanical but touches Mathlib's metric space API.

### Proposal C: wPhaseOf ForMathlib lemmas as Mathlib PR

**Status**: Propose (for upstreaming, not internal refactoring).

The four files in `ForMathlib/Analysis/SpecialFunctions/Complex/` contain
pure-complex-analysis lemmas with no project dependencies:

1. `PhasePerturbation.lean`: `abs_arg_one_add_lt` and prerequisites -- near-identity
   argument bound useful for any perturbation theory.
2. `SectorBound.lean`: `norm_sum_exp_ge_cos_mul_sum` -- sector norm bound useful
   for any "sum of vectors in a cone" estimate.
3. `ArgConvexity.lean`: `arg_add_le_max`, `min_arg_le_arg_add` -- arg convexity for
   sums in the upper half plane.

These are genuine contributions to Mathlib's `Complex.arg` API. None of them
duplicate existing Mathlib lemmas. They should be upstreamed independently of
the Bridgeland project.

**Effort**: Small per file (clean, self-contained, Mathlib-importable).

**No code change needed in this project.** The proposal is about Mathlib PR, not
internal refactoring.

### Proposal D: wPhaseOf as a standalone definition

**Status**: Decline.

`wPhaseOf` is defined in `Deformation/WPhase.lean` inside the
`CategoryTheory.Triangulated` namespace, even though the definition and ~7 core
lemmas are pure complex analysis (no category dependency). Moving `wPhaseOf` to
`ForMathlib/` or a standalone file would be consistent with the existing `ForMathlib/`
pattern.

However:
- The definition is **project-specific**: the normalization `arg/π` and the branch
  cut `α` are tailored to Bridgeland stability. There is no natural Mathlib home.
- The category-free lemmas in WPhase.lean are already cleanly separated (inside an
  `omit [IsTriangulated C]` block). The file is well-organized.
- Moving them would create import churn with no functional benefit.

**Verdict**: Decline. The current organization is fine.

### Proposal E: stabSeminorm on PreStabilityCondition

**Status**: Decline (low priority).

The definition of `stabSeminorm` and its algebraic properties (`_zero`, `_neg`,
`_add_le`, `_smul`, `stabSeminorm_bound_real`) do not use `locallyFinite`. They
could technically take a `PreStabilityCondition` instead of `StabilityCondition`.

However:
- Every non-trivial theorem (`sector_bound`, seminorm comparison, deformation)
  requires `IsTriangulated` for HN filtrations, which in practice means the full
  stability condition.
- The `PreStabilityCondition` type is not used independently in the codebase; it
  exists only as the parent structure of `StabilityCondition`.
- Weakening the definition's hypothesis would require touching the 22 files that
  import `stabSeminorm`, for no downstream benefit.

**Verdict**: Decline. Correct observation, zero payoff.

---

## Summary Table

| Item | Proposal | Status | Effort |
|---|---|---|---|
| K0 / HeartK0 duplication | K0Presentation factoring | **Propose** (reaffirm) | Small |
| slicingDist metric | PseudoEMetricSpace instance | **Propose** (conditional) | Medium |
| ForMathlib complex lemmas | Mathlib upstreaming PR | **Propose** (external) | Small/file |
| wPhaseOf file reorganization | Move pure lemmas | **Decline** | -- |
| stabSeminorm on PreStab | Weaken hypothesis | **Decline** | -- |
| stabSeminorm as Mathlib Seminorm | Register ℝ≥0∞ seminorm | **Decline** (blocked by Mathlib) | -- |
| wPhaseOf Mathlib overlap | None (correctly uses Mathlib) | **No action** | -- |
