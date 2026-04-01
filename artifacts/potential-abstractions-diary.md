# Potential Abstractions Diary

Running log of abstractions considered during the WithClassMap refactor.
When breakage is encountered, ask: would a new abstraction help? If not
used immediately, record here with context for later review.

---

## Entry 1: Charge application patterns (2026-04-01)

**Trigger:** Generalizing Deformation/ from `StabilityCondition C` to
`WithClassMap C v` requires 75 proof changes: `σ.Z (K₀.of C E)` →
`σ.Z (v (K₀.of C E))`.

**Decision:** Proceed with mechanical `v` insertion. Revisit after
the refactor stabilizes.

### Context

When generalizing the Deformation/ directory from `StabilityCondition C`
(= `WithClassMap C id`) to `WithClassMap C v`, 75 proof-internal occurrences
of `σ.Z (K₀.of C E)` must become `σ.Z (v (K₀.of C E))`. These all compute
"the charge of object E" in various contexts.

The mechanical `v` insertion is correct and makes the class-map dependency
explicit. But two potential abstractions may be worth revisiting once the
refactor stabilizes.

## B: `chargeOf` — the charge of an object

```lean
/-- The central charge evaluated at the class of `E`. This is the
composition `Z ∘ v ∘ K₀.of`, written as a single application. -/
def StabilityCondition.WithClassMap.chargeOf {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) (E : C) : ℂ :=
  σ.Z (v (K₀.of C E))
```

**Pros:**
- Matches mathematical notation: papers write `Z(E)` or `Z([E])`,
  eliding the class map
- Shorter: `σ.chargeOf C E` vs `σ.Z (v (K₀.of C E))`
- At `v = id`: `σ.chargeOf C E = σ.Z (K₀.of C E)` definitionally
- Provides a natural API surface for simp lemmas about charges

**Needed API:**
```lean
@[simp] theorem chargeOf_def : σ.chargeOf C E = σ.Z (v (K₀.of C E)) := rfl

theorem chargeOf_isZero (hE : IsZero E) : σ.chargeOf C E = 0

theorem chargeOf_triangle {X E Y : C} {f : X ⟶ E} {g : E ⟶ Y}
    {h : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C) :
    σ.chargeOf C E = σ.chargeOf C X + σ.chargeOf C Y

theorem chargeOf_compat (hP : σ.slicing.P φ E) (hNZ : ¬IsZero E) :
    ∃ m > 0, σ.chargeOf C E = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)
```

**Cons:**
- Adds a definition layer; proofs may need `simp [chargeOf]` or
  `unfold chargeOf` in some contexts
- The 75 occurrences don't reduce — same number of changes either way
- Risk of elaboration issues if Lean doesn't unfold `chargeOf` when needed

**When to revisit:** After the mechanical refactor lands and the deformation
proofs are stable at general `v`. If `σ.Z (v (K₀.of C E))` feels verbose
in practice, introduce `chargeOf` as a follow-up.

## C: Domain-specific helpers for repeated charge computations

Several proof patterns appear repeatedly across the 75 occurrences:

### C1: Rotated imaginary part

```lean
/-- The imaginary part of the charge of `E`, rotated by phase `φ`. -/
def StabilityCondition.WithClassMap.rotatedIm {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) (E : C) (φ : ℝ) : ℝ :=
  (σ.Z (v (K₀.of C E)) * Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im
```

Used in: IntervalAbelian.lean (im_Z_nonpos_of_heart_phases and variants),
BoundaryTriangle.lean, TStructure.lean. The pattern `(σ.Z (v (K₀.of C E)) *
exp(-iπφ)).im` appears ~15 times.

**Key lemma (already exists):** `im_ofReal_mul_exp_mul_exp_neg` shows that for
semistable E of phase ψ, `rotatedIm σ E φ = m * sin(π(ψ - φ))`.

A `rotatedIm` definition would let the proofs work with `σ.rotatedIm C E φ`
and its sign properties, rather than repeatedly setting up the exp computation.

### C2: Charge norm

```lean
/-- The norm of the charge of `E`. -/
def StabilityCondition.WithClassMap.chargeNorm {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) (E : C) : ℝ :=
  ‖σ.Z (v (K₀.of C E))‖
```

Used in: stabSeminorm comparisons, sector bound arguments. The pattern
`‖σ.Z (v (K₀.of C E))‖` appears ~10 times.

### C3: Charge additivity from triangles

The pattern "decompose σ.Z([E]) as a sum over HN factors using the
K₀ triangle relation and additivity of Z" appears in ~8 proofs. Currently
each proof manually applies `map_add` / `map_sum` and the K₀ relation.
A dedicated lemma could absorb this.

```lean
theorem chargeOf_eq_sum_factors (σ : WithClassMap C v) (F : HNFiltration C σ.slicing.P E) :
    σ.chargeOf C E = ∑ i : Fin F.n, σ.chargeOf C (F.factor i)
```

This would eliminate repeated `have hsum := ...` + `map_sum` blocks.

**When to revisit:** After the refactor. If the deformation proofs feel
repetitive in their charge-decomposition arguments, these helpers would
reduce boilerplate. But adding them during the refactor risks scope creep.

---

## Entry 2: K₀ → Λ additivity chain (2026-04-01)

**Trigger:** After mechanical generalization, 38 errors remain in
IntervalAbelian.lean and WPhase.lean. Three patterns:

1. **`map_sum` needs two steps:** `K₀.of_postnikovTower_eq_sum` gives a
   sum in `K₀ C`. Then `v.map_sum` lifts to `Λ`. Then `σ.Z.map_sum` lifts
   to `ℂ`. The old code had one `map_sum` (σ.Z composed directly on K₀).
   Now needs `v.map_sum` then `σ.Z.map_sum`, or a combined lemma.

2. **`K₀.of_isZero` needs `map_zero`:** `K₀.of_isZero C hi` gives
   `K₀.of C E = 0` in `K₀ C`. Then `v.map_zero` gives `v (K₀.of C E) = 0`.
   Simp calls need `[K₀.of_isZero C hi, map_zero]`.

3. **`stabilityCondition_compat_apply` → `σ.compat`:** The v=id helper
   doesn't exist at general v. Use `σ.compat` directly (same content).

**Potential abstraction (connects to C3 above):** A `chargeOf_eq_sum_factors`
lemma would absorb pattern 1. A `chargeOf_isZero` lemma would absorb pattern 2.
These are exactly the API sketched in Entry 1, section C.

**Decision:** SUPERSEDED by Entry 3 below.

---

## Entry 3: `cl` — the class map to Λ (2026-04-01)

**Trigger:** After attempting the mechanical `v` insertion (1000+ changes of
`K₀.of C E` → `v (K₀.of C E)`), we realized this is LOCAL OPTIMIZATION,
not the right abstraction. The proofs become MORE verbose (longer expressions,
double `map_sum`, `K₀.of_isZero + map_zero` chains). That violates the ethos.

**The insight:** In the math, `v([E])` is a single operation — "the class of
E in Λ." The proofs shouldn't decompose it into "take the K₀ class, then
apply v." The composition `v ∘ K₀.of C` should be a named operation.

### The abstraction: `cl`

```lean
/-- The class of an object `E` in the target lattice `Λ`, via the class
map `v : K₀(C) → Λ`. This is the composition `v ∘ K₀.of C`.

At `v = id`: `cl v E = K₀.of C E` definitionally. -/
abbrev cl (v : K₀ C →+ Λ) (E : C) : Λ := v (K₀.of C E)
```

**Why `abbrev`:** We're still testing whether the abstraction earns its keep.
`abbrev` means `cl v E` and `v (K₀.of C E)` are interchangeable — existing
proofs don't break, the `cl_*` lemmas are convenient shortcuts not mandatory
rewrites. Can tighten to `def` later if the API proves sufficient.

**Where it lives:** `GrothendieckGroup/Basic.lean`, right after the `K₀.of`
lemmas. This is about the K₀ class map, not about stability conditions.

### Required API (mirrors the K₀.of API, lifted through v)

Each lemma absorbs the `v.map_*` step that currently requires manual
insertion:

| `cl` lemma | K₀ lemma it lifts | Usage count in Deformation/ | What it absorbs |
|---|---|---|---|
| `cl_isZero` | `K₀.of_isZero` + `map_zero` | 12 | Two-step simp → one |
| `cl_triangle` | `K₀.of_triangle` + `map_add` | 9 | Two `map_add` → one lemma |
| `cl_iso` | `K₀.of_iso` + `congr` | 42 | Explicit congr → one lemma |
| `cl_postnikovTower_eq_sum` | `K₀.of_postnikovTower_eq_sum` + `map_sum` | 10 | Two `map_sum` → one lemma |
| `cl_shift_one` | `K₀.of_shift_one` + `map_neg` | 6 | Two steps → one |
| `cl_shift_neg_one` | `K₀.of_shift_neg_one` + `map_neg` | 1 | Two steps → one |

```lean
@[simp] lemma cl_isZero {E : C} (hE : IsZero E) : cl v E = 0 := by
  simp [cl, K₀.of_isZero C hE, map_zero]

lemma cl_triangle {T : Triangle C} (hT : T ∈ distTriang C) :
    cl v T.obj₂ = cl v T.obj₁ + cl v T.obj₃ := by
  simp [cl, K₀.of_triangle C T hT, map_add]

lemma cl_iso {X Y : C} (e : X ≅ Y) : cl v X = cl v Y := by
  simp [cl, K₀.of_iso C e]

theorem cl_postnikovTower_eq_sum {E : C} (P : PostnikovTower C E) :
    cl v E = ∑ i : Fin P.n, cl v (P.factor i) := by
  simp [cl, K₀.of_postnikovTower_eq_sum C P, map_sum]

@[simp] lemma cl_shift_one (E : C) :
    cl v (E⟦(1 : ℤ)⟧) = -cl v E := by
  simp [cl]

@[simp] lemma cl_shift_neg_one (E : C) :
    cl v (E⟦(-1 : ℤ)⟧) = -cl v E := by
  simp [cl]
```

### How this changes the refactor

With `cl`, the Deformation/ generalization becomes:

- `σ.Z (K₀.of C E)` → `σ.Z (cl v E)` (shorter, not longer)
- `rw [K₀.of_triangle, map_add, map_add]` → `rw [cl_triangle hT]` (one step, not three)
- `simp [K₀.of_isZero C hi, map_zero]` → `simp [cl_isZero hi]` (one lemma, not two)
- `rw [K₀.of_postnikovTower_eq_sum, map_sum, map_sum]` → `rw [cl_postnikovTower_eq_sum P]`

The 30 remaining errors in IntervalAbelian.lean and WPhase.lean (from Entry 2)
would likely resolve because they were all about the double-map chain.

### How `stabSeminorm` reads with `cl`

```lean
def stabSeminorm {v : K₀ C →+ Λ} (σ : WithClassMap C v) (U : Λ →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (cl v E)‖ / ‖σ.Z (cl v E)‖)
```

### Why NOT `chargeOf` (Entry 1B) yet

`σ.Z (cl v E)` reads as "the charge Z applied to the class of E" — this
matches the mathematical notation `Z([E])` closely enough. A separate
`chargeOf` would add another layer without clear benefit. If after the
refactor `σ.Z (cl v E)` feels verbose, introduce `chargeOf` then.

### Decision

**Introduce `cl` in GrothendieckGroup/Basic.lean BEFORE continuing the
Deformation/ generalization.** Build the API. Then return to the proofs
with the new tool. This replaces the mechanical `v` insertion approach
(Entry 1A / Entry 2) with a cleaner abstraction.

---

## Entry 4: `SkewedStabilityFunction` at the Λ level (2026-04-01)

**Trigger:** Generalizing Deformation/ to `WithClassMap C v` created a type
conflict at the `SkewedStabilityFunction` boundary. The SSF stored
`W : K₀ C →+ ℂ`, but the generalized seminorm/charge code operates at
`W : Λ →+ ℂ`. Callers of `wPhaseOf_gt/lt_of_intervalProp` had `ssf.W : K₀ C →+ ℂ`
where `Λ →+ ℂ` was expected.

**The question:** Should `SkewedStabilityFunction` store `W : Λ →+ ℂ` or
`W : K₀ C →+ ℂ`?

**Resolution from the source math:** Bridgeland's deformation theorem
(Section 7) starts with `W : Λ → ℂ` — a charge on the lattice. The W-phase
of an object `E` is `arg(W(v[E]))/π = arg(W(cl v E))/π`. The stability
function on the interval category is `W ∘ v : K₀(C) → ℂ`, derived from `W`.

The SSF is the derived stability function from the charge `W`. Storing
`W : Λ →+ ℂ` is correct — it's the charge, and `W(cl v E)` is how the
math evaluates it. The K₀-level map `W ∘ v` is a consequence, not the
primary data.

**Decision:** Generalize `SkewedStabilityFunction` (in `IntervalCategory/FiniteLength.lean`)
to store `W : Λ →+ ℂ` and parameterize by `v`. All internal uses of
`ssf.W (K₀.of C E)` become `ssf.W (cl C v E)`.

**What changed:**
- `SkewedStabilityFunction` gains `v` parameter, `W` field becomes `Λ →+ ℂ`
- `strict_additive` proof needs `simp only [cl, ...]` instead of `rw [K0_of_strictShortExact, map_add]`
  (K₀ lemma result at K₀ level, goal at Λ level — `cl` bridges the gap)
- `skewedStabilityFunction_of_near` passes `W` directly (was `W.comp v`)
- ~664 `ssf.W (K₀.of C E)` → `ssf.W (cl C v E)` in Deformation/

---

## Entry 5: `cl_id` simp lemma for v=id normalization (2026-04-01)

**Trigger:** After generalizing `Seminorm.lean`, downstream v=id code
(WPhase.lean, PhaseArithmetic.lean) saw `cl C (AddMonoidHom.id (K₀ C)) E`
in hypotheses from `stabSeminorm_bound_real`, but proofs expected `K₀.of C E`.
`rw` couldn't match because `AddMonoidHom.id` is a `def` and doesn't reduce.

**Resolution:** Added `@[simp] lemma cl_id : cl C (AddMonoidHom.id (K₀ C)) E = K₀.of C E := rfl`
in `GrothendieckGroup/Basic.lean`. Temporary `simp only [cl_id] at hbd`
fixes in WPhase and PhaseArithmetic. These were removed when those files
were generalized to general `v` (the `cl_id` pattern only arises at v=id).

**Decision:** `cl_id` is the permanent solution for v=id normalization.
The temporary call-site patches were correctly removed during generalization.

---

## Entry 6: Surjectivity barrier for ConnectedComponent/LocalHomeomorphism (2026-04-01)

**Trigger:** Attempting to generalize ConnectedComponent.lean to `WithClassMap C v`.
The theorem `eq_zero_of_stabSeminorm_toReal_eq_zero` claims `‖U‖_σ = 0 ⟹ U = 0`
for `U : Λ →+ ℂ`. At general `v`, the seminorm only tests `U` on `im(v)` —
we get `U ∘ v = 0` but not `U = 0` unless `v` is surjective.

**Mathematical analysis:** The seminorm `‖U‖_σ = sup |U(cl v E)| / |Z(cl v E)|`
over semistable `E`. If this is zero, `U(v(K₀.of C E)) = 0` for all semistable `E`.
By K₀ generation, `U ∘ v = 0`. This only implies `U = 0` if `v` is surjective.

In the literature, the manifold theorem assumes finite-rank `Λ` and `v` is always
surjective (e.g., `numericalQuotientMap k C` is surjective by definition). So the
issue only matters at the generality level.

**Affected theorems:**
- `eq_zero_of_stabSeminorm_toReal_eq_zero`: needs `Surjective v` or conclusion `U.comp v = 0`
- `finiteSeminormSubgroup` is a subgroup of `Hom(Λ, ℂ)` — at general `v`, only
  detects the image of `precomposeClassMap`
- The norm on `V(Σ)` requires surjectivity to be a norm (vs seminorm)

**Initial decision:** Defer — keep at v=id.

**Correction (same session):** The user pointed out that surjectivity is ALWAYS
present at every call site (`id` is surjective; `numericalQuotientMap` is surjective).
The "barrier" was an illusion — it's just an extra hypothesis, not an obstruction.

**Revised decision:** Generalize with `[Fact (Function.Surjective v)]`. The `Fact`
wrapper makes surjectivity available to typeclass synthesis (needed for the norm
instances). At `v = id`, `Fact.mk Function.surjective_id` provides it. At
`v = numericalQuotientMap`, the quotient surjectivity provides it.

**Lesson:** When a generalization seems blocked by a hypothesis, check whether
the hypothesis is always available at the call sites. If it is, the
"barrier" is just an API surface question, not a mathematical one.

## Overall status

- Entry 1A (mechanical `v` insertion): SUPERSEDED by Entry 3
- Entry 1B (`chargeOf`): DEFERRED — `σ.Z (cl v E)` is clean enough for now
- Entry 1C (rotatedIm, chargeNorm, chargeOf_eq_sum_factors): DEFERRED —
  C3 (sum over factors) is partially absorbed by `cl_postnikovTower_eq_sum`
- Entry 2 (K₀→Λ additivity chain): RESOLVED by Entry 3
- Entry 3 (`cl`): DONE — implemented, earning its keep across Deformation/
- Entry 4 (`SkewedStabilityFunction` at Λ): DONE — matches source math
- Entry 5 (`cl_id`): DONE — permanent v=id normalization
- Entry 6 (surjectivity for norm tower): DONE — `[Fact (Function.Surjective v)]`
  carries surjectivity through instances. Initial "barrier" was illusory.
