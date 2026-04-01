# Refactor Plan: Make `WithClassMap C v` Primary (Phase 1 — Defs.lean)

## Goal

Generalize `stabSeminorm`, `basisNhd`, and the topology instance from
`StabilityCondition C` to `WithClassMap C v`. This is the foundation
for the full refactor. `StabilityCondition C` (= `WithClassMap C id`)
becomes a specialization, not the primary type.

## Absolute Constraints

1. **NO BACKSLIDING.** Every proof that changes must become cleaner or
   stay the same. No elaboration hacks, no `maxHeartbeats`, no new
   `sorry`. If a proof gets harder, that is a signal to fix the
   abstraction, not to force the proof.

2. **No parallel definitions.** We do NOT add `stabSeminorm.WithClassMap`
   alongside `stabSeminorm`. We REPLACE `stabSeminorm` with the general
   version. The old name still works (it is the `v = id` case).

3. **No bridge code.** The topology on `WithClassMap C v` is defined
   directly, not induced. The existing induced topology becomes a lemma
   (`topologicalSpace_eq_induced`) for backwards compat, not the
   definition.

4. **Build and lint must pass** after every step. No "we'll fix it later."

## File: `StabilityCondition/Defs.lean`

### Current state (lines 134-206)

```
slicingDist          -- on Slicing C (v-independent, no change)
stabSeminorm         -- on StabilityCondition C, takes K₀ C →+ ℂ
basisNhd             -- on StabilityCondition C
topologicalSpace     -- on StabilityCondition C, via GenerateFrom
topologicalSpace     -- on WithClassMap C v, via induced
ComponentIndex       -- on WithClassMap C v (already general)
Component            -- on WithClassMap C v (already general)
CentralCharge...     -- on WithClassMap C v (already general)
```

### Target state

```
slicingDist          -- on Slicing C (unchanged)
stabSeminorm         -- on WithClassMap C v, takes Λ →+ ℂ     ← CHANGED
basisNhd             -- on WithClassMap C v                     ← CHANGED
topologicalSpace     -- on WithClassMap C v, via GenerateFrom   ← CHANGED
  (StabilityCondition C inherits as v = id case)
ComponentIndex       -- unchanged
Component            -- unchanged
CentralCharge...     -- unchanged
```

### Step 1: Generalize `stabSeminorm`

**Current:**
```lean
def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)
```

**New:**
```lean
def stabSeminorm {v : K₀ C →+ Λ} (σ : WithClassMap C v) (U : Λ →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (v (K₀.of C E))‖ / ‖σ.Z (v (K₀.of C E))‖)
```

**What changes:**
- `σ : StabilityCondition C` → `σ : WithClassMap C v` (general)
- `U : K₀ C →+ ℂ` → `U : Λ →+ ℂ` (charge on the class lattice)
- `U (K₀.of C E)` → `U (v (K₀.of C E))` (apply class map first)
- `σ.Z (K₀.of C E)` → `σ.Z (v (K₀.of C E))` (class-map charge applied to class)

**When `v = id`:** `v (K₀.of C E) = K₀.of C E`, so the formula is identical.
`Λ = K₀ C`, so `U : K₀ C →+ ℂ` and `σ.Z : K₀ C →+ ℂ` as before.

**Impact on Seminorm.lean:** Every theorem about `stabSeminorm` needs the
same generalization. The proofs should be identical — they manipulate
`‖U (...)‖ / ‖σ.Z (...)‖` abstractly, and the `v (K₀.of C E)` vs
`K₀.of C E` distinction doesn't affect the algebraic/analytic reasoning.

**Risk:** LOW. The change is syntactic in the definition. The risk is in
downstream theorems where `K₀.of C E` is used as a key for rewriting —
we need to check that `v (K₀.of C E)` works the same way.

### Step 2: Generalize `basisNhd`

**Current:**
```lean
def basisNhd (σ : StabilityCondition C) (ε : ℝ) : Set (StabilityCondition C) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}
```

**New:**
```lean
def basisNhd {v : K₀ C →+ Λ} (σ : WithClassMap C v) (ε : ℝ) :
    Set (WithClassMap C v) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}
```

**What changes:**
- `σ : StabilityCondition C` → `σ : WithClassMap C v`
- `Set (StabilityCondition C)` → `Set (WithClassMap C v)`
- `τ.Z - σ.Z` is now `Λ →+ ℂ` (was `K₀ C →+ ℂ`)
- `stabSeminorm` is now the generalized version (Step 1)
- `slicingDist` is unchanged (works on slicings)

**Risk:** LOW. Direct consequence of Step 1.

### Step 3: Replace the topology

**Current:** Two definitions:
```lean
-- Direct topology on StabilityCondition C
instance StabilityCondition.topologicalSpace :
    TopologicalSpace (StabilityCondition C) :=
  TopologicalSpace.generateFrom
    {U | ∃ (σ : StabilityCondition C) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧
      U = basisNhd C σ ε}

-- Induced topology on WithClassMap C v
abbrev WithClassMap.topologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (WithClassMap C v) :=
  TopologicalSpace.induced toStabilityCondition inferInstance
```

**New:** One definition:
```lean
-- Direct topology on WithClassMap C v (the BLMNPS topology)
instance WithClassMap.topologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (WithClassMap C v) :=
  TopologicalSpace.generateFrom
    {U | ∃ (σ : WithClassMap C v) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧
      U = basisNhd C σ ε}
```

`StabilityCondition.topologicalSpace` is now just the `v = id` case —
no separate definition needed, it's an instance of the above.

**Backwards compat lemma (add, don't block on):**
```lean
theorem WithClassMap.topologicalSpace_eq_induced [Function.Surjective v] :
    (WithClassMap.topologicalSpace : TopologicalSpace (WithClassMap C v)) =
      TopologicalSpace.induced toStabilityCondition
        (StabilityCondition.topologicalSpace (C := C))
```

This is NOT needed for the refactor to proceed — it's a mathematical
fact for later. The existing downstream proofs use `GenerateFrom` /
`GenerateOpen.basic` directly, not `isOpen_induced_iff`, so they should
work with the new definition.

**Risk:** MEDIUM. This is the most impactful change. Proofs that
previously used `isOpen_induced_iff` to move between `WithClassMap C v`
opens and `StabilityCondition C` opens need to change. But these proofs
are in LocalHomeomorphism.lean (Phase 3 of the full refactor), not in
Defs.lean or Seminorm.lean.

### Step 4: Delete the induced topology

Remove:
```lean
abbrev topologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  TopologicalSpace.induced
    (StabilityCondition.WithClassMap.toStabilityCondition (C := C) (v := v))
    inferInstance

instance (priority := 100) instTopologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  StabilityCondition.WithClassMap.topologicalSpace (C := C) (v := v)
```

Replace with the direct topology from Step 3. No `priority` hack needed.

### Step 5: Verify `stabilityCondition_compat_apply` still works

```lean
theorem stabilityCondition_compat_apply (σ : StabilityCondition C)
    (φ : ℝ) (E : C) (hE : σ.slicing.P φ E) (hNZ : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      σ.Z (K₀.of C E) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) := by
  simpa using σ.compat φ E hE hNZ
```

Here `σ : StabilityCondition C = WithClassMap C id`, so `σ.Z : K₀ C →+ ℂ`
and `σ.Z (K₀.of C E)` = `σ.Z (id (K₀.of C E))`. The `simpa` might need
`AddMonoidHom.id_apply` or it might reduce definitionally. Check.

### Step 6: Verify `CentralChargeIsLocalHomeomorphOnConnectedComponents` unchanged

This definition (lines 192-202) is already parameterized by `v`. It uses
`σ.Z : Λ →+ ℂ` and `Component C v cc`. It should require NO changes.
But verify that the topology it references is now the direct topology
from Step 3.

## Verification Protocol

After completing Steps 1-6:

1. `lake build BridgelandStability.StabilityCondition.Defs` must succeed
2. `lake build BridgelandStability.StabilityCondition.Seminorm` — expect
   failures. Catalog every failure. Each one is a theorem in Seminorm.lean
   that needs the same generalization. These are Phase 2 of the refactor.
3. Do NOT proceed to fix Seminorm.lean in this phase. The goal of Phase 1
   is to get Defs.lean clean and to understand the blast radius.

## Proof Quality Checklist

For every proof touched:
- [ ] Does it use fewer tactics than before? (or the same)
- [ ] Does it avoid `change` / `show` / explicit type annotations that
      weren't there before?
- [ ] Does it elaborate in ≤ heartbeats as before?
- [ ] Does it avoid any `.toStabilityCondition` coercion?

If any of these fail, STOP and reassess the abstraction. The proof
getting worse means the types are wrong, not that the proof needs forcing.

## What NOT to Do

- Do NOT add `toStabilityCondition` coercions anywhere. The whole point
  is to eliminate them.
- Do NOT add `@[simp] theorem v_id_apply ...` lemmas to paper over
  the generalization. If `v = id` doesn't reduce cleanly, the
  definition is wrong.
- Do NOT add universe annotations or explicit type ascriptions that
  weren't needed before. If elaboration needs them, the types are wrong.
- Do NOT touch any file other than Defs.lean in this phase.
