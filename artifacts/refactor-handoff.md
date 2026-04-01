# Refactor Handoff: WithClassMap C v Primary

## Read first
- `artifacts/refactor-withclassmap-primary.md` — master plan (math, ethos, phases)
- `artifacts/potential-abstractions-diary.md` — `cl` abstraction design (Entry 3)
- `AGENTS.md` — project conventions

## Branch state

Branch: `refactor/withclassmap-primary`, 7 commits ahead of main.

### Files done (committed, clean build)

| File | What changed |
|---|---|
| `StabilityCondition/Defs.lean` | `stabSeminorm`, `basisNhd`, topology generalized to `WithClassMap C v`. Two topology defs → one. |
| `GrothendieckGroup/Basic.lean` | Added `cl v E := v (K₀.of C E)` with API: `cl_isZero`, `cl_triangle`, `cl_iso`, `cl_shift_one`, `cl_shift_neg_one`, `cl_postnikovTower_eq_sum`. |
| `StabilityCondition/Basic.lean` | Generalized signatures. Fixed namespace `StabilityCondition.phase_eq_of_same_Z` → `WithClassMap.phase_eq_of_same_Z`. |
| `StabilityCondition/Seminorm.lean` | Fully generalized (13 signatures, 10 charge types, 71 K₀.of → cl). Proofs got shorter via `cl` API. |

### Files in progress (stashed with `git stash`)

**`StabilityCondition/Topology.lean`** — 9 errors remaining:
- 5 `cl_isZero` application failures — the `cl_postnikovTower_eq_sum C v _`
  rewrite upstream leaves `sorry` in goals, causing downstream `cl_isZero`
  to fail. Fix: use explicit PostnikovTower argument instead of `_`.
- 2 namespace fixes still needed for dot notation
- 2 errors at the end of the file (lines 707, 711) — the v=id duplicate
  `StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents`
  Prop, which should be DELETED per the plan.

**`Deformation/` (24 files)** — all signatures generalized, charge types
replaced, `K₀.of C` → `v (K₀.of C` (not yet `cl`). 30 errors remaining
in IntervalAbelian.lean (17) and WPhase.lean (13). Errors are:
- `K₀.of_postnikovTower_eq_sum` rewrites not finding pattern (need `cl_postnikovTower_eq_sum`)
- `K₀.of_isZero` + `map_zero` chains (need `cl_isZero`)
- `stabilityCondition_compat_apply` → `σ.compat` (some not yet fixed)
- Namespace dot-notation failures (declarations still in `StabilityCondition.` namespace)

**Note:** The Deformation/ stash used raw `v (K₀.of C E)` not `cl C v E`.
When resuming, consider re-doing with `cl` from the start (as done in
Seminorm.lean) rather than patching the stashed version.

### Files not yet touched

- `StabilityCondition/Deformation.lean` (the wrapper file — 850 lines)
- `StabilityCondition/ConnectedComponent.lean`
- `StabilityCondition/LocalHomeomorphism.lean`
- `NumericalStabilityManifold.lean` (the big payoff — ~400 lines to delete)
- `NumericalStability/Defs.lean`, `NumericalStability/Basic.lean`
- `EulerForm/Basic.lean`

### Known issues

1. **`continuous_toStabilityCondition`** in Topology.lean has a `sorry`.
   All consumers are bridge code slated for deletion. Likely becomes
   unnecessary after Phase 3. If needed, move to Deformation.lean where
   `basisNhd_mono` etc. are available for the proof.

2. **`NumericalStabilityManifold.lean:79`** — the one pre-existing error
   from Phase 1. Bridge code that should be deleted, not fixed.

## The mechanical recipe for generalizing a file

Apply in this order:

### 1. Section variables
```bash
# Add universe u' if needed
sed -i 's/^universe v u$/universe v u u'\''/' FILE

# Add variable block after [IsTriangulated C] or [Pretriangulated C]
# (check which the file uses — Deformation/ uses IsTriangulated,
#  Seminorm.lean uses only Pretriangulated)
sed -i '/\[IsTriangulated C\]$/a variable {Λ : Type u'\''} [AddCommGroup Λ] {v : K₀ C →+ Λ}' FILE
```

### 2. Type signatures
```bash
sed -i 's/StabilityCondition C/StabilityCondition.WithClassMap C v/g' FILE
sed -i 's/K₀ C →+ ℂ/Λ →+ ℂ/g' FILE
```

### 3. Charge applications (use `cl`, not raw `v`)
```bash
sed -i 's/(K₀\.of C /(cl C v /g' FILE
```

### 4. Compat helper
```bash
sed -i 's/stabilityCondition_compat_apply (C := C) σ/σ.compat/g' FILE
sed -i 's/stabilityCondition_compat_apply (C := C) τ/τ.compat/g' FILE
```

### 5. K₀ lemma chains → cl API
```
rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  → rw [cl_postnikovTower_eq_sum C v P, map_sum]

rw [K₀.of_isZero C hi, map_zero, zero_mul]
  → rw [cl_isZero (v := v) hi, zero_mul]

rw [K₀.of_triangle C T hT, map_add]
  → rw [cl_triangle C v T hT, map_add]

simp [K₀.of_isZero C hi]
  → simp [cl_isZero (v := v) hi]
```

### 6. Namespace fixes for dot notation
Declarations like `StabilityCondition.X` where X is used via dot
notation on `σ : WithClassMap C v` need the prefix changed to
`StabilityCondition.WithClassMap.X`. Check each file for:
```bash
grep -n 'theorem StabilityCondition\.\|def StabilityCondition\.' FILE | grep -v 'WithClassMap'
```

### 7. Build and fix remaining errors
```bash
lake build MODULE_NAME 2>&1 | grep '^error:'
```
Read each error. Most fall into the patterns above. If a genuinely new
pattern appears, record it in `artifacts/potential-abstractions-diary.md`
before fixing.

## Ethos reminder

- The metric is SIMPLIFICATION. If a change makes code longer or harder
  to read, the abstraction is wrong.
- No local optimizations. If a proof breaks, understand WHY.
- No bridge code. No `toStabilityCondition` in new code.
- The `cl` API should make proofs SHORTER (one lemma replacing two-step
  chains). If it doesn't, the API is incomplete — add a lemma.
- Record potential abstractions in the diary before deciding.
