# Agent Guidelines for BridgelandStability

## Build & Lint Workflow

Always run these three steps in order before committing:

```bash
lake exe cache get                # fetch Mathlib cached oleans (skip if already cached)
lake build BridgelandStability    # build only our project, not all of Mathlib
lake exe runLinter                # the actual Mathlib declaration linter
```

- **Never** run bare `lake build` — it rebuilds Mathlib from source (~30+ min).
- **`lake exe runLinter`** is the linter. Not build warnings. Not `lake exe lint-style`.
- After `lake update`, always re-run `lake exe cache get`.

## Tactic Selection

- **`lia`** for all Nat/Fin/Int linear arithmetic (bounds, equalities from negation, etc.).
  Never use `omega`. The codebase is `omega`-free and should stay that way.
- **`grind`** is powerful but expensive in category-theoretic contexts. A single `grind` on
  a Fin/Nat goal can consume 100M+ heartbeats exploring irrelevant Subobject/Functor context.
  Use `lia` instead for arithmetic goals.
- **`linarith`** for ℝ/ℚ linear arithmetic. Don't use `grind` for these either.

## Diagnosing Heartbeat Issues

Use Lean's built-in profiler — never guess:

```lean
set_option trace.profiler true in
set_option trace.profiler.useHeartbeats true in
set_option trace.profiler.threshold 5000 in
theorem my_slow_theorem ...
```

Read the output, find the expensive tactic, replace it with something targeted.
Remove the profiler options before committing.

`set_option diagnostics true in` shows unfolding counts and instance resolution stats —
useful for understanding why type class synthesis is slow.

## No Elaboration Hacks

Don't ship workarounds for slow proofs:

- No `set_option maxHeartbeats` bumps
- No `field := ?_` placeholder splits to force independent elaboration
- No blind tactic substitutions without profiling

If you can't eliminate a heartbeat bump, you haven't found the root cause yet.
Profile first, fix the actual expensive tactic.
