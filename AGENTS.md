# Agent Guidelines for BridgelandStability

## Mathematical Fidelity

**The paper or book being formalized is the source of truth.** Never weaken a
definition to make a proof easier. If the proof needs a stronger hypothesis than
the paper, the proof strategy is wrong.

## Commit Provenance

- Commit messages must describe what actually happened and why.
- If local history contains a misleading docs/provenance commit, rewrite it locally instead of
  stacking a misleading revert on top.
- AI-assisted commits should record truthful provenance in the commit body or footer.

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

## Lint Cleanup

Treat linter failures as declaration/interface problems first. No `nolint
docBlame` or proof rewrites just to satisfy `unusedArguments`. Hidden unused
args often come from file-wide section variables or typeclass scope — fix the
boundary, not the proof. Keep proof edits trivial during cleanup.

## Naming & API Design

Names describe mathematical content, not bibliographic provenance.
`localHomeomorphismOfCentralCharge`, not `bridgelandTheorem_1_2`. Before
renaming public APIs, check 5-10 nearest Mathlib implementations for precedent.
See `artifacts/mathlib-naming-notes.md`.

## Reporting & Documentation

Include actual declarations and proposed text in audits — not just file paths
and line numbers. For Bridgeland theorem statements, prefer paper-faithful
quotation over paraphrase. Write audit notes to `artifacts/`.
