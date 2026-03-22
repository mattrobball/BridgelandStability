# `grind` Migration Report — Bridgeland Stability Project

**Date**: 2026-03-22
**Lean toolchain**: v4.29.0-rc6
**Scope**: 68 files, ~37K lines, formalization of Bridgeland stability conditions on triangulated categories

## Summary

Migrated **1,340 of 2,281** arithmetic tactic calls (59%) from `omega`/`linarith`/`nlinarith`/`ring`/`norm_num` to `grind`. The remaining 779 calls are blocked by two root causes: **grind timeouts in large proof contexts** (626 calls across 12 files) and **nonlinear arithmetic** (153 `nlinarith` calls).

| Tactic | Before | After | Converted |
|--------|--------|-------|-----------|
| `omega` | 1,023 | 63 | **94%** |
| `linarith` | 927 | 491 | 47% |
| `nlinarith` | 169 | 153 | 9% |
| `ring` | 129 | ~70 | ~46% |
| `norm_num` | 33 | 2 | 94% |

## What worked well

**Pattern 1: Standalone arithmetic** — `by omega`, `by linarith`, `by ring`, `by norm_num` in term-mode positions. These convert to `by grind` with zero issues. ~960 conversions.

```lean
-- Before                              -- After
Fin.ext (by omega)                     Fin.ext (by grind)
congrArg F.chain (by omega)            congrArg F.chain (by grind)
⟨by linarith, by linarith⟩            ⟨by grind, by grind⟩
_ = b := by ring                       _ = b := by grind
```

**Pattern 2: `simp` + arithmetic combos** — `simp [...]; omega` and `dsimp [...]; linarith` replaced by `simp [...]; grind` or just `grind`. ~50 conversions.

```lean
-- Before                                    -- After
congr 1; ext; simp; omega                    congr 1; ext; grind
dsimp only [HNFiltration.phiPlus]; linarith  dsimp only [HNFiltration.phiPlus]; grind
simp [a, b]; linarith                        simp [a, b]; grind
```

**Pattern 3: `linarith [computed_expr]` → `grind [computed_expr]`** — grind accepts E-matching theorems via `[...]` syntax, which serves the same purpose as linarith's hypothesis hints. ~90 conversions.

```lean
-- Before                              -- After
linarith [F.hφ hij]                    grind [F.hφ hij]
linarith [(hI ⟨0, hn⟩).2]             grind [(hI ⟨0, hn⟩).2]
linarith [ssf.hα_mem.1]               grind [ssf.hα_mem.1]
```

**Pattern 4: `@[grind →]` annotations** — Adding forward-reasoning annotations to `StrictAnti.imp` etc. lets grind derive order inequalities automatically, eliminating some `[F.hφ hij]` arguments entirely.

```lean
-- Added to Slicing/Basic.lean:
attribute [grind →] StrictAnti.imp
attribute [grind →] StrictMono.imp

-- Then this just works:
hφ := by intro i j hij; change F.φ j - t < F.φ i - t; grind
-- (grind fires StrictAnti.imp on F.hφ and hij automatically)
```

## What blocks the remaining 779 calls

### Issue 1: grind timeouts in large proof contexts (626 calls, 12 files)

**The problem**: Files with `set_option maxHeartbeats 800000` (or higher) have proof contexts with 30+ hypotheses. `grind` exhausts the default 200K heartbeats trying E-matching and case splitting before reaching the linear arithmetic that `linarith` solves instantly.

**Representative example** (`Deformation/DeformedGtLe.lean:171`):
```lean
-- Context has 30+ hypotheses about stability conditions, phase bounds, etc.
-- Goal is: a - ε₀ < wPhaseOf (ssf.W (K₀.of C E)) ssf.α
-- linarith closes this in <1ms using 3 local hypotheses
-- grind times out at 200K heartbeats doing E-matching on all 30+ hypotheses
```

**Affected files** (all in Deformation/ and StabilityCondition/):
- `DeformedGtLe.lean` — 60 calls, 27s build time
- `PhaseConfinement.lean` — 99 calls
- `HomVanishing.lean` — 47 calls
- `HNExistence.lean` — 43 calls
- `BoundaryTriangle.lean` — 75 calls
- `Pullback.lean` — 14 calls
- `PhiPlusHN.lean` — 17 calls
- `PhiPlusMDQ.lean` — 25 calls
- `StabilityCondition/Deformation.lean` — 80 calls
- `StabilityCondition/Topology.lean` — 64 calls
- `StabilityCondition/Seminorm.lean` — 51 calls
- `StabilityCondition/LocalHomeomorphism.lean` — 19 calls

**Root cause**: `grind` is a general-purpose SMT-like solver that explores a large search space. In contexts with many hypotheses, it instantiates too many E-matching rules before the linear arithmetic engine gets a chance to close the goal. `linarith` is specialized: it immediately extracts linear atoms and runs Simplex, ignoring non-arithmetic hypotheses.

**Potential fix**: `grind -lia -ring +linarith (ematch := 0)` might work by disabling E-matching and going straight to linear arithmetic. But this defeats the purpose of using grind. The real fix would be grind learning to prioritize linear arithmetic in contexts where it's sufficient.

**Workaround attempted**: Adding `@[grind →]` annotations on `StrictAnti.imp` etc. actually made timeouts *worse* in these files — more E-matching rules means more work before reaching the arithmetic solver.

### Issue 2: Nonlinear arithmetic (153 `nlinarith` calls, ~8 files)

**The problem**: `nlinarith` multiplies inequalities together to derive new linear facts. `grind` treats products like `x * y` as opaque variables and cannot do this.

**Representative example** (`StabilityCondition/Basic.lean:131`):
```lean
-- Goal: -Real.pi < Real.pi * (θ i - ψ)
-- Hypotheses: hθ_gt i : ψ - 1 < θ i, Real.pi_pos : 0 < Real.pi
-- nlinarith multiplies (ψ - 1 < θ i) by Real.pi_pos to get:
--   Real.pi * (ψ - 1) < Real.pi * (θ i), hence -Real.pi < Real.pi * (θ i - ψ)
-- grind cannot do this multiplication step
```

**Affected files**: `StabilityCondition/{Basic,Seminorm,Deformation,Topology,LocalHomeomorphism}`, `ForMathlib/Analysis/*`, `HeartEquivalence/{Basic,Forward,Reverse}`, `Deformation/{PhaseArithmetic,WPhase,IntervalAbelian,PhasePerturbation}`

**FRO status**: Nonlinear arithmetic is on the Year 3 roadmap (Aug 2025 – Jul 2026) but not yet shipped as of v4.29.0-rc6. Current progress is limited to propagating known numerals through monomials (v4.24.0).

### Issue 3: Redundant parameter errors in `grind [local, expr]`

**The problem**: When `linarith [local_hyp, computed_expr]` is converted to `grind [local_hyp, computed_expr]`, grind errors with "redundant parameter `local_hyp`" because it auto-finds local hypotheses. But stripping the local sometimes causes grind to fail on the remaining computed expression alone.

**Representative example** (`Deformation/BoundaryTriangle.lean:142`):
```lean
-- Original: linarith [hlo_pert', (hphases ⟨0, hn⟩).1]
-- grind [hlo_pert', (hphases ⟨0, hn⟩).1] → "redundant parameter hlo_pert'"
-- grind [(hphases ⟨0, hn⟩).1] → grind fails (needs hlo_pert' too)
-- The local IS needed but grind auto-includes it and errors on the explicit mention
```

**Workaround**: A Python script strips single-identifier args (locals) while keeping computed expressions. This works in ~80% of cases but fails when grind can't close the goal without the explicit hint combination.

### Issue 4: `omega` timeouts in struct construction (63 calls, 1 file)

**The problem**: Inside `refine ⟨{ field := ..., field := ... }⟩` blocks, `by grind` times out where `by omega` is instant. This is specific to `StabilityFunction/HarderNarasimhan.lean` lines 620-700.

```lean
-- Inside struct construction:
else hn_Q'.φ ⟨j - 1, by omega⟩  -- omega: <1ms
else hn_Q'.φ ⟨j - 1, by grind⟩  -- grind: timeout at 200K heartbeats
```

**Root cause**: grind's elaboration overhead in struct contexts. The Fin arithmetic goal `j - 1 < n` is trivial but grind spends heartbeats on congruence closure setup that omega skips entirely.

## Methodology

1. **Wave 1**: `sed` replacement of `by omega`, `; omega`, standalone `omega` → `grind`. Same for `linarith`, `ring`, `norm_num`. Excluded files known to have nonlinear goals.

2. **Wave 2**: Fixed missed patterns — `by omega)`, `by ring)`, `by linarith)` (term-mode positions with closing parens/brackets).

3. **Wave 3**: `linarith [expr]` → `grind [expr]` using `perl -0pe` for multiline safety. Python script to strip redundant local-hypothesis args.

4. **Wave 4**: Added `@[grind →]` annotations on `StrictAnti.imp`, `StrictMono.imp`, `Antitone.imp`, `Monotone.imp`. Retried files where bare `grind` now closes goals the annotations unlocked.

5. **Each wave**: Full project build (3219 jobs), surgical revert of failing files, iterate until clean.

## Recommendations

1. **Monitor Lean FRO Year 3**: Nonlinear arithmetic in grind would unlock ~153 `nlinarith` calls immediately.

2. **Performance profiling**: The timeout files could benefit from `grind (ematch := 2, splits := 3)` or similar reduced-search configurations. This was not systematically attempted.

3. **More `@[grind →]` annotations**: Annotating phase-bound lemmas (`Slicing.phiPlus_le_of_hn`, `Slicing.hom_eq_zero_of_phase_gap`) could let grind close more complex goals without explicit `[...]` args.

4. **`grind?` for minimization**: Running `grind?` on successful grind calls could produce `grind only [...]` invocations that are faster and more stable.
