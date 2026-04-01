---
name: improve
description: "Improve Lean proofs: style, readability, and golfing. Use when asked to improve, golf, compress, shorten, or clean up Lean proofs."
paths:
  - "**/*.lean"
---

# Improve Lean Proofs

Style, readability, and golfing techniques for Lean proofs.

## Mandatory verification

Every change MUST be verified before committing. Run all four checks
from AGENTS.md in order and READ the output — warnings count as failures:

```bash
lake exe cache get
lake build BridgelandStability    # READ warnings, not just exit code
lake exe runLinter
lake exe lint-style
```

If there are ANY new warnings compared to the baseline, revert.

## Workflow

Two phases: a file-wide scan (tiers 1-3), then theorem-by-theorem improvements (tiers 4-8). Verify each edit with `lean_diagnostic_messages` before moving on.

## Phase 1: File-wide

### 1. Extract helpers for duplicated proof skeletons

The single highest-ROI technique. If 2+ proofs differ only in the function/lemma/constant applied, extract the skeleton into a parameterized helper. Typical savings: 10-30 lines per extraction. Scan for pairs of proofs with identical structure before doing anything else.

Also look for deduplication via:
- **`wlog`** for symmetric cases — eliminates one branch entirely.
- **`suffices`** to deduplicate symmetric case splits — extract the common proof, have each branch only produce the witness.
- **`by_cases` hoisting** — when two branches share the same conclusion, hoist it to a `have ... by` block containing the `by_cases`.

### 2. Replace with mathlib or derive from neighbours

- **Replace private helpers with mathlib lemmas** — use `lean_loogle` with the type signature to find exact matches.
- **Derive lemmas from each other** — build on what's already proven nearby rather than reproving from scratch.

### 3. Run the pattern checker

```bash
python3 "${CLAUDE_SKILL_DIR}/check_patterns.py" <file.lean>
```

Detects mechanical improvements: `push_neg → push Not` (deprecated),
consecutive blank lines, consecutive `rw`, `:= by exact → :=`,
`grind [.symm]`, duplicate `open`, long lines (>100 codepoints).

Fix all findings before moving to per-theorem work.

## Phase 2: Theorem-by-theorem

Work through each declaration individually. Verify with `lean_diagnostic_messages` after each edit.

### Instant wins (always apply)

| Before | After |
|--------|-------|
| `ext x; rfl` | `rfl` |
| `simp; rfl` | `simp` |
| `constructor; exact h1; exact h2` | `exact ⟨h1, h2⟩` |
| `apply f; exact h` | `exact f h` |
| `:= by exact t` | `:= t` |
| `push_neg` | `push Not` |

### Minimum value filter

1-line savings are only worth making if (a) zero-risk syntax cleanup (e.g. `by exact` → term) or (b) they also improve clarity or performance. Don't churn code for marginal compression.

### 4. `linear_combination` for algebraic goals

Try on EVERY proof that ends in `ring` or `ring_nf` and has hypotheses in context. Closes goals that `ring` can't when hypotheses are needed. For goals involving `I² = -1`: `linear_combination (coefficient) * I_sq`. Does not work on `Prop`-valued goals or goals with `ofReal` casts.

### 5. Inline single-use `have` blocks

The highest-volume technique. `have h := X; exact h.foo` → `exact X.foo`. Inline into function arguments: `have hf := ...; apply g hf` → `apply g (...)`. Best targets: single-use `have`s where the body is ≤1 line.

Caveat: `grind` and `omega` are context-sensitive — `grind [lemma]` can time out in large proof contexts. Keep standalone lemmas when inlining causes timeouts.

### 6. grind subsumption

`grind` often subsumes preceding tactics — try deleting what comes before it:
- `rw [h]; grind` → `grind` (when `h` is a local hypothesis or simple rewrite)
- `congr 1; grind` → `grind`
- `simp; grind` → `grind`
- `simp [lemmas] <;> grind` → `grind [lemmas]`
- `rw [ht]; omega` → `grind` (when `ht` is a substitution)
- `grind [lemma.symm]` → `grind [lemma]` (grind handles symmetry internally)

### 7. API shortcuts

- `fun_prop` for continuity/differentiability — `(by fun_prop : Continuous _).continuousOn` inlines 3-line proofs.
- `field_simp` + `ring` replaces verbose calc chains with denominators. `field` is shorthand for `field_simp; ring`.
- `push_cast; ring` for ℝ→ℂ cast goals.
- `gcongr` for monotonicity/congruence goals.
- `nlinarith [explicit_product_hint]` for nonlinear inequalities.
- `simp only [def, h₁, h₂] at h` to replace `unfold foo; rw [if_pos h1]; rw [if_neg h2]` chains.
- `refine ⟨..., ?_, ?_⟩ <;> grind [def, key_fact]` to close multiple structurally similar goals at once.
- Collapse `calc` to term-mode: `calc a ≤ b := h1; _ ≤ c := h2` → `le_trans h1 h2`. Two-step `calc` with `gcongr` → `rw [...]; gcongr`.

### 8. Remove unused parameters

Check for "unused variable" warnings and remove the parameter + all caller arguments. Grep for `_h` prefix to find them quickly.

## Known-bad patterns (DO NOT apply without LSP verification)

- **`rw [...]; exact t` → `rwa [...]`** — Only works when `t` is a
  bare local hypothesis. `rwa` calls `assumption`, which cannot find
  library lemmas, function applications, or complex expressions.
  ALWAYS verify with `lean_diagnostic_messages` after applying.
- **`by_contra!`** — Expands to `by_contra; push_neg`, and `push_neg`
  is deprecated in current Mathlib. Do NOT use.
- **`show T from inferInstance` → `inferInstance`** — The `show`
  provides a type hint needed for instance synthesis. Do NOT remove
  without LSP verification.

## What doesn't work

- **Semicolon joins in multiline proofs** — banned antipattern.
- **`grind`** — rarely closes goals with `zpow`, `Even`/`Odd`, or cast arithmetic.
- **Analysis boilerplate** — integrability/measurability/continuity proofs resist compression without new API. These are the hardest to golf.
- **Modular form slash action proofs** — specialized API doesn't simplify further.
- **Dominated convergence proofs** — each sub-proof (bound, summability, pointwise convergence) is already near-minimal.
