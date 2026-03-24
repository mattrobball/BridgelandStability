# Lessons from Cleaning Up Have-Chains

## 1. `nlinarith` can replace `have` + `grind` + `linarith` chains

When you have a chain like:
```lean
have h1 := (abs_lt.mp harg_u).1
have h2 := (abs_lt.mp harg_u).2
constructor
· have : ... := by grind [...]
  linarith
· have : ... := by grind [...]
  linarith
```

Try `nlinarith` first:
```lean
obtain ⟨h1, h2⟩ := abs_lt.mp harg_u
exact ⟨by nlinarith [hφ.1], by nlinarith [hφ.2]⟩
```

`nlinarith` handles nonlinear arithmetic that `linarith` can't, often
eliminating the need for intermediate `have`s that set up the linear part.

## 2. Chain `rw` calls instead of naming intermediates

If a `have` is used exactly once in a subsequent `rw`, inline it:
```lean
-- Before
have harg_prod := Complex.arg_mul hz1 hz2 hsum_mem
have hsimpl : ... := by field_simp; ring
rw [hreassoc, harg_prod, harg1]
rw [hsimpl, abs_div, ...]

-- After
rw [hreassoc, Complex.arg_mul hz1 hz2 hsum_mem, harg1,
  show ... from by field_simp; ring,
  abs_div, ...]
```

## 3. Scope `have`s to where they're used

If `hexp_combine` is only used inside `hreassoc`, make it a local `have`
inside `hreassoc`'s proof block rather than a top-level `have`.

## 4. `calc` + `ring` + `rw` for expression rewriting under non-`ring` subterms

When you need to rewrite `exp(a) * exp(b)` inside a larger expression that
also has `ring`-level structure, Lean's `rw` can't find the subpattern
directly. The working pattern is:

```lean
have : exp(a) * exp(b) = exp(a + b) := by rw [← exp_add]; congr 1; push_cast; ring
calc _ = m * (exp(a) * exp(b)) * z := by ring
  _ = _ := by rw [this]
```

Don't try `rw [show _ = ... from ...]` with a metavariable LHS — Lean
rejects it. The `calc` approach separates `ring`-level reassociation from
the `rw` step.

## 5. Verify `have`s are truly unused before removing

A `have` may look unused because no later `have` or tactic names it
explicitly, but it can be in the local context where `grind`, `linarith`,
or `nlinarith` consume it silently. Test the build after each removal.

Example: `hu1 : ‖u‖ < 1` appeared unused but `linarith` needed it to
close `1 = ‖u‖ → False`.

## 6. `obtain` beats `have` + `have` for destructuring

```lean
-- Before
have h1 := (abs_lt.mp harg_u).1
have h2 := (abs_lt.mp harg_u).2

-- After
obtain ⟨h1, h2⟩ := abs_lt.mp harg_u
```

## 7. Use direct term proofs for simple facts

```lean
-- Before
have hz1 : z₁ ≠ 0 := mul_ne_zero
  (by exact_mod_cast hm.ne') (Complex.exp_ne_zero _)

-- This is already good — it's a direct term proof, not a tactic block.
-- Don't add `have`s for things that are one-liners.
```

The threshold: if a `have` proof is a single tactic or term application,
it's fine. If it's 3+ lines of tactic proof, consider whether the
conclusion is really needed as a named intermediate.
