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

## 8. Destructure `And` chains directly in `obtain`, use `-` for unused conjuncts

When an existential returns a conjunction `A ∧ B ∧ C ∧ D`, don't pull
conjuncts out with `And.left`/`And.right`:
```lean
-- Before
obtain ⟨X, Y, GX, GY, f, g, h, hT, hprops⟩ := split_hn_filtration ...
have hGX_gt := And.left hprops
have hGY_le := And.left (And.right hprops)
have hGY_bound := And.left (And.right (And.right hprops))
have hGX_contain := And.right (And.right (And.right hprops))

-- After
obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX_gt, hGY_le, hGY_bound, hGX_contain⟩ :=
  split_hn_filtration ...
```

Use `-` for unused conjuncts:
```lean
obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, -⟩ := ...
```

## 9. `simpa using` replaces `have := ...; simp at this; exact this`

The pattern `have := expr; simp [...] at this; exact this` is exactly
what `simpa` is for:
```lean
-- Before
have hphiPlus_le : phiPlus ≤ φ := by
  have := phiPlus_le_phiPlus_of_hn C hKne GXorig hGXn
  simp only [HNFiltration.phiPlus, hGXorig_phases_eq] at this; exact this

-- After
have hphiPlus_le : phiPlus ≤ φ := by
  simpa only [HNFiltration.phiPlus, hGXorig_phases_eq] using
    phiPlus_le_phiPlus_of_hn C hKne GXorig hGXn
```

## 10. Inline one-shot equality `have`s into `rwa`

When a `have` proving an equality is used only once in a subsequent `rw`/`rwa`,
inline the proof term directly:
```lean
-- Before
have hpe : phiPlus = φ :=
  le_antisymm hphiPlus_le (le_trans hphiMinus_ge (heq ▸ le_refl _))
have hsem := semistable_of_phiPlus_eq_phiMinus C hKne heq
rwa [hpe] at hsem

-- After
have hsem := semistable_of_phiPlus_eq_phiMinus C hKne heq
rwa [le_antisymm hphiPlus_le (heq ▸ hphiMinus_ge)] at hsem
```

Note: `heq ▸ hphiMinus_ge` is a shorter form of
`le_trans hphiMinus_ge (heq ▸ le_refl _)` — the `▸` rewrites the
expected type so the proof term matches directly.

## 11. Don't duplicate hypotheses just to `rw` — rewrite in place

If a `have` is copied only so `rw` can mutate the copy while preserving
the original, check whether the original is used again. If not, rewrite
directly:
```lean
-- Before
have hK_heart : t.heart K.obj := K.property
have hK_heart' := hK_heart
rw [toTStructure_heart_iff] at hK_heart'
... hK_heart'.1 ...

-- After (hK_heart never used after rewrite)
have hK_heart : t.heart K.obj := K.property
rw [toTStructure_heart_iff] at hK_heart
... hK_heart.1 ...
```

## 12. Replace step1/step2/step3 `have` chains with `calc`

Sequential inequality chains where each step feeds the next are natural
`calc` blocks:
```lean
-- Before
have step1 : K * sin(πδ) ≤ K * πδ := mul_le_mul_of_nonneg_left h1 hKnn
have step2 : K * πδ ≤ (K+1) * πδ := by gcongr; linarith
have step3 : (K+1) * πδ = δ * ((K+1) * 2π) / 2 := by ring
linarith [half_lt_self hgapZ]

-- After
calc K * sin(πδ)
    ≤ K * πδ := mul_le_mul_of_nonneg_left h1 hKnn
  _ ≤ (K+1) * πδ := by gcongr; linarith
  _ = δ * ((K+1) * 2π) / 2 := by ring
  _ < gapZ := by linarith [half_lt_self hgapZ]
```

## 13. Don't inline terms that produce metavariable LHS in `rw`

`rw [zero_of_source_iso_zero _ hIZH.isoZero]` fails because the LHS is
a metavariable. Keep a named `have` for the equation, then `rw` with it:
```lean
have hiI_zero : i_I = 0 := zero_of_source_iso_zero _ hIZH.isoZero
exact hfH (by rw [← hpH, hiI_zero]; simp)
```
