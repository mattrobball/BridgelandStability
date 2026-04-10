# `grind` Tactic Reference for Bridgeland Stability Project

## How `grind` works

`grind` proves goals **by contradiction**. It negates the goal, adds everything to a shared
"whiteboard", then runs cooperating engines (congruence closure, E-matching, linear arithmetic,
ring solver, case splitting) until it derives `False`.

**E-matching** is the core mechanism: when grind sees a term matching an annotated theorem's
**pattern**, it instantiates the theorem and adds the result to the whiteboard. This can
trigger further instantiations, building chains of reasoning.

Key difference from `simp`: simp rewrites destructively (replaces LHS with RHS). grind
accumulates equalities bidirectionally (both terms coexist in the same equivalence class).

---

## Annotation reference

### `@[grind =]` — simplify LHS to RHS

The workhorse (87% of all annotations in Lean core). Pattern is the LHS of an equality.
When grind sees a matching term, it adds the equality.

```lean
-- "f ≫ 𝟙 Y" simplifies to "f"
attribute [simp, grind =] Category.comp_id

-- "F.map (𝟙 X)" simplifies to "𝟙 (F.obj X)"
attribute [grind =] Functor.map_id

-- "e.hom ≫ e.inv" simplifies to "𝟙 X"
attribute [grind =] Iso.hom_inv_id

-- Auto-generate grind = projections for a structure
@[simps (attr := grind =)] def Iso.refl (X : C) : X ≅ X where ...
```

**Use when**: LHS is the "unreduced" form, RHS is simpler. Corresponds to `@[simp]`.

### `@[grind _=_]` — bidirectional (fire from either side)

Registers both LHS and RHS as patterns. Used for structural identities where
both forms appear in practice.

```lean
-- Associativity: (f ≫ g) ≫ h = f ≫ (g ≫ h) — match from either side
attribute [simp, grind _=_] Category.assoc

-- Naturality: α.app X ≫ G.map f = F.map f ≫ α.app Y
attribute [grind _=_] NatTrans.naturality

-- Functor preserves composition
attribute [grind _=_] Functor.map_comp
```

**Danger**: Can cause runaway instantiation chains. Mathlib explicitly avoids
`@[grind =]` on `Iso.trans_mk` because it "triggers a run-away chain of
`Category.assoc` instantiations."

### `@[grind →]` — forward reasoning (derive facts from hypotheses)

Pattern comes from the **hypotheses**. When grind sees matching facts on the
whiteboard, it instantiates the theorem and adds the conclusion.

```lean
-- When grind sees R a b AND R b c, derive R a c
@[grind →] axiom Rtrans {x y z} : R x y → R y z → R x z

-- When grind sees b ∈ replicate n a, derive b = a
@[grind →] theorem eq_of_mem_replicate (h : b ∈ replicate n a) : b = a

-- When grind sees find? p xs = some a, derive p a
@[grind →] theorem find?_some (h : find? p xs = some a) : p a
```

**This is the key to replacing `linarith [expr]`**. Instead of manually passing
computed facts, annotate the source lemma so grind fires it automatically:

```lean
-- Replaces: linarith [F.hφ hij]
-- When grind sees StrictAnti f AND a < b, it derives f b < f a
@[grind →] theorem StrictAnti.lt (hf : StrictAnti f) (h : a < b) : f b < f a
```

### `@[grind ←]` — backward reasoning (match against goal shape)

Pattern comes from the **conclusion**. When grind's negated goal matches,
it applies the lemma.

```lean
-- Close goals of the form "a ∈ #v[]" (by contradiction)
@[grind ←] theorem not_mem_empty (a : α) : ¬ a ∈ #v[]

-- Preserve sublist through eraseP
@[grind ←] theorem Sublist.eraseP : l₁ <+ l₂ → l₁.eraseP p <+ l₂.eraseP p
```

**Use when**: you want grind to recognize a goal pattern and apply a lemma backward.

### `@[grind .]` — default auto-pattern

Scans conclusion first, then hypotheses left-to-right, picking subterms until
all universally-quantified variables are covered. Good when you're unsure which
modifier to use.

```lean
@[grind .] theorem Precoverage.generate_mem_toGrothendieck ...
```

### `@[grind ext]` — extensionality

When grind has `a ≠ b`, it case-splits on whether the components are equal.

```lean
@[ext, grind ext] theorem Iso.ext (h : e₁.hom = e₂.hom) : e₁ = e₂
```

**Warning**: Not every `@[ext]` lemma should be `@[grind ext]`. Lean core explicitly
notes that `Option.ext` "results in too much case splitting."

### `@[grind inj]` — injectivity

When grind sees `f a = f b`, it derives `a = b`.

```lean
@[grind inj] theorem Functor.map_injective [Faithful F] : Function.Injective F.map
```

### `@[grind norm]` — preprocessing normalization

Applied during preprocessing before E-matching starts. Like a simp pass.

**Caution**: Can prevent E-matching if it partially simplifies a term that
a pattern needs to match on.

### `@[grind unfold]` — unfold definitions

`abbrev`s unfold automatically. `def`s don't. Use this when grind needs to
see through a `def`.

### `@[grind cases]` — case-split inductive predicates

```lean
@[grind cases] inductive MyPred : Nat → Prop where ...
```

With `eager`: split during preprocessing rather than waiting.

---

## `grind_pattern` command

Manual pattern control when automatic selection is wrong:

```lean
-- Fire when grind sees f applied to anything (not g ∘ f)
grind_pattern my_thm => f x

-- Multi-pattern: fire only when BOTH are present
grind_pattern Rtrans => R x y, R y z

-- With constraints
grind_pattern my_thm => xs.countP p, x ∈ xs where
  guard xs.countP p = 0
```

Available constraints: `x =/= term`, `size x < n`, `depth x < n`,
`is_ground x`, `is_value x`, `gen < n`, `max_insts < n`, `guard e`.

---

## Configuration knobs

```lean
grind                           -- default settings
grind (splits := 20)            -- more case-splits (default 9)
grind (gen := 12)               -- deeper instantiation chains (default 8)
grind (ematch := 10)            -- more E-matching rounds (default 5)
grind -lia                      -- disable integer arithmetic
grind -ring                     -- disable ring solver
grind -linarith                 -- disable linear arithmetic
grind +splitImp                 -- split on implications (off by default)
grind +suggestions              -- library premise selection
grind (ringSteps := 50000)      -- more ring solver budget
grind only [foo, bar]           -- only use listed theorems
grind?                          -- report minimal sufficient grind only call
```

Wrapper tactics (thin wrappers enabling one solver):
- `lia` — linear integer arithmetic only
- `grobner` — ring solver only
- `grind_order` — partial/linear order only
- `grind_linarith` — linear arithmetic only

---

## Mathlib CategoryTheory integration

7 core files enable grind as the category theory discharger:

```lean
set_option mathlib.tactic.category.grind true
-- cat_disch now calls: intros; (try dsimp only) <;> ((try ext) <;> grind (gen := 20) (ematch := 20))
```

Annotated lemmas in CategoryTheory:

| Lemma | Annotation | Why |
|-------|-----------|-----|
| `comp_id` / `id_comp` | `@[grind =]` | Identity elimination |
| `assoc` | `@[grind _=_]` | Associativity from either side |
| `hom_inv_id` / `inv_hom_id` | `@[grind =]` | Iso cancellation |
| `Iso.ext` | `@[grind ext]` | Iso extensionality |
| `map_id` | `@[grind =]` | Functor identity |
| `map_comp` | `@[grind _=_]` | Functor composition |
| `naturality` | `@[grind _=_]` | Natural transformation |
| `Functor.map_injective` | `@[grind inj]` | Faithful functor injection |

---

## What NOT to annotate

1. **Self-triggering equalities**: `Iso.trans_mk` causes runaway `assoc` chains
2. **Excessive case-splitters**: `Option.ext` causes too much splitting
3. **Nonlinear arithmetic**: grind can't handle `x * y < z` with variable `x, y`
4. **`Real.pi_pos`-dependent goals**: `nlinarith [Real.pi_pos, sq_nonneg ...]` genuinely needs nlinarith

---

## Bridgeland project: remaining migration targets

The 618 remaining `linarith [expr]` calls mostly use these patterns:

| Pattern | Count | Fix |
|---------|-------|-----|
| `linarith [F.hφ hij]` | ~200 | `@[grind →]` on `StrictAnti` |
| `linarith [(hI i).1, (hI i).2]` | ~100 | `@[grind →]` on interval bound extraction |
| `linarith [hperturb ...]` | ~80 | `@[grind →]` on phase perturbation bounds |
| `nlinarith [Real.pi_pos]` | ~160 | Cannot migrate (nonlinear) |
| `linarith [hε₀, hthin]` | ~80 | May work as bare `grind` if locals in scope |
