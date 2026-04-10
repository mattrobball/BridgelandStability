# Debugging `simp`

## Don't guess — use traces

When `simp` doesn't close a goal or a simp lemma doesn't fire, don't
shotgun different `simp [...]` argument combinations. Use the diagnostics.

### See which lemmas fired and what's left

```lean
simp?              -- suggests the minimal simp call that reproduces what simp did
simp? [my_lemma]   -- same, but with my_lemma included
```

### See why a specific lemma didn't match

```lean
set_option trace.Debug.Meta.Tactic.simp true in
```

This shows simp's matching attempts — which patterns it tried and why
they failed to unify.

### Before writing new `@[simp]` lemmas

1. Run `simp` on the goal and read what's left — that's the simp-normal form.
2. Check which existing simp lemmas fired to produce that form (`simp?`).
3. Write the new lemma to close the **post-simp residual**, not the original goal.
4. Test in a real proof context (`lean_multi_attempt`), not in isolation.

A simp lemma that matches the pre-simp goal is useless if other simp
lemmas fire first and rewrite the goal into a different shape.

## Reducibility and simp pattern matching

Simp's pattern matcher uses **reducible transparency** by default. If a
definition is not `@[reducible]`, simp cannot unfold it during matching.

### Example: `ObjectProperty.homMk`

`homMk` is a plain `def`, so `(homMk g).hom` does NOT reduce to `g` at
reducible transparency, even though `rfl` closes it at default transparency.

This means a simp lemma with LHS `(kernel.ι ?f).hom ≫ ?f.hom` will NOT
match `(kernel.ι (homMk g)).hom ≫ g`, because matching `?f = homMk g`
requires `?f.hom = (homMk g).hom` to reduce to `g`, which simp can't see.

### The fix: state lemmas in the post-simp-reduction form

Instead of one lemma parameterized by `f : X ⟶ Y`:
```lean
-- Matches when f is directly a FullSubcategory morphism
@[simp] lemma kernel_condition_hom (f : X ⟶ Y) [HasKernel f] :
    (kernel.ι f).hom ≫ f.hom = 0
```

Also provide a variant with `homMk` explicit:
```lean
-- Matches after simp has unfolded a functor map to homMk
@[simp] lemma kernel_condition_homMk (g : X.obj ⟶ Y.obj)
    [HasKernel (ObjectProperty.homMk g : X ⟶ Y)] :
    (kernel.ι (ObjectProperty.homMk g : X ⟶ Y)).hom ≫ g = 0
```

The `_homMk` variant fires when a functor between FullSubcategories
(like `toLeftHeart`) maps `f` to `ObjectProperty.homMk f.hom`, and simp
has already unfolded the functor map but can't see through `homMk`.

### General principle

When a simp lemma has `?f` appearing in two positions and one position
involves a projection (like `.hom`), check whether the projection reduces
at reducible transparency after `?f` is matched. If not, provide a
variant where the non-reducible constructor is explicit in the pattern.

## Conflicting simp directions

`comp_hom` normalizes `(f ≫ g).hom` → `f.hom ≫ g.hom` (distributes).
`kernel.condition` needs `kernel.ι f ≫ f` (undistributed) to match.
After `comp_hom` fires, `kernel.condition` can never match.

The fix: state the lemma in the distributed (post-`comp_hom`) form.
See `FullSubcategoryLimits.lean` for the full set of 8 lemmas.
