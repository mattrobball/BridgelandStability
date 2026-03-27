# K0Presentation: Unified Grothendieck group quotient layer

## Status: Implemented

Implemented in `BridgelandStability/GrothendieckGroup/Presentation.lean`.
Both `K₀` (via `trianglePresentation`) and `HeartK0` (via `heartPresentation`)
are now defined as instances of `K0Presentation`.

## Problem (original)

The project had two separate K₀ constructions that follow the identical algebraic
pattern — free abelian group on objects, quotient by relations from a class of
"exact sequences":

1. **Triangulated K₀** (`GrothendieckGroup/Defs.lean`): relations from
   distinguished triangles `A → B → C → A[1]`.
2. **Heart K₀** (`HeartEquivalence/Basic.lean`): relations from short exact
   sequences `0 → A → B → C → 0`.

The duplicated surface was ~6 declarations: subgroup, quotient type,
`instAddCommGroup`, `of`, `of_rel`/`of_triangle`/`of_shortExact`, `lift`.

## Mathematical context

**Extriangulated categories** (Nakaoka-Palu 2019) are the canonical framework
unifying triangulated and exact K₀. An extriangulated category has a bifunctor
`E : C^op × C → Ab` and a realization sending extensions to "E-triangles."
K₀ is `FreeAbelianGroup(Obj) / {E-triangle relations}`, specializing to
distinguished-triangle relations and short-exact-sequence relations.

However, formalizing extriangulated categories is a substantial project orthogonal
to Bridgeland stability. The right move here is a lightweight **purely algebraic**
abstraction at just the quotient/universal-property layer.

## Implementation

In `GrothendieckGroup/Presentation.lean`:

```lean
structure K0Presentation (Obj : Type u) (Rel : Type v) where
  obj₁ : Rel → Obj
  obj₂ : Rel → Obj
  obj₃ : Rel → Obj

namespace K0Presentation

def subgroup : AddSubgroup (FreeAbelianGroup Obj) := ...
abbrev K0 : Type _ := FreeAbelianGroup Obj ⧸ P.subgroup
def of (X : Obj) : P.K0 := ...
theorem of_rel (r : Rel) : P.of (P.obj₂ r) = P.of (P.obj₁ r) + P.of (P.obj₃ r) := ...
class IsAdditive {A : Type*} [AddCommGroup A] (f : Obj → A) : Prop where ...
def lift {A : Type*} [AddCommGroup A] (f : Obj → A) [P.IsAdditive f] : P.K0 →+ A := ...
theorem hom_ext {f g : P.K0 →+ A} (h : ∀ X, f (P.of X) = g (P.of X)) : f = g := ...
theorem induction_on (x : P.K0) ... : motive x := ...
def map (f : Obj → QObj) (hf : P.IsAdditive (Q.of ∘ f)) : P.K0 →+ Q.K0 := ...

end K0Presentation
```

## Instantiations

In `GrothendieckGroup/Defs.lean`:

```lean
abbrev trianglePresentation :
    K0Presentation C {T : Pretriangulated.Triangle C // T ∈ distTriang C} where
  obj₁ := fun r => r.1.obj₁
  obj₂ := fun r => r.1.obj₂
  obj₃ := fun r => r.1.obj₃

def K₀ : Type _ := (trianglePresentation C).K0
```

In `HeartEquivalence/Basic.lean`:

```lean
abbrev heartPresentation (h : HeartStabilityData C) :
    K0Presentation h.t.heart.FullSubcategory
      {S : ShortComplex h.t.heart.FullSubcategory // S.ShortExact} where
  obj₁ := fun S => S.1.X₁
  obj₂ := fun S => S.1.X₂
  obj₃ := fun S => S.1.X₃

def HeartK0 (h : HeartStabilityData C) : Type _ := (heartPresentation h).K0
```

## Design decisions

- **Not a typeclass.** The same object type can support multiple presentations
  (a triangulated category that is also the heart of a t-structure on a larger
  category). Explicit parameters + `abbrev` wrappers are safer.
- **`abbrev` not `def` for public names.** Preserves reducibility so existing
  proofs that unfold `K₀` continue to work.
- **No categorical content.** The abstraction lives below category theory — it's
  just a quotient of a free abelian group by a closure relation. This keeps
  imports light and avoids coupling to any specific categorical framework.
- **Keep it internal unless a third user appears.** For Mathlib upstreaming,
  the concrete triangulated `K₀` is the right public API. The presentation
  layer is a factoring convenience, not a standalone contribution.

## What this does NOT touch

- Category-specific lemmas: `K₀.of_postnikovTower_eq_sum`, shift arguments,
  `heartK0ToK0_surjective` — these are genuine mathematical content about the
  specific presentation, not quotient plumbing.
- The `heartK0ToK0 : HeartK0 h →+ K₀ C` comparison map — this relates two
  different presentations and cannot be abstracted.
- The `IsTriangleAdditive` typeclass — this is triangulated-specific and stays.

## Outcome

The refactoring also added `hom_ext`, `induction_on`, and `map` at the
`K0Presentation` level, which were then inherited by both `K₀` and `HeartK0`.
The `abbrev` strategy kept all downstream consumers working without changes.

## References

- Nakaoka, Palu. "Extriangulated categories, Hovey twin cotorsion pairs and
  model structures." Cahiers de Topologie et Géométrie Différentielle
  Catégoriques 60.2 (2019).
- Ogawa. "K₀ of Weak Waldhausen Extriangulated Categories." (2023).
- Quillen. "Higher algebraic K-theory: I." Algebraic K-theory I, LNM 341 (1973).
