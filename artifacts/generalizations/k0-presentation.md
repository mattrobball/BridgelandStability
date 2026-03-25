# K0Presentation: Unified Grothendieck group quotient layer

## Status: Proposed

## Problem

The project has two separate K₀ constructions that follow the identical algebraic
pattern — free abelian group on objects, quotient by relations from a class of
"exact sequences":

1. **Triangulated K₀** (`GrothendieckGroup/Defs.lean`): relations from
   distinguished triangles `A → B → C → A[1]`.
2. **Heart K₀** (`HeartEquivalence/Basic.lean`): relations from short exact
   sequences `0 → A → B → C → 0`.

The duplicated surface is ~6 declarations: subgroup, quotient type,
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

## Proposed abstraction

```lean
structure K0Presentation where
  Obj : Type u
  Rel : Type v
  obj₁ : Rel → Obj
  obj₂ : Rel → Obj
  obj₃ : Rel → Obj

namespace K0Presentation

def subgroup (P : K0Presentation) : AddSubgroup (FreeAbelianGroup P.Obj) :=
  AddSubgroup.closure
    {x | ∃ r : P.Rel,
      x = FreeAbelianGroup.of (P.obj₂ r) - FreeAbelianGroup.of (P.obj₁ r) -
          FreeAbelianGroup.of (P.obj₃ r)}

abbrev K0 (P : K0Presentation) : Type _ :=
  FreeAbelianGroup P.Obj ⧸ P.subgroup

instance (P : K0Presentation) : AddCommGroup P.K0 :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup P.Obj ⧸ P.subgroup))

def of (P : K0Presentation) (X : P.Obj) : P.K0 :=
  QuotientAddGroup.mk (FreeAbelianGroup.of X)

lemma of_rel (P : K0Presentation) (r : P.Rel) :
    P.of (P.obj₂ r) = P.of (P.obj₁ r) + P.of (P.obj₃ r) := ...

class IsAdditive (P : K0Presentation) {A : Type w} [AddCommGroup A]
    (f : P.Obj → A) : Prop where
  additive : ∀ r : P.Rel, f (P.obj₂ r) = f (P.obj₁ r) + f (P.obj₃ r)

def lift (P : K0Presentation) {A : Type w} [AddCommGroup A]
    (f : P.Obj → A) [P.IsAdditive f] : P.K0 →+ A := ...

@[simp] lemma lift_of (P : K0Presentation) {A : Type w} [AddCommGroup A]
    (f : P.Obj → A) [P.IsAdditive f] (X : P.Obj) :
    P.lift f (P.of X) = f X := ...

end K0Presentation
```

## Instantiations

```lean
abbrev trianglePresentation (C) : K0Presentation where
  Obj := C
  Rel := {T : Pretriangulated.Triangle C // T ∈ distTriang C}
  obj₁ := fun T => T.1.obj₁
  obj₂ := fun T => T.1.obj₂
  obj₃ := fun T => T.1.obj₃

abbrev heartPresentation (h : HeartStabilityData C) : K0Presentation where
  Obj := h.t.heart.FullSubcategory
  Rel := {S : ShortComplex h.t.heart.FullSubcategory // S.ShortExact}
  obj₁ := fun S => S.1.X₁
  obj₂ := fun S => S.1.X₂
  obj₃ := fun S => S.1.X₃
```

Public names stay as wrappers:

```lean
abbrev K₀ C := (trianglePresentation C).K0
abbrev HeartK0 h := (heartPresentation h).K0
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

## Effort estimate

Small. The proofs for `of_rel`, `lift`, `lift_of` are copy-paste from the
existing `K₀` versions with `Triangle`/`ShortComplex` replaced by `P.Rel`.
The main work is rewiring downstream consumers to use the wrapper names,
which should be transparent if `abbrev` is used correctly.

## References

- Nakaoka, Palu. "Extriangulated categories, Hovey twin cotorsion pairs and
  model structures." Cahiers de Topologie et Géométrie Différentielle
  Catégoriques 60.2 (2019).
- Ogawa. "K₀ of Weak Waldhausen Extriangulated Categories." (2023).
- Quillen. "Higher algebraic K-theory: I." Algebraic K-theory I, LNM 341 (1973).
