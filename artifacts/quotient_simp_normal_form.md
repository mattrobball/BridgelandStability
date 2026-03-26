# Quotient Simp Normal Form — Mathlib Conventions

## The Three-Layer Pattern

Mathlib quotient constructions follow a three-layer architecture:

| Layer | Example | Role |
|---|---|---|
| 0. Lean core | `Quot.mk`, `Quotient.mk` | Raw quotient constructor |
| 1. Generic math | `QuotientAddGroup.mk`, `Submodule.Quotient.mk` | Generic group/module quotient API |
| 2. Domain-specific | `Abelianization.of`, `Ideal.Quotient.mk`, `K₀.of` | User-facing API |

## Simp Direction: Always Toward Domain

`@[simp]` lemmas normalize **from generic to domain-specific** (toward the outermost layer):

```lean
-- Abelianization (GroupTheory/Abelianization/Defs.lean:65)
@[simp] theorem mk_eq_of (a : G) : Quot.mk _ a = of a := rfl

-- Ideal.Quotient (RingTheory/Ideal/Quotient/Defs.lean:108)
@[simp] theorem mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R ⧸ I) = mk I x := rfl

-- QuotientGroup (GroupTheory/QuotientGroup/Defs.lean:91)
@[simp] theorem coe_mk' : (mk' N : G → G ⧸ N) = mk := rfl
```

Generic layer terms should **never** remain in goals after `simp`.

## Standard API Components

Every quotient construction provides:

### 1. `@[simp] lift_of` / `lift_mk`
```lean
@[simp] theorem lift_of (f) [IsAdditive f] (X) : P.lift f (P.of X) = f X
```
Present in: Abelianization, QuotientGroup, Ideal.Quotient, FreeAbelianGroup, K0Presentation.

### 2. `@[ext]` with elevated priority
```lean
-- QuotientGroup (Defs.lean:112)
@[ext 1100] theorem monoidHom_ext ⦃f g⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g

-- Ideal.Quotient (Defs.lean:96)
@[ext 1100] theorem ringHom_ext ⦃f g⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g

-- FreeAbelianGroup (FreeAbelianGroup.lean:140)
@[ext high] theorem lift_ext {f g} (h : ∀ a, f (of a) = g (of a)) : f = g
```

The elevated priority (`1100` or `high`) ensures these fire **before** generic
`AddMonoidHom.ext` or `LinearMap.ext`, giving goals in domain terms.

### 3. Bridging simp lemmas for multi-layer constructions
When domain-specific `of` wraps a presentation/generic `of`:
```lean
@[simp] theorem trianglePresentation_of (X : C) :
    (trianglePresentation C).of X = K₀.of C X := rfl
```

## Application to K0Presentation

Our construction has **four layers**: Lean core → FreeAbelianGroup → K0Presentation → K₀/HeartK0.

The simp normal form is the outermost domain layer:
- `K₀.of C X` (not `(trianglePresentation C).of X`)
- `HeartK0.of h E` (not `(heartPresentation h).of E`)

Required API at each domain wrapper:
1. `@[simp]` bridging: `trianglePresentation_of`, `heartPresentation_of`
2. `@[simp] lift_of`: `K₀.lift_of`, inherited from K0Presentation
3. `@[ext 1100]` hom_ext: `K₀.hom_ext`, `HeartK0.hom_ext`
4. Domain-specific relation lemma: `K₀.of_triangle`, `HeartK0.of_shortExact`
