# Audit: `SkewedStabilityFunction` -- Right Abstraction

**File:** `BridgelandStability/IntervalCategory/FiniteLength.lean` (definition, line 668)
**File:** `BridgelandStability/Deformation/WPhase.lean` (constructor + `Semistable`, lines 69, 369)
**Date:** 2026-03-26

---

## Phase 1: Definition and API Catalog

### The structure (verbatim)

```lean
structure SkewedStabilityFunction (s : Slicing C) (a b : ℝ) where
  W : K₀ C →+ ℂ
  α : ℝ
  hα_mem : a < α ∧ α < b
  nonzero : ∀ (E : C) (φ : ℝ), a < φ → φ < b →
    (s.P φ) E → ¬IsZero E → W (K₀.of C E) ≠ 0
```

### The semistability predicate (verbatim)

```lean
structure SkewedStabilityFunction.Semistable {s : Slicing C} {a b : ℝ}
    (ssf : SkewedStabilityFunction C s a b) (E : C) (ψ : ℝ) : Prop where
  intervalProp : s.intervalProp C a b E
  nonzero : ¬IsZero E
  wNe : ssf.W (K₀.of C E) ≠ 0
  phase_eq : wPhaseOf (ssf.W (K₀.of C E)) ssf.α = ψ
  le_of_distTriang : ∀ ⦃K Q : C⦄ ⦃f₁ : K ⟶ E⦄ ⦃f₂ : E ⟶ Q⦄ ⦃f₃ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
    Triangle.mk f₁ f₂ f₃ ∈ distTriang C →
    s.intervalProp C a b K → s.intervalProp C a b Q →
    ¬IsZero K →
    wPhaseOf (ssf.W (K₀.of C K)) ssf.α ≤ ψ
```

### The main constructor

```lean
def StabilityCondition.skewedStabilityFunction_of_near (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b) :
    SkewedStabilityFunction C σ.slicing a b where
  W := W
  α := (a + b) / 2
  hα_mem := ⟨by linarith, by linarith⟩
  nonzero := fun E φ _ _ hP hE ↦
    σ.W_ne_zero_of_seminorm_lt_one C W hW hP hE
```

### Usage counts

| Identifier | Occurrences | Files |
|------------|-------------|-------|
| `SkewedStabilityFunction` (structure/type) | ~100 | 15 |
| `ssf.W` | 716 | 12 |
| `ssf.α` | 499 | 11 |
| `ssf.nonzero` | 5 | 1 (PhaseConfinement.lean) |
| `ssf.hα_mem` | 15 | 2 (PhaseConfinement.lean, WPhase.lean) |
| `SkewedStabilityFunction.Semistable` | ~80 | 10 |
| `strict_additive` | ~15 | 5 |

### Critical downstream API

| Theorem | File |
|---------|------|
| `phase_le_of_strictQuotient` | PhaseConfinement.lean |
| `phase_le_of_strictQuotient_of_window` | StrictShortExactSequence.lean |
| `phase_le_of_triangle_quotient` | PhaseConfinement.lean |
| `exists_phase_gt_strictSubobject_of_not_semistable` | IntervalSelection.lean |
| `exists_semistable_strictQuotient_le_phase_of_finiteLength` | MaximalDestabilizingQuotient.lean |
| `exists_strictMDQ_of_finiteLength` | MaximalDestabilizingQuotient.lean |
| `hn_exists_in_thin_interval` | FiniteLengthHN.lean |
| `hn_exists_in_thin_interval_of_quotientLowerBound` | FiniteLengthHN.lean |
| `hn_exists_in_thin_interval_of_finiteSubobjects` | MaximalDestabilizingQuotientKernel.lean |
| `isStrictMDQKernel_of_minPhase_strictKernel_of_finiteLength` | MaximalDestabilizingQuotientKernel.lean |
| `semistable_of_iso` | FirstStrictSES.lean |

---

## Phase 2: Duplication Analysis

### The three "stability-like" objects in this codebase

| | `StabilityFunction` | `PreStabilityCondition` | `SkewedStabilityFunction` |
|---|---|---|---|
| **Context** | Abelian category `A` | Triangulated category `C` | Triangulated `C`, thin interval `P((a,b))` |
| **Central charge** | `Zobj : A -> C` (object-level) | `Z : K_0(C) ->+ C` (K_0-level) | `W : K_0(C) ->+ C` (K_0-level) |
| **Phase** | `(1/pi) * arg(Z(E))`, lies in `(0,1]` | Implicit via `P(phi)` slicing | `wPhaseOf(W([E]), alpha)`, lies in `(alpha-1, alpha+1]` |
| **Nonvanishing** | `upper : nonzero E -> Z(E) in H union R_-` | `compat : P(phi) E -> Z([E]) = m*exp(i*pi*phi)` | `nonzero : P(phi) E -> W([E]) != 0` |
| **Semistability** | Phase of subobjects <= phase of ambient | Membership in `P(phi)` | Triangle test: `wPhaseOf(W([K])) <= psi` for all kernel-like `K` |
| **HN existence** | Proved for finite-length abelian cats | Axiom of `Slicing` | Proved for thin finite-length intervals |
| **Additivity** | On short exact sequences | Via K_0 | On strict short exact sequences (via K_0) |

### Shared pattern?

All three structures follow the pattern:

1. An additive function from objects/classes to `C`.
2. A derived "phase" function from `C` to `R`.
3. A notion of "semistable" = nonzero + phase-maximality among sub-objects.
4. HN filtrations into semistable factors with decreasing phases.

The question is whether these should be unified into a single abstract framework.

### Why they are NOT instances of a common typeclass

The three structures live at fundamentally different categorical levels:

**`StabilityFunction`** operates on an abelian category. Subobjects are actual
monomorphisms. Short exact sequences are the ambient exact structure. The phase
function takes values in `(0, 1]` (no branch-cut parameter). The `upper` axiom
constrains the image of `Z` to a specific region of `C` (the semiclosed upper
half-plane), which is what forces phase into `(0, 1]`.

**`PreStabilityCondition` / `StabilityCondition`** operates on a triangulated
category. There are no subobjects in the classical sense -- semistability is
given by the slicing `P(phi)`, which is an *axiom*, not a derived notion. The
central charge `Z` is compatible with the slicing via the polar decomposition
`Z([E]) = m * exp(i*pi*phi)`. The phase is `phi in R` (all of `R`, not `(0,1]`),
and the shift-by-1 axiom connects `P(phi)` to `P(phi+1)`.

**`SkewedStabilityFunction`** is a *localized perturbation* of a stability
condition's central charge, restricted to a thin interval `P((a,b))` with
`b - a <= 1`. It has:
- A branch-cut parameter `alpha in (a,b)` that disambiguates the phase via
  `wPhaseOf(w, alpha) = alpha + arg(w * exp(-i*pi*alpha)) / pi`.
- A weaker nonvanishing axiom (`W([E]) != 0` rather than the full polar
  decomposition).
- Semistability defined via the triangle test (because the interval
  subcategory is quasi-abelian, not abelian, and "subobject" means
  "strict mono" = kernel of a strict epi).

A common typeclass would need to abstract over:
- The ambient category (abelian vs triangulated vs interval)
- The notion of subobject/quotient (monomorphism vs strict mono vs triangle)
- The phase function (fixed `arg/pi` vs parametrized `wPhaseOf`)
- The semistability predicate (subobject test vs triangle test vs axiom)
- The additivity mechanism (short exact vs distinguished triangle vs strict SES)

This would produce a typeclass with so many parameters that instantiation
proofs would be as long as the current definitions themselves. The payoff --
shared lemmas -- would be negligible: the phase-seesaw lemma, the
max-phase-implies-semistable lemma, and the MDQ construction are all
proved by arguments specific to their categorical setting.

### Mathlib comparison

Mathlib (as of the project's dependency snapshot) has:
- No stability functions, no slope stability, no HN filtrations for stability.
- `Subobject.IsArtinianObject`, `Subobject.IsNoetherianObject` -- chain conditions.
- No abstract "ordered stability" or "slope function" framework.

The closest mathematical precedent for a common abstraction would be
Rudakov's "stability data on an abelian category" or Joyce's "weak stability
conditions", but neither of these is in Mathlib, and both still hardcode abelian
categories.

---

## Phase 3: Mathematical Identity

### What is a skewed stability function?

**Reference:** Bridgeland (2007), Section 7 (specifically the proof of Theorem
7.1 / Proposition 7.7). The term "skewed stability function" is a
*project-specific name* for an auxiliary object that Bridgeland constructs
implicitly during the deformation argument. Bridgeland does not name or
axiomatize it; he works directly with a perturbation `W` of the central charge
`Z` and argues that `W`-phases are well-defined in thin intervals.

**What the project extracts into a definition:**

Given a stability condition `sigma = (Z, P)` and a group homomorphism `W` close
to `Z` (in the seminorm `||W - Z||_sigma < 1`), and a thin interval `(a, b)`
with `b - a <= 1`:

1. `W` is nonvanishing on semistable objects of phase `phi in (a, b)`.
2. A "W-phase" can be defined via `wPhaseOf(W([E]), alpha)` for a branch-cut
   parameter `alpha in (a, b)`.
3. "W-semistability" of an interval object `E` means: `E` is nonzero, in the
   interval, `W([E]) != 0`, has W-phase `psi`, and for every distinguished
   triangle `K -> E -> Q -> K[1]` with `K, Q` in the interval and `K` nonzero,
   `wPhaseOf(W([K])) <= psi`.

**Is the `Semistable` bundling standard?**

The five fields of `Semistable` are:
1. `intervalProp` -- E lives in P((a,b))
2. `nonzero` -- E is nonzero
3. `wNe` -- W([E]) != 0
4. `phase_eq` -- the W-phase equals a given value psi
5. `le_of_distTriang` -- triangle inequality on phases

Field (5) is the mathematical content of semistability. Fields (1)-(4) are
"well-formedness" conditions that ensure the phase is defined and the object is
in scope. This is a reasonable packaging: the `Semistable` structure bundles
the well-formedness guards with the mathematical content, so that downstream
lemmas do not need to repeat `hI : intervalProp ...`, `hne : not IsZero E`,
`hW : W([E]) != 0` as separate hypotheses.

**Comparison to Bridgeland Section 7:** Bridgeland's argument in Section 7 does
not define "W-semistability" as a standalone concept. Instead, he constructs HN
filtrations directly by the descent argument (Artinian induction on strict
subobjects, Noetherian induction on strict quotients). The project's
`Semistable` structure is a useful formalization device that makes the recursion
cleaner, but it is not a definition from the paper.

The triangle-test formulation (field 5) is equivalent to the subobject-test
formulation that Bridgeland uses implicitly, because in the quasi-abelian
interval category, strict subobjects correspond to kernels of strict epis,
which correspond to distinguished triangles with all vertices in the interval.

---

## Phase 4: Verdict -- Decline to Refactor

### No common abstraction is warranted

The three stability-like structures (`StabilityFunction`, `StabilityCondition`,
`SkewedStabilityFunction`) share a *mathematical pattern* but not a
*formal interface*. The pattern -- "additive function to C, derived phase,
semistability as phase-maximality, HN filtrations" -- does not factor into a
useful typeclass because:

1. **The categorical contexts are incompatible.** Subobjects in abelian
   categories, slicing predicates on triangulated categories, and strict monos in
   interval categories require different type-level infrastructure. A typeclass
   would need to abstract over the ambient exact structure, which Lean/Mathlib
   does not provide in a form that covers all three cases.

2. **The phase functions are structurally different.**
   - `StabilityFunction.phase` = `(1/pi) * arg(Z(E))`, branch-cut at 0.
   - Slicing phases are *axioms*, not computed from `Z`.
   - `wPhaseOf(W([E]), alpha)` has an explicit branch-cut parameter `alpha`.
   A common "phase" function would need to parametrize over branch cuts, which
   adds complexity with no shared lemma payoff.

3. **The nonvanishing axioms have different strengths.**
   - `StabilityFunction.upper`: image in `H union R_-` (implies nonzero + phase in (0,1])
   - `StabilityCondition.compat`: polar decomposition (implies nonzero + exact phase)
   - `SkewedStabilityFunction.nonzero`: just `W([E]) != 0`
   Weakening to a common "`Z(E) != 0` for nonzero semistables" would lose the
   polar decomposition that stability conditions need.

4. **The shared lemmas are few and short.** The phase-seesaw inequalities,
   iso-invariance, max-phase-implies-semistable, and simple-implies-semistable
   are each 5-15 line proofs. Unifying them would save at most ~50 lines
   across the entire codebase while requiring ~100+ lines of typeclass
   infrastructure and instantiation.

### The `SkewedStabilityFunction` definition is well-scoped

- It bundles exactly what the deformation argument needs: `W`, `alpha`, and
  the nonvanishing guarantee.
- The `Semistable` structure bundles well-formedness guards with the
  mathematical content, preventing hypothesis-proliferation in downstream
  lemmas.
- The constructor `skewedStabilityFunction_of_near` shows the definition
  is easy to instantiate from the actual use case.
- `ssf.nonzero` is used only 5 times (all in PhaseConfinement.lean);
  `ssf.hα_mem` is used 15 times (PhaseConfinement.lean + WPhase.lean).
  The fields carry their weight.

### One minor observation (not a recommendation)

The `nonzero` field of `SkewedStabilityFunction` quantifies over semistable
objects `E` with `(s.P phi) E`, but the downstream API almost exclusively
uses `hW_interval : forall F, intervalProp C a b F -> not IsZero F ->
ssf.W (K0.of C F) != 0` -- that is, W-nonvanishing for *all* nonzero interval
objects, not just semistable ones. Every major theorem
(`phase_le_of_strictQuotient`, `hn_exists_in_thin_interval`, etc.) carries
`hW_interval` as a separate hypothesis alongside `ssf`. This suggests that in
practice the nonvanishing extends beyond semistables to all interval objects.

However, mathematically, `skewedStabilityFunction_of_near` proves the stronger
`hW_interval` from the seminorm bound (via `W_ne_zero_of_seminorm_lt_one` and
the fact that every nonzero interval object has semistable HN factors). The
weaker field in the structure is correct: it records only what the definition
guarantees (nonvanishing on semistables), and the stronger property flows from
the construction. Strengthening the field to all interval objects would couple
the definition to HN existence, which is a theorem, not an axiom. The current
design correctly separates the definition from its instantiation context.

### Summary

**Decline to propose code changes.** The `SkewedStabilityFunction` and its
`Semistable` predicate are at the right level of abstraction for their role
in the deformation machine. No common typeclass with `StabilityFunction` or
`StabilityCondition` is mathematically or practically warranted.
