# Trusted Formalization Base

The 59 project declarations reachable from Corollary 1.3, paired with the
corresponding natural language definitions from the paper. These are the
declarations a reader must trust to accept the formal statement — analogous to
a trusted code base.

Auto-generated `._proof_N` declarations are grouped with their parent.

Reference: Bridgeland, "Stability conditions on triangulated categories", Annals of
Mathematics 166 (2007), 317–345.

---

## PostnikovTower.Defs (3 declarations)

No direct paper counterpart. This is infrastructure: a finite chain of distinguished
triangles filtering an object `E`, with zero base and `E` at the top. Used as the
underlying data for HN filtrations.

```lean
structure PostnikovTower (C : Type u) [Category.{v} C] ... (E : C) where
  n : ℕ
  chain : ComposableArrows C n
  triangle : Fin n → Triangle C
  triangle_dist : ∀ i, triangle i ∈ distTriang C
  triangle_obj₁ : ∀ i, Nonempty (triangle i).obj₁ ≅ chain.obj' i.val ...
  triangle_obj₂ : ∀ i, Nonempty (triangle i).obj₂ ≅ chain.obj' (i.val + 1) ...
  base_isZero : IsZero chain.left
  top_iso : Nonempty (chain.right ≅ E)
  zero_isZero : n = 0 → IsZero E
```

**Declarations:** `PostnikovTower`, `PostnikovTower.n`, `PostnikovTower.triangle`

---

## GrothendieckGroup.Defs (8 declarations)

### K₀(D)

**Paper (implicit).** The Grothendieck group K(D) is the free abelian group on
objects of D modulo [B] = [A] + [C] for each distinguished triangle A → B → C → A[1].

```lean
def K₀Subgroup : AddSubgroup (FreeAbelianGroup C) := ...
def K₀ : Type _ := FreeAbelianGroup C ⧸ K₀Subgroup C
instance K₀.instAddCommGroup : AddCommGroup (K₀ C) := ...
def K₀.of (E : C) : K₀ C := QuotientAddGroup.mk (FreeAbelianGroup.of E)
```

### Universal property

```lean
class IsTriangleAdditive (f : C → A) [AddCommGroup A] : Prop where
  additive : ∀ T ∈ distTriang C, f T.obj₂ = f T.obj₁ + f T.obj₃
def K₀.lift [IsTriangleAdditive f] : K₀ C →+ A := ...
```

**Declarations:** `K₀`, `K₀.instAddCommGroup`, `K₀.of`, `K₀.lift`,
`K₀.lift._proof_1`, `K₀.lift._proof_2`, `K₀Subgroup`, `IsTriangleAdditive`

---

## Slicing.Defs (13 declarations)

### HN filtration — Definition 3.3 (iii)

**Paper.** For each nonzero object E ∈ D there is a finite sequence of
distinguished triangles with factors Aᵢ ∈ P(φᵢ) and φ₁ > φ₂ > ⋯ > φₙ.

```lean
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C)
    extends PostnikovTower C E where
  φ : Fin n → ℝ
  hφ : StrictAnti φ
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j)
```

**Declarations:** `HNFiltration`, `HNFiltration.toPostnikovTower`, `HNFiltration.φ`

### Slicing — Definition 3.3

**Paper.** A slicing P of D consists of full additive subcategories P(φ) ⊂ D
for each φ ∈ ℝ, satisfying:

(i) P(φ)[1] = P(φ + 1) for all φ

(ii) if φ₁ > φ₂ and Aⱼ ∈ P(φⱼ) then Hom(A₁, A₂) = 0

(iii) every nonzero E has an HN filtration

```lean
structure Slicing where
  P : ℝ → ObjectProperty C
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)
```

The formalization uses `ObjectProperty` (a predicate on objects) rather than a
subcategory, so `closedUnderIso` and `zero_mem` are stated explicitly (they
follow from P(φ) being a full additive subcategory). `hn_exists` quantifies
over all objects including zero, returning `Nonempty`.

**Declarations:** `Slicing`, `Slicing.P`

### Intrinsic phases — §3 after Lemma 3.2

**Paper.** For a nonzero object E, define φ⁺(E) as the highest phase and
φ⁻(E) as the lowest phase in any HN filtration. These are well-defined
(independent of the choice of filtration).

```lean
noncomputable def Slicing.phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hn := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  F.φ ⟨0, hn⟩

noncomputable def Slicing.phiMinus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_last C s hE).choose
  let hn := ... F.φ ⟨F.n - 1, ...⟩
```

Well-definedness (`phiPlus_eq`, `phiMinus_eq`) is proved in `Slicing/Phase.lean`
but is not in the challenge path. The definitions use `Classical.choice` to
pick a witness.

**Declarations:** `Slicing.phiPlus`, `Slicing.phiPlus._proof_1`,
`Slicing.phiMinus`, `Slicing.phiMinus._proof_1`, `Slicing.phiMinus._proof_2`,
`HNFiltration.exists_nonzero_first`, `HNFiltration.exists_nonzero_last`,
`HNFiltration.exists_nonzero_last._proof_1`

---

## IntervalCategory.FiniteLength (1 declaration)

### Local finiteness — Definition 5.7

**Paper.** A slicing P is locally finite if there exists η > 0 such that for
each t ∈ ℝ, the quasi-abelian category P((t − η, t + η)) has finite length.

```lean
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  intervalFinite : ∃ η : ℝ, ∃ hη : 0 < η, ∃ hη' : η < 1 / 2, ∀ t : ℝ,
    ...
    ∀ (E : s.IntervalCat C a b),
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E
```

"Finite length" is formalized as strict-Artinian ∧ strict-Noetherian.
In a quasi-abelian category, strict subobjects (via strict monos) may be a
proper subset of all subobjects (via monos), so strict-Artinian is weaker than
Artinian. The bound `η < 1/2` ensures the interval width stays ≤ 1, which is
needed for the quasi-abelian structure on P((a,b)).

**Declarations:** `Slicing.IsLocallyFinite`

---

## StabilityCondition.Defs (21 declarations)

### Prestability condition — Definition 5.1

**Paper.** A stability condition on D is a pair σ = (Z, P) where Z : K(D) → ℂ
is a group homomorphism (the central charge) and P is a slicing, with
compatibility: for nonzero E ∈ P(φ), Z(E) ∈ ℝ₊ · exp(iπφ).

```lean
structure PreStabilityCondition.WithClassMap (v : K₀ C →+ Λ) where
  slicing : Slicing C
  Z : Λ →+ ℂ
  compat : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)
```

The class-map version factors Z through v : K₀(C) → Λ. The ordinary
stability condition recovers v = id. The `compat` condition says
Z(v([E])) = m · exp(iπφ) for some m > 0.

### Stability condition — Definition 5.7

**Paper.** A stability condition is locally finite if its slicing is locally
finite.

```lean
structure StabilityCondition.WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  locallyFinite : slicing.IsLocallyFinite C

abbrev StabilityCondition :=
  StabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))
```

**Declarations:** `PreStabilityCondition.WithClassMap`, `.Z`, `.mk`, `.slicing`,
`.toPreStabilityCondition`, `.toPreStabilityCondition._proof_1`,
`StabilityCondition`, `StabilityCondition.WithClassMap`, `.locallyFinite`, `.mk`,
`.toStabilityCondition`, `.toWithClassMap`

### Generalized metric — Proposition 8.1

**Paper.** d(P, Q) = sup_{0 ≠ E ∈ D} { |φ⁺_P(E) − φ⁺_Q(E)|, |φ⁻_P(E) − φ⁻_Q(E)| }
∈ [0, ∞].

```lean
def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)
```

### Seminorm — Section 6 (before Proposition 6.1)

**Paper.** ‖W‖_σ = sup_{E σ-semistable, E ≠ 0} |W(E)| / |Z(E)|.

```lean
def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)
```

### Topology — Section 6 (before Proposition 6.2)

**Paper.** The topology on Stab(D) has basis neighborhoods
B_ε(σ) = { τ : ‖Z_τ − Z_σ‖_σ < sin(πε) and d(P_σ, P_τ) < ε }.

```lean
def basisNhd (σ : StabilityCondition C) (ε : ℝ) : Set (StabilityCondition C) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}

instance StabilityCondition.topologicalSpace :
    TopologicalSpace (StabilityCondition C) :=
  TopologicalSpace.generateFrom
    {U | ∃ (σ : StabilityCondition C) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧
      U = basisNhd C σ ε}
```

The paper does not restrict ε to (0, 1/8). The bound ensures certain sector
estimates hold. `generateFrom` with `ε < 1/8` produces the same topology as
using all ε > 0 because B_ε(σ) nests downward and the neighborhoods form a
basis (Proposition 6.2, proved outside the challenge path).

### Induced topology on Stab_v(D)

```lean
abbrev WithClassMap.topologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  TopologicalSpace.induced
    (WithClassMap.toStabilityCondition (C := C) (v := v)) inferInstance

instance (priority := 100) instTopologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  WithClassMap.topologicalSpace (C := C) (v := v)
```

The induced topology pulls back along `toStabilityCondition`, which composes Z
with v. For the numerical case (Corollary 1.3), v = numericalQuotientMap is
surjective, so toStabilityCondition is injective.

### Connected components

```lean
abbrev ComponentIndex (v : K₀ C →+ Λ) :=
  ConnectedComponents (StabilityCondition.WithClassMap C v)

abbrev Component (v : K₀ C →+ Λ)
    (cc : ComponentIndex C v) :=
  {σ : StabilityCondition.WithClassMap C v // ConnectedComponents.mk σ = cc}
```

**Declarations:** `slicingDist`, `stabSeminorm`, `basisNhd`,
`StabilityCondition.topologicalSpace`, `.topologicalSpace._proof_1`,
`WithClassMap.topologicalSpace`, `.instTopologicalSpace`,
`ComponentIndex`, `Component`

---

## NumericalStability.Defs (2 declarations)

### Finite type — Blueprint B0

**Paper (implicit).** A k-linear triangulated category has finite type if all
Hom spaces are finite-dimensional and for each pair (E, F), only finitely many
Hom(E, F[n]) are nonzero.

```lean
class IsFiniteType [Linear k C] : Prop where
  finite_dim : ∀ (E F : C), Module.Finite k (E ⟶ F)
  finite_support : ∀ (E F : C),
    Set.Finite {n : ℤ | Nontrivial (E ⟶ (shiftFunctor C n).obj F)}
```

### Euler form on objects — Section 1

**Paper.** χ(E, F) = Σᵢ (−1)ⁱ dim Hom(E, F[i]).

```lean
def eulerFormObj [Linear k C] (E F : C) : ℤ :=
  ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ (shiftFunctor C n).obj F) : ℤ)
```

**Declarations:** `IsFiniteType`, `eulerFormObj`

---

## EulerForm.Basic (10 declarations)

### Euler form on K₀ — Section 1

**Paper.** The Euler form descends to a bilinear form χ : K(D) × K(D) → ℤ.

```lean
def eulerFormInner (E : C) : K₀ C →+ ℤ := by
  letI := eulerFormObj_contravariant_triangleAdditive (k := k) (C := C) E
  exact K₀.lift C (fun F ↦ eulerFormObj k C E F)

def eulerForm [(shiftFunctor C (1 : ℤ)).Linear k] : K₀ C →+ K₀ C →+ ℤ :=
  K₀.lift C (eulerFormInner k C)
```

Triangle-additivity in both arguments is proved in
`eulerFormObj_contravariant_triangleAdditive` (second argument) and
`eulerFormInner_isTriangleAdditive` (first argument). These theorems appear in
the 59 declarations because `eulerFormInner` and `eulerForm` reference them in
their definitions via `letI` and `K₀.lift`.

### Numerical Grothendieck group — Section 1

**Paper.** N(D) = K(D) / K(D)⊥ where K(D)⊥ = ker(χ) = {x : χ(x, y) = 0 ∀y}.

```lean
def eulerFormRad : AddSubgroup (K₀ C) := (eulerForm k C).ker
def NumericalK₀ : Type _ := K₀ C ⧸ eulerFormRad k C
instance NumericalK₀.instAddCommGroup : AddCommGroup (NumericalK₀ k C) := ...
abbrev numericalQuotientMap : K₀ C →+ NumericalK₀ k C :=
  QuotientAddGroup.mk' (eulerFormRad k C)
```

`eulerFormRad` is the left radical: ker(E ↦ χ(E, −)). The Euler form is not
symmetric in general, so left radical ≠ right radical.

### Numerical finiteness — Section 1

**Paper.** D is numerically finite if N(D) is finitely generated.

```lean
class NumericallyFinite [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] : Prop where
  fg : AddGroup.FG (NumericalK₀ k C)
```

**Declarations:** `eulerFormInner`, `eulerFormInner_isTriangleAdditive`,
`eulerFormObj_contravariant_triangleAdditive`, `eulerForm`, `eulerFormRad`,
`NumericalK₀`, `NumericalK₀.instAddCommGroup`, `numericalQuotientMap`,
`numericalQuotientMap._proof_1`, `NumericallyFinite`

---

## EulerForm.Defs (1 declaration)

### Connected component type

```lean
abbrev NumericalComponent [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C
      (numericalQuotientMap k C)) :=
  StabilityCondition.WithClassMap.Component C (numericalQuotientMap k C) cc
```

**Declarations:** `NumericalComponent`

