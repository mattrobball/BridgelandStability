# Trusted Formalization Base

The 59 project declarations reachable from Corollary 1.3, paired with the
corresponding natural language definitions from the paper. These are the
declarations a reader must trust to accept the formal statement — analogous to
a trusted code base.

For defs: the full definition term is shown. For theorems: only the type
signature (the proof is not part of the trusted base). Auto-generated
`._proof_N` declarations are grouped with their parent.

Reference: Bridgeland, "Stability conditions on triangulated categories",
Annals of Mathematics 166 (2007), 317--345.

---

## PostnikovTower/Defs.lean (3 declarations)

No direct paper counterpart. A finite chain of distinguished triangles
filtering an object E, with zero base and E at the top. Used as the
underlying data for HN filtrations.

```lean
structure PostnikovTower (E : C) where
  n : ℕ
  chain : ComposableArrows C n
  triangle : Fin n → Pretriangulated.Triangle C
  triangle_dist : ∀ i, triangle i ∈ distTriang C
  triangle_obj₁ : ∀ i, Nonempty ((triangle i).obj₁ ≅ chain.obj' i.val (by grind))
  triangle_obj₂ : ∀ i, Nonempty ((triangle i).obj₂ ≅ chain.obj' (i.val + 1) (by grind))
  base_isZero : IsZero (chain.left)
  top_iso : Nonempty (chain.right ≅ E)
  zero_isZero : n = 0 → IsZero E

variable {C} in
def PostnikovTower.factor {E : C} (P : PostnikovTower C E) (i : Fin P.n) : C :=
  (P.triangle i).obj₃
```

**Declarations:** `PostnikovTower`, `PostnikovTower.n`, `PostnikovTower.triangle`

---

## GrothendieckGroup/Defs.lean (8 declarations)

**Paper (implicit).** K(D) is the free abelian group on objects of D modulo
`[B] = [A] + [C]` for each distinguished triangle `A → B → C → A[1]`.

```lean
def K₀Subgroup : AddSubgroup (FreeAbelianGroup C) :=
  AddSubgroup.closure
    {x | ∃ (T : Pretriangulated.Triangle C), (T ∈ distTriang C) ∧
        x = FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ -
          FreeAbelianGroup.of T.obj₃}

def K₀ : Type _ := FreeAbelianGroup C ⧸ K₀Subgroup C

instance K₀.instAddCommGroup : AddCommGroup (K₀ C) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup C ⧸ K₀Subgroup C))

def K₀.of (X : C) : K₀ C :=
  (QuotientAddGroup.mk (FreeAbelianGroup.of X) : FreeAbelianGroup C ⧸ K₀Subgroup C)

class IsTriangleAdditive {A : Type*} [AddCommGroup A] (f : C → A) : Prop where
  additive : ∀ (T : Pretriangulated.Triangle C),
    T ∈ (distTriang C) → f T.obj₂ = f T.obj₁ + f T.obj₃

def K₀.lift {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] : K₀ C →+ A :=
  QuotientAddGroup.lift (K₀Subgroup C) (FreeAbelianGroup.lift f)
    ((AddSubgroup.closure_le _).mpr fun x ⟨T, hT, hx⟩ ↦ by
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hx, map_sub,
        FreeAbelianGroup.lift_apply_of]
      have h := IsTriangleAdditive.additive (f := f) T hT
      rw [h]; abel)
```

**Declarations:** `K₀Subgroup`, `K₀`, `K₀.instAddCommGroup`, `K₀.of`,
`IsTriangleAdditive`, `K₀.lift`, `K₀.lift._proof_1`, `K₀.lift._proof_2`

---

## Slicing/Defs.lean (13 declarations)

**Paper, Definition 3.3.** A slicing P of a triangulated category D consists
of full additive subcategories P(φ) ⊂ D for each φ ∈ ℝ, satisfying:

> (i) for all φ ∈ ℝ, P(φ + 1) = P(φ)[1],
>
> (ii) if φ₁ > φ₂ and Aⱼ ∈ P(φⱼ), then Hom_D(A₁, A₂) = 0,
>
> (iii) for each nonzero object E ∈ D there is a finite sequence of exact
> triangles [with] φ₁ > φ₂ > ⋯ > φₙ [and] Aᵢ ∈ P(φᵢ).

**Paper, after Lemma 3.2.** φ⁺(E) and φ⁻(E) denote the highest and lowest
phases appearing in the HN filtration of a nonzero object E.

```lean
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C) extends PostnikovTower C E where
  φ : Fin n → ℝ
  hφ : StrictAnti φ
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j)

structure Slicing where
  P : ℝ → ObjectProperty C
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)

noncomputable def Slicing.phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hn := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  F.φ ⟨0, hn⟩

noncomputable def Slicing.phiMinus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_last C s hE).choose
  let hn : 0 < F.n := (HNFiltration.exists_nonzero_last C s hE).choose_spec.choose
  F.φ ⟨F.n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩

-- Statements only (proofs omitted):

lemma HNFiltration.exists_nonzero_first (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n), ¬IsZero (F.triangle ⟨0, hn⟩).obj₃

lemma HNFiltration.exists_nonzero_last (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.triangle ⟨F.n - 1, by grind⟩).obj₃
```

**Declarations:** `HNFiltration`, `HNFiltration.toPostnikovTower`, `HNFiltration.φ`,
`Slicing`, `Slicing.P`, `Slicing.phiPlus`, `Slicing.phiPlus._proof_1`,
`Slicing.phiMinus`, `Slicing.phiMinus._proof_1`, `Slicing.phiMinus._proof_2`,
`HNFiltration.exists_nonzero_first`, `HNFiltration.exists_nonzero_last`,
`HNFiltration.exists_nonzero_last._proof_1`

---

## IntervalCategory/FiniteLength.lean (1 declaration)

**Paper, Definition 5.7.** A stability condition (Z, P) on D is locally
finite if there exists some η > 0 such that for all φ ∈ ℝ the quasi-abelian
category P((φ − η, φ + η)) is of finite length.

```lean
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  intervalFinite : ∃ η : ℝ, ∃ hη : 0 < η, ∃ hη' : η < 1 / 2, ∀ t : ℝ,
    let a := t - η
    let b := t + η
    letI : Fact (a < b) := ⟨by dsimp [a, b]; linarith⟩
    letI : Fact (b - a ≤ 1) := ⟨by dsimp [a, b]; linarith⟩
    ∀ (E : s.IntervalCat C a b),
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E
```

**Declarations:** `Slicing.IsLocallyFinite`

---

## StabilityCondition/Defs.lean (21 declarations)

**Paper, Definition 5.1.** A stability condition on a triangulated category
D consists of a group homomorphism Z : K(D) → ℂ called the central charge,
and full additive subcategories P(φ) ⊂ D for each φ ∈ ℝ, [...] satisfying
the following conditions:

> (a) if 0 ≠ E ∈ P(φ) then Z(E) = m(E) exp(iπφ) for some m(E) ∈ ℝ₊,
>
> (b) for all φ ∈ ℝ, P(φ + 1) = P(φ)[1],
>
> (c) if φ₁ > φ₂ and Aⱼ ∈ P(φⱼ) then Hom_D(A₁, A₂) = 0,
>
> (d) for each 0 ≠ E ∈ D there exist [...] Harder--Narasimhan filtrations.

**Paper, Proposition 8.1.** For slicings P and Q, define
d(P, Q) = sup { |φ⁺_P(E) − φ⁺_Q(E)|, |φ⁻_P(E) − φ⁻_Q(E)| : 0 ≠ E ∈ D } ∈ [0, ∞].

**Paper, §6 before Proposition 6.1.** For U : K(D) → ℂ, define
‖U‖_σ = sup { |U(E)| / |Z(E)| : E σ-semistable, E ≠ 0 }.

**Paper, §6 before Proposition 6.2.** Define
B_ε(σ) = { τ ∈ Stab(D) : ‖Z_τ − Z_σ‖_σ < sin(πε) and d(P_σ, P_τ) < ε }.

```lean
structure PreStabilityCondition.WithClassMap (v : K₀ C →+ Λ) where
  slicing : Slicing C
  Z : Λ →+ ℂ
  compat : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)

structure StabilityCondition.WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  locallyFinite : slicing.IsLocallyFinite C

def PreStabilityCondition.WithClassMap.toPreStabilityCondition {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) :
    WithClassMap C (AddMonoidHom.id (K₀ C)) where
  slicing := σ.slicing
  Z := σ.Z.comp v
  compat := by
    intro φ E hE hNZ
    simpa [AddMonoidHom.comp_apply] using σ.compat φ E hE hNZ

def StabilityCondition.WithClassMap.toStabilityCondition {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) :
    WithClassMap C (AddMonoidHom.id (K₀ C)) where
  toWithClassMap := σ.toWithClassMap.toPreStabilityCondition
  locallyFinite := σ.locallyFinite

abbrev StabilityCondition :=
  StabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))

-- Statement only (proof omitted):
theorem stabilityCondition_compat_apply (σ : StabilityCondition C)
    (φ : ℝ) (E : C) (hE : σ.slicing.P φ E) (hNZ : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      σ.Z (K₀.of C E) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)

def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)

def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)

def basisNhd (σ : StabilityCondition C) (ε : ℝ) : Set (StabilityCondition C) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}

instance StabilityCondition.topologicalSpace :
    TopologicalSpace (StabilityCondition C) :=
  TopologicalSpace.generateFrom
    {U | ∃ (σ : StabilityCondition C) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧
      U = basisNhd C σ ε}

abbrev StabilityCondition.WithClassMap.topologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  TopologicalSpace.induced
    (StabilityCondition.WithClassMap.toStabilityCondition (C := C) (v := v))
    inferInstance

instance (priority := 100) StabilityCondition.WithClassMap.instTopologicalSpace
    {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  StabilityCondition.WithClassMap.topologicalSpace (C := C) (v := v)

abbrev StabilityCondition.WithClassMap.ComponentIndex (v : K₀ C →+ Λ) :=
  _root_.ConnectedComponents (StabilityCondition.WithClassMap C v)

abbrev StabilityCondition.WithClassMap.Component (v : K₀ C →+ Λ)
    (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :=
  {σ : StabilityCondition.WithClassMap C v // _root_.ConnectedComponents.mk σ = cc}

def StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents
    {v : K₀ C →+ Λ} : Prop :=
  ∀ (cc : StabilityCondition.WithClassMap.ComponentIndex C v),
    ∃ (V : Submodule ℂ (Λ →+ ℂ))
      (_ : NormedAddCommGroup V)
      (_ : NormedSpace ℂ V)
      (hZ : ∀ σ : StabilityCondition.WithClassMap C v,
        ConnectedComponents.mk σ = cc → σ.Z ∈ V),
      @IsLocalHomeomorph
        (StabilityCondition.WithClassMap.Component C v cc)
        V inferInstance inferInstance
        (fun ⟨σ, hσ⟩ ↦ ⟨σ.Z, hZ σ hσ⟩)
```

**Declarations:** `PreStabilityCondition.WithClassMap`, `.Z`, `.mk`, `.slicing`,
`.toPreStabilityCondition`, `.toPreStabilityCondition._proof_1`,
`StabilityCondition`, `StabilityCondition.WithClassMap`, `.locallyFinite`,
`.mk`, `.toStabilityCondition`, `.toWithClassMap`, `stabilityCondition_compat_apply`,
`slicingDist`, `stabSeminorm`, `basisNhd`, `StabilityCondition.topologicalSpace`,
`.topologicalSpace._proof_1`, `WithClassMap.topologicalSpace`,
`.instTopologicalSpace`, `ComponentIndex`, `Component`,
`CentralChargeIsLocalHomeomorphOnConnectedComponents`

---

## NumericalStability/Defs.lean (2 declarations)

**Paper (implicit in §1).** A k-linear triangulated category has finite type
if all Hom spaces are finite-dimensional and only finitely many shifted Hom
spaces are nonzero.

**Paper, §1.** χ(E, F) = Σᵢ (−1)ⁱ dim Hom(E, F[i]).

```lean
class IsFiniteType [Linear k C] : Prop where
  finite_dim : ∀ (E F : C), Module.Finite k (E ⟶ F)
  finite_support : ∀ (E F : C),
    Set.Finite {n : ℤ | Nontrivial (E ⟶ (shiftFunctor C n).obj F)}

def eulerFormObj [Linear k C] (E F : C) : ℤ :=
  ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ (shiftFunctor C n).obj F) : ℤ)
```

**Declarations:** `IsFiniteType`, `eulerFormObj`

---

## EulerForm/Basic.lean (10 declarations)

**Paper, §1.** The Euler form χ descends to a bilinear form on K(D) and
N(D) = K(D) / K(D)⊥ where K(D)⊥ = {x ∈ K(D) : χ(x, y) = 0 for all y}.
The category is numerically finite if N(D) is finitely generated.

```lean
def eulerFormInner (E : C) : K₀ C →+ ℤ := by
  letI := eulerFormObj_contravariant_triangleAdditive (k := k) (C := C) E
  exact K₀.lift C (fun F ↦ eulerFormObj k C E F)

-- Statement only (proof omitted):
instance eulerFormInner_isTriangleAdditive
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    IsTriangleAdditive (eulerFormInner k C)

-- Statement only (proof omitted):
theorem eulerFormObj_contravariant_triangleAdditive (E : C) :
    IsTriangleAdditive (fun F ↦ eulerFormObj k C E F)

def eulerForm [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ K₀ C →+ ℤ :=
  K₀.lift C (eulerFormInner k C)

def eulerFormRad [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddSubgroup (K₀ C) :=
  (eulerForm k C).ker

def NumericalK₀ [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    Type _ :=
  K₀ C ⧸ eulerFormRad k C

instance NumericalK₀.instAddCommGroup [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddCommGroup (NumericalK₀ k C) :=
  inferInstanceAs (AddCommGroup (K₀ C ⧸ eulerFormRad k C))

abbrev numericalQuotientMap [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ NumericalK₀ k C :=
  QuotientAddGroup.mk' (eulerFormRad k C)

class NumericallyFinite [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] : Prop where
  fg : AddGroup.FG (NumericalK₀ k C)
```

**Declarations:** `eulerFormInner`, `eulerFormInner_isTriangleAdditive`,
`eulerFormObj_contravariant_triangleAdditive`, `eulerForm`, `eulerFormRad`,
`NumericalK₀`, `NumericalK₀.instAddCommGroup`, `numericalQuotientMap`,
`numericalQuotientMap._proof_1`, `NumericallyFinite`

---

## EulerForm/Defs.lean (1 declaration)

**Paper, Corollary 1.3.** Connected component of Stab_N(D).

```lean
abbrev NumericalComponent [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :=
  StabilityCondition.WithClassMap.Component C (numericalQuotientMap k C) cc
```

**Declarations:** `NumericalComponent`
