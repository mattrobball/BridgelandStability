# Trusted Formalization Base

The 63 project declarations reachable from Corollary 1.3, paired with the
corresponding natural language definitions from the paper. These are the
declarations a reader must trust to accept the formal statement — analogous to
a trusted code base.

For defs: the full definition term is shown. For theorems: only the type
signature. Auto-generated `._proof_N` declarations (compiler-generated
auxiliary proofs with fragile numbering) are omitted; structure field
projections are grouped with their parent structure.

Found by `Expr.foldConsts` on the theorem's type, descending into bodies of
non-theorem declarations and into inductive constructor types.

Reference: Bridgeland, "Stability conditions on triangulated categories",
Annals of Mathematics 166 (2007), 317--345. All section/line references
below are to the LaTeX source of the arXiv version (math/0212237v2).

### Formalization notes

The following points were verified by auditing against Bridgeland's LaTeX
source:

- **`intervalProp`** uses `∃ F : HNFiltration, ...` (exists an HN filtration
  with phases in (a,b)) rather than the paper's characterization via intrinsic
  phases a < φ⁻(E) ≤ φ⁺(E) < b (line 795). These are equivalent by
  uniqueness of HN phases, which is proved outside the TFB.

- **`basisNhd`** restricts ε < 1/8. The paper uses ε ∈ (0, 1/4) (line 1335).
  Both generate the same topology since the neighborhoods nest downward.

- **`slicingDist`** matches the metric on slicings from §6 (line 1276). This
  is NOT Proposition 8.1 (line 1772), which defines a metric on stability
  conditions with an additional log-mass term.

- **`IsLocallyFinite`** uses per-object strict-Artinian ∧ strict-Noetherian.
  Bridgeland defines "artinian" and "noetherian" for quasi-abelian categories
  via DCC/ACC on strict subobjects of each fixed object (lines 1003--1009),
  and "finite length" = artinian + noetherian (line 1008). The deformation
  proof applies these per-object chain conditions through Proposition 2.4
  (label `rud`, line 569) and Lemma 7.2 (label `floor`, line 1650). The
  modern "support property" (Kontsevich--Soibelman, Bayer--Macrì--Toda) is a
  stronger condition that implies locally finite; the formalization follows
  Bridgeland's original paper.

- **`QuasiAbelian`** does not appear in the 78 declarations. Bridgeland's
  Definition 5.7 says "the quasi-abelian category P((t−η, t+η))," but the
  quasi-abelian property of interval categories is a theorem proved in
  `IntervalCategory/QuasiAbelian.lean`, not an assumption. The TFB includes
  the resulting `intervalCat_hasKernels` and `intervalCat_hasCokernels`
  instances (statements only).

---

## PostnikovTower/Defs.lean (4 declarations)

No direct paper counterpart. A Postnikov tower is a finite chain of
distinguished triangles 0 = A₀ → A₁ → ⋯ → Aₙ ≅ E filtering an object E.

```lean
structure PostnikovTower (E : C) where
  -- Number of factors (= number of distinguished triangles)
  n : ℕ
  -- Chain of objects A₀ → A₁ → ⋯ → Aₙ
  chain : ComposableArrows C n
  -- Each consecutive pair completes to a distinguished triangle
  triangle : Fin n → Pretriangulated.Triangle C
  triangle_dist : ∀ i, triangle i ∈ distTriang C
  triangle_obj₁ : ∀ i, Nonempty ((triangle i).obj₁ ≅ chain.obj' i.val (by grind))
  triangle_obj₂ : ∀ i, Nonempty ((triangle i).obj₂ ≅ chain.obj' (i.val + 1) (by grind))
  -- A₀ = 0
  base_isZero : IsZero (chain.left)
  -- Aₙ ≅ E
  top_iso : Nonempty (chain.right ≅ E)
  zero_isZero : n = 0 → IsZero E

-- The i-th factor Fᵢ = (triangle i).obj₃
variable {C} in
def PostnikovTower.factor {E : C} (P : PostnikovTower C E) (i : Fin P.n) : C :=
  (P.triangle i).obj₃
```

**Declarations:** `PostnikovTower`, `PostnikovTower.n`, `PostnikovTower.triangle`,
`PostnikovTower.factor`

---

## GrothendieckGroup/Defs.lean (6 declarations)

**Paper (implicit).** K(D) is the free abelian group on objects of D modulo
[B] = [A] + [C] for each distinguished triangle A → B → C → A[1].

```lean
-- Paper: K(D) = Free(Ob D) / ⟨[B] - [A] - [C] : A → B → C → A[1] distinguished⟩
def K₀Subgroup : AddSubgroup (FreeAbelianGroup C) :=
  AddSubgroup.closure
    {x | ∃ (T : Pretriangulated.Triangle C), (T ∈ distTriang C) ∧
        x = FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ -
          FreeAbelianGroup.of T.obj₃}

def K₀ : Type _ := FreeAbelianGroup C ⧸ K₀Subgroup C

instance K₀.instAddCommGroup : AddCommGroup (K₀ C) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup C ⧸ K₀Subgroup C))

-- Paper: [E] ∈ K(D) denotes the class of an object E
def K₀.of (X : C) : K₀ C :=
  (QuotientAddGroup.mk (FreeAbelianGroup.of X) : FreeAbelianGroup C ⧸ K₀Subgroup C)

-- Paper: f is triangle-additive if f(B) = f(A) + f(C) for each dist. triangle A → B → C → A[1]
class IsTriangleAdditive {A : Type*} [AddCommGroup A] (f : C → A) : Prop where
  additive : ∀ (T : Pretriangulated.Triangle C),
    T ∈ (distTriang C) → f T.obj₂ = f T.obj₁ + f T.obj₃

-- Paper: universal property — triangle-additive f : Ob D → A lifts to K(D) →+ A
def K₀.lift {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] : K₀ C →+ A :=
  QuotientAddGroup.lift (K₀Subgroup C) (FreeAbelianGroup.lift f)
    ((AddSubgroup.closure_le _).mpr fun x ⟨T, hT, hx⟩ ↦ by
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hx, map_sub,
        FreeAbelianGroup.lift_apply_of]
      have h := IsTriangleAdditive.additive (f := f) T hT
      rw [h]; abel)
```

**Declarations:** `K₀Subgroup`, `K₀`, `K₀.instAddCommGroup`, `K₀.of`,
`IsTriangleAdditive`, `K₀.lift`

---

## ForMathlib/CategoryTheory/QuasiAbelian/Basic.lean (8 declarations)

No direct paper counterpart. Strict monomorphisms, strict subobjects, and the
strict-Artinian/Noetherian conditions used by `IsLocallyFinite`. In an abelian
category, strict = ordinary; in a quasi-abelian category, strict subobjects
(via strict monos) may be a proper subset of all subobjects.

```lean
-- A morphism is strict if its coimage-image comparison is an isomorphism
def IsStrict {X Y : C} (f : X ⟶ Y) : Prop :=
  IsIso (Abelian.coimageImageComparison f)

-- A strict monomorphism: mono + strict
structure IsStrictMono {X Y : C} (f : X ⟶ Y) : Prop where
  mono : Mono f
  strict : IsStrict f

-- A subobject is strict if its arrow is a strict monomorphism
def Subobject.IsStrict {X : C} (P : Subobject X) : Prop :=
  IsStrictMono P.arrow

-- Strict subobjects of X
abbrev StrictSubobject (X : C) :=
  { P : Subobject X // P.IsStrict }

-- Paper, Definition 5.7: "finite length" in the quasi-abelian sense
-- Strict-Artinian: DCC on strict subobjects
def isStrictArtinianObject : ObjectProperty C :=
  fun X ↦ WellFoundedLT (StrictSubobject X)

abbrev IsStrictArtinianObject : Prop := isStrictArtinianObject.Is X

-- Strict-Noetherian: ACC on strict subobjects
def isStrictNoetherianObject : ObjectProperty C :=
  fun X ↦ WellFoundedGT (StrictSubobject X)

abbrev IsStrictNoetherianObject : Prop := isStrictNoetherianObject.Is X
```

**Declarations:** `IsStrict`, `IsStrictMono`, `Subobject.IsStrict`,
`StrictSubobject`, `isStrictArtinianObject`, `IsStrictArtinianObject`,
`isStrictNoetherianObject`, `IsStrictNoetherianObject`

---

## Slicing/Defs.lean (10 declarations)

**Paper, Definition 3.3.** A slicing P of D consists of full additive
subcategories P(φ) ⊂ D for each φ ∈ ℝ, satisfying:
(i) P(φ + 1) = P(φ)[1],
(ii) if φ₁ > φ₂ and Aⱼ ∈ P(φⱼ), then Hom(A₁, A₂) = 0,
(iii) for each 0 ≠ E ∈ D there is a finite sequence of exact triangles with
φ₁ > φ₂ > ⋯ > φₙ and Aᵢ ∈ P(φᵢ).

**Paper, after Lemma 3.2.** φ⁺(E) and φ⁻(E) denote the highest and lowest
phases in the HN filtration of a nonzero object E.

**Paper, Definition 4.1.** P((a, b)) is the full subcategory of objects whose
HN factors all have phases in (a, b).

```lean
-- Paper, Definition 3.3 (iii): HN filtration with factors Aᵢ ∈ P(φᵢ), φ₁ > ⋯ > φₙ
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C) extends PostnikovTower C E where
  φ : Fin n → ℝ
  hφ : StrictAnti φ                                       -- φ₁ > φ₂ > ⋯ > φₙ
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j) -- Aⱼ ∈ P(φⱼ)

structure Slicing where
  P : ℝ → ObjectProperty C                                -- Paper: P(φ) ⊂ D
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)                    -- P(φ) additive ⇒ 0 ∈ P(φ)
  -- Paper (i): P(φ + 1) = P(φ)[1]
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  -- Paper (ii): φ₁ > φ₂, Aⱼ ∈ P(φⱼ) ⇒ Hom(A₁, A₂) = 0
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0
  -- Paper (iii): every object has an HN filtration
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)

-- Paper, Definition 4.1: P((a,b)) = {E : all HN phases of E lie in (a,b)}
def Slicing.intervalProp (s : Slicing C) (a b : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E), ∀ i, a < F.φ i ∧ F.φ i < b

-- Paper: φ⁺(E) = highest phase in the HN filtration of E
noncomputable def Slicing.phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hn := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  F.φ ⟨0, hn⟩

-- Paper: φ⁻(E) = lowest phase in the HN filtration of E
noncomputable def Slicing.phiMinus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_last C s hE).choose
  let hn : 0 < F.n := (HNFiltration.exists_nonzero_last C s hE).choose_spec.choose
  F.φ ⟨F.n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩

-- Statements only (proofs not part of the trusted base):

-- There exists an HN filtration whose first factor is nonzero
lemma HNFiltration.exists_nonzero_first (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n), ¬IsZero (F.triangle ⟨0, hn⟩).obj₃

-- There exists an HN filtration whose last factor is nonzero
lemma HNFiltration.exists_nonzero_last (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.triangle ⟨F.n - 1, by grind⟩).obj₃
```

**Declarations:** `HNFiltration`, `HNFiltration.toPostnikovTower`, `HNFiltration.φ`,
`Slicing`, `Slicing.P`, `Slicing.intervalProp`,
`Slicing.phiPlus`, `Slicing.phiMinus`,
`HNFiltration.exists_nonzero_first`, `HNFiltration.exists_nonzero_last`

---

## IntervalCategory/Basic.lean (1 declaration)

**Paper, Definition 4.1.** The interval subcategory P((a, b)).

```lean
-- Paper: P((a,b)) as a full subcategory of D
abbrev Slicing.IntervalCat (s : Slicing C) (a b : ℝ) :=
  (s.intervalProp C a b).FullSubcategory
```

**Declarations:** `Slicing.IntervalCat`

---

## IntervalCategory/QuasiAbelian.lean (2 declarations)

**Paper (implicit in Definition 5.7).** The interval category P((a, b)) has
kernels and cokernels (it is quasi-abelian when b − a ≤ 1).

```lean
-- Statements only (proofs not part of the trusted base):

noncomputable instance Slicing.intervalCat_hasKernels (s : Slicing C) :
    HasKernels (s.IntervalCat C a b)

noncomputable instance Slicing.intervalCat_hasCokernels (s : Slicing C) :
    HasCokernels (s.IntervalCat C a b)
```

**Declarations:** `Slicing.intervalCat_hasKernels`, `Slicing.intervalCat_hasCokernels`

---

## IntervalCategory/FiniteLength.lean (1 declaration)

**Paper, Definition 5.7.** A stability condition (Z, P) on D is locally
finite if there exists some η > 0 such that for all φ ∈ ℝ the quasi-abelian
category P((φ − η, φ + η)) is of finite length.

```lean
-- Paper: ∃ η > 0 s.t. P((t − η, t + η)) has finite length for all t
-- Formalization: "finite length" = strict-Artinian ∧ strict-Noetherian
-- The bound η < 1/2 ensures interval width ≤ 1 (needed for quasi-abelian structure)
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

## StabilityCondition/Defs.lean (19 declarations)

**Paper, Definition 5.1.** A stability condition on D consists of
Z : K(D) → ℂ (the central charge) and subcategories P(φ) satisfying:
(a) 0 ≠ E ∈ P(φ) ⇒ Z(E) = m(E) exp(iπφ) for some m(E) ∈ ℝ₊,
(b)--(d) as in Definition 3.3.

**Paper, Definition 5.7.** Locally finite = slicing is locally finite.

**Paper, Proposition 8.1.** d(P, Q) = sup { |φ⁺\_P(E) − φ⁺\_Q(E)|, |φ⁻\_P(E) − φ⁻\_Q(E)| : 0 ≠ E ∈ D }.

**Paper, §6.** ‖U‖\_σ = sup { |U(E)|/|Z(E)| : E σ-semistable, E ≠ 0 }.
B\_ε(σ) = { τ : ‖Z\_τ − Z\_σ‖\_σ < sin(πε) and d(P\_σ, P\_τ) < ε }.

```lean
namespace PreStabilityCondition

-- Paper, Definition 5.1: σ = (Z, P) with Z : K(D) → ℂ and P a slicing
-- Class-map version: Z factors through v : K₀(C) → Λ
structure WithClassMap (v : K₀ C →+ Λ) where
  slicing : Slicing C                                     -- Paper: P
  Z : Λ →+ ℂ                                              -- Paper: Z (on class lattice)
  -- Paper (a): 0 ≠ E ∈ P(φ) ⇒ Z(E) = m·exp(iπφ), m > 0
  compat : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)

-- Forget class map: (Z, P) on Λ ↦ (Z ∘ v, P) on K₀(C)
def WithClassMap.toPreStabilityCondition {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) :
    WithClassMap C (AddMonoidHom.id (K₀ C)) where
  slicing := σ.slicing
  Z := σ.Z.comp v
  compat := by
    intro φ E hE hNZ
    simpa [AddMonoidHom.comp_apply] using σ.compat φ E hE hNZ

end PreStabilityCondition

namespace StabilityCondition

-- Paper, Definition 5.7: locally finite stability condition
structure WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  locallyFinite : slicing.IsLocallyFinite C               -- Paper: P is locally finite

-- Forget class map for stability conditions
def WithClassMap.toStabilityCondition {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) :
    WithClassMap C (AddMonoidHom.id (K₀ C)) where
  toWithClassMap := σ.toWithClassMap.toPreStabilityCondition
  locallyFinite := σ.locallyFinite

end StabilityCondition

-- Paper: Stab(D) = stability conditions with v = id
abbrev StabilityCondition :=
  StabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))

-- Paper, Proposition 8.1: d(P, Q) = sup_{0≠E} max(|φ⁺_P(E)−φ⁺_Q(E)|, |φ⁻_P(E)−φ⁻_Q(E)|)
def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)

-- Paper, §6: ‖U‖_σ = sup_{E semistable, E≠0} |U(E)|/|Z(E)|
def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)

-- Paper, §6: B_ε(σ) = {τ : ‖Z_τ − Z_σ‖_σ < sin(πε) and d(P_σ, P_τ) < ε}
def basisNhd (σ : StabilityCondition C) (ε : ℝ) : Set (StabilityCondition C) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}

-- Paper, §6: topology on Stab(D) generated by B_ε(σ)
instance StabilityCondition.topologicalSpace :
    TopologicalSpace (StabilityCondition C) :=
  TopologicalSpace.generateFrom
    {U | ∃ (σ : StabilityCondition C) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧
      U = basisNhd C σ ε}

-- Topology on Stab_v(D): induced from Stab(D) via forgetting the class map
abbrev StabilityCondition.WithClassMap.topologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  TopologicalSpace.induced
    (StabilityCondition.WithClassMap.toStabilityCondition (C := C) (v := v))
    inferInstance

instance (priority := 100) StabilityCondition.WithClassMap.instTopologicalSpace
    {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  StabilityCondition.WithClassMap.topologicalSpace (C := C) (v := v)

-- Paper: connected components of Stab_v(D)
abbrev StabilityCondition.WithClassMap.ComponentIndex (v : K₀ C →+ Λ) :=
  _root_.ConnectedComponents (StabilityCondition.WithClassMap C v)

-- Paper: Σ ⊂ Stab_v(D), a single connected component
abbrev StabilityCondition.WithClassMap.Component (v : K₀ C →+ Λ)
    (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :=
  {σ : StabilityCondition.WithClassMap C v // _root_.ConnectedComponents.mk σ = cc}
```

**Declarations:** `PreStabilityCondition.WithClassMap`, `.Z`, `.mk`, `.slicing`,
`.toPreStabilityCondition`,
`StabilityCondition.WithClassMap`, `.locallyFinite`, `.mk`,
`.toStabilityCondition`, `.toWithClassMap`,
`StabilityCondition`,
`slicingDist`, `stabSeminorm`, `basisNhd`,
`StabilityCondition.topologicalSpace`,
`StabilityCondition.WithClassMap.topologicalSpace`, `.instTopologicalSpace`,
`.ComponentIndex`, `.Component`

---

## NumericalStability/Defs.lean (2 declarations)

**Paper (implicit in §1).** A k-linear triangulated category has finite type
if all Hom spaces are finite-dimensional and only finitely many shifted Hom
spaces Hom(E, F[n]) are nonzero.

**Paper, §1.** χ(E, F) = Σᵢ (−1)ⁱ dim Hom(E, F[i]).

```lean
-- Paper: D is of finite type over k
class IsFiniteType [Linear k C] : Prop where
  finite_dim : ∀ (E F : C), Module.Finite k (E ⟶ F)       -- dim_k Hom(E,F) < ∞
  finite_support : ∀ (E F : C),                            -- {n : Hom(E,F[n]) ≠ 0} is finite
    Set.Finite {n : ℤ | Nontrivial (E ⟶ (shiftFunctor C n).obj F)}

-- Paper: χ(E,F) = Σₙ (-1)ⁿ dim_k Hom(E, F[n])
def eulerFormObj [Linear k C] (E F : C) : ℤ :=
  ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ (shiftFunctor C n).obj F) : ℤ)
```

**Declarations:** `IsFiniteType`, `eulerFormObj`

---

## EulerForm/Basic.lean (9 declarations)

**Paper, §1.** The Euler form χ descends to a bilinear form χ : K(D) × K(D) → ℤ.
N(D) = K(D) / K(D)⊥ where K(D)⊥ = {x ∈ K(D) : χ(x, y) = 0 for all y}.
D is numerically finite if N(D) is finitely generated.

```lean
-- Paper: for fixed E, F ↦ χ(E, F) is triangle-additive, so lifts to K₀
def eulerFormInner (E : C) : K₀ C →+ ℤ := by
  letI := eulerFormObj_contravariant_triangleAdditive (k := k) (C := C) E
  exact K₀.lift C (fun F ↦ eulerFormObj k C E F)

-- Statement only: E ↦ χ(E, −) is triangle-additive
instance eulerFormInner_isTriangleAdditive
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    IsTriangleAdditive (eulerFormInner k C)

-- Statement only: F ↦ χ(−, F) is triangle-additive
theorem eulerFormObj_contravariant_triangleAdditive (E : C) :
    IsTriangleAdditive (fun F ↦ eulerFormObj k C E F)

-- Paper: χ : K(D) × K(D) → ℤ, bilinear on K₀
def eulerForm [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ K₀ C →+ ℤ :=
  K₀.lift C (eulerFormInner k C)

-- Paper: K(D)⊥ = ker(χ) = {x : χ(x, y) = 0 ∀y} (left radical)
def eulerFormRad [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddSubgroup (K₀ C) :=
  (eulerForm k C).ker

-- Paper: N(D) = K(D) / K(D)⊥
def NumericalK₀ [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    Type _ :=
  K₀ C ⧸ eulerFormRad k C

instance NumericalK₀.instAddCommGroup [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddCommGroup (NumericalK₀ k C) :=
  inferInstanceAs (AddCommGroup (K₀ C ⧸ eulerFormRad k C))

-- Paper: the quotient map K(D) → N(D)
abbrev numericalQuotientMap [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ NumericalK₀ k C :=
  QuotientAddGroup.mk' (eulerFormRad k C)

-- Paper: D is numerically finite if N(D) is finitely generated
class NumericallyFinite [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] : Prop where
  fg : AddGroup.FG (NumericalK₀ k C)
```

**Declarations:** `eulerFormInner`, `eulerFormInner_isTriangleAdditive`,
`eulerFormObj_contravariant_triangleAdditive`, `eulerForm`, `eulerFormRad`,
`NumericalK₀`, `NumericalK₀.instAddCommGroup`, `numericalQuotientMap`,
`NumericallyFinite`

---

## EulerForm/Defs.lean (1 declaration)

**Paper, Corollary 1.3.** Σ ⊂ Stab\_N(D), a connected component of
numerical stability conditions.

```lean
-- Paper: Σ ⊂ Stab_N(D)
abbrev NumericalComponent [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :=
  StabilityCondition.WithClassMap.Component C (numericalQuotientMap k C) cc
```

**Declarations:** `NumericalComponent`
