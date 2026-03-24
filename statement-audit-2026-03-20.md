# Statement Audit: Theorem 1.2 and Corollary 1.3 (2026-03-20)

Ruthless audit of the Lean formalization of the **statements** of Bridgeland's
Theorem 1.2 and Corollary 1.3, including ALL definitions and data-carrying types
that feed into them. Every definition unfolded and compared to the primary source:

> Bridgeland, "Stability conditions on triangulated categories",
> arXiv:math/0212237v3, Annals of Mathematics 2007.

**Update (2026-03-24):** the repo now uses a class-map-first architecture.
The primary generic object is `StabilityCondition.WithClassMap`, and the
public generic local-homeomorphism statement is
`StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents`.
Older references in this audit to `ClassMapStabilityCondition` as the primary
object, or to `sigma.factors.choose` in Corollary 1.3 packaging, are
superseded by the updates below.

---

## Part I: Paper Statements (verbatim)

### Definition 1.1 (p.2)

A stability condition (Z, P) on a triangulated category D consists of a group
homomorphism Z: K(D) -> C called the *central charge*, and full additive
subcategories P(phi) in D for each phi in R, satisfying:

(a) if E in P(phi) then Z(E) = m(E) exp(i pi phi) for some m(E) in R_{>0},
(b) for all phi in R, P(phi + 1) = P(phi)[1],
(c) if phi_1 > phi_2 and A_j in P(phi_j) then Hom_D(A_1, A_2) = 0,
(d) for each nonzero object E in D there is a finite sequence of real numbers
    phi_1 > phi_2 > ... > phi_n and a collection of triangles [diagram] with
    A_j in P(phi_j) for all j.

### Definition 5.7 (p.14)

A stability condition is *locally finite* if there exists eta > 0 such that
for each phi in R, the quasi-abelian category P((phi - eta, phi + eta)) has
finite length.

### Theorem 1.2 (p.3)

Let D be a triangulated category. For each connected component
Sigma in Stab(D) there is a **linear subspace** V(Sigma) in Hom_Z(K(D), C)
with a **well-defined linear topology** and a local homeomorphism
Z: Sigma -> V(Sigma) which maps a stability condition (Z, P) to its central
charge Z.

### Corollary 1.3 (p.3)

Suppose D is numerically finite. For each connected component
Sigma in Stab_N(D) there is a subspace V(Sigma) in Hom_Z(N(D), C) and a local
homeomorphism Z: Sigma -> V(Sigma) which maps a stability condition to its
central charge Z. In particular Sigma is a finite-dimensional complex manifold.

---

## Part II: Complete Dependency Tree

```
StabilityCondition C
|
+-- Slicing C
|   +-- P : R -> ObjectProperty C
|   +-- closedUnderIso : forall phi, (P phi).IsClosedUnderIsomorphisms
|   +-- zero_mem : forall phi, (P phi) (0 : C)
|   +-- shift_iff : forall phi X, (P phi) X <-> (P (phi+1)) (X[1])
|   +-- hom_vanishing : forall phi1 phi2 A B, phi2 < phi1 -> P(phi1)(A) -> P(phi2)(B)
|   |                    -> forall f : A --> B, f = 0
|   +-- hn_exists : forall E, Nonempty (HNFiltration C P E)
|       +-- HNFiltration C P E
|           +-- extends PostnikovTower C E
|           |   +-- n : Nat
|           |   +-- chain : ComposableArrows C n    (A_0 -> A_1 -> ... -> A_n)
|           |   +-- triangle : Fin n -> Triangle C
|           |   +-- triangle_dist : forall i, triangle i in distTriang C
|           |   +-- triangle_obj1 : forall i, Nonempty ((triangle i).obj1 ~= chain(i))
|           |   +-- triangle_obj2 : forall i, Nonempty ((triangle i).obj2 ~= chain(i+1))
|           |   +-- base_isZero : IsZero chain.left
|           |   +-- top_iso : Nonempty (chain.right ~= E)
|           |   +-- zero_isZero : n = 0 -> IsZero E
|           |   +-- factor i := (triangle i).obj3     (derived, not stored)
|           +-- phi : Fin n -> R
|           +-- hphi : StrictAnti phi
|           +-- semistable : forall j, (P (phi j)) (factor j)
|
+-- Z : K0 C ->+ C
|   +-- K0 C := FreeAbelianGroup C / K0Subgroup C
|       +-- K0Subgroup C := closure {[B]-[A]-[C] : T in distTriang C}
|
+-- compat : forall phi E, P(phi)(E) -> not (IsZero E) ->
|            exists m > 0, Z([E]) = m * exp(i*pi*phi)
|
+-- locallyFinite : Slicing.IsLocallyFinite C
    +-- IsLocallyFinite s :=
        exists eta > 0, eta < 1/2, forall t,
          forall E in IntervalCat(t-eta, t+eta),
            IsStrictArtinianObject E /\ IsStrictNoetherianObject E
        |
        +-- IntervalCat s a b := FullSubcategory (intervalProp s a b)
        |   +-- intervalProp s a b E :=
        |       IsZero E \/ exists (F : HNFiltration), forall i, a < F.phi i /\ F.phi i < b
        |
        +-- IsStrictArtinianObject E := WellFoundedLT (StrictSubobject E)
        +-- IsStrictNoetherianObject E := WellFoundedGT (StrictSubobject E)
            +-- StrictSubobject E := { P : Subobject E // IsStrictMono P.arrow }
                +-- IsStrictMono f := Mono f /\ IsStrict f
                    +-- IsStrict f := IsIso (coimageImageComparison f)
```

For Theorem 1.2 additionally:

```
StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents C :=
  forall cc : ConnectedComponents (StabilityCondition C),
    exists (V : AddSubgroup (K0 C ->+ C))
           (tau_V : TopologicalSpace V)
           (hZ : forall sigma, mk sigma = cc -> sigma.Z in V),
      IsLocalHomeomorph (fun sigma => (sigma.Z, hZ ...))
|
+-- StabilityCondition.topologicalSpace :=
|   TopologicalSpace.generateFrom
|     { U | exists sigma eps, 0 < eps /\ eps < 1/8 /\ U = basisNhd sigma eps }
|   +-- basisNhd sigma eps :=
|       { tau | stabSeminorm sigma (tau.Z - sigma.Z) < ofReal(sin(pi*eps))
|               /\ slicingDist sigma.slicing tau.slicing < ofReal(eps) }
|       +-- stabSeminorm sigma U :=
|           sup over nonzero sigma-semistable E of ||U([E])|| / ||Z([E])||
|       +-- slicingDist s1 s2 :=
|           sup over nonzero E of max(|phi+(E)-phi+(E)|, |phi-(E)-phi-(E)|)
|
+-- finiteSeminormSubgroup sigma := { U | stabSeminorm sigma U < top }
```

For Corollary 1.3 additionally:

```
StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents
  (C := C) (Λ := Λ) (v := v) :=
  forall cc : ConnectedComponents (StabilityCondition.WithClassMap C v),
    exists (V : Submodule C (Λ ->+ C)) ...
      IsLocalHomeomorph (fun sigma => sigma.1.Z)
|
+-- eulerForm k C : K0 C ->+ K0 C ->+ Z
|   := K0.lift C (eulerFormInner k C)
|   +-- eulerFormInner k C (E : C) : K0 C ->+ Z
|       := K0.lift C (fun F => eulerFormObj k C E F)
|       +-- eulerFormObj k C E F : Z
|           := finsum n, (-1)^n * finrank_k Hom(E, F[n])
|
+-- PreStabilityCondition.WithClassMap C v
|   +-- slicing : Slicing C
|   +-- Z : Λ ->+ C
|   +-- compat : ...
+-- StabilityCondition.WithClassMap C v
|   +-- extends PreStabilityCondition.WithClassMap C v
|   +-- locallyFinite : ...
+-- StabilityCondition.FactorsThrough C v sigma :=
|     exists Z' : Λ ->+ C, sigma.Z = Z'.comp v
+-- ClassMapStabilityCondition C v :=
|     { sigma : StabilityCondition C // sigma.FactorsThrough v }
+-- eulerFormRad k C := (eulerForm k C).ker
+-- NumericalK0 k C := K0 C / eulerFormRad k C
+-- NumericallyFinite k C := AddGroup.FG (NumericalK0 k C)
+-- NumericalStabilityCondition k C :=
|     StabilityCondition.WithClassMap C (numericalQuotientMap k C)
+-- NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents
|     := NumericallyFinite k C ->
|        StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents
|             (C := C) (Λ := NumericalK0 k C) (v := numericalQuotientMap k C)
```

---

## Part III: Declaration-by-Declaration Comparison

### PostnikovTower (`PostnikovTower.lean:63`)

| Field | Lean | Paper (Def 1.1(d)) | Verdict |
|-------|------|---------------------|---------|
| `n : Nat` | Number of factors | n (length of filtration) | FAITHFUL |
| `chain : ComposableArrows C n` | A_0 -> A_1 -> ... -> A_n | 0=E_0 -> E_1 -> ... -> E_n=E | FAITHFUL |
| `triangle : Fin n -> Triangle C` | Distinguished triangles | Triangles E_{j-1} -> E_j -> A_j | FAITHFUL |
| `triangle_dist` | Each triangle distinguished | Same | FAITHFUL |
| `triangle_obj1 i` | `Nonempty (obj1 ~= chain(i))` | E_{j-1} = first vertex | FAITHFUL (iso not eq, standard) |
| `triangle_obj2 i` | `Nonempty (obj2 ~= chain(i+1))` | E_j = second vertex | FAITHFUL |
| `base_isZero` | `IsZero chain.left` | 0 = E_0 | FAITHFUL |
| `top_iso` | `Nonempty (chain.right ~= E)` | E_n = E | FAITHFUL |
| `zero_isZero` | `n = 0 -> IsZero E` | (implicit) | FAITHFUL |
| `factor i` | `(triangle i).obj3` (derived) | A_j = third vertex | FAITHFUL |

### HNFiltration (`Slicing/Basic.lean:65`)

| Field | Lean | Paper | Verdict |
|-------|------|-------|---------|
| extends PostnikovTower | Filtration data | Same | FAITHFUL |
| `phi : Fin n -> R` | Phases | phi_1 > ... > phi_n | FAITHFUL |
| `hphi : StrictAnti phi` | Strictly decreasing | phi_1 > phi_2 > ... > phi_n | FAITHFUL |
| `semistable : forall j, (P (phi j)) (factor j)` | Factor j in P(phi_j) | A_j in P(phi_j) | FAITHFUL |

**Note on indexing**: Lean's `Fin n` runs 0..n-1, paper's indices run 1..n.
`StrictAnti` on `Fin n` means phi(0) > phi(1) > ... > phi(n-1), matching
the paper's phi_1 > phi_2 > ... > phi_n. Factor(i) in Lean = A_{i+1} in paper.

### Slicing (`Slicing/Basic.lean:80`)

| Field | Lean | Paper (Def 1.1) | Verdict |
|-------|------|-----------------|---------|
| `P : R -> ObjectProperty C` | Phase slices | P(phi) full additive subcategories | FAITHFUL |
| `closedUnderIso` | Each P(phi) closed under iso | (Implicit in "subcategory") | OK -- standard |
| `zero_mem : forall phi, (P phi) 0` | Zero in every P(phi) | P(phi) additive => contains 0 | FAITHFUL |
| `shift_iff` | `(P phi) X <-> (P (phi+1)) (X[1])` | Axiom (b): P(phi+1) = P(phi)[1] | FAITHFUL |
| `hom_vanishing` | phi2 < phi1, A in P(phi1), B in P(phi2) => f = 0 | Axiom (c) | FAITHFUL |
| `hn_exists` | `forall E, Nonempty (HNFiltration C P E)` | Axiom (d) | FAITHFUL |
| *(not required)* | Closure under direct sums | Paper says "additive" | OK -- derivable |

**On "full additive subcategory"**: The paper requires P(phi) to be additive
(closed under direct sums, contains zero). The Lean formalization requires
`zero_mem` explicitly. Closure under direct sums is derivable from the HN
filtration axioms: if A, B in P(phi), then A + B has an HN filtration whose
factors are all of phase phi (by uniqueness), so A + B in P(phi).

**On axiom (a) and zero objects**: The paper's axiom (a) says E in P(phi) =>
Z(E) = m(E)exp(i*pi*phi) with m(E) > 0. This is impossible for E = 0 since
Z(0) = 0. Yet P(phi) is additive, so 0 in P(phi). Resolution: axiom (a) only
applies to nonzero E. The Lean formalization captures this correctly with
`not (IsZero E)` in the `compat` field.

### K_0 (`GrothendieckGroup.lean:58-66`)

| Definition | Lean | Paper | Verdict |
|-----------|------|-------|---------|
| `K0Subgroup C` | `closure {[B]-[A]-[C] : T in distTriang C}` | Triangle relations | FAITHFUL |
| `K0 C` | `FreeAbelianGroup C / K0Subgroup C` | K(D) | FAITHFUL |
| `K0.of X` | Class map C -> K0 C | [X] | FAITHFUL |
| `K0.of_triangle` | [obj2] = [obj1] + [obj3] | Additivity on triangles | FAITHFUL |
| `IsTriangleAdditive f` | f(obj2) = f(obj1) + f(obj3) for dist. tri. | Triangle-additive function | FAITHFUL |
| `K0.lift` | Universal property | K(D) universal property | FAITHFUL |

**Convention check**: In a distinguished triangle obj1 -> obj2 -> obj3 -> obj1[1],
the K0 relation is [obj2] = [obj1] + [obj3]. This matches the standard convention
and the paper's [E_j] = [E_{j-1}] + [A_j].

### StabilityCondition (`StabilityCondition/Basic.lean:216`)

| Field | Lean | Paper (Def 1.1 + 5.7) | Verdict |
|-------|------|------------------------|---------|
| `slicing : Slicing C` | Slicing | The P part of (Z, P) | FAITHFUL |
| `Z : K0 C ->+ C` | Central charge | Z: K(D) -> C group hom | FAITHFUL |
| `compat` | See below | Axiom (a) | FAITHFUL |
| `locallyFinite` | See Layer 6 | Definition 5.7 | FAITHFUL |

Compat in full:
```lean
compat : forall (phi : R) (E : C), slicing.P phi E -> not (IsZero E) ->
  exists (m : R), 0 < m /\ Z (K0.of C E) = m * exp(Real.pi * phi * I)
```
Matches axiom (a): Z(E) = m(E) exp(i pi phi) for m(E) > 0, with the `not IsZero E`
guard correctly handling the zero object convention.

### intervalProp (`Slicing/Basic.lean:192`)

```lean
def Slicing.intervalProp (s : Slicing C) (a b : R) : ObjectProperty C :=
  fun E => IsZero E \/ exists (F : HNFiltration C s.P E), forall i, a < F.phi i /\ F.phi i < b
```

Paper (Definition 4.1): P((a,b)) is the extension closure of the union of P(phi)
for phi in (a,b).

**Equivalence**: An object E is in the extension closure of {P(phi) : phi in (a,b)}
iff E has an HN filtration with all phases in (a,b). This is a theorem, not a
tautology, but the two characterizations are equivalent. The Lean formalization
uses the HN-filtration characterization directly. FAITHFUL.

### IntervalCat (`IntervalCategory/Basic.lean:76`)

```lean
abbrev Slicing.IntervalCat (s : Slicing C) (a b : R) :=
  (s.intervalProp C a b).FullSubcategory
```

FAITHFUL -- full subcategory on objects with HN phases in (a,b).

### IsStrict, IsStrictMono (`Strict.lean:70-76`)

```lean
def IsStrict : Prop := IsIso (Abelian.coimageImageComparison f)

structure IsStrictMono : Prop where
  mono : Mono f
  strict : IsStrict f
```

Paper/Schneiders: a morphism is strict if the canonical morphism from coimage to
image is an isomorphism. A strict mono is a monomorphism that is strict.

FAITHFUL -- matches the quasi-abelian definition exactly.

### StrictSubobject, IsStrictArtinian/Noetherian (`Strict.lean:430-454`)

```lean
abbrev StrictSubobject (X : C) := { P : Subobject X // P.IsStrict }

def isStrictArtinianObject : ObjectProperty C :=
  fun X => WellFoundedLT (StrictSubobject X)

def isStrictNoetherianObject : ObjectProperty C :=
  fun X => WellFoundedGT (StrictSubobject X)
```

Paper (Definition 5.7): P((phi-eta, phi+eta)) has "finite length" = artinian +
noetherian in the quasi-abelian sense.

In a quasi-abelian category, the correct chain conditions use **strict**
subobjects (not all subobjects), because the exact structure is defined by
strict short exact sequences. The Lean formalization correctly uses
`StrictSubobject` (subobjects whose arrow is a strict mono) and checks
well-foundedness of the strict subobject lattice.

FAITHFUL -- correct quasi-abelian chain conditions.

### IsLocallyFinite (`IntervalCategory/FiniteLength.lean:268`)

```lean
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  intervalFinite : exists eta : R, exists h_eta : 0 < eta, exists h_eta' : eta < 1/2,
    forall t : R,
      [Fact (t - eta < t + eta)] [Fact ((t + eta) - (t - eta) <= 1)]
      forall (E : s.IntervalCat C (t - eta) (t + eta)),
        IsStrictArtinianObject E /\ IsStrictNoetherianObject E
```

| Aspect | Lean | Paper (Def 5.7) | Verdict |
|--------|------|-----------------|---------|
| exists eta > 0 | Yes | Yes | FAITHFUL |
| eta < 1/2 | Extra bound | Paper: just eta > 0 | FAITHFUL (see note below) |
| forall t | For each center t | For each phi in R | FAITHFUL |
| P((t-eta, t+eta)) | IntervalCat | P((phi-eta, phi+eta)) | FAITHFUL |
| Finite length | Strict art. + strict noeth. | "has finite length" | FAITHFUL |
| Where measured | In IntervalCat (strict subobjects of the interval category) | In P((phi-eta, phi+eta)) | FAITHFUL |

**Note on `eta < 1/2`**: The paper only requires eta > 0. The Lean formalization
adds eta < 1/2, ensuring the interval width 2*eta < 1. This is NOT a harmless
normalization — it is a **well-definedness guard** making explicit an implicit
assumption in the paper. Bridgeland's Lemma 4.3 proves P((a,b)) is quasi-abelian
only when b - a <= 1. "Finite length" (= strict-artinian + strict-noetherian)
is defined via strict subobjects, which require the quasi-abelian
kernel/cokernel structure. For eta >= 1/2 the interval width 2*eta >= 1 and the
quasi-abelian structure is not established, so "finite length" is not
well-defined in the intended sense. The Lean formalization correctly surfaces
this constraint that the paper leaves implicit.

### slicingDist (`Seminorm.lean:42`)

```lean
def slicingDist (s1 s2 : Slicing C) : ENNReal :=
  sup over (E : C) (hE : not (IsZero E)) of
    ofReal (max |s1.phiPlus C E hE - s2.phiPlus C E hE|
                |s1.phiMinus C E hE - s2.phiMinus C E hE|)
```

Paper (Section 6): d(P1, P2) = sup over nonzero E of
max(|phi+_1(E) - phi+_2(E)|, |phi-_1(E) - phi-_2(E)|).

FAITHFUL.

### stabSeminorm (`Seminorm.lean:173`)

```lean
def stabSeminorm (sigma : StabilityCondition C) (U : K0 C ->+ C) : ENNReal :=
  sup over (E : C) (phi : R) (_ : sigma.slicing.P phi E) (_ : not (IsZero E)) of
    ofReal (||U (K0.of C E)|| / ||sigma.Z (K0.of C E)||)
```

Paper (Section 6): ||U||_sigma = sup over nonzero sigma-semistable E of
|U(E)| / |Z(E)|.

FAITHFUL.

### basisNhd (`Topology.lean:42`)

```lean
def basisNhd (sigma : StabilityCondition C) (eps : R) : Set (StabilityCondition C) :=
  { tau | stabSeminorm C sigma (tau.Z - sigma.Z) < ofReal (sin(pi * eps))
          /\ slicingDist C sigma.slicing tau.slicing < ofReal eps }
```

Paper (Proposition 8.1): B_eps(sigma) = { tau : ||Z(tau) - Z(sigma)||_sigma < sin(pi*eps)
and d(P(sigma), P(tau)) < eps }.

FAITHFUL.

### StabilityCondition.topologicalSpace (`Topology.lean:48`)

```lean
instance StabilityCondition.topologicalSpace :
    TopologicalSpace (StabilityCondition C) :=
  TopologicalSpace.generateFrom
    { U | exists sigma eps, 0 < eps /\ eps < 1/8 /\ U = basisNhd C sigma eps }
```

FAITHFUL -- generates the Bridgeland topology from basis neighborhoods.

### finiteSeminormSubgroup (`Seminorm.lean:193`)

```lean
def finiteSeminormSubgroup (sigma : StabilityCondition C) : AddSubgroup (K0 C ->+ C) where
  carrier := { U | stabSeminorm C sigma U < top }
```

Paper (Section 6): V(sigma) = { U in Hom_Z(K(D), C) : ||U||_sigma < infinity }.

Note: This is an `AddSubgroup`, but the paper and the proof
(`LocalHomeomorphism.lean:51`) establish it as a `Submodule C` (a C-linear
subspace). See Flag 1 below.

### eulerFormObj (`NumericalStability.lean:78`)

```lean
def eulerFormObj [Linear k C] (E F : C) : Z :=
  finsum n : Z, (n.negOnePow : Z) * (Module.finrank k (E --> F[n]) : Z)
```

Paper (Section 1.3): chi(E, F) = sum_i (-1)^i dim_k Hom_D(E, F[i]).

FAITHFUL.

### Euler form descent (proved in `EulerForm.lean`)

```lean
def eulerForm : K0 C ->+ K0 C ->+ Z :=
  K0.lift C (eulerFormInner k C)
```

The old `EulerFormDescends` typeclass has been removed. The descent is now proved directly and the
canonical numerical quotient is built from the actual Euler form.

Paper: proves this from the long exact Hom sequence.

FAITHFUL as a definition. The paper proves it; the Lean formalization takes it as
an axiom (typeclass). This adds an extra hypothesis to Corollary 1.3 that is not
in the paper, but the proof of descent is available as an instance in
`EulerForm.lean`. See Flag 6 below.

### eulerForm (`NumericalStability.lean:125`)

```lean
def eulerForm : K0 C ->+ K0 C ->+ Z :=
  K0.lift C (eulerFormInner k C)
```

Paper: bilinear form chi on K(D), lifted via universal property twice.

FAITHFUL.

### eulerFormRad, NumericalK0, NumericallyFinite (`EulerForm.lean`)

```lean
def eulerFormRad : AddSubgroup (K0 C) := (eulerForm k C).ker

def NumericalK0 := K0 C / eulerFormRad k C

class NumericallyFinite : Prop where
  fg : AddGroup.FG (NumericalK0 k C)
```

| Definition | Lean | Paper | Verdict |
|-----------|------|-------|---------|
| `eulerFormRad` | `(eulerForm k C).ker` = left radical | K(D)^perp = {x : chi(x,y) = 0 for all y} | FAITHFUL |
| `NumericalK0` | `K0 C / ker(eulerForm)` | N(D) = K(D) / K(D)^perp | FAITHFUL |
| `NumericallyFinite` | `AddGroup.FG` (finitely generated) | "has finite rank" | See Flag 5 |

### `StabilityCondition.WithClassMap`, `ClassMapStabilityCondition`, and `NumericalStabilityCondition` (`Basic.lean`, `NumericalStability.lean`, `EulerForm.lean`)

```lean
structure PreStabilityCondition.WithClassMap (v : K0 C ->+ Λ) where
  slicing : Slicing C
  Z : Λ ->+ C
  compat : ...

structure StabilityCondition.WithClassMap (v : K0 C ->+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  locallyFinite : slicing.IsLocallyFinite C

def StabilityCondition.FactorsThrough (v : K0 C ->+ Λ) (sigma : StabilityCondition C) : Prop :=
  exists Z' : Λ ->+ C, sigma.Z = Z'.comp v

abbrev ClassMapStabilityCondition (v : K0 C ->+ Λ) :=
  { sigma : StabilityCondition C // sigma.FactorsThrough v }

abbrev NumericalStabilityCondition :=
  StabilityCondition.WithClassMap C (numericalQuotientMap k C)
```

Paper: the generic literature extension fixes a class map `v : K(D) -> Λ` and
works with central charges on `Λ`; the numerical case is the specialization to
the canonical quotient `K(D) -> N(D)`.

FAITHFUL. The generic object now stores the `Λ`-valued charge directly, while
the factorization subtype is retained only as a comparison object. The
numerical case is the canonical `v = numericalQuotientMap` specialization.

### `StabilityCondition.WithClassMap.topologicalSpace` (`StabilityCondition/Topology.lean`)

```lean
abbrev StabilityCondition.WithClassMap.topologicalSpace {v : K0 C ->+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  TopologicalSpace.induced
    (StabilityCondition.WithClassMap.toStabilityCondition (C := C) (v := v))
    inferInstance
```

FAITHFUL -- `Stab_v(D)` carries the topology induced from the ordinary
Bridgeland topology on `Stab(D)` by forgetting the class-map charge to the
ambient `K0`-valued charge.

---

## Part IV: Theorem Statements

### StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents (`StabilityCondition/Topology.lean`)

```lean
def StabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents : Prop :=
  forall (cc : ConnectedComponents (StabilityCondition C)),
    exists (V : Submodule C (K0 C ->+ C))
      (_ : NormedAddCommGroup V)
      (_ : NormedSpace C V)
      (hZ : forall sigma, ConnectedComponents.mk sigma = cc -> sigma.Z in V),
      @IsLocalHomeomorph
        { sigma // ConnectedComponents.mk sigma = cc }
        V inferInstance inferInstance
        (fun (sigma, h) => (sigma.Z, hZ sigma h))
```

### NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents (`EulerForm.lean`)

```lean
abbrev NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents
    [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k] : Prop :=
  NumericallyFinite k C ->
    StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents
      (C := C) (Λ := NumericalK0 k C) (v := numericalQuotientMap k C)
```

---

## Part V: Flags

### FLAG 1 (RESOLVED): V is now a complex linear subspace

**Paper**: "there is a **linear subspace** V(Sigma) in Hom_Z(K(D), C)"

**Lean**: `V : Submodule C (K0 C ->+ C)` together with
`NormedAddCommGroup V` and `NormedSpace C V`

The proof (`LocalHomeomorphism.lean:279`) actually constructs:
```lean
structure ComponentTopologicalLinearLocalModel ... where
  V : Submodule C (K0 C ->+ C)
  instNormedAddCommGroup : NormedAddCommGroup V
  instNormedSpace : NormedSpace C V
```
**Verdict**: This objection has been fixed. The proposition-object now records the
linear subspace structure directly.

### FLAG 2 (RESOLVED): The theorem statements now record the local linear topology data

**Paper**: "with a **well-defined linear topology**"

**Lean**: the proposition-objects now require `NormedAddCommGroup V` and
`NormedSpace C V`, which is stronger than the paper's bare "well-defined linear
topology" and records the intended local model directly.

**Verdict**: Together with the resolution of Flag 1, the current Theorem 1.2
statement now records the intended local linear model.

### FLAG 3 (RESOLVED): Corollary 1.3 is now a clean specialization of the generic theorem

`NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents`
is now just the specialization of
`StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents`
to the canonical numerical quotient map.

### FLAG 4 (RESOLVED): Corollary 1.3 no longer uses `sigma.factors.choose`

The numerical proposition-object now uses the `WithClassMap` charge `sigma.Z`
directly, so the old `Classical.choice`-driven presentation has disappeared
from the public statement.

### FLAG 5 (MINOR): `NumericallyFinite` uses `AddGroup.FG` vs "finite rank"

**Paper**: "If this group N(D) has **finite rank**..."

**Lean**: `AddGroup.FG (NumericalK0 k C)` = finitely generated.

Finitely generated is **stronger** than finite rank for general abelian groups
(e.g., Q has rank 1 but is not finitely generated). For quotients of finitely
generated free abelian groups they coincide, so this is fine in practice but
the abstraction is slightly off.

### FLAG 6 (RESOLVED): `EulerFormDescends` has been removed

The paper proves Euler form descent from the long exact Hom sequence. The Lean
formalization now does the same: `EulerForm.lean` proves the descent and the
Corollary 1.3 packaging no longer carries a fake typeclass hypothesis.

### FLAG 7 (FAITHFUL): `IsLocallyFinite` requires eta < 1/2

The paper's Definition 5.7 only requires eta > 0. The Lean formalization adds
eta < 1/2, ensuring interval width 2*eta < 1. This is not a harmless
normalization but a **well-definedness guard**: Bridgeland's Lemma 4.3 proves
P((a,b)) is quasi-abelian only when b - a <= 1, and "finite length" (=
strict-artinian + strict-noetherian) requires the quasi-abelian
kernel/cokernel structure to define "strict subobject." For eta >= 1/2 the
quasi-abelian structure is not established, so the paper's definition is only
well-formed for small eta. The Lean formalization makes this implicit
constraint explicit.

---

## Part VI: Summary

### Definitions: ALL FAITHFUL

Every definition in the dependency tree of `StabilityCondition` and
`IsLocallyFinite` is faithful to Bridgeland's paper:

- `PostnikovTower`, `HNFiltration` -- correct filtration structure
- `Slicing` -- encodes axioms (b), (c), (d) correctly; `zero_mem` explicit
  but matches "additive subcategory"; direct-sum closure derivable
- `K0` -- standard Grothendieck group with correct triangle relations
- `StabilityCondition` -- correctly bundles slicing + central charge +
  compatibility + local finiteness
- `intervalProp`, `IntervalCat` -- equivalent to extension-closure definition
- `IsStrict`, `IsStrictMono`, `StrictSubobject` -- correct quasi-abelian notions
- `IsStrictArtinian/NoetherianObject` -- correct chain conditions for
  quasi-abelian categories
- `IsLocallyFinite` -- faithful to Definition 5.7
- `slicingDist`, `stabSeminorm`, `basisNhd`, topology -- all faithful
- `eulerFormObj`, `eulerForm`, `eulerFormRad`, `NumericalK0`,
  `StabilityCondition.WithClassMap`, `ClassMapStabilityCondition`,
  `NumericalStabilityCondition` -- all faithful

### Theorem statements: no remaining material mismatch in the packaging

The earlier statement-level objections have been fixed:

1. The local models are recorded as complex `Submodule`s, not bare additive
   subgroups.
2. The local topology is recorded via `NormedAddCommGroup` and `NormedSpace`,
   not an unconstrained existential topology.
3. Corollary 1.3 is now a clean specialization of the generic class-map-first
   theorem rather than a separate ad hoc wrapper.

The remaining caveat in this audit is the minor abstraction mismatch in
`NumericallyFinite` noted in Flag 5.
