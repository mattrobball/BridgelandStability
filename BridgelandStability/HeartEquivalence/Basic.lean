/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.Topology
public import BridgelandStability.StabilityFunction.Uniqueness
public import BridgelandStability.IntervalCategory.FiniteLength
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import BridgelandStability.TStructure.HeartAbelian
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.CategoryTheory.Shift.ShiftSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import BridgelandStability.Deformation.IntervalAbelian
public import BridgelandStability.Deformation.PhaseArithmetic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

open scoped BigOperators

/-!
# Heart Equivalence and Blueprint Scaffolding

This file captures the definitions and theorem statements from the Bridgeland
stability conditions blueprint (§§3–5) that are not yet present in the branch.
The currently formalized reverse direction is packaged through a local
`PreStabilityCondition`, isolating the induced phase predicates and their
pre-slicing axioms before the ambient central charge and full HN existence are
packaged.

## Contents

### §3 — t-structures and slicings

* `Slicing.toTStructure_bounded`: the t-structure from a slicing is bounded
  (Lemma 3.2 / Node 3.2a).
* `Slicing.toTStructure_heart_iff`: the heart of the slicing-induced t-structure
  is exactly the half-open interval `P((0, 1])` (Node 3.5b).

### §5 — Stability conditions

* `StabilityCondition.P_phi_abelian`: each phase subcategory `P(φ)` is abelian
  (Lemma 5.2).
* `StabilityCondition.stabilityFunctionOnPhase`: the central charge restricted
  to `P(φ)` gives a stability function on that abelian category.
* `HeartStabilityData`: a bounded t-structure with an HN stability function on
  its heart (one side of Proposition 5.3).
* `StabilityCondition.toHeartStabilityData`: extract heart data (Prop 5.3a).
* `HeartStabilityData.toPreStabilityCondition`: construct the induced reverse-
  direction pre-stability package from heart data (5.3b, packaged so far).
* `StabilityCondition.roundtrip`, `HeartStabilityData.roundtrip`:
  inverse lemmas (Proposition 5.3c).

### §7 — Deformation infrastructure

* `TStructure.heart_shortExact_triangle`: SES in the heart lifts to a
  distinguished triangle (bridge between abelian and triangulated).

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals 2007
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject BigOperators

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ## §3: t-structures from slicings

`Slicing.toTStructure_bounded` and `Slicing.toTStructure_heart_iff` are now proved
in `Slicing.lean` (near the `toTStructure` definition) to avoid import cycles.
-/

/-! ## §5: Stability conditions — Lemma 5.2 and Proposition 5.3 -/

section Lemma52

variable [IsTriangulated C]

/-- If the underlying object of a full-subcategory object is zero, then the
full-subcategory object itself is zero. -/
theorem ObjectProperty.FullSubcategory.isZero_of_obj_isZero
    {P : ObjectProperty C} [HasZeroObject P.FullSubcategory]
    {X : P.FullSubcategory} (hX : IsZero X.obj) : IsZero X := by
  let Z : P.FullSubcategory := 0
  have hZ : IsZero Z.obj := (P.ι.map_isZero (show IsZero Z from isZero_zero _))
  let e : X.obj ≅ Z.obj := hX.iso hZ
  exact (show IsZero Z from isZero_zero _).of_iso (P.isoMk e)

set_option backward.isDefEq.respectTransparency false in
/-- A short exact sequence in the abelian slice `P(φ)` extends to a distinguished
triangle in the ambient triangulated category. -/
theorem StabilityCondition.P_phi_shortExact_triangle
    (σ : StabilityCondition C) (φ : ℝ)
    {A B Q : (σ.slicing.P φ).FullSubcategory}
    (f : A ⟶ B) (g : B ⟶ Q) (hfg : f ≫ g = 0)
    [Mono f] [Epi g]
    (hexact : ∀ {W : (σ.slicing.P φ).FullSubcategory} (α : W ⟶ B), α ≫ g = 0 →
      ∃ (β : W ⟶ A), β ≫ f = α) :
    ∃ (h : Q.obj ⟶ A.obj⟦(1 : ℤ)⟧),
      Triangle.mk f.hom g.hom h ∈ distTriang C := by
  letI : Abelian (σ.slicing.P φ).FullSubcategory := σ.P_phi_abelian C φ
  let ι := (σ.slicing.P φ).ι
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (σ.P_phi_hom_vanishing C φ) (σ.P_phi_admissible C φ) g
  have h_ig : (ι.map i) ≫ g.hom = 0 := by
    have := comp_distTriang_mor_zero₁₂ _ hT
    change (ι.map i) ≫ g.hom = 0 at this
    exact this
  have h_ig' : ObjectProperty.homMk (ι.map i) ≫ g = 0 := by
    ext
    exact h_ig
  obtain ⟨β_hom, hβ_hom⟩ := hexact (W := K) (ObjectProperty.homMk (ι.map i)) h_ig'
  let β : K ⟶ A := β_hom
  have hβf : β ≫ f = i := by
    ext
    exact congrArg InducedCategory.Hom.hom hβ_hom
  have hKer :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (σ.P_phi_hom_vanishing C φ) i g δ hT
  have hfg' : f ≫ g = 0 := hfg
  let γ : A ⟶ K := hKer.lift (KernelFork.ofι f hfg')
  have hγi : γ ≫ i = f := Fork.IsLimit.lift_ι hKer
  have hβγ : β ≫ γ = 𝟙 K :=
    Fork.IsLimit.hom_ext hKer (by simp [hγi, hβf])
  have hγβ : γ ≫ β = 𝟙 A := by
    rw [← cancel_mono f, Category.assoc, hβf, hγi, Category.id_comp]
  let eKA : K ≅ A :=
    { hom := β, inv := γ, hom_inv_id := hβγ, inv_hom_id := hγβ }
  refine ⟨δ ≫ ((shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)), ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (ι.mapIso eKA.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom,
      Triangle.mk_mor₁]
    change f.hom = ι.map γ ≫ ι.map i
    rw [← Functor.map_comp, hγi]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Triangle.mk_mor₃, Functor.mapIso_hom,
      Iso.symm_hom]
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp, ← ι.map_comp, hβγ, ι.map_id,
      Functor.map_id, Category.comp_id]

/-- **Stability function restricted to P(φ).**
The central charge `Z` of a stability condition, restricted to `σ`-semistable
objects of phase `φ`, for `0 < φ ≤ 1`, defines a stability function on the
abelian category `P(φ)`.

The `Zobj` field sends `E : P(φ)` to `σ.Z (K₀.of C (ι E))`, where `ι` is
the inclusion `P(φ) ↪ C`. Additivity follows from `K₀.of_shortExact_P_phi`;
the upper half plane condition follows from the compatibility axiom of `σ`. -/
def StabilityCondition.stabilityFunctionOnPhase
    (σ : StabilityCondition C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1) :
    @StabilityFunction (σ.slicing.P φ).FullSubcategory _
      (σ.P_phi_abelian C φ) := by
  letI : Abelian (σ.slicing.P φ).FullSubcategory := σ.P_phi_abelian C φ
  exact {
    Zobj := fun E => σ.Z (K₀.of C ((σ.slicing.P φ).ι.obj E))
    map_zero' := fun X hX => by
      simpa using congrArg σ.Z (K₀.of_isZero C (((σ.slicing.P φ).ι.map_isZero hX)))
    additive := fun S hS => by
      letI : Abelian (σ.slicing.P φ).FullSubcategory := σ.P_phi_abelian C φ
      letI : IsNormalMonoCategory (σ.slicing.P φ).FullSubcategory := Abelian.toIsNormalMonoCategory
      letI : IsNormalEpiCategory (σ.slicing.P φ).FullSubcategory := Abelian.toIsNormalEpiCategory
      letI : Balanced (σ.slicing.P φ).FullSubcategory := by infer_instance
      haveI := hS.mono_f
      haveI := hS.epi_g
      obtain ⟨δ, hT⟩ :=
        StabilityCondition.P_phi_shortExact_triangle (C := C) σ φ S.f S.g S.zero
          (fun {W} α hα ↦ by
            have hker : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
            exact ⟨hker.lift (KernelFork.ofι α hα), hker.fac _ WalkingParallelPair.zero⟩)
      simpa using congrArg σ.Z (K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT)
    upper := fun E hE => by
      have hEobj : ¬IsZero E.obj := fun hZ ↦
        hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := σ.slicing.P φ) (X := E) hZ)
      obtain ⟨m, hm, hmZ⟩ := σ.compat φ E.obj E.property hEobj
      have harg_eq :
          Complex.arg ((m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I)) = Real.pi * φ := by
        rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
        constructor
        · nlinarith [Real.pi_pos, hφ.1]
        · nlinarith [Real.pi_pos, hφ.2]
      have harg : 0 < Complex.arg ((m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I)) := by
        rw [harg_eq]
        nlinarith [Real.pi_pos, hφ.1]
      have hmem :
          ((m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I)) ∈ upperHalfPlaneUnion :=
        mem_upperHalfPlaneUnion_of_arg_pos harg
      simpa [hmZ] using hmem }

theorem StabilityCondition.phase_eq_of_mem_P_phi
    (σ : StabilityCondition C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1)
    (E : (σ.slicing.P φ).FullSubcategory) (hE : ¬IsZero E) :
    @StabilityFunction.phase _ _ (σ.P_phi_abelian C φ)
      (σ.stabilityFunctionOnPhase C hφ) E = φ := by
  letI : Abelian (σ.slicing.P φ).FullSubcategory := σ.P_phi_abelian C φ
  have hEobj : ¬IsZero E.obj := fun hZ ↦
    hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := σ.slicing.P φ) (X := E) hZ)
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E.obj E.property hEobj
  have harg : Complex.arg ((m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I)) = Real.pi * φ := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor
    · nlinarith [Real.pi_pos, hφ.1]
    · nlinarith [Real.pi_pos, hφ.2]
  change (1 / Real.pi) * Complex.arg (σ.Z (K₀.of C E.obj)) = φ
  rw [hmZ, harg]
  field_simp [Real.pi_ne_zero]

/-- **HasHN for the restricted stability function on P(φ).**
For `0 < φ ≤ 1`, every nonzero object of `P(φ)` is already semistable of phase
`φ`, so the HN filtration has a single factor. -/
theorem StabilityCondition.stabilityFunctionOnPhase_hasHN
    (σ : StabilityCondition C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1) :
    @StabilityFunction.HasHNProperty (σ.slicing.P φ).FullSubcategory _
      (σ.P_phi_abelian C φ) (σ.stabilityFunctionOnPhase C hφ) := by
  letI : Abelian (σ.slicing.P φ).FullSubcategory := σ.P_phi_abelian C φ
  intro E hE
  let Z := σ.stabilityFunctionOnPhase C hφ
  have hss : Z.IsSemistable E := by
    refine ⟨hE, ?_⟩
    intro B hB
    rw [σ.phase_eq_of_mem_P_phi C hφ B hB, σ.phase_eq_of_mem_P_phi C hφ E hE]
  refine ⟨{
    n := 1
    hn := Nat.one_pos
    chain := fun i => if i = 0 then ⊥ else ⊤
    chain_strictMono := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ h
      simp only [Fin.lt_def] at h
      have hi0 : i = 0 := by omega
      have hj1 : j = 1 := by omega
      subst hi0
      subst hj1
      simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ↓reduceIte,
        Fin.mk_one, one_ne_zero, gt_iff_lt]
      exact lt_of_le_of_ne bot_le
        (Ne.symm (StabilityFunction.subobject_top_ne_bot_of_not_isZero hE))
    chain_bot := by simp
    chain_top := by simp
    φ := fun _ => φ
    φ_anti := by
      intro i j hij
      exact False.elim (by omega)
    factor_phase := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by omega
      subst hj0
      change Z.phase (cokernel (Subobject.ofLE ⊥ ⊤ bot_le)) = φ
      have htop :
          Z.phase (cokernel (Subobject.ofLE ⊥ ⊤ bot_le)) =
            Z.phase ((⊤ : Subobject E) : (σ.slicing.P φ).FullSubcategory) :=
        Z.phase_eq_of_iso
          (StabilityFunction.Subobject.cokernelBotIso (⊤ : Subobject E) bot_le)
      calc
        Z.phase (cokernel (Subobject.ofLE ⊥ ⊤ bot_le))
            = Z.phase ((⊤ : Subobject E) : (σ.slicing.P φ).FullSubcategory) := htop
        _ = Z.phase E := Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow)
        _ = φ := σ.phase_eq_of_mem_P_phi C hφ E hE
    factor_semistable := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by omega
      subst hj0
      change Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ bot_le))
      refine Z.isSemistable_of_iso
        ((asIso (⊤ : Subobject E).arrow).symm ≪≫
          (StabilityFunction.Subobject.cokernelBotIso ⊤ bot_le).symm) ?_
      exact hss
  }⟩

end Lemma52

section Proposition53

variable [IsTriangulated C]

/-- **Heart stability data (Proposition 5.3).**
This structure bundles a bounded t-structure with a stability function on its
heart that has the Harder-Narasimhan property. It represents one side of the
equivalence in Bridgeland's Proposition 5.3.

The heart `t.heart.FullSubcategory` is abelian by
`heartFullSubcategoryAbelian`. -/
structure HeartStabilityData where
  /-- The t-structure on `C`. -/
  t : TStructure C
  /-- The t-structure is bounded. -/
  bounded : t.IsBounded
  /-- The stability function on the heart. -/
  Z : @StabilityFunction t.heart.FullSubcategory _ t.heartFullSubcategoryAbelian
  /-- The stability function has the HN property. -/
  hasHN : @StabilityFunction.HasHNProperty t.heart.FullSubcategory _
    t.heartFullSubcategoryAbelian Z

noncomputable instance HeartStabilityData.instHeartFullSubcategoryAbelian
    (h : HeartStabilityData C) : Abelian h.t.heart.FullSubcategory :=
  h.t.heartFullSubcategoryAbelian

/-- The subgroup of the free abelian group on the heart generated by short exact
sequence relations. This is the Grothendieck-group presentation of the heart
used in Bridgeland Proposition 5.3. -/
def HeartK0Subgroup (h : HeartStabilityData C) :
    AddSubgroup (FreeAbelianGroup h.t.heart.FullSubcategory) := by
  exact AddSubgroup.closure
    {x | ∃ (S : ShortComplex h.t.heart.FullSubcategory), S.ShortExact ∧
        x = FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ -
          FreeAbelianGroup.of S.X₃}

/-- The Grothendieck group of the heart of a bounded t-structure, presented by
short exact sequence relations. -/
def HeartK0 (h : HeartStabilityData C) : Type _ :=
  FreeAbelianGroup h.t.heart.FullSubcategory ⧸ HeartK0Subgroup (C := C) h

instance HeartK0.instAddCommGroup (h : HeartStabilityData C) :
    AddCommGroup (HeartK0 (C := C) h) :=
  inferInstanceAs
    (AddCommGroup
      (FreeAbelianGroup h.t.heart.FullSubcategory ⧸ HeartK0Subgroup (C := C) h))

namespace HeartK0

/-- The class of a heart object in the Grothendieck group of the heart. -/
def of (h : HeartStabilityData C) (E : h.t.heart.FullSubcategory) : HeartK0 (C := C) h :=
  (QuotientAddGroup.mk (FreeAbelianGroup.of E) :
    FreeAbelianGroup h.t.heart.FullSubcategory ⧸ HeartK0Subgroup (C := C) h)

/-- A short exact sequence in the heart yields the defining relation in `HeartK0`. -/
theorem of_shortExact (h : HeartStabilityData C)
    {S : ShortComplex h.t.heart.FullSubcategory} (hS : S.ShortExact) :
    HeartK0.of (C := C) h S.X₂ = HeartK0.of (C := C) h S.X₁ + HeartK0.of (C := C) h S.X₃ := by
  have hq :
      -HeartK0.of (C := C) h S.X₁ +
          (HeartK0.of (C := C) h S.X₂ + -HeartK0.of (C := C) h S.X₃) = 0 := by
    simpa [HeartK0.of, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (QuotientAddGroup.eq_zero_iff
        (N := HeartK0Subgroup (C := C) h)
        (x := FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃)).2
          (AddSubgroup.subset_closure ⟨S, hS, rfl⟩)
  calc
    HeartK0.of (C := C) h S.X₂
        = HeartK0.of (C := C) h S.X₁ + HeartK0.of (C := C) h S.X₃ +
            (-HeartK0.of (C := C) h S.X₁ +
              (HeartK0.of (C := C) h S.X₂ + -HeartK0.of (C := C) h S.X₃)) := by
              abel
    _ = HeartK0.of (C := C) h S.X₁ + HeartK0.of (C := C) h S.X₃ := by rw [hq, add_zero]

/-- For an exact sequence `A ⟶ B ⟶ D` in the heart, the Grothendieck-group class of
`B` splits as the sum of the classes of the two successive images. This is the
standard abelian-category relation used later to telescope bounded exact sequences. -/
theorem of_exact (h : HeartStabilityData C)
    {A B D : h.t.heart.FullSubcategory} {f : A ⟶ B} {g : B ⟶ D}
    [HasImage f] [HasImage g] (w : f ≫ g = 0)
    (hex : (ShortComplex.mk f g w).Exact) :
    HeartK0.of (C := C) h B =
      HeartK0.of (C := C) h (Limits.image f) +
        HeartK0.of (C := C) h (Limits.image g) := by
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  let S₀ : ShortComplex h.t.heart.FullSubcategory := ShortComplex.mk f g w
  have hex₀ : S₀.Exact := by simpa [S₀] using hex
  let S₁' : ShortComplex h.t.heart.FullSubcategory :=
    ShortComplex.mk (Abelian.image.ι f) g (Abelian.image_ι_comp_eq_zero w)
  have hExact₁' : S₁'.Exact := by
    simpa [S₀, S₁'] using (S₀.exact_iff_exact_image_ι.mp hex₀)
  let S₁ : ShortComplex h.t.heart.FullSubcategory :=
    ShortComplex.mk (Limits.image.ι f) g (Limits.image_ι_comp_eq_zero w)
  let e₁ : S₁' ≅ S₁ :=
    ShortComplex.isoMk
      (Abelian.imageIsoImage f)
      (Iso.refl _)
      (Iso.refl _)
      (by simpa using Abelian.imageIsoImage_hom_comp_image_ι (f := f))
      (by simp [S₁, S₁'])
  have hExact₁ : S₁.Exact := (ShortComplex.exact_iff_of_iso e₁).mp hExact₁'
  let S : ShortComplex h.t.heart.FullSubcategory :=
    ShortComplex.mk (Limits.image.ι f) (Limits.factorThruImage g)
      (by
        have : Limits.image.ι f ≫ g = 0 := Limits.image_ι_comp_eq_zero w
        simpa using Limits.comp_factorThruImage_eq_zero this)
  let φ : S ⟶ S₁ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Limits.image.ι g }
  have hExact : S.Exact := by
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hExact₁
  have hSE : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  simpa [S] using HeartK0.of_shortExact (C := C) h hSE

/-- For an exact sequence of five consecutive arrows in the heart,
the alternating sum of the middle three terms equals the sum of the
endpoint images. This is the Grothendieck-group identity that later
makes long exact cohomology sequences telescope. -/
theorem of_exact_five (h : HeartStabilityData C)
    {A₀ A₁ A₂ A₃ A₄ : h.t.heart.FullSubcategory}
    {f₀ : A₀ ⟶ A₁} {f₁ : A₁ ⟶ A₂} {f₂ : A₂ ⟶ A₃} {f₃ : A₃ ⟶ A₄}
    [HasImage f₀] [HasImage f₁] [HasImage f₂] [HasImage f₃]
    (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (hex₀ : (ShortComplex.mk f₀ f₁ w₀).Exact)
    (hex₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (hex₂ : (ShortComplex.mk f₂ f₃ w₂).Exact) :
    HeartK0.of (C := C) h A₁ - HeartK0.of (C := C) h A₂ + HeartK0.of (C := C) h A₃ =
      HeartK0.of (C := C) h (Limits.image f₀) + HeartK0.of (C := C) h (Limits.image f₃) := by
  rw [HeartK0.of_exact (C := C) h w₀ hex₀, HeartK0.of_exact (C := C) h w₁ hex₁,
    HeartK0.of_exact (C := C) h w₂ hex₂]
  abel

/-- The class of a zero object in the heart vanishes in `HeartK0`. -/
theorem of_isZero (h : HeartStabilityData C)
    {E : h.t.heart.FullSubcategory} (hE : IsZero E) :
    HeartK0.of (C := C) h E = 0 := by
  let S : ShortComplex h.t.heart.FullSubcategory :=
    ShortComplex.mk (0 : (0 : h.t.heart.FullSubcategory) ⟶ 0) hE.isoZero.symm.hom (by simp)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact ShortComplex.exact_of_isZero_X₂ (S := S) (isZero_zero _)
  have hs := HeartK0.of_shortExact (C := C) h hS
  have hs' : HeartK0.of (C := C) h (0 : h.t.heart.FullSubcategory) =
      HeartK0.of (C := C) h (0 : h.t.heart.FullSubcategory) + HeartK0.of (C := C) h E := by
    simpa [S] using hs
  have hs'' : HeartK0.of (C := C) h (0 : h.t.heart.FullSubcategory) + 0 =
      HeartK0.of (C := C) h (0 : h.t.heart.FullSubcategory) + HeartK0.of (C := C) h E := by
    simpa using hs'
  exact (add_left_cancel hs'').symm

/-- The class of the explicit zero object vanishes in `HeartK0`. -/
theorem of_zero (h : HeartStabilityData C) :
    HeartK0.of (C := C) h (0 : h.t.heart.FullSubcategory) = 0 :=
  of_isZero (C := C) h (isZero_zero _)

/-- Isomorphic heart objects have the same class in `HeartK0`. -/
theorem of_iso (h : HeartStabilityData C)
    {E F : h.t.heart.FullSubcategory} (e : E ≅ F) :
    HeartK0.of (C := C) h E = HeartK0.of (C := C) h F := by
  let S : ShortComplex h.t.heart.FullSubcategory :=
    ShortComplex.mk e.hom (0 : F ⟶ (0 : h.t.heart.FullSubcategory)) (by simp)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact ((S.exact_iff_epi (by simp [S])).2 inferInstance)
  calc
    HeartK0.of (C := C) h E = HeartK0.of (C := C) h E + HeartK0.of (C := C) h (0 : h.t.heart.FullSubcategory) := by
      rw [HeartK0.of_zero (C := C) h, add_zero]
    _ = HeartK0.of (C := C) h F := by
      simpa [S] using (HeartK0.of_shortExact (C := C) h hS).symm

/-- The image of a zero morphism has trivial class in `HeartK0`. -/
theorem of_image_eq_zero (h : HeartStabilityData C)
    {A B : h.t.heart.FullSubcategory} {f : A ⟶ B} [HasImage f] (hf : f = 0) :
    HeartK0.of (C := C) h (Limits.image f) = 0 := by
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  calc
    HeartK0.of (C := C) h (Limits.image f)
        = HeartK0.of (C := C) h (0 : h.t.heart.FullSubcategory) := by
            exact HeartK0.of_iso (C := C) h (Limits.imageZero' hf)
    _ = 0 := HeartK0.of_zero (C := C) h

end HeartK0

/-- The object-level central charge on heart objects, viewed as a plain function.
This helper keeps the heart's abelian instance explicit when transporting `Z`
through local quotient constructions. -/
def HeartStabilityData.heartZObj (h : HeartStabilityData C) :
    h.t.heart.FullSubcategory → ℂ := by
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  exact h.Z.Zobj

omit [IsTriangulated C] in
set_option backward.isDefEq.respectTransparency false in
/-- The heart stability function extends uniquely to the Grothendieck group of
the heart. -/
def HeartStabilityData.ZOnHeartK0 (h : HeartStabilityData C) :
    HeartK0 (C := C) h →+ ℂ := by
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  exact QuotientAddGroup.lift (HeartK0Subgroup (C := C) h)
    (FreeAbelianGroup.lift h.heartZObj)
    ((AddSubgroup.closure_le _).mpr fun x ⟨S, hS, hx⟩ ↦ by
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hx, map_sub, FreeAbelianGroup.lift_apply_of]
      change h.Z.Zobj S.X₂ - h.Z.Zobj S.X₁ - h.Z.Zobj S.X₃ = 0
      rw [h.Z.additive S hS]
      abel)

@[simp]
theorem HeartStabilityData.ZOnHeartK0_of (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) :
    h.ZOnHeartK0 (C := C) (HeartK0.of (C := C) h E) =
      HeartStabilityData.heartZObj (C := C) h E := by
  change (FreeAbelianGroup.lift (HeartStabilityData.heartZObj (C := C) h))
      (FreeAbelianGroup.of E) = HeartStabilityData.heartZObj (C := C) h E
  simpa using
    (FreeAbelianGroup.lift_apply_of (HeartStabilityData.heartZObj (C := C) h) E)

set_option backward.isDefEq.respectTransparency false in
/-- A short exact sequence in the heart full subcategory extends to a distinguished
triangle in the ambient triangulated category. -/
theorem TStructure.heartFullSubcategory_shortExact_triangle
    (t : TStructure C)
    {A B Q : t.heart.FullSubcategory}
    (f : A ⟶ B) (g : B ⟶ Q) (hfg : f ≫ g = 0)
    [Mono f] [Epi g]
    (hexact : ∀ {W : t.heart.FullSubcategory} (α : W ⟶ B), α ≫ g = 0 →
      ∃ (β : W ⟶ A), β ≫ f = α) :
    ∃ (h : Q.obj ⟶ A.obj⟦(1 : ℤ)⟧),
      Triangle.mk f.hom g.hom h ∈ distTriang C := by
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let ι := t.heart.ι
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (heart_hι t) (heart_admissible t) g
  have h_ig : (ι.map i) ≫ g.hom = 0 := by
    have := comp_distTriang_mor_zero₁₂ _ hT
    change (ι.map i) ≫ g.hom = 0 at this
    exact this
  have h_ig' : ObjectProperty.homMk (ι.map i) ≫ g = 0 := by
    ext
    exact h_ig
  obtain ⟨β_hom, hβ_hom⟩ := hexact (W := K) (ObjectProperty.homMk (ι.map i)) h_ig'
  let β : K ⟶ A := β_hom
  have hβf : β ≫ f = i := by
    ext
    exact congrArg InducedCategory.Hom.hom hβ_hom
  have hKer :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (heart_hι t) i g δ hT
  let γ : A ⟶ K := hKer.lift (KernelFork.ofι f hfg)
  have hγi : γ ≫ i = f := Fork.IsLimit.lift_ι hKer
  have hβγ : β ≫ γ = 𝟙 K :=
    Fork.IsLimit.hom_ext hKer (by simp [hγi, hβf])
  have hγβ : γ ≫ β = 𝟙 A := by
    rw [← cancel_mono f, Category.assoc, hβf, hγi, Category.id_comp]
  let eKA : K ≅ A :=
    { hom := β, inv := γ, hom_inv_id := hβγ, inv_hom_id := hγβ }
  refine ⟨δ ≫ ((shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)), ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (ι.mapIso eKA.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom,
      Triangle.mk_mor₁]
    change f.hom = ι.map γ ≫ ι.map i
    rw [← Functor.map_comp, hγi]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Triangle.mk_mor₃, Functor.mapIso_hom,
      Iso.symm_hom]
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp, ← ι.map_comp, hβγ]
    change δ ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 (ι.obj K)) = δ
    have hmap :
        (shiftFunctor C (1 : ℤ)).map (𝟙 (ι.obj K)) = 𝟙 ((shiftFunctor C (1 : ℤ)).obj (ι.obj K)) := by
      simpa using (Functor.map_id (shiftFunctor C (1 : ℤ)) (ι.obj K))
    rw [hmap]
    exact Category.comp_id δ

set_option backward.isDefEq.respectTransparency false in
/-- A distinguished triangle whose three vertices lie in the heart induces a short
exact sequence in the heart. -/
theorem TStructure.heartFullSubcategory_shortExact_of_distTriang
    (t : TStructure C)
    {A B Q : t.heart.FullSubcategory}
    {f : A ⟶ B} {g : B ⟶ Q} {δ : Q.obj ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f.hom g.hom δ ∈ distTriang C) :
    (ShortComplex.mk f g (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hT)).ShortExact := by
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let S : ShortComplex t.heart.FullSubcategory := ShortComplex.mk f g (by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hT)
  have hKer :
      IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S] using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) f g δ hT
  have hCok :
      IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    simpa [S] using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι t) f g δ hT
  have hExact : S.Exact := ShortComplex.exact_of_f_is_kernel (S := S) hKer
  exact ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) (Cofork.IsColimit.epi hCok)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from the Grothendieck group of the heart to the ambient
triangulated Grothendieck group. -/
def HeartStabilityData.heartK0ToK0
    (h : HeartStabilityData C) [IsTriangulated C] :
    HeartK0 (C := C) h →+ K₀ C := by
      letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
      letI : IsNormalMonoCategory h.t.heart.FullSubcategory := Abelian.toIsNormalMonoCategory
      letI : IsNormalEpiCategory h.t.heart.FullSubcategory := Abelian.toIsNormalEpiCategory
      letI : Balanced h.t.heart.FullSubcategory := by
        infer_instance
      exact QuotientAddGroup.lift (HeartK0Subgroup (C := C) h)
        (FreeAbelianGroup.lift fun E : h.t.heart.FullSubcategory => K₀.of C E.obj)
        ((AddSubgroup.closure_le _).mpr fun x ⟨S, hS, hx⟩ ↦ by
          haveI := hS.mono_f
          haveI := hS.epi_g
          obtain ⟨δ, hT⟩ :=
            TStructure.heartFullSubcategory_shortExact_triangle (C := C) h.t S.f S.g S.zero
              (fun {W} α hα ↦ by
                have hker : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
                exact ⟨hker.lift (KernelFork.ofι α hα), hker.fac _ WalkingParallelPair.zero⟩)
          simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hx, map_sub, FreeAbelianGroup.lift_apply_of]
          have htri : K₀.of C S.X₂.obj = K₀.of C S.X₁.obj + K₀.of C S.X₃.obj := by
            simpa using (K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT)
          rw [htri]
          abel)

@[simp]
theorem HeartStabilityData.heartK0ToK0_of
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : h.t.heart.FullSubcategory) :
    h.heartK0ToK0 C (HeartK0.of (C := C) h E) = K₀.of C E.obj := by
  change (FreeAbelianGroup.lift fun E : h.t.heart.FullSubcategory => K₀.of C E.obj)
      (FreeAbelianGroup.of E) = K₀.of C E.obj
  simpa using
    (FreeAbelianGroup.lift_apply_of (fun E : h.t.heart.FullSubcategory => K₀.of C E.obj) E)

lemma K₀.of_shift_nat (X : C) :
    ∀ n : ℕ, K₀.of C (X⟦(n : ℤ)⟧) = (((-1 : ℤ) ^ n) • K₀.of C X) := by
  intro n
  induction n with
  | zero =>
      simpa using K₀.of_iso C ((shiftFunctorZero C ℤ).app X)
  | succ n ih =>
      calc
        K₀.of C (X⟦((n + 1 : ℕ) : ℤ)⟧)
            = K₀.of C ((X⟦(n : ℤ)⟧)⟦(1 : ℤ)⟧) := by
                simpa only [Functor.comp_obj] using
                  (K₀.of_iso C
                    (((shiftFunctorAdd' C (n : ℤ) (1 : ℤ) ((n : ℤ) + 1) (by omega)).app X).symm)).symm
        _ = -K₀.of C (X⟦(n : ℤ)⟧) := K₀.of_shift_one C (X⟦(n : ℤ)⟧)
        _ = -((((-1 : ℤ) ^ n) • K₀.of C X)) := by rw [ih]
        _ = (((-1 : ℤ) ^ (n + 1)) • K₀.of C X) := by
              rw [show -((((-1 : ℤ) ^ n) • K₀.of C X)) =
                  (-1 : ℤ) • (((-1 : ℤ) ^ n) • K₀.of C X) by simp,
                pow_succ', mul_zsmul, neg_one_zsmul]

lemma K₀.of_shift_negSucc (X : C) :
    ∀ n : ℕ, K₀.of C (X⟦(Int.negSucc n : ℤ)⟧) = (((-1 : ℤ) ^ (n + 1)) • K₀.of C X) := by
  intro n
  induction n with
  | zero =>
      simpa using K₀.of_shift_neg_one C X
  | succ n ih =>
      calc
        K₀.of C (X⟦(Int.negSucc (n + 1) : ℤ)⟧)
            = K₀.of C ((X⟦(Int.negSucc n : ℤ)⟧)⟦(-1 : ℤ)⟧) := by
                simpa only [Functor.comp_obj] using
                  (K₀.of_iso C
                    (((shiftFunctorAdd' C (Int.negSucc n : ℤ) (-1 : ℤ)
                      (Int.negSucc (n + 1) : ℤ) (by omega)).app X).symm)).symm
        _ = -K₀.of C (X⟦(Int.negSucc n : ℤ)⟧) := K₀.of_shift_neg_one C (X⟦(Int.negSucc n : ℤ)⟧)
        _ = -((((-1 : ℤ) ^ (n + 1)) • K₀.of C X)) := by rw [ih]
        _ = (((-1 : ℤ) ^ (n + 2)) • K₀.of C X) := by
              simpa [pow_succ', mul_zsmul, neg_one_zsmul]

/-- Shifting by `n : ℤ` multiplies the Grothendieck-group class by the parity sign
`(-1)^(|n|)`. -/
theorem K₀.of_shift_int (X : C) (n : ℤ) :
    K₀.of C (X⟦n⟧) = (((-1 : ℤ) ^ Int.natAbs n) • K₀.of C X) := by
  cases n with
  | ofNat m =>
      simpa using K₀.of_shift_nat (C := C) X m
  | negSucc m =>
      simpa using K₀.of_shift_negSucc (C := C) X m

/-- If `X` is concentrated in degree `n`, then `X⟦-n⟧` is an object of the heart. -/
def HeartStabilityData.heartShiftOfPure (h : HeartStabilityData C)
    {X : C} (n : ℤ) (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.t.heart.FullSubcategory := by
  letI := hLE
  letI := hGE
  exact ⟨X⟦(n : ℤ)⟧, (h.t.mem_heart_iff _).mpr ⟨by
    simpa using (h.t.isLE_shift X n (n : ℤ) 0 (by omega)),
    by simpa using (h.t.isGE_shift X n (n : ℤ) 0 (by omega))⟩⟩

/-- A `t`-pure object contributes a class coming from the heart. -/
theorem HeartStabilityData.exists_preimage_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} (n : ℤ) (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    ∃ x : HeartK0 (C := C) h, h.heartK0ToK0 C x = K₀.of C X := by
  let H := HeartStabilityData.heartShiftOfPure (C := C) h n hLE hGE
  refine ⟨(((-1 : ℤ) ^ Int.natAbs n) • HeartK0.of (C := C) h H), ?_⟩
  rw [map_zsmul]
  change (((-1 : ℤ) ^ Int.natAbs n) • K₀.of C H.obj) = K₀.of C X
  have hshift := K₀.of_shift_int (C := C) (X := X⟦(n : ℤ)⟧) (-n)
  have hX :
      K₀.of C ((X⟦(n : ℤ)⟧)⟦(-n : ℤ)⟧) = K₀.of C X := by
    calc
      K₀.of C ((X⟦(n : ℤ)⟧)⟦(-n : ℤ)⟧) = K₀.of C (X⟦(0 : ℤ)⟧) := by
        exact (K₀.of_iso C ((shiftFunctorAdd' C (n : ℤ) (-n : ℤ) 0 (by omega)).app X)).symm
      _ = K₀.of C X := K₀.of_iso C ((shiftFunctorZero C ℤ).app X)
  rw [hX] at hshift
  simpa [H, HeartStabilityData.heartShiftOfPure] using hshift.symm

theorem HeartStabilityData.exists_preimage_of_width
    (h : HeartStabilityData C) [IsTriangulated C] (b : ℤ) :
    ∀ n : ℕ, ∀ {E : C}, h.t.IsLE E (b + n) → h.t.IsGE E b →
      ∃ x : HeartK0 (C := C) h, h.heartK0ToK0 C x = K₀.of C E := by
  intro n
  induction n with
  | zero =>
      intro E hLE hGE
      simpa using h.exists_preimage_of_pure (C := C) (X := E) b
        (by simpa using hLE) hGE
  | succ n ih =>
      intro E hLE hGE
      let top : ℤ := b + (n + 1 : ℕ)
      let A := (h.t.truncLT top).obj E
      let P := (h.t.truncGE top).obj E
      obtain ⟨xA, hxA⟩ := ih
        (E := A)
        (by
          dsimp [A, top]
          exact h.t.isLE_truncLT_obj E (b + (n + 1 : ℕ)) (b + (n : ℕ)))
        (by
          letI := hGE
          dsimp [A]
          infer_instance)
      have hP_top : h.t.IsLE P (b + (n + 1 : ℕ)) := by
        letI := hLE
        have hP' : h.t.IsLE ((h.t.truncGE top).obj E) top := by infer_instance
        simpa [P, top] using hP'
      have hP_ge : h.t.IsGE P (b + (n + 1 : ℕ)) := by
        dsimp [P, top]
        infer_instance
      obtain ⟨xP, hxP⟩ := h.exists_preimage_of_pure (C := C)
        (X := P) (b + (n + 1 : ℕ)) hP_top hP_ge
      refine ⟨xA + xP, ?_⟩
      rw [map_add, hxA, hxP]
      have htri := K₀.of_triangle C ((h.t.triangleLTGE top).obj E)
        (h.t.triangleLTGE_distinguished top E)
      simpa [A, P, top, TStructure.triangleLTGE] using htri.symm

/-- Every ambient Grothendieck-group class comes from the Grothendieck group of the
heart of a bounded t-structure. This is the surjective half of the canonical map
`K₀(heart(t)) → K₀(C)`. -/
theorem HeartStabilityData.heartK0ToK0_surjective
    (h : HeartStabilityData C) [IsTriangulated C] :
    Function.Surjective (h.heartK0ToK0 C) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H a =>
      induction a using FreeAbelianGroup.induction_on with
      | zero =>
          exact ⟨0, map_zero _⟩
      | of E =>
          obtain ⟨a, b, hLE, hGE⟩ := h.bounded E
          by_cases hba : b ≤ a
          · have ha : b + (Int.toNat (a - b) : ℤ) = a := by
              have hnonneg : 0 ≤ a - b := by omega
              rw [Int.toNat_of_nonneg hnonneg]
              omega
            have hLE' : h.t.IsLE E (b + (Int.toNat (a - b) : ℤ)) := by
              have hLE'' : h.t.IsLE E a := ⟨hLE⟩
              rw [Int.toNat_of_nonneg (show 0 ≤ a - b by omega)]
              simpa using hLE''
            have hGE' : h.t.IsGE E b := ⟨hGE⟩
            exact h.exists_preimage_of_width (C := C) b (Int.toNat (a - b)) (E := E) hLE' hGE'
          · letI : h.t.IsLE E a := ⟨hLE⟩
            letI : h.t.IsGE E b := ⟨hGE⟩
            have hzero : IsZero E := h.t.isZero E a b (by omega)
            refine ⟨0, ?_⟩
            simpa [K₀.of] using (K₀.of_isZero C hzero).symm
      | neg E ih =>
          rcases ih with ⟨x, hx⟩
          refine ⟨-x, ?_⟩
          rw [map_neg, hx]
          rfl
      | add x y hx hy =>
          rcases hx with ⟨x', hx'⟩
          rcases hy with ⟨y', hy'⟩
          refine ⟨x' + y', ?_⟩
          rw [map_add, hx', hy']
          rfl


end Proposition53

end CategoryTheory.Triangulated
