/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.StabilityCondition
import Mathlib.CategoryTheory.Triangulated.StabilityFunction
import Mathlib.CategoryTheory.Triangulated.IntervalCategory
import Mathlib.CategoryTheory.Triangulated.TStructure.HeartAbelian
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.CategoryTheory.Triangulated.Deformation.PPhiAbelian
import Mathlib.CategoryTheory.Triangulated.Deformation.PhaseArithmetic

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
private theorem ObjectProperty.FullSubcategory.isZero_of_obj_isZero
    {P : ObjectProperty C} [HasZeroObject P.FullSubcategory]
    {X : P.FullSubcategory} (hX : IsZero X.obj) : IsZero X := by
  let Z : P.FullSubcategory := 0
  have hZ : IsZero Z.obj := (P.ι.map_isZero (show IsZero Z from isZero_zero _))
  let e : X.obj ≅ Z.obj := hX.iso hZ
  exact (show IsZero Z from isZero_zero _).of_iso (P.isoMk e)

set_option backward.isDefEq.respectTransparency false in
/-- A short exact sequence in the abelian slice `P(φ)` extends to a distinguished
triangle in the ambient triangulated category. -/
private theorem StabilityCondition.P_phi_shortExact_triangle
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

private theorem StabilityCondition.phase_eq_of_mem_P_phi
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
private theorem HeartStabilityData.ZOnHeartK0_of (h : HeartStabilityData C)
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
private theorem TStructure.heartFullSubcategory_shortExact_triangle
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
private theorem TStructure.heartFullSubcategory_shortExact_of_distTriang
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

private lemma K₀.of_shift_nat (X : C) :
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

private lemma K₀.of_shift_negSucc (X : C) :
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
private theorem K₀.of_shift_int (X : C) (n : ℤ) :
    K₀.of C (X⟦n⟧) = (((-1 : ℤ) ^ Int.natAbs n) • K₀.of C X) := by
  cases n with
  | ofNat m =>
      simpa using K₀.of_shift_nat (C := C) X m
  | negSucc m =>
      simpa using K₀.of_shift_negSucc (C := C) X m

/-- If `X` is concentrated in degree `n`, then `X⟦-n⟧` is an object of the heart. -/
private def HeartStabilityData.heartShiftOfPure (h : HeartStabilityData C)
    {X : C} (n : ℤ) (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.t.heart.FullSubcategory := by
  letI := hLE
  letI := hGE
  exact ⟨X⟦(n : ℤ)⟧, (h.t.mem_heart_iff _).mpr ⟨by
    simpa using (h.t.isLE_shift X n (n : ℤ) 0 (by omega)),
    by simpa using (h.t.isGE_shift X n (n : ℤ) 0 (by omega))⟩⟩

/-- A `t`-pure object contributes a class coming from the heart. -/
private theorem HeartStabilityData.exists_preimage_of_pure
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

private theorem HeartStabilityData.exists_preimage_of_width
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
      | C0 =>
          exact ⟨0, map_zero _⟩
      | C1 E =>
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
      | Cn E ih =>
          rcases ih with ⟨x, hx⟩
          refine ⟨-x, ?_⟩
          rw [map_neg, hx]
          rfl
      | Cp x y hx hy =>
          rcases hx with ⟨x', hx'⟩
          rcases hy with ⟨y', hy'⟩
          refine ⟨x' + y', ?_⟩
          rw [map_add, hx', hy']
          rfl

/-- The degree-`n` heart cohomology object of `E`, realized as the pure
truncation `τ^[n,n]E` shifted into the heart. -/
private def HeartStabilityData.heartCoh
    (h : HeartStabilityData C) (n : ℤ) (E : C) :
    h.t.heart.FullSubcategory :=
  h.heartShiftOfPure (C := C) (X := (h.t.truncGELE n n).obj E) n inferInstance inferInstance

/-- The `HeartK0` class corresponding to the degree-`n` heart cohomology object,
with the usual alternating sign already built in so that its ambient image is the
pure truncation class `[τ^[n,n]E]`. -/
private def HeartStabilityData.heartCohClass
    (h : HeartStabilityData C) (n : ℤ) (E : C) : HeartK0 (C := C) h :=
  (((-1 : ℤ) ^ Int.natAbs n) • HeartK0.of (C := C) h (h.heartCoh (C := C) n E))

/-- The ambient image of the signed heart cohomology class is the class of the
pure truncation `τ^[n,n]E`. -/
private theorem HeartStabilityData.heartK0ToK0_heartCohClass
    (h : HeartStabilityData C) [IsTriangulated C] (n : ℤ) (E : C) :
    h.heartK0ToK0 C (h.heartCohClass (C := C) n E) =
      K₀.of C ((h.t.truncGELE n n).obj E) := by
  dsimp [HeartStabilityData.heartCohClass]
  rw [map_zsmul]
  let X : C := (h.t.truncGELE n n).obj E
  let H : h.t.heart.FullSubcategory := h.heartCoh (C := C) n E
  change (((-1 : ℤ) ^ Int.natAbs n) • K₀.of C H.obj) = K₀.of C X
  have hshift := K₀.of_shift_int (C := C) (X := X⟦(n : ℤ)⟧) (-n)
  have hX :
      K₀.of C ((X⟦(n : ℤ)⟧)⟦(-n : ℤ)⟧) = K₀.of C X := by
    calc
      K₀.of C ((X⟦(n : ℤ)⟧)⟦(-n : ℤ)⟧) = K₀.of C (X⟦(0 : ℤ)⟧) := by
        exact (K₀.of_iso C ((shiftFunctorAdd' C (n : ℤ) (-n : ℤ) 0 (by omega)).app X)).symm
      _ = K₀.of C X := K₀.of_iso C ((shiftFunctorZero C ℤ).app X)
  rw [hX] at hshift
  simpa [X, H, HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure]
    using hshift.symm

/-- One-step telescoping for the bounded truncations: passing from `τ≤(n-1)E` to
`τ≤nE` adds exactly the degree-`n` pure truncation. -/
private theorem HeartStabilityData.k0_truncLE_step
    (h : HeartStabilityData C) [IsTriangulated C] (n : ℤ) (E : C) :
    K₀.of C ((h.t.truncLE n).obj E) =
      K₀.of C ((h.t.truncLE (n - 1)).obj E) +
        h.heartK0ToK0 C (h.heartCohClass (C := C) n E) := by
  have htri :=
    K₀.of_triangle C ((h.t.triangleLTLTGELT n (n + 1) (by omega)).obj E)
      (h.t.triangleLTLTGELT_distinguished n (n + 1) (by omega) E)
  calc
    K₀.of C ((h.t.truncLE n).obj E)
        = K₀.of C ((h.t.truncLE (n - 1)).obj E) +
            K₀.of C ((h.t.truncGELE n n).obj E) := by
              have htri' :
                  K₀.of C ((h.t.truncLT (n + 1)).obj E) =
                    K₀.of C ((h.t.truncLT n).obj E) +
                      K₀.of C ((h.t.truncGELT n (n + 1)).obj E) := by
                simpa using htri
              rw [← K₀.of_iso C ((h.t.truncGELEIsoTruncGELT n n (n + 1) rfl).app E)] at htri'
              simpa [TStructure.truncLE] using htri'
    _ = K₀.of C ((h.t.truncLE (n - 1)).obj E) +
          h.heartK0ToK0 C (h.heartCohClass (C := C) n E) := by
            rw [h.heartK0ToK0_heartCohClass (C := C) n E]

/-- The finite alternating sum of heart cohomology classes from degrees `b` to
`b + n`. -/
private def HeartStabilityData.heartCohClassSum
    (h : HeartStabilityData C) (b : ℤ) (n : ℕ) (E : C) : HeartK0 (C := C) h :=
  Finset.sum (Finset.range (n + 1)) (fun j =>
    h.heartCohClass (C := C) (b + (j : ℤ)) E)

/-- Telescoping formula for the classes of bounded truncations: if `E` is
concentrated in degrees `≥ b`, then `τ≤(b+n)E` is the sum of the heart
cohomology classes in degrees `b, …, b+n`. -/
private theorem HeartStabilityData.heartK0ToK0_heartCohClassSum_truncLE
    (h : HeartStabilityData C) [IsTriangulated C] (b : ℤ) :
    ∀ n : ℕ, ∀ {E : C}, h.t.IsGE E b →
      h.heartK0ToK0 C (h.heartCohClassSum (C := C) b n E) =
        K₀.of C ((h.t.truncLE (b + (n : ℤ))).obj E) := by
  intro n
  induction n with
  | zero =>
      intro E hGE
      have hbase :=
        h.k0_truncLE_step (C := C) b E
      have hzero : IsZero ((h.t.truncLE (b - 1)).obj E) := by
        letI := hGE
        exact h.t.isZero_truncLE_obj_of_isGE (b - 1) b (by omega) E
      calc
        h.heartK0ToK0 C (h.heartCohClassSum (C := C) b 0 E)
            = h.heartK0ToK0 C (h.heartCohClass (C := C) b E) := by
                simp [HeartStabilityData.heartCohClassSum]
        _ = K₀.of C ((h.t.truncLE (b - 1)).obj E) +
              h.heartK0ToK0 C (h.heartCohClass (C := C) b E) := by
                rw [K₀.of_isZero C hzero, zero_add]
        _ = K₀.of C ((h.t.truncLE (b + (0 : ℤ))).obj E) := by
              simpa using hbase.symm
  | succ n ihn =>
      intro E hGE
      calc
        h.heartK0ToK0 C (h.heartCohClassSum (C := C) b (n + 1) E)
            = h.heartK0ToK0 C
                (h.heartCohClassSum (C := C) b n E +
                  h.heartCohClass (C := C) (b + ((n + 1 : ℕ) : ℤ)) E) := by
                rw [HeartStabilityData.heartCohClassSum, HeartStabilityData.heartCohClassSum,
                  Finset.sum_range_succ]
        _ = h.heartK0ToK0 C (h.heartCohClassSum (C := C) b n E) +
              h.heartK0ToK0 C
                (h.heartCohClass (C := C) (b + ((n + 1 : ℕ) : ℤ)) E) := by
                rw [map_add]
        _ = K₀.of C ((h.t.truncLE (b + (n : ℤ))).obj E) +
              h.heartK0ToK0 C
                (h.heartCohClass (C := C) (b + ((n + 1 : ℕ) : ℤ)) E) := by
                rw [ihn hGE]
        _ = K₀.of C ((h.t.truncLE (b + (((n + 1 : ℕ) : ℤ)))).obj E) := by
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                  (h.k0_truncLE_step (C := C) (b + (((n + 1 : ℕ) : ℤ))) E).symm

/-- The canonical bounded interval sum of heart cohomology classes maps to `[E]` in
ambient `K₀`. This is the usual formula `[E] = Σ (-1)^n [H^n_t(E)]`. -/
private theorem HeartStabilityData.heartK0ToK0_heartCohClassSum
    (h : HeartStabilityData C) [IsTriangulated C]
    {E : C} (a b : ℤ) (hab : b ≤ a) (hLE : h.t.IsLE E a) (hGE : h.t.IsGE E b) :
    h.heartK0ToK0 C (h.heartCohClassSum (C := C) b (Int.toNat (a - b)) E) = K₀.of C E := by
  have hsum :=
    h.heartK0ToK0_heartCohClassSum_truncLE (C := C) b (Int.toNat (a - b)) (E := E) hGE
  have ha : b + (Int.toNat (a - b) : ℤ) = a := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    omega
  rw [ha] at hsum
  have hτ : K₀.of C ((h.t.truncLE a).obj E) = K₀.of C E := by
    have hIso : IsIso ((h.t.truncLEι a).app E) :=
      (h.t.isLE_iff_isIso_truncLEι_app a E).mp hLE
    let e : (h.t.truncLE a).obj E ≅ E := @asIso _ _ _ _ ((h.t.truncLEι a).app E) hIso
    exact K₀.of_iso C e
  exact hsum.trans hτ

/-- A classical choice of an upper bound for an object with respect to the bounded
t-structure. -/
private noncomputable def HeartStabilityData.upperBound
    (h : HeartStabilityData C) (E : C) : ℤ := by
  classical
  exact if hE : h.t.heart E then 0 else Classical.choose (h.bounded E)

/-- A classical choice of a lower bound for an object with respect to the bounded
t-structure. -/
private noncomputable def HeartStabilityData.lowerBound
    (h : HeartStabilityData C) (E : C) : ℤ := by
  classical
  exact if hE : h.t.heart E then 0 else Classical.choose (Classical.choose_spec (h.bounded E))

private theorem HeartStabilityData.isLE_upperBound
    (h : HeartStabilityData C) (E : C) :
    h.t.IsLE E (h.upperBound (C := C) E) := by
  classical
  by_cases hE : h.t.heart E
  · simpa [HeartStabilityData.upperBound, hE] using ((h.t.mem_heart_iff E).mp hE).1
  · simpa [HeartStabilityData.upperBound, hE] using
      (⟨(Classical.choose_spec (Classical.choose_spec (h.bounded E))).1⟩ :
        h.t.IsLE E (Classical.choose (h.bounded E)))

private theorem HeartStabilityData.isGE_lowerBound
    (h : HeartStabilityData C) (E : C) :
    h.t.IsGE E (h.lowerBound (C := C) E) := by
  classical
  by_cases hE : h.t.heart E
  · simpa [HeartStabilityData.lowerBound, hE] using ((h.t.mem_heart_iff E).mp hE).2
  · simpa [HeartStabilityData.lowerBound, hE] using
      (⟨(Classical.choose_spec (Classical.choose_spec (h.bounded E))).2⟩ :
        h.t.IsGE E (Classical.choose (Classical.choose_spec (h.bounded E))))

/-- The canonical object-level lift of `[E]` to `K₀(heart)`, given by the
alternating sum of the chosen bounded heart cohomology classes. If the chosen
bounds are reversed, then `E` is zero and we return `0`. -/
private noncomputable def HeartStabilityData.heartEulerClassObj
    (h : HeartStabilityData C) [IsTriangulated C] (E : C) : HeartK0 (C := C) h := by
  classical
  let a := h.upperBound (C := C) E
  let b := h.lowerBound (C := C) E
  by_cases hab : b ≤ a
  · exact h.heartCohClassSum (C := C) b (Int.toNat (a - b)) E
  · exact 0

/-- The canonical object-level lift maps to the ambient Grothendieck-group class
of the original object. -/
private theorem HeartStabilityData.heartK0ToK0_heartEulerClassObj
    (h : HeartStabilityData C) [IsTriangulated C] (E : C) :
    h.heartK0ToK0 C (h.heartEulerClassObj (C := C) E) = K₀.of C E := by
  classical
  let a := h.upperBound (C := C) E
  let b := h.lowerBound (C := C) E
  have hLE : h.t.IsLE E a := h.isLE_upperBound (C := C) E
  have hGE : h.t.IsGE E b := h.isGE_lowerBound (C := C) E
  by_cases hab : b ≤ a
  · simpa [HeartStabilityData.heartEulerClassObj, a, b, hab] using
      h.heartK0ToK0_heartCohClassSum (C := C) (E := E) a b hab hLE hGE
  · have hzero : IsZero E := h.t.isZero E a b (by omega)
    rw [HeartStabilityData.heartEulerClassObj, dif_neg hab, map_zero, K₀.of_isZero C hzero]

private theorem HeartStabilityData.heartCohClass_zero_of_heart
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : h.t.heart.FullSubcategory) :
    h.heartCohClass (C := C) 0 E.obj = HeartK0.of (C := C) h E := by
  have hLE0 : h.t.IsLE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.1
  have hGE0 : h.t.IsGE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.2
  let eLE : (h.t.truncLE 0).obj E.obj ≅ E.obj :=
    @asIso _ _ _ _ ((h.t.truncLEι 0).app E.obj) ((h.t.isLE_iff_isIso_truncLEι_app 0 E.obj).mp hLE0)
  let eGE : E.obj ≅ (h.t.truncGE 0).obj E.obj :=
    @asIso _ _ _ _ ((h.t.truncGEπ 0).app E.obj) ((h.t.isGE_iff_isIso_truncGEπ_app 0 E.obj).mp hGE0)
  let e0 : (h.t.truncGELE 0 0).obj E.obj ≅ E.obj :=
    (h.t.truncGE 0).mapIso eLE ≪≫ eGE.symm
  let e0' : (h.heartCoh (C := C) 0 E.obj).obj ≅ E.obj := by
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      ((shiftFunctorZero C ℤ).app ((h.t.truncGELE 0 0).obj E.obj) ≪≫ e0)
  let eH : h.heartCoh (C := C) 0 E.obj ≅ E := ObjectProperty.isoMk _ e0'
  simpa [HeartStabilityData.heartCohClass, HeartStabilityData.heartCoh] using
    HeartK0.of_iso (C := C) h eH

/-- On objects already lying in the heart, the Euler lift is the obvious heart
Grothendieck-group class. -/
private theorem HeartStabilityData.heartEulerClassObj_of_heart
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : h.t.heart.FullSubcategory) :
    h.heartEulerClassObj (C := C) E.obj = HeartK0.of (C := C) h E := by
  have hE : h.t.heart E.obj := E.property
  simp [HeartStabilityData.heartEulerClassObj, HeartStabilityData.upperBound,
    HeartStabilityData.lowerBound, hE, HeartStabilityData.heartCohClassSum,
    h.heartCohClass_zero_of_heart (C := C) E]

/-- The object-level central charge candidate obtained by taking the Euler class in
`HeartK0` and then applying the heart central charge. This is the expected extension
of `Z` along `K₀(heart) → K₀(C)` once the latter is shown to be an equivalence. -/
private noncomputable def HeartStabilityData.eulerZObj
    (h : HeartStabilityData C) [IsTriangulated C] (E : C) : ℂ :=
  h.ZOnHeartK0 (C := C) (h.heartEulerClassObj (C := C) E)

private theorem HeartStabilityData.eulerZObj_of_heart
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : h.t.heart.FullSubcategory) :
    h.eulerZObj (C := C) E.obj = HeartStabilityData.heartZObj (C := C) h E := by
  simp [HeartStabilityData.eulerZObj, h.heartEulerClassObj_of_heart (C := C) E]

private theorem HeartStabilityData.ZOnHeartK0_heartCohClass
    (h : HeartStabilityData C) [IsTriangulated C] (n : ℤ) (E : C) :
    h.ZOnHeartK0 (C := C) (h.heartCohClass (C := C) n E) =
      (((-1 : ℤ) ^ Int.natAbs n) •
        HeartStabilityData.heartZObj (C := C) h (h.heartCoh (C := C) n E)) := by
  rw [HeartStabilityData.heartCohClass, map_zsmul, h.ZOnHeartK0_of (C := C)]

/-- If a distinguished triangle is concentrated in a single `t`-degree `n`, then after
shifting by `n` it yields the expected short exact relation in the heart Grothendieck
group. -/
private theorem HeartStabilityData.heartK0_relation_of_pure_distTriang
    (h : HeartStabilityData C) [IsTriangulated C]
    {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧}
    (n : ℤ) (hT : Triangle.mk f g δ ∈ distTriang C)
    (h₁LE : h.t.IsLE X₁ n) (h₁GE : h.t.IsGE X₁ n)
    (h₂LE : h.t.IsLE X₂ n) (h₂GE : h.t.IsGE X₂ n)
    (h₃LE : h.t.IsLE X₃ n) (h₃GE : h.t.IsGE X₃ n) :
    let H₁ := h.heartShiftOfPure (C := C) (X := X₁) n h₁LE h₁GE
    let H₂ := h.heartShiftOfPure (C := C) (X := X₂) n h₂LE h₂GE
    let H₃ := h.heartShiftOfPure (C := C) (X := X₃) n h₃LE h₃GE
    (((-1 : ℤ) ^ Int.natAbs n) • HeartK0.of (C := C) h H₂) =
      (((-1 : ℤ) ^ Int.natAbs n) • HeartK0.of (C := C) h H₁) +
        (((-1 : ℤ) ^ Int.natAbs n) • HeartK0.of (C := C) h H₃) := by
  let H₁ := h.heartShiftOfPure (C := C) (X := X₁) n h₁LE h₁GE
  let H₂ := h.heartShiftOfPure (C := C) (X := X₂) n h₂LE h₂GE
  let H₃ := h.heartShiftOfPure (C := C) (X := X₃) n h₃LE h₃GE
  let shT := (Triangle.shiftFunctor C n).obj (Triangle.mk f g δ)
  have hT_sh : shT ∈ distTriang C := Triangle.shift_distinguished _ hT n
  let fH : H₁ ⟶ H₂ := ObjectProperty.homMk shT.mor₁
  let gH : H₂ ⟶ H₃ := ObjectProperty.homMk shT.mor₂
  have hSE :
      (ShortComplex.mk fH gH (by
        ext
        exact comp_distTriang_mor_zero₁₂ _ hT_sh)).ShortExact := by
    refine TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) h.t (A := H₁) (B := H₂) (Q := H₃) (f := fH) (g := gH) (δ := shT.mor₃) ?_
    simpa [fH, gH, shT] using hT_sh
  have hK0 := HeartK0.of_shortExact (C := C) h hSE
  simpa [H₁, H₂, H₃, zsmul_add] using
    congrArg (fun x : HeartK0 (C := C) h => (((-1 : ℤ) ^ Int.natAbs n) • x)) hK0

private theorem HeartStabilityData.heartCohClass_eq_zero_of_lt_bound
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {m n : ℤ} (hmn : m < n) (hGE : h.t.IsGE X n) :
    h.heartCohClass (C := C) m X = 0 := by
  have hGE' : h.t.IsGE X (m + 1) := h.t.isGE_of_ge X (m + 1) n (by omega)
  have hzeroObj : IsZero ((h.t.truncGELE m m).obj X) := by
    dsimp [TStructure.truncGELE]
    exact Functor.map_isZero (h.t.truncGE m)
      (h.t.isZero_truncLE_obj_of_isGE m (m + 1) (by omega) X)
  have hzeroHeart : IsZero (h.heartCoh (C := C) m X) := by
    refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      (shiftFunctor C m).map_isZero hzeroObj
  rw [HeartStabilityData.heartCohClass]
  simp [HeartK0.of_isZero (C := C) h hzeroHeart]

private theorem HeartStabilityData.heartCohClass_eq_zero_of_lt_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {m n : ℤ} (hmn : m < n)
    (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.heartCohClass (C := C) m X = 0 :=
  h.heartCohClass_eq_zero_of_lt_bound (C := C) hmn hGE

private theorem HeartStabilityData.heartCohClass_eq_zero_of_gt_bound
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {m n : ℤ} (hmn : n < m) (hLE : h.t.IsLE X n) :
    h.heartCohClass (C := C) m X = 0 := by
  have hLE' : h.t.IsLE X (m - 1) := h.t.isLE_of_le X n (m - 1) (by omega)
  have hLEm : h.t.IsLE X m := h.t.isLE_of_le X n m (by omega)
  let eLE : (h.t.truncLE m).obj X ≅ X :=
    @asIso _ _ _ _ ((h.t.truncLEι m).app X) ((h.t.isLE_iff_isIso_truncLEι_app m X).mp hLEm)
  have hzeroObj : IsZero ((h.t.truncGELE m m).obj X) := by
    dsimp [TStructure.truncGELE]
    exact (h.t.isZero_truncGE_obj_of_isLE (m - 1) m (by omega) X).of_iso
      ((h.t.truncGE m).mapIso eLE)
  have hzeroHeart : IsZero (h.heartCoh (C := C) m X) := by
    refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      (shiftFunctor C m).map_isZero hzeroObj
  rw [HeartStabilityData.heartCohClass]
  simp [HeartK0.of_isZero (C := C) h hzeroHeart]

private theorem HeartStabilityData.heartCohClass_eq_zero_of_gt_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {m n : ℤ} (hmn : n < m)
    (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.heartCohClass (C := C) m X = 0 :=
  h.heartCohClass_eq_zero_of_gt_bound (C := C) hmn hLE

private theorem HeartStabilityData.heartCohClassSum_eq_zero_of_lt_bound
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {b c : ℤ} {n : ℕ} (hbc : b + (n : ℤ) < c) (hGE : h.t.IsGE X c) :
    h.heartCohClassSum (C := C) b n X = 0 := by
  rw [HeartStabilityData.heartCohClassSum]
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hjn : (j : ℤ) ≤ n := by
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjc : b + (j : ℤ) < c := by omega
  exact h.heartCohClass_eq_zero_of_lt_bound (C := C) (X := X) (m := b + (j : ℤ))
    (n := c) hjc hGE

private theorem HeartStabilityData.heartCohClassSum_eq_zero_of_gt_bound
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {b c : ℤ} {n : ℕ} (hcb : c < b) (hLE : h.t.IsLE X c) :
    h.heartCohClassSum (C := C) b n X = 0 := by
  rw [HeartStabilityData.heartCohClassSum]
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hjc : c < b + (j : ℤ) := by
    have hj0 : 0 ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
    omega
  exact h.heartCohClass_eq_zero_of_gt_bound (C := C) (X := X) (m := b + (j : ℤ))
    (n := c) hjc hLE

private theorem HeartStabilityData.heartCohClassSum_eq_single_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {n b : ℤ} {m : ℕ}
    (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n)
    (hb : b ≤ n) (hn : n ≤ b + (m : ℤ)) :
    h.heartCohClassSum (C := C) b m X = h.heartCohClass (C := C) n X := by
  let k : ℕ := Int.toNat (n - b)
  have hk_eq : b + (k : ℤ) = n := by
    dsimp [k]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hb)]
    omega
  have hk_mem : k ∈ Finset.range (m + 1) := by
    apply Finset.mem_range.mpr
    have hkm : (n - b).toNat ≤ m := by
      have hkm' : n - b ≤ (m : ℤ) := by
        omega
      rw [Int.toNat_le]
      exact hkm'
    exact Nat.lt_succ_of_le hkm
  rw [HeartStabilityData.heartCohClassSum]
  rw [Finset.sum_eq_single_of_mem k hk_mem]
  · simpa [hk_eq]
  · intro j hj hjk
    by_cases hjn : b + (j : ℤ) < n
    · simpa [hjn] using
        h.heartCohClass_eq_zero_of_lt_pure (C := C) (X := X) (m := b + (j : ℤ))
          (n := n) hjn hLE hGE
    · have hnj : n < b + (j : ℤ) := by
        omega
      simpa [hnj] using
        h.heartCohClass_eq_zero_of_gt_pure (C := C) (X := X) (m := b + (j : ℤ))
          (n := n) hnj hLE hGE

private theorem HeartStabilityData.heartCohClassSum_eq_top_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {a b : ℤ} (hab : b ≤ a)
    (hLE : h.t.IsLE X a) (hGE : h.t.IsGE X a) :
    h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X =
      h.heartCohClass (C := C) a X := by
  refine h.heartCohClassSum_eq_single_of_pure (C := C) (X := X) (n := a) (b := b)
    (m := Int.toNat (a - b)) hLE hGE hab ?_
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
  omega

private theorem HeartStabilityData.ZOnHeartK0_heartCohClassSum_eq_top_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {a b : ℤ} (hab : b ≤ a)
    (hLE : h.t.IsLE X a) (hGE : h.t.IsGE X a) :
    h.ZOnHeartK0 (C := C) (h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X) =
      h.ZOnHeartK0 (C := C) (h.heartCohClass (C := C) a X) := by
  exact congrArg (h.ZOnHeartK0 (C := C))
    (h.heartCohClassSum_eq_top_of_pure (C := C) hab hLE hGE)

private theorem HeartStabilityData.ZOnHeartK0_heartCohClassSum_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {a b : ℤ} (hab : b ≤ a)
    (hLE : h.t.IsLE X a) (hGE : h.t.IsGE X a) :
    h.ZOnHeartK0 (C := C) (h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X) =
      (((-1 : ℤ) ^ Int.natAbs a) •
        HeartStabilityData.heartZObj (C := C) h (h.heartCoh (C := C) a X)) := by
  rw [h.ZOnHeartK0_heartCohClassSum_eq_top_of_pure (C := C) hab hLE hGE,
    h.ZOnHeartK0_heartCohClass (C := C) a X]

private theorem HeartStabilityData.eulerZObj_additive_of_heart_shortExact
    (h : HeartStabilityData C) [IsTriangulated C]
    {S : ShortComplex h.t.heart.FullSubcategory} (hS : S.ShortExact) :
    h.eulerZObj (C := C) S.X₂.obj =
      h.eulerZObj (C := C) S.X₁.obj + h.eulerZObj (C := C) S.X₃.obj := by
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  rw [h.eulerZObj_of_heart (C := C) S.X₂, h.eulerZObj_of_heart (C := C) S.X₁,
    h.eulerZObj_of_heart (C := C) S.X₃]
  exact h.Z.additive S hS

private theorem TStructure.triangleLTGE_iso_of_amp_negOne_zero
    (t : TStructure C) [IsTriangulated C]
    {X K Q : C} (hK : t.heart K) (hQ : t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [t.IsLE X 0] [t.IsGE X (-1)] :
    ∃ e : Triangle.mk α β γ ≅ (t.triangleLTGE 0).obj X, e.hom.hom₂ = 𝟙 X := by
  obtain ⟨e, he⟩ := t.triangle_iso_exists hT (t.triangleLTGE_distinguished 0 X) (Iso.refl X) (-1) 0
    (by
      have hK' := (t.mem_heart_iff K).mp hK
      letI : t.IsLE K 0 := hK'.1
      exact t.isLE_shift K 0 1 (-1))
    (by
      have hQ' := (t.mem_heart_iff Q).mp hQ
      exact hQ'.2)
    (by
      have : t.IsLE ((t.triangleLTGE 0).obj X).obj₁ (0 - 1) := by infer_instance
      simpa using this)
    (by infer_instance)
  exact ⟨e, he⟩

private noncomputable def HeartStabilityData.heartCoh_negOne_iso_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] [h.t.IsGE X (-1)] :
    h.heartCoh (C := C) (-1) X ≅ ⟨K, hK⟩ := by
  classical
  let hEx := TStructure.triangleLTGE_iso_of_amp_negOne_zero
    (C := C) (t := h.t) (X := X) (K := K) (Q := Q) hK hQ hT
  let eT := Classical.choose hEx
  let e₁ :
      ((h.t.truncGELE (-1) (-1)).obj X) ≅ ((h.t.truncGELT (-1) 0).obj X) :=
    (h.t.truncGELEIsoTruncGELT (-1) (-1) 0 rfl).app X
  let e₂ :
      ((h.t.truncGELT (-1) 0).obj X) ≅ (h.t.truncLT 0).obj X :=
    by
      simpa [TStructure.truncGELT] using
        ((@asIso _ _ _ _ ((h.t.truncGEπ (-1)).app ((h.t.truncLT 0).obj X))
          (by
            change IsIso ((h.t.truncGEπ (-1)).app ((h.t.truncLT 0).obj X))
            infer_instance)).symm)
  let e₃ : (h.t.truncLT 0).obj X ≅ K⟦(1 : ℤ)⟧ :=
    (asIso eT.hom.hom₁).symm
  let e : ((h.t.truncGELE (-1) (-1)).obj X) ≅ K⟦(1 : ℤ)⟧ := e₁ ≪≫ e₂ ≪≫ e₃
  let e' : (h.heartCoh (C := C) (-1) X).obj ≅ K := by
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      ((shiftFunctor C (-1 : ℤ)).mapIso e ≪≫ shiftShiftNeg (X := K) (i := (1 : ℤ)))
  exact ObjectProperty.isoMk _ e'

private noncomputable def HeartStabilityData.heartCoh_zero_iso_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] [h.t.IsGE X (-1)] :
    h.heartCoh (C := C) 0 X ≅ ⟨Q, hQ⟩ := by
  classical
  let hEx := TStructure.triangleLTGE_iso_of_amp_negOne_zero
    (C := C) (t := h.t) (X := X) (K := K) (Q := Q) hK hQ hT
  let eT := Classical.choose hEx
  let e₁ :
      ((h.t.truncGELE 0 0).obj X) ≅ (h.t.truncGE 0).obj X :=
    by
      refine ((h.t.truncGELEIsoLEGE 0 0).app X) ≪≫ ?_
      simpa [TStructure.truncLEGE] using
        (@asIso _ _ _ _ ((h.t.truncLEι 0).app ((h.t.truncGE 0).obj X))
          (by
            change IsIso ((h.t.truncLEι 0).app ((h.t.truncGE 0).obj X))
            infer_instance))
  let e₂ : (h.t.truncGE 0).obj X ≅ Q :=
    (asIso eT.hom.hom₃).symm
  let e : ((h.t.truncGELE 0 0).obj X) ≅ Q := e₁ ≪≫ e₂
  let e' : (h.heartCoh (C := C) 0 X).obj ≅ Q := by
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      ((shiftFunctorZero C ℤ).app ((h.t.truncGELE 0 0).obj X) ≪≫ e)
  exact ObjectProperty.isoMk _ e'

private theorem HeartStabilityData.heartCohClassSum_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] [h.t.IsGE X (-1)] :
    h.heartCohClassSum (C := C) (-1) 1 X =
      -HeartK0.of (C := C) h ⟨K, hK⟩ + HeartK0.of (C := C) h ⟨Q, hQ⟩ := by
  have hneg :
      HeartK0.of (C := C) h (h.heartCoh (C := C) (-1) X) =
        HeartK0.of (C := C) h ⟨K, hK⟩ := by
    exact HeartK0.of_iso (C := C) h
      (h.heartCoh_negOne_iso_of_amp_negOne_zero (C := C)
        (X := X) (K := K) (Q := Q) hK hQ hT)
  have hzero :
      HeartK0.of (C := C) h (h.heartCoh (C := C) 0 X) =
        HeartK0.of (C := C) h ⟨Q, hQ⟩ := by
    exact HeartK0.of_iso (C := C) h
      (h.heartCoh_zero_iso_of_amp_negOne_zero (C := C)
        (X := X) (K := K) (Q := Q) hK hQ hT)
  rw [HeartStabilityData.heartCohClassSum, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp [HeartStabilityData.heartCohClass, hneg, hzero]

private theorem HeartStabilityData.ZOnHeartK0_heartCohClassSum_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] [h.t.IsGE X (-1)] :
    h.ZOnHeartK0 (C := C) (h.heartCohClassSum (C := C) (-1) 1 X) =
      -HeartStabilityData.heartZObj (C := C) h ⟨K, hK⟩ +
        HeartStabilityData.heartZObj (C := C) h ⟨Q, hQ⟩ := by
  have hclass := h.heartCohClassSum_of_amp_negOne_zero (C := C)
    (X := X) (K := K) (Q := Q) hK hQ hT
  simpa using congrArg (h.ZOnHeartK0 (C := C)) hclass

private def StabilityCondition.stabilityFunctionOnHeart
    (σ : StabilityCondition C) :
    @StabilityFunction (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian) := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  exact {
    Zobj := fun E => σ.Z (K₀.of C E.obj)
    map_zero' := fun X hX => by
      simpa using congrArg σ.Z (K₀.of_isZero C (((t.heart).ι.map_isZero hX)))
    additive := fun S hS => by
      letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
      letI : IsNormalMonoCategory t.heart.FullSubcategory := Abelian.toIsNormalMonoCategory
      letI : IsNormalEpiCategory t.heart.FullSubcategory := Abelian.toIsNormalEpiCategory
      letI : Balanced t.heart.FullSubcategory := by infer_instance
      haveI := hS.mono_f
      haveI := hS.epi_g
      obtain ⟨δ, hT⟩ :=
        TStructure.heartFullSubcategory_shortExact_triangle (C := C) t S.f S.g S.zero
          (fun {W} α hα ↦ by
            have hker : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
            exact ⟨hker.lift (KernelFork.ofι α hα), hker.fac _ WalkingParallelPair.zero⟩)
      simpa using congrArg σ.Z (K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT)
    upper := fun E hE => by
      classical
      let ι := (t.heart).ι
      have hEobj : ¬IsZero E.obj := fun hZ ↦
        hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := t.heart) (X := E) hZ)
      have hEheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
      obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEobj
      let P := F.toPostnikovTower
      let s : Finset (Fin F.n) := Finset.univ.filter (fun i => ¬IsZero (P.factor i))
      have hs : s.Nonempty := by
        obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hEobj
        exact ⟨i, by simpa [s, P] using hi⟩
      have hphiMinus : 0 < σ.slicing.phiMinus C E.obj hEobj :=
        gt_phases_of_gtProp C σ.slicing hEobj hEheart.1
      have hphiPlus : σ.slicing.phiPlus C E.obj hEobj ≤ 1 :=
        σ.slicing.phiPlus_le_of_leProp C hEobj hEheart.2
      have hphase_mem : ∀ i ∈ s, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
        intro i hi
        constructor
        · calc
            0 < σ.slicing.phiMinus C E.obj hEobj := hphiMinus
            _ = F.φ ⟨F.n - 1, by omega⟩ := by
              rw [σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast]
            _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
        · calc
            F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C E.obj hEobj := by
              rw [σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst]
            _ ≤ 1 := hphiPlus
      have hterm : ∀ i ∈ s, σ.Z (K₀.of C (P.factor i)) ∈ upperHalfPlaneUnion := by
        intro i hi
        letI : Abelian (σ.slicing.P (F.φ i)).FullSubcategory := σ.P_phi_abelian C (F.φ i)
        let Xi : (σ.slicing.P (F.φ i)).FullSubcategory := ⟨P.factor i, F.semistable i⟩
        have hXi : ¬IsZero Xi := by
          intro hZ
          exact (show ¬IsZero (P.factor i) from by simpa [s, P] using hi)
            ((σ.slicing.P (F.φ i)).ι.map_isZero hZ)
        exact (σ.stabilityFunctionOnPhase C (hphase_mem i hi)).upper Xi hXi
      let f : Fin F.n → ℂ := fun i => σ.Z (K₀.of C (P.factor i))
      have hsum_all : σ.Z (K₀.of C E.obj) = Finset.sum Finset.univ f := by
        rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
      let z : Finset (Fin F.n) := Finset.univ.filter (fun i => IsZero (P.factor i))
      have hzero_filter :
          Finset.sum z f = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simp only [z, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [K₀.of_isZero C hi, map_zero]
      have hsum_filter :
          Finset.sum Finset.univ f = Finset.sum s f := by
        calc
          Finset.sum Finset.univ f = Finset.sum s f + Finset.sum z f := by
            simpa [s, z, f] using
              (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
                (p := fun i : Fin F.n => ¬IsZero (P.factor i)) (f := f)).symm
          _ = Finset.sum s f + 0 := by rw [hzero_filter]
          _ = Finset.sum s f := by simp
      rw [hsum_all, hsum_filter]
      exact sum_mem_upperHalfPlane hs hterm }

private theorem StabilityCondition.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi
    (σ : StabilityCondition C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1)
    (E : (σ.slicing.toTStructure.heart).FullSubcategory)
    (hP : σ.slicing.P φ E.obj) (hE : ¬IsZero E) :
    @StabilityFunction.phase _ _ ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      (σ.stabilityFunctionOnHeart C) E = φ := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦
    hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ)
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E.obj hP hEobj
  have harg : Complex.arg ((m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I)) = Real.pi * φ := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor
    · nlinarith [Real.pi_pos, hφ.1]
    · nlinarith [Real.pi_pos, hφ.2]
  change (1 / Real.pi) * Complex.arg (σ.Z (K₀.of C E.obj)) = φ
  rw [hmZ, harg]
  field_simp [Real.pi_ne_zero]

private theorem StabilityCondition.stabilityFunctionOnHeart_phase_le_phiPlus
    (σ : StabilityCondition C)
    (E : (σ.slicing.toTStructure.heart).FullSubcategory) (hE : ¬IsZero E) :
    @StabilityFunction.phase _ _ ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      (σ.stabilityFunctionOnHeart C) E ≤
        σ.slicing.phiPlus C E.obj
          (fun hZ ↦ hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
            (C := C) (P := σ.slicing.toTStructure.heart) (X := E) hZ)) := by
  classical
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦
    hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ)
  have hEheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEobj
  let P := F.toPostnikovTower
  let s : Finset (Fin F.n) := Finset.univ.filter (fun i => ¬IsZero (P.factor i))
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hEobj
    exact ⟨i, by simpa [s, P] using hi⟩
  have hphiMinus : 0 < σ.slicing.phiMinus C E.obj hEobj :=
    gt_phases_of_gtProp C σ.slicing hEobj hEheart.1
  have hphiPlus : σ.slicing.phiPlus C E.obj hEobj ≤ 1 :=
    σ.slicing.phiPlus_le_of_leProp C hEobj hEheart.2
  have hphase_mem : ∀ i ∈ s, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i hi
    constructor
    · calc
        0 < σ.slicing.phiMinus C E.obj hEobj := hphiMinus
        _ = F.φ ⟨F.n - 1, by omega⟩ := by
          rw [σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast]
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C E.obj hEobj := by
          rw [σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst]
        _ ≤ 1 := hphiPlus
  let f : Fin F.n → ℂ := fun i => σ.Z (K₀.of C (P.factor i))
  have hterm : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion := by
    intro i hi
    letI : Abelian (σ.slicing.P (F.φ i)).FullSubcategory := σ.P_phi_abelian C (F.φ i)
    let Xi : (σ.slicing.P (F.φ i)).FullSubcategory := ⟨P.factor i, F.semistable i⟩
    have hXi : ¬IsZero Xi := by
      intro hZ
      exact (show ¬IsZero (P.factor i) from by simpa [s, P] using hi)
        ((σ.slicing.P (F.φ i)).ι.map_isZero hZ)
    simpa [f] using (σ.stabilityFunctionOnPhase C (hphase_mem i hi)).upper Xi hXi
  have harg_factor : ∀ i ∈ s, Complex.arg (f i) = Real.pi * F.φ i := by
    intro i hi
    have hi_ne : ¬IsZero (P.factor i) := by
      simpa [s, P] using hi
    obtain ⟨m, hm, hmZ⟩ := σ.compat (F.φ i) (P.factor i) (F.semistable i) hi_ne
    rw [show f i = (m : ℂ) * Complex.exp (↑(Real.pi * F.φ i) * Complex.I) by
      simpa [f] using hmZ]
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor
    · nlinarith [Real.pi_pos, (hphase_mem i hi).1]
    · nlinarith [Real.pi_pos, (hphase_mem i hi).2]
  have hsum_all : σ.Z (K₀.of C E.obj) = Finset.sum Finset.univ f := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  let z : Finset (Fin F.n) := Finset.univ.filter (fun i => IsZero (P.factor i))
  have hzero_filter :
      Finset.sum z f = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [z, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    change σ.Z (K₀.of C (P.factor i)) = 0
    rw [K₀.of_isZero C hi, map_zero]
  have hsum_filter :
      Finset.sum Finset.univ f = Finset.sum s f := by
    calc
      Finset.sum Finset.univ f = Finset.sum s f + Finset.sum z f := by
        simpa [s, z, f] using
          (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
            (p := fun i : Fin F.n => ¬IsZero (P.factor i)) (f := f)).symm
      _ = Finset.sum s f + 0 := by rw [hzero_filter]
      _ = Finset.sum s f := by simp
  have hsup_le :
      s.sup' hs (Complex.arg ∘ f) ≤ Real.pi * σ.slicing.phiPlus C E.obj hEobj := by
    refine (Finset.sup'_le_iff hs (Complex.arg ∘ f)).2 ?_
    intro i hi
    rw [Function.comp_apply, harg_factor i hi]
    have hle : F.φ i ≤ σ.slicing.phiPlus C E.obj hEobj := by
      calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C E.obj hEobj := by
          rw [σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst]
    nlinarith [Real.pi_pos, hle]
  change (1 / Real.pi) * Complex.arg (σ.Z (K₀.of C E.obj)) ≤ σ.slicing.phiPlus C E.obj hEobj
  rw [hsum_all, hsum_filter]
  have harg_le := arg_sum_le_sup'_of_upperHalfPlane hs hterm
  have harg_le' :
      Complex.arg (Finset.sum s f) ≤ Real.pi * σ.slicing.phiPlus C E.obj hEobj :=
    harg_le.trans hsup_le
  have hmul : (1 / Real.pi) * Complex.arg (Finset.sum s f) ≤
      (1 / Real.pi) * (Real.pi * σ.slicing.phiPlus C E.obj hEobj) := by
    exact mul_le_mul_of_nonneg_left harg_le' (by positivity)
  simpa [Real.pi_ne_zero] using hmul

private theorem StabilityCondition.stabilityFunctionOnHeart_isSemistable_of_mem_P_phi
    (σ : StabilityCondition C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1)
    (E : (σ.slicing.toTStructure.heart).FullSubcategory)
    (hP : σ.slicing.P φ E.obj) (hE : ¬IsZero E) :
    @StabilityFunction.IsSemistable _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      (σ.stabilityFunctionOnHeart C) E := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦
    hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ)
  refine ⟨hE, ?_⟩
  intro B hB
  let B' : t.heart.FullSubcategory := (B : t.heart.FullSubcategory)
  have hBobj : ¬IsZero B'.obj := fun hZ ↦
    hB (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := B') hZ)
  have hphiPlus_le : σ.slicing.phiPlus C B'.obj hBobj ≤ φ := by
    by_contra hgt
    push_neg at hgt
    have hBheart := (σ.slicing.toTStructure_heart_iff C B'.obj).mp B'.property
    obtain ⟨F, hn, hfirst⟩ := HNFiltration.exists_nonzero_first C σ.slicing hBobj
    have htop : σ.slicing.phiPlus C B'.obj hBobj = F.φ ⟨0, hn⟩ := by
      exact σ.slicing.phiPlus_eq C B'.obj hBobj F hn hfirst
    have hphase_gt : φ < F.φ ⟨0, hn⟩ := by
      rw [← htop]
      exact hgt
    have hphase_mem : F.φ ⟨0, hn⟩ ∈ Set.Ioc (0 : ℝ) 1 := by
      constructor
      · exact lt_trans hφ.1 hphase_gt
      · rw [← htop]
        exact σ.slicing.phiPlus_le_of_leProp C hBobj hBheart.2
    have hA0_heart : t.heart (F.triangle ⟨0, hn⟩).obj₃ := by
      rw [σ.slicing.toTStructure_heart_iff C]
      exact ⟨σ.slicing.gtProp_of_semistable C (F.φ ⟨0, hn⟩) 0 _
          (F.semistable ⟨0, hn⟩) hphase_mem.1,
        σ.slicing.leProp_of_semistable C (F.φ ⟨0, hn⟩) 1 _
          (F.semistable ⟨0, hn⟩) hphase_mem.2⟩
    have hα :
        ∃ α : (F.triangle ⟨0, hn⟩).obj₃ ⟶ B'.obj, α ≠ 0 := by
      by_contra hzero
      push_neg at hzero
      exact hfirst (F.isZero_factor_zero_of_hom_eq_zero C σ.slicing hn hzero)
    rcases hα with ⟨α, hα⟩
    let A0 : t.heart.FullSubcategory := ⟨(F.triangle ⟨0, hn⟩).obj₃, hA0_heart⟩
    let αH : A0 ⟶ B' := ObjectProperty.homMk α
    have hcomp_ne : α ≫ B.arrow.hom ≠ 0 := by
      intro h0
      have h0H : αH ≫ B.arrow = 0 := by
        ext
        exact h0
      have hαH0 : αH = 0 := (cancel_mono B.arrow).mp (by simpa using h0H)
      exact hα (by simpa [αH] using congrArg InducedCategory.Hom.hom hαH0)
    exact hcomp_ne <| σ.slicing.hom_vanishing (F.φ ⟨0, hn⟩) φ _ _ hphase_gt
      (F.semistable ⟨0, hn⟩) hP (α ≫ B.arrow.hom)
  calc
    (σ.stabilityFunctionOnHeart C).phase B' ≤ σ.slicing.phiPlus C B'.obj hBobj :=
      σ.stabilityFunctionOnHeart_phase_le_phiPlus C B' hB
    _ ≤ φ := hphiPlus_le
    _ = (σ.stabilityFunctionOnHeart C).phase E :=
      (σ.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi C hφ E hP hE).symm

section AbelianHelpers

variable {A : Type*} [Category A] [Abelian A]

private theorem phase_cokernel_ofLE_congr_local (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂} :
    Z.phase (cokernel (Subobject.ofLE A₁ B₁ h₁)) =
      Z.phase (cokernel (Subobject.ofLE A₂ B₂ h₂)) := by
  subst hA
  subst hB
  rfl

private theorem isSemistable_cokernel_ofLE_congr_local (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂}
    (hs : Z.IsSemistable (cokernel (Subobject.ofLE A₂ B₂ h₂))) :
    Z.IsSemistable (cokernel (Subobject.ofLE A₁ B₁ h₁)) := by
  subst hA
  subst hB
  exact hs

private theorem Subobject.map_eq_mk_mono_local {X Y : A} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    (Subobject.map f).obj S = Subobject.mk (S.arrow ≫ f) := by
  calc
    (Subobject.map f).obj S = (Subobject.map f).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ f) := by
      simpa using (Subobject.map_mk S.arrow f)

private noncomputable def Subobject.mapMonoIso_local {X Y : A} (f : X ⟶ Y) [Mono f]
    (S : Subobject X) :
    ((Subobject.map f).obj S : A) ≅ (S : A) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ f) (Subobject.map_eq_mk_mono_local f S)

private theorem Subobject.ofLE_map_comp_mapMonoIso_hom_local {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
        ((Subobject.map f).monotone h) ≫ (Subobject.mapMonoIso_local f T).hom =
      (Subobject.mapMonoIso_local f S).hom ≫ Subobject.ofLE S T h := by
  apply Subobject.eq_of_comp_arrow_eq
  apply (cancel_mono f).1
  simp [Subobject.mapMonoIso_local, Subobject.map_eq_mk_mono_local, Category.assoc]

private noncomputable def Subobject.cokernelMapMonoIso_local {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h)) ≅
      cokernel (Subobject.ofLE S T h) :=
  cokernel.mapIso _ _ (Subobject.mapMonoIso_local f S) (Subobject.mapMonoIso_local f T)
    (by simpa [Category.assoc] using (Subobject.ofLE_map_comp_mapMonoIso_hom_local f h))

private theorem phase_cokernel_mapMono_eq_local (Z : StabilityFunction A) {X Y : A} (f : X ⟶ Y)
    [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.phase (cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h))) =
      Z.phase (cokernel (Subobject.ofLE S T h)) :=
  Z.phase_eq_of_iso (Subobject.cokernelMapMonoIso_local f h)

private theorem isSemistable_cokernel_mapMono_iff_local (Z : StabilityFunction A) {X Y : A}
    (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.IsSemistable (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
      ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) ↔
      Z.IsSemistable (cokernel (Subobject.ofLE S T h)) := by
  constructor <;> intro hs
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso_local f h) hs
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso_local f h).symm hs

private theorem StabilityFunction.exists_hn_with_last_phase_of_semistable_local
    (Z : StabilityFunction A) {E : A} (hss : Z.IsSemistable E) :
    ∃ F : AbelianHNFiltration Z E,
      F.φ ⟨F.n - 1, by have := F.hn; omega⟩ = Z.phase E := by
  refine ⟨{
    n := 1
    hn := Nat.one_pos
    chain := fun i ↦ if i = 0 then ⊥ else ⊤
    chain_strictMono := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ h
      simp only [Fin.lt_def] at h
      have hi0 : i = 0 := by omega
      have hj1 : j = 1 := by omega
      subst hi0; subst hj1
      simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ↓reduceIte,
        Fin.mk_one, one_ne_zero, gt_iff_lt]
      exact lt_of_le_of_ne bot_le
        (Ne.symm (StabilityFunction.subobject_top_ne_bot_of_not_isZero hss.1))
    chain_bot := by simp
    chain_top := by simp
    φ := fun _ ↦ Z.phase E
    φ_anti := fun a b h ↦ by exfalso; exact absurd h (by omega)
    factor_phase := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by omega
      subst hj0
      change Z.phase (cokernel (Subobject.ofLE (⊥ : Subobject E) (⊤ : Subobject E) bot_le)) =
        Z.phase E
      have h₁ :
          Z.phase (cokernel (Subobject.ofLE (⊥ : Subobject E) (⊤ : Subobject E) bot_le)) =
            Z.phase (⊤ : Subobject E) := by
        exact Z.phase_eq_of_iso (StabilityFunction.Subobject.cokernelBotIso ⊤ bot_le)
      exact h₁.trans (Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow))
    factor_semistable := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by omega
      subst hj0
      change Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ _))
      exact Z.isSemistable_of_iso
        ((asIso (⊤ : Subobject E).arrow).symm ≪≫
          (StabilityFunction.Subobject.cokernelBotIso ⊤ bot_le).symm) hss
  }, by simp⟩

set_option maxHeartbeats 2000000 in
private theorem StabilityFunction.append_hn_filtration_of_mono_local
    (Z : StabilityFunction A) {X Y B : A}
    (i : X ⟶ Y) [Mono i] (F : AbelianHNFiltration Z X) (eB : cokernel i ≅ B)
    (hB : Z.IsSemistable B)
    (hlast : Z.phase B < F.φ ⟨F.n - 1, by have := F.hn; omega⟩) :
    ∃ G : AbelianHNFiltration Z Y,
      G.φ ⟨G.n - 1, by have := G.hn; omega⟩ = Z.phase B := by
  let K : Subobject Y := Subobject.mk i
  let eK : cokernel K.arrow ≅ B := by
    let eKi : cokernel K.arrow ≅ cokernel i := by
      refine cokernel.mapIso (f := K.arrow) (f' := i) (Subobject.underlyingIso i) (Iso.refl _)
        ?_
      calc
        K.arrow ≫ (Iso.refl Y).hom = K.arrow := by simp
        _ = (Subobject.underlyingIso i).hom ≫ i := by
            simpa [K] using (Subobject.underlyingIso_hom_comp_eq_mk i).symm
    exact eKi ≪≫ eB
  have hK_ne_top : K ≠ ⊤ := by
    intro hK
    have hmk : Subobject.mk i = ⊤ := by simpa [K] using hK
    haveI : IsIso i := (Subobject.isIso_iff_mk_eq_top i).2 hmk
    exact hB.1 ((isZero_cokernel_of_epi i).of_iso eB.symm)
  have hK_lt_top : K < ⊤ := lt_of_le_of_ne le_top hK_ne_top
  let newChain : Fin (F.n + 2) → Subobject Y := fun j =>
    if h : (j : ℕ) ≤ F.n then
      (Subobject.map i).obj (F.chain ⟨j, by omega⟩)
    else ⊤
  have hNewBot : newChain ⟨0, by omega⟩ = ⊥ := by
    change (Subobject.map i).obj (F.chain ⟨0, by omega⟩) = ⊥
    rw [F.chain_bot]
    simpa using (Subobject.map_bot i)
  have hNewK : newChain ⟨F.n, by omega⟩ = K := by
    simp [newChain, K, Subobject.map_top, F.chain_top]
  have hNewTop : newChain ⟨F.n + 1, by omega⟩ = ⊤ := by
    simp [newChain]
  have hNewMono : StrictMono newChain := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    change newChain ⟨j, by omega⟩ < newChain ⟨j + 1, by omega⟩
    by_cases hjn : j = F.n
    · subst hjn
      rw [hNewK, hNewTop]
      exact hK_lt_top
    · have hjle : j + 1 ≤ F.n := by omega
      simp [newChain, show (j : ℕ) ≤ F.n by omega, hjle]
      apply (Subobject.map i).monotone.strictMono_of_injective (Subobject.map_obj_injective i)
      exact F.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
  let φ : Fin (F.n + 1) → ℝ := fun j =>
    if h : (j : ℕ) < F.n then F.φ ⟨j, h⟩ else Z.phase B
  refine ⟨{
    n := F.n + 1
    hn := Nat.succ_pos _
    chain := newChain
    chain_strictMono := hNewMono
    chain_bot := hNewBot
    chain_top := hNewTop
    φ := φ
    φ_anti := by
      intro a b hab
      dsimp [φ]
      by_cases hb : (b : ℕ) < F.n
      · have ha : (a : ℕ) < F.n := by
          exact lt_trans (Fin.mk_lt_mk.mp hab) hb
        simp [ha, hb]
        exact F.φ_anti (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hab))
      · have ha : (a : ℕ) < F.n := by omega
        have hlast_le :
            F.φ ⟨F.n - 1, by have := F.hn; omega⟩ ≤ F.φ ⟨a, ha⟩ := by
          exact F.φ_anti.antitone (Fin.mk_le_mk.mpr (by omega))
        simp [ha, hb]
        linarith
    factor_phase := by
      intro j
      by_cases hj : (j : ℕ) < F.n
      · let j' : Fin F.n := ⟨j, hj⟩
        have hcast :
            newChain j.castSucc = (Subobject.map i).obj (F.chain j'.castSucc) := by
          have hj_le : (j : ℕ) ≤ F.n := by omega
          simpa [newChain, j', hj_le]
        have hsucc :
            newChain j.succ = (Subobject.map i).obj (F.chain j'.succ) := by
          have hj1_le : (j : ℕ) + 1 ≤ F.n := by omega
          simpa [newChain, j', hj1_le]
        have hphase :
            Z.phase (cokernel (Subobject.ofLE ((Subobject.map i).obj (F.chain j'.castSucc))
              ((Subobject.map i).obj (F.chain j'.succ))
              ((Subobject.map i).monotone
                (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))))) =
              F.φ j' :=
          (phase_cokernel_mapMono_eq_local Z i
            (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).trans (F.factor_phase j')
        have hφj : φ j = F.φ j' := by
          simp [φ, hj, j']
        exact ((phase_cokernel_ofLE_congr_local Z hcast hsucc).trans hphase).trans hφj.symm
      · have hj_eq : (j : ℕ) = F.n := by omega
        have hcast : j.castSucc = ⟨F.n, by omega⟩ := Fin.ext hj_eq
        have hsucc : j.succ = ⟨F.n + 1, by omega⟩ := Fin.ext (by simp [hj_eq])
        have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
        have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
        have hφj : φ j = Z.phase B := by
          simp [φ, hj]
        have htarget :
            Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) =
              Z.phase (cokernel K.arrow) := by
          exact Z.phase_eq_of_iso
            ((cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _).symm)
        have htarget' : Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) = Z.phase B := by
          exact htarget.trans (Z.phase_eq_of_iso eK)
        exact ((phase_cokernel_ofLE_congr_local Z hcast_obj hsucc_obj).trans htarget').trans
          hφj.symm
    factor_semistable := by
      intro j
      by_cases hj : (j : ℕ) < F.n
      · let j' : Fin F.n := ⟨j, hj⟩
        have hcast :
            newChain j.castSucc = (Subobject.map i).obj (F.chain j'.castSucc) := by
          have hj_le : (j : ℕ) ≤ F.n := by omega
          simpa [newChain, j', hj_le]
        have hsucc :
            newChain j.succ = (Subobject.map i).obj (F.chain j'.succ) := by
          have hj1_le : (j : ℕ) + 1 ≤ F.n := by omega
          simpa [newChain, j', hj1_le]
        have hsemistable :
            Z.IsSemistable
              (cokernel (Subobject.ofLE ((Subobject.map i).obj (F.chain j'.castSucc))
                ((Subobject.map i).obj (F.chain j'.succ))
                ((Subobject.map i).monotone
                  (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))))) :=
          (isSemistable_cokernel_mapMono_iff_local Z i
            (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).2 (F.factor_semistable j')
        exact isSemistable_cokernel_ofLE_congr_local Z hcast hsucc hsemistable
      · have hj_eq : (j : ℕ) = F.n := by omega
        have hcast : j.castSucc = ⟨F.n, by omega⟩ := Fin.ext hj_eq
        have hsucc : j.succ = ⟨F.n + 1, by omega⟩ := Fin.ext (by simp [hj_eq])
        have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
        have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
        let eTop : B ≅ cokernel (Subobject.ofLE K ⊤ le_top) :=
          eK.symm ≪≫ (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _)
        exact isSemistable_cokernel_ofLE_congr_local Z hcast_obj hsucc_obj <|
          Z.isSemistable_of_iso eTop hB
  }, by simp [φ]⟩

end AbelianHelpers

/-- The stability function on the heart attached to a stability condition has the
Harder-Narasimhan property, proved by induction on a slicing HN filtration of a
heart object and peeling off the last semistable quotient as in Bridgeland's
Proposition 5.3. -/
private theorem StabilityCondition.stabilityFunctionOnHeart_hasHN_local
    (σ : StabilityCondition C) :
    @StabilityFunction.HasHNProperty (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian) (σ.stabilityFunctionOnHeart C) := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  intro E hE
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hE <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  suffices hmain :
      ∀ (m : ℕ) {X : t.heart.FullSubcategory} (hXobj : ¬IsZero X.obj)
        (F : HNFiltration C σ.slicing.P X.obj) (hnF : 0 < F.n) (hFm : F.n ≤ m)
        (hfirst : ¬IsZero (F.triangle ⟨0, hnF⟩).obj₃),
        ∃ G : AbelianHNFiltration (σ.stabilityFunctionOnHeart C) X,
          G.φ ⟨G.n - 1, by have := G.hn; omega⟩ = σ.slicing.phiMinus C X.obj hXobj by
    obtain ⟨F, hnF, hfirst, _⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEobj
    exact ⟨(hmain F.n hEobj F hnF le_rfl hfirst).choose⟩
  intro m
  induction m with
  | zero =>
      intro X hXobj F hnF hFm
      omega
  | succ m ih =>
      intro X hXobj F hnF hFm hfirst
      have hX : ¬IsZero X := fun hZ ↦ hXobj ((t.heart).ι.map_isZero hZ)
      have hXheart := (σ.slicing.toTStructure_heart_iff C X.obj).mp X.property
      by_cases h1 : F.n = 1
      · let φ := F.φ ⟨0, hnF⟩
        have hlast : ¬IsZero (F.triangle ⟨F.n - 1, by omega⟩).obj₃ := by
          have hidx : (⟨F.n - 1, by omega⟩ : Fin F.n) = ⟨0, hnF⟩ := Fin.ext (by omega)
          simpa [hidx] using hfirst
        have hall : ∀ i : Fin F.n, F.φ i = φ := by
          intro i
          have hidx : i = ⟨0, hnF⟩ := Fin.ext (by omega)
          subst hidx
          rfl
        have hP : (σ.slicing.P φ) X.obj := σ.slicing.semistable_of_HN_all_eq C F hall
        have hφm : σ.slicing.phiMinus C X.obj hXobj = φ := by
          rw [σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast]
          have hidx : (⟨F.n - 1, by omega⟩ : Fin F.n) = ⟨0, hnF⟩ := Fin.ext (by omega)
          simpa [φ, hidx]
        have hφp : σ.slicing.phiPlus C X.obj hXobj = φ := by
          simpa [φ] using (σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst)
        have hφ : φ ∈ Set.Ioc (0 : ℝ) 1 := by
          constructor
          · linarith [gt_phases_of_gtProp C σ.slicing hXobj hXheart.1, hφm]
          · linarith [σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2, hφp]
        have hss :
            @StabilityFunction.IsSemistable _ _ t.heartFullSubcategoryAbelian
              (σ.stabilityFunctionOnHeart C) X :=
          σ.stabilityFunctionOnHeart_isSemistable_of_mem_P_phi C hφ X hP hX
        obtain ⟨G, hG⟩ :=
          StabilityFunction.exists_hn_with_last_phase_of_semistable_local
            (σ.stabilityFunctionOnHeart C) hss
        refine ⟨G, ?_⟩
        calc
          G.φ ⟨G.n - 1, by have := G.hn; omega⟩ =
              @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                (σ.stabilityFunctionOnHeart C) X := hG
          _ = φ := σ.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi C hφ X hP hX
          _ = σ.slicing.phiMinus C X.obj hXobj := hφm.symm
      · have htwo : 2 ≤ F.n := by omega
        by_cases hlast : IsZero (F.triangle ⟨F.n - 1, by omega⟩).obj₃
        · let F' := F.dropLast C (by omega) hlast
          have hnF' : 0 < F'.n := F'.n_pos C hXobj
          have hF'm : F'.n ≤ m := by
            change F.n - 1 ≤ m
            omega
          have hfirst' : ¬IsZero (F'.triangle ⟨0, hnF'⟩).obj₃ := by
            simpa [F', HNFiltration.dropLast, HNFiltration.prefix] using hfirst
          exact ih hXobj F' hnF' hF'm hfirst'
        · have hall_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
            intro i
            constructor
            · calc
                0 < σ.slicing.phiMinus C X.obj hXobj :=
                  gt_phases_of_gtProp C σ.slicing hXobj hXheart.1
                _ = F.φ ⟨F.n - 1, by omega⟩ :=
                  σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast
                _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
            · calc
                F.φ i ≤ F.φ ⟨0, hnF⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
                _ = σ.slicing.phiPlus C X.obj hXobj := by
                  symm
                  exact σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst
                _ ≤ 1 := σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2
          let FX : HNFiltration C σ.slicing.P (F.chain.obj ⟨F.n - 1, by omega⟩) :=
            F.prefix C (F.n - 1) (by omega) (by omega)
          have hFXn : 0 < FX.n := by
            change 0 < F.n - 1
            omega
          have hFXheart : t.heart (F.chain.obj ⟨F.n - 1, by omega⟩) := by
            rw [σ.slicing.toTStructure_heart_iff C]
            constructor
            · exact HNFiltration.chain_obj_gtProp C σ.slicing F (F.n - 1) (by omega) (by omega) 0
                (fun j ↦ (hall_mem ⟨j, by omega⟩).1)
            · exact HNFiltration.chain_obj_leProp C σ.slicing F (F.n - 1) (by omega) (by omega) 1
                (fun j ↦ (hall_mem ⟨j, by omega⟩).2)
          let X' : t.heart.FullSubcategory := ⟨F.chain.obj ⟨F.n - 1, by omega⟩, hFXheart⟩
          have hfirstFX : ¬IsZero (FX.triangle ⟨0, hFXn⟩).obj₃ := by
            simpa [FX, HNFiltration.prefix] using hfirst
          have hX'obj : ¬IsZero X'.obj := by
            intro hZ
            have hzero :
                ∀ f : (FX.triangle ⟨0, hFXn⟩).obj₃ ⟶ F.chain.obj ⟨F.n - 1, by omega⟩, f = 0 :=
              fun f ↦ hZ.eq_of_tgt _ _
            exact hfirstFX <|
              HNFiltration.isZero_factor_zero_of_hom_eq_zero C σ.slicing FX hFXn hzero
          obtain ⟨GX, hGX⟩ := ih hX'obj FX hFXn (by
            change F.n - 1 ≤ m
            omega) hfirstFX
          let jLast : Fin F.n := ⟨F.n - 1, by omega⟩
          have hBheart : t.heart (F.triangle jLast).obj₃ := by
            rw [σ.slicing.toTStructure_heart_iff C]
            exact ⟨σ.slicing.gtProp_of_semistable C (F.φ jLast) 0 _ (F.semistable jLast)
                (hall_mem jLast).1,
              σ.slicing.leProp_of_semistable C (F.φ jLast) 1 _ (F.semistable jLast)
                (hall_mem jLast).2⟩
          let B : t.heart.FullSubcategory := ⟨(F.triangle jLast).obj₃, hBheart⟩
          have hB : ¬IsZero B := fun hZ ↦ hlast ((t.heart).ι.map_isZero hZ)
          have hBss :
              @StabilityFunction.IsSemistable _ _ t.heartFullSubcategoryAbelian
                (σ.stabilityFunctionOnHeart C) B :=
            σ.stabilityFunctionOnHeart_isSemistable_of_mem_P_phi C (hall_mem jLast)
              B (F.semistable jLast) hB
          have hBphase :
              @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                (σ.stabilityFunctionOnHeart C) B = F.φ jLast :=
            σ.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi C (hall_mem jLast)
              B (F.semistable jLast) hB
          have hX'gt :
              σ.slicing.gtProp C (F.φ jLast) X'.obj :=
            HNFiltration.chain_obj_gtProp C σ.slicing F (F.n - 1) (by omega) (by omega)
              (F.φ jLast) <|
              fun j ↦ by
                have hjlt : (⟨j.val, by omega⟩ : Fin F.n) < jLast := by
                  exact Fin.mk_lt_mk.mpr (by simpa [jLast] using j.is_lt)
                exact F.hφ hjlt
          have hphase_lt :
              @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                (σ.stabilityFunctionOnHeart C) B <
                  GX.φ ⟨GX.n - 1, by have := GX.hn; omega⟩ := by
            calc
              @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                  (σ.stabilityFunctionOnHeart C) B = F.φ jLast := hBphase
              _ < σ.slicing.phiMinus C X'.obj hX'obj :=
                gt_phases_of_gtProp C σ.slicing hX'obj hX'gt
              _ = GX.φ ⟨GX.n - 1, by have := GX.hn; omega⟩ := hGX.symm
          let Tlast := F.triangle jLast
          let e₁ := Classical.choice (F.triangle_obj₁ jLast)
          let e₂ := Classical.choice (F.triangle_obj₂ jLast)
          have hobj₂_eq : F.chain.obj' (F.n - 1 + 1) (by omega) = F.chain.right := by
            simp only [ComposableArrows.obj']
            congr 1
            ext
            simp
            omega
          let e₂X : Tlast.obj₂ ≅ X.obj :=
            e₂.trans ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
          let i : X' ⟶ X := ObjectProperty.homMk (e₁.inv ≫ Tlast.mor₁ ≫ e₂X.hom)
          let q : X ⟶ B := ObjectProperty.homMk (e₂X.inv ≫ Tlast.mor₂)
          let δ : B.obj ⟶ X'.obj⟦(1 : ℤ)⟧ := Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hTlast : Triangle.mk i.hom q.hom δ ∈ distTriang C := by
            refine isomorphic_distinguished _ (F.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm e₂X.symm (Iso.refl _)
              (by simp [Tlast, i, e₂X]) (by simp [Tlast, q, e₂X]) (by simp [Tlast, δ])
          have hiq_hom : i.hom ≫ q.hom = 0 := by
            have := comp_distTriang_mor_zero₁₂ _ hTlast
            simpa using this
          have hiq : i ≫ q = 0 := by
            ext
            exact hiq_hom
          have hKer : IsLimit (KernelFork.ofι i hiq) := by
            simpa [hiq] using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
              (TStructure.heart_hι t) i q δ hTlast
          have hCok : IsColimit (CokernelCofork.ofπ q hiq) := by
            simpa [hiq] using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
              (TStructure.heart_hι t) i q δ hTlast
          let eB : cokernel i ≅ B :=
            IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel i) hCok
          haveI : Mono i := Fork.IsLimit.mono hKer
          obtain ⟨G, hG⟩ := StabilityFunction.append_hn_filtration_of_mono_local
            (σ.stabilityFunctionOnHeart C) i GX eB hBss hphase_lt
          refine ⟨G, ?_⟩
          calc
            G.φ ⟨G.n - 1, by have := G.hn; omega⟩ =
                @StabilityFunction.phase _ _ t.heartFullSubcategoryAbelian
                  (σ.stabilityFunctionOnHeart C) B := hG
            _ = F.φ jLast := hBphase
            _ = σ.slicing.phiMinus C X.obj hXobj := by
              symm
              exact σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast

/-- **Proposition 5.3a / forward direction.**
Every stability condition `σ` determines heart stability data:
1. The t-structure is `σ.slicing.toTStructure`.
2. Boundedness follows from the HN filtration axiom.
3. The stability function on the heart `P((0, 1])` is the restriction of `Z`.
4. The HN property on the heart is obtained by taking the slicing HN filtration of
   a heart object and reading it as an abelian HN filtration, exactly as in
   Bridgeland's proof of Proposition 5.3.

The key identification is that semistable objects of phase `φ ∈ (0, 1]` in the
heart are exactly the objects of `P(φ)`, and the slicing's HN filtration of a
heart object is exactly an HN filtration in the sense of
`StabilityFunction`. -/
def StabilityCondition.toHeartStabilityData
    (σ : StabilityCondition C) : HeartStabilityData C where
  t := σ.slicing.toTStructure
  bounded := σ.slicing.toTStructure_bounded C
  Z := σ.stabilityFunctionOnHeart C
  hasHN := σ.stabilityFunctionOnHeart_hasHN_local C

private noncomputable def phaseBase
    (h : HeartStabilityData C) (φ : ℝ) : ℝ :=
  toIocMod zero_lt_one (0 : ℝ) φ

private noncomputable def phaseIndex
    (h : HeartStabilityData C) (φ : ℝ) : ℤ :=
  toIocDiv zero_lt_one (0 : ℝ) φ

private theorem phaseBase_mem
    (h : HeartStabilityData C) (φ : ℝ) :
    phaseBase (C := C) h φ ∈ Set.Ioc (0 : ℝ) 1 := by
  simpa [phaseBase] using
    (toIocMod_mem_Ioc zero_lt_one (0 : ℝ) φ)

private theorem phaseBase_add_phaseIndex
    (h : HeartStabilityData C) (φ : ℝ) :
    phaseBase (C := C) h φ + phaseIndex (C := C) h φ = φ := by
  simpa [phaseBase, phaseIndex] using
    (toIocMod_add_toIocDiv_mul zero_lt_one (0 : ℝ) φ)

private theorem phaseBase_add_one
    (h : HeartStabilityData C) (φ : ℝ) :
    phaseBase (C := C) h (φ + (1 : ℝ)) = phaseBase (C := C) h φ := by
  simpa [phaseBase] using
    (toIocMod_add_intCast_mul zero_lt_one (0 : ℝ) φ 1)

private theorem phaseIndex_add_one
    (h : HeartStabilityData C) (φ : ℝ) :
    phaseIndex (C := C) h (φ + (1 : ℝ)) = phaseIndex (C := C) h φ + (1 : ℤ) := by
  simpa [phaseIndex] using
    (toIocDiv_add_intCast_mul zero_lt_one (0 : ℝ) φ 1)

private theorem phaseBase_eq_of_mem_Ioc
    (h : HeartStabilityData C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1) :
    phaseBase (C := C) h φ = φ := by
  exact (toIocMod_eq_self zero_lt_one).2 (by simpa using hφ)

private theorem phaseIndex_eq_zero_of_mem_Ioc
    (h : HeartStabilityData C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1) :
    phaseIndex (C := C) h φ = 0 := by
  exact (toIocDiv_eq_of_sub_zsmul_mem_Ioc (hp := zero_lt_one) (a := (0 : ℝ))
    (b := φ) (n := (0 : ℤ))) (by simpa using hφ)

private abbrev HeartSemistable
    (h : HeartStabilityData C) (E : h.t.heart.FullSubcategory) : Prop :=
  @StabilityFunction.IsSemistable _ _ h.t.heartFullSubcategoryAbelian h.Z E

private abbrev HeartPhase
    (h : HeartStabilityData C) (E : h.t.heart.FullSubcategory) : ℝ :=
  @StabilityFunction.phase _ _ h.t.heartFullSubcategoryAbelian h.Z E

/-- Bridgeland's reverse-direction phase slices, before packaging them into a full
slicing: objects whose `[-n]`-shift lies in the heart and is semistable there of
phase `ψ`, together with the zero object. -/
private def shiftedHeartSemistable
    (h : HeartStabilityData C) (ψ : ℝ) (n : ℤ) : ObjectProperty C := by
  exact fun X ↦
    IsZero X ∨
      ∃ hX : h.t.heart (X⟦(-n : ℤ)⟧),
        let XH : h.t.heart.FullSubcategory := ⟨X⟦(-n : ℤ)⟧, hX⟩
        HeartSemistable (C := C) h XH ∧ HeartPhase (C := C) h XH = ψ

/-- The ambient phase predicate attached to heart stability data: normalize the phase
into `(0,1]`, then shift the object back by the corresponding integer. -/
private def phasePredicate
    (h : HeartStabilityData C) (φ : ℝ) : ObjectProperty C :=
  shiftedHeartSemistable (C := C) h (phaseBase (C := C) h φ) (phaseIndex (C := C) h φ)

private theorem shiftedHeartSemistable_zero_iff
    (h : HeartStabilityData C) (ψ : ℝ) (X : C) :
    shiftedHeartSemistable (C := C) h ψ 0 X ↔
      IsZero X ∨
        ∃ hX : h.t.heart X,
          let XH : h.t.heart.FullSubcategory := ⟨X, hX⟩
          HeartSemistable (C := C) h XH ∧ HeartPhase (C := C) h XH = ψ := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  let e0 : X⟦(0 : ℤ)⟧ ≅ X := (shiftFunctorZero C ℤ).app X
  constructor
  · intro hX
    rcases hX with hX | ⟨hX0, hXss, hXphase⟩
    · exact Or.inl hX
    · have hX : h.t.heart X := (h.t.heart).prop_of_iso e0 hX0
      let X0H : h.t.heart.FullSubcategory := ⟨X⟦(0 : ℤ)⟧, hX0⟩
      let XH : h.t.heart.FullSubcategory := ⟨X, hX⟩
      let eH : X0H ≅ XH := ObjectProperty.isoMk _ e0
      exact Or.inr ⟨hX, h.Z.isSemistable_of_iso eH hXss, by
        rw [← hXphase]
        exact (h.Z.phase_eq_of_iso eH).symm⟩
  · intro hX
    rcases hX with hX | ⟨hX0, hXss, hXphase⟩
    · exact Or.inl hX
    · have hX : h.t.heart (X⟦(0 : ℤ)⟧) := (h.t.heart).prop_of_iso e0.symm hX0
      let XH : h.t.heart.FullSubcategory := ⟨X, hX0⟩
      let X0H : h.t.heart.FullSubcategory := ⟨X⟦(0 : ℤ)⟧, hX⟩
      let eH : XH ≅ X0H := ObjectProperty.isoMk _ e0.symm
      exact Or.inr ⟨hX, h.Z.isSemistable_of_iso eH hXss, by
        rw [← hXphase]
        exact (h.Z.phase_eq_of_iso eH).symm⟩

private theorem phasePredicate_iff_of_mem_Ioc
    (h : HeartStabilityData C) {φ : ℝ} (hφ : φ ∈ Set.Ioc (0 : ℝ) 1) (X : C) :
    phasePredicate (C := C) h φ X ↔
      IsZero X ∨
        ∃ hX : h.t.heart X,
          let XH : h.t.heart.FullSubcategory := ⟨X, hX⟩
          HeartSemistable (C := C) h XH ∧ HeartPhase (C := C) h XH = φ := by
  simpa [phasePredicate, phaseBase_eq_of_mem_Ioc (C := C) h hφ,
    phaseIndex_eq_zero_of_mem_Ioc (C := C) h hφ] using
    (shiftedHeartSemistable_zero_iff (C := C) h φ X)

private theorem arg_add_lt_max_local {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ upperHalfPlaneUnion) (h₂ : z₂ ∈ upperHalfPlaneUnion)
    (hne : Complex.arg z₁ ≠ Complex.arg z₂) :
    Complex.arg (z₁ + z₂) < max (Complex.arg z₁) (Complex.arg z₂) := by
  have cross_eq_norm_mul_sin_local (w₁ w₂ : ℂ) :
      w₁.re * w₂.im - w₁.im * w₂.re =
        ‖w₁‖ * ‖w₂‖ * Real.sin (Complex.arg w₂ - Complex.arg w₁) := by
    rw [← Complex.norm_mul_cos_arg w₁, ← Complex.norm_mul_sin_arg w₁,
      ← Complex.norm_mul_cos_arg w₂, ← Complex.norm_mul_sin_arg w₂, Real.sin_sub]
    ring
  have cross_pos_of_arg_lt_local {w₁ w₂ : ℂ}
      (hwarg₁ : 0 < Complex.arg w₁) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
      (hw : Complex.arg w₁ < Complex.arg w₂) :
      0 < w₁.re * w₂.im - w₁.im * w₂.re := by
    have hnn : 0 < ‖w₁‖ * ‖w₂‖ := mul_pos (norm_pos_iff.mpr hw₁) (norm_pos_iff.mpr hw₂)
    rw [cross_eq_norm_mul_sin_local]
    exact mul_pos hnn (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hw)
      (by linarith [Complex.arg_le_pi w₂]))
  have arg_lt_of_cross_pos_local {w₁ w₂ : ℂ}
      (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hwarg₂ : 0 < Complex.arg w₂)
      (hcross : 0 < w₁.re * w₂.im - w₁.im * w₂.re) :
      Complex.arg w₁ < Complex.arg w₂ := by
    have hnn : 0 < ‖w₁‖ * ‖w₂‖ := mul_pos (norm_pos_iff.mpr hw₁) (norm_pos_iff.mpr hw₂)
    rw [cross_eq_norm_mul_sin_local] at hcross
    have hsin : 0 < Real.sin (Complex.arg w₂ - Complex.arg w₁) := by
      rcases (mul_pos_iff.mp hcross).elim id
        (fun ⟨h1, h2⟩ ↦ absurd h1 (not_lt.mpr hnn.le)) with ⟨_, h⟩
      exact h
    by_contra h
    push_neg at h
    rcases h.eq_or_lt with heq | hlt
    · rw [heq, sub_self, Real.sin_zero] at hsin
      exact lt_irrefl _ hsin
    · have : Real.sin (Complex.arg w₂ - Complex.arg w₁) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt (sub_neg.mpr hlt)
          (by linarith [Complex.arg_le_pi w₁])
      linarith
  have hz₁ := upperHalfPlaneUnion_ne_zero h₁
  have hz₂ := upperHalfPlaneUnion_ne_zero h₂
  have hs_mem := mem_upperHalfPlaneUnion_of_add h₁ h₂
  have hs_ne := upperHalfPlaneUnion_ne_zero hs_mem
  have him₁ := im_nonneg_of_mem_upperHalfPlaneUnion h₁
  have him₂ := im_nonneg_of_mem_upperHalfPlaneUnion h₂
  have harg₁ := arg_pos_of_mem_upperHalfPlaneUnion h₁
  have harg₂ := arg_pos_of_mem_upperHalfPlaneUnion h₂
  set cp := z₁.re * z₂.im - z₁.im * z₂.re
  rcases hne.lt_or_gt with h | h
  · rw [max_eq_right h.le]
    apply arg_lt_of_cross_pos_local hs_ne hz₂ harg₂
    show 0 < (z₁ + z₂).re * z₂.im - (z₁ + z₂).im * z₂.re
    have : (z₁ + z₂).re * z₂.im - (z₁ + z₂).im * z₂.re = cp := by
      simp only [Complex.add_re, Complex.add_im, cp]
      ring
    rw [this]
    exact cross_pos_of_arg_lt_local harg₁ hz₁ hz₂ h
  · rw [max_eq_left h.le]
    apply arg_lt_of_cross_pos_local hs_ne hz₁ harg₁
    show 0 < (z₁ + z₂).re * z₁.im - (z₁ + z₂).im * z₁.re
    have : (z₁ + z₂).re * z₁.im - (z₁ + z₂).im * z₁.re = -cp := by
      simp only [Complex.add_re, Complex.add_im, cp]
      ring
    rw [this]
    have : 0 < z₂.re * z₁.im - z₂.im * z₁.re :=
      cross_pos_of_arg_lt_local harg₂ hz₂ hz₁ h
    linarith

private theorem heart_phase_le_of_epi
    (h : HeartStabilityData C)
    {E Q : h.t.heart.FullSubcategory} (p : E ⟶ Q) [Epi p]
    (hss : HeartSemistable (C := C) h E) (hQ : ¬IsZero Q) :
    HeartPhase (C := C) h E ≤ HeartPhase (C := C) h Q := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  letI : IsNormalMonoCategory h.t.heart.FullSubcategory := Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory h.t.heart.FullSubcategory := Abelian.toIsNormalEpiCategory
  letI : Balanced h.t.heart.FullSubcategory := by infer_instance
  by_cases hker : IsZero (kernel p)
  · haveI : Mono p := Preadditive.mono_of_kernel_zero
        (zero_of_source_iso_zero _ hker.isoZero)
    haveI : IsIso p := isIso_of_mono_of_epi p
    exact le_of_eq (h.Z.phase_eq_of_iso (asIso p))
  · have hK_sub : h.Z.phase (kernel p) ≤ h.Z.phase E := by
      calc h.Z.phase (kernel p)
          = h.Z.phase (kernelSubobject p : h.t.heart.FullSubcategory) :=
            h.Z.phase_eq_of_iso (kernelSubobjectIso p).symm
        _ ≤ h.Z.phase E := by
            apply hss.2
            intro hZ
            exact hker (hZ.of_iso (kernelSubobjectIso p).symm)
    by_contra hlt
    push_neg at hlt
    have hadd : h.Z.Zobj E = h.Z.Zobj (kernel p) + h.Z.Zobj Q :=
      h.Z.additive _
        (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance)
    have hK_mem := h.Z.upper (kernel p) hker
    have hQ_mem := h.Z.upper Q hQ
    have pi_pos := Real.pi_pos
    have hargK : Complex.arg (h.Z.Zobj (kernel p)) ≤ Complex.arg (h.Z.Zobj E) := by
      unfold StabilityFunction.phase at hK_sub
      exact le_of_mul_le_mul_left (by linarith) (div_pos one_pos pi_pos)
    have hargQ : Complex.arg (h.Z.Zobj Q) < Complex.arg (h.Z.Zobj E) := by
      unfold HeartPhase at hlt
      unfold StabilityFunction.phase at hlt
      exact lt_of_mul_lt_mul_left (by linarith) (div_pos one_pos pi_pos).le
    rw [hadd] at hargK hargQ
    have hub := arg_add_le_max hK_mem hQ_mem
    have hQ_lt_max :
        Complex.arg (h.Z.Zobj Q) <
          max (Complex.arg (h.Z.Zobj (kernel p))) (Complex.arg (h.Z.Zobj Q)) :=
      lt_of_lt_of_le hargQ hub
    have hK_gt_Q :
        Complex.arg (h.Z.Zobj Q) < Complex.arg (h.Z.Zobj (kernel p)) := by
      rcases lt_max_iff.mp hQ_lt_max with h | h
      · exact h
      · exact absurd h (lt_irrefl _)
    have hne : Complex.arg (h.Z.Zobj (kernel p)) ≠ Complex.arg (h.Z.Zobj Q) :=
      ne_of_gt hK_gt_Q
    have hstrict := arg_add_lt_max_local hK_mem hQ_mem hne
    rw [max_eq_left hK_gt_Q.le] at hstrict
    linarith

private theorem heart_hom_zero_of_semistable_phase_gt
    (h : HeartStabilityData C)
    {E F : h.t.heart.FullSubcategory}
    (hE : HeartSemistable (C := C) h E) (hF : HeartSemistable (C := C) h F)
    (hph : HeartPhase (C := C) h F < HeartPhase (C := C) h E) (f : E ⟶ F) : f = 0 := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  by_contra hf
  have hI : ¬IsZero (Limits.image f) := by
    intro hZ
    apply hf
    have : Limits.image.ι f = 0 := zero_of_source_iso_zero _ hZ.isoZero
    have hzero : factorThruImage f ≫ Limits.image.ι f = 0 := by
      rw [this, comp_zero]
    exact (Limits.image.fac f).symm.trans hzero
  have hge := heart_phase_le_of_epi (C := C) h (factorThruImage f) hE hI
  have hle : h.Z.phase (Limits.image f) ≤ h.Z.phase F := by
    calc h.Z.phase (Limits.image f)
        = h.Z.phase (imageSubobject f : h.t.heart.FullSubcategory) :=
          h.Z.phase_eq_of_iso (imageSubobjectIso f).symm
      _ ≤ h.Z.phase F := by
          apply hF.2
          intro hZ
          exact hI (hZ.of_iso (imageSubobjectIso f).symm)
  linarith

private theorem phasePredicate_hom_zero_of_mem_Ioc
    (h : HeartStabilityData C)
    {φ₁ φ₂ : ℝ}
    (hφ₁ : φ₁ ∈ Set.Ioc (0 : ℝ) 1)
    (hφ₂ : φ₂ ∈ Set.Ioc (0 : ℝ) 1)
    {E F : C}
    (hE : phasePredicate (C := C) h φ₁ E)
    (hF : phasePredicate (C := C) h φ₂ F)
    (hgap : φ₂ < φ₁)
    (f : E ⟶ F) : f = 0 := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  rcases (phasePredicate_iff_of_mem_Ioc (C := C) h hφ₁ E).1 hE with hEZ | ⟨hEheart, hEss, hEphase⟩
  · exact hEZ.eq_of_src f 0
  rcases (phasePredicate_iff_of_mem_Ioc (C := C) h hφ₂ F).1 hF with hFZ | ⟨hFheart, hFss, hFphase⟩
  · exact hFZ.eq_of_tgt f 0
  let EH : h.t.heart.FullSubcategory := ⟨E, hEheart⟩
  let FH : h.t.heart.FullSubcategory := ⟨F, hFheart⟩
  have hphase : h.Z.phase FH < h.Z.phase EH := by
    calc
      h.Z.phase FH = φ₂ := hFphase
      _ < φ₁ := hgap
      _ = h.Z.phase EH := hEphase.symm
  have hzero : (ObjectProperty.homMk f : EH ⟶ FH) = 0 :=
    heart_hom_zero_of_semistable_phase_gt (C := C) h hEss hFss hphase (ObjectProperty.homMk f)
  exact congrArg InducedCategory.Hom.hom hzero

private theorem shiftedHeartSemistable_closedUnderIso
    (h : HeartStabilityData C) (ψ : ℝ) (n : ℤ) :
    (shiftedHeartSemistable (C := C) h ψ n).IsClosedUnderIsomorphisms := by
  refine ⟨?_⟩
  intro X Y e hX
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  rcases hX with hX | ⟨hXheart, hXss, hXphase⟩
  · exact Or.inl (hX.of_iso e.symm)
  · let eShift : X⟦(-n : ℤ)⟧ ≅ Y⟦(-n : ℤ)⟧ := ((shiftFunctor C (-n : ℤ)).mapIso e)
    have hYheart : h.t.heart (Y⟦(-n : ℤ)⟧) :=
      (h.t.heart).prop_of_iso eShift hXheart
    let XH : h.t.heart.FullSubcategory := ⟨X⟦(-n : ℤ)⟧, hXheart⟩
    let YH : h.t.heart.FullSubcategory := ⟨Y⟦(-n : ℤ)⟧, hYheart⟩
    let eH : XH ≅ YH := ObjectProperty.isoMk _ eShift
    exact Or.inr ⟨hYheart, h.Z.isSemistable_of_iso eH hXss, by
      rw [← hXphase]
      change h.Z.phase YH = h.Z.phase XH
      simpa using (h.Z.phase_eq_of_iso eH).symm⟩

private theorem phasePredicate_closedUnderIso
    (h : HeartStabilityData C) (φ : ℝ) :
    (phasePredicate (C := C) h φ).IsClosedUnderIsomorphisms :=
  shiftedHeartSemistable_closedUnderIso (C := C) h
    (phaseBase (C := C) h φ) (phaseIndex (C := C) h φ)

private instance phasePredicate_instClosedUnderIso
    (h : HeartStabilityData C) (φ : ℝ) :
    (phasePredicate (C := C) h φ).IsClosedUnderIsomorphisms :=
  phasePredicate_closedUnderIso (C := C) h φ

private theorem shiftedHeartSemistable_shift_iff
    (h : HeartStabilityData C) (ψ : ℝ) (n : ℤ) (X : C) :
    shiftedHeartSemistable (C := C) h ψ n X ↔
      shiftedHeartSemistable (C := C) h ψ (n + 1) (X⟦(1 : ℤ)⟧) := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  let eShift :
      (X⟦(1 : ℤ)⟧)⟦(-(n + 1) : ℤ)⟧ ≅ X⟦(-n : ℤ)⟧ :=
    ((shiftFunctorAdd' C (1 : ℤ) (-(n + 1) : ℤ) (-n : ℤ) (by omega)).app X).symm
  constructor
  · intro hX
    rcases hX with hX | ⟨hXheart, hXss, hXphase⟩
    · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hX)
    · have hYheart : h.t.heart ((X⟦(1 : ℤ)⟧)⟦(-(n + 1) : ℤ)⟧) :=
        (h.t.heart).prop_of_iso eShift.symm hXheart
      let XH : h.t.heart.FullSubcategory := ⟨X⟦(-n : ℤ)⟧, hXheart⟩
      let YH : h.t.heart.FullSubcategory :=
        ⟨(X⟦(1 : ℤ)⟧)⟦(-(n + 1) : ℤ)⟧, hYheart⟩
      let eH : XH ≅ YH := ObjectProperty.isoMk _ eShift.symm
      exact Or.inr ⟨hYheart, h.Z.isSemistable_of_iso eH hXss, by
        rw [← hXphase]
        change h.Z.phase YH = h.Z.phase XH
        simpa using (h.Z.phase_eq_of_iso eH).symm⟩
  · intro hX
    rcases hX with hX | ⟨hXheart, hXss, hXphase⟩
    · exact Or.inl <|
        (((shiftFunctor C (-1 : ℤ)).map_isZero hX).of_iso
          (shiftShiftNeg (X := X) (i := (1 : ℤ))).symm)
    · have hYheart : h.t.heart (X⟦(-n : ℤ)⟧) :=
        (h.t.heart).prop_of_iso eShift hXheart
      let XH : h.t.heart.FullSubcategory :=
        ⟨(X⟦(1 : ℤ)⟧)⟦(-(n + 1) : ℤ)⟧, hXheart⟩
      let YH : h.t.heart.FullSubcategory := ⟨X⟦(-n : ℤ)⟧, hYheart⟩
      let eH : XH ≅ YH := ObjectProperty.isoMk _ eShift
      exact Or.inr ⟨hYheart, h.Z.isSemistable_of_iso eH hXss, by
        rw [← hXphase]
        change h.Z.phase YH = h.Z.phase XH
        simpa using (h.Z.phase_eq_of_iso eH).symm⟩

private theorem phasePredicate_shift_iff
    (h : HeartStabilityData C) (φ : ℝ) (X : C) :
    phasePredicate (C := C) h φ X ↔
      phasePredicate (C := C) h (φ + (1 : ℝ)) (X⟦(1 : ℤ)⟧) := by
  simpa [phasePredicate, phaseBase_add_one (C := C) h φ, phaseIndex_add_one (C := C) h φ] using
    (shiftedHeartSemistable_shift_iff (C := C) h
      (phaseBase (C := C) h φ) (phaseIndex (C := C) h φ) X)

private theorem phasePredicate_shift_int
    (h : HeartStabilityData C) (φ : ℝ) (X : C) (n : ℤ) :
    phasePredicate (C := C) h φ X ↔
      phasePredicate (C := C) h (φ + (n : ℝ)) (X⟦n⟧) := by
  induction n using Int.induction_on generalizing φ X with
  | zero =>
      constructor
      · intro hX
        have hX' : phasePredicate (C := C) h φ (X⟦(0 : ℤ)⟧) :=
          (phasePredicate (C := C) h φ).prop_of_iso ((shiftFunctorZero C ℤ).app X).symm hX
        simpa using hX'
      · intro hX
        have hX' : phasePredicate (C := C) h φ (X⟦(0 : ℤ)⟧) := by
          simpa using hX
        exact (phasePredicate (C := C) h φ).prop_of_iso ((shiftFunctorZero C ℤ).app X) hX'
  | succ n ih =>
      constructor
      · intro hX
        let Y : C := X⟦(n : ℤ)⟧
        have h0 : phasePredicate (C := C) h (φ + (n : ℝ)) Y := by
          simpa [Y] using ((ih φ X).mp hX)
        have h1 : phasePredicate (C := C) h (φ + (n : ℝ) + 1) (Y⟦(1 : ℤ)⟧) :=
          (phasePredicate_shift_iff (C := C) h (φ + (n : ℝ)) Y).mp h0
        simpa [Y, Nat.cast_succ, add_assoc] using
          (phasePredicate (C := C) h (φ + (n : ℝ) + 1)).prop_of_iso
            ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) (by omega)).app X).symm h1
      · intro hX
        let Y : C := X⟦(n : ℤ)⟧
        have h1 : phasePredicate (C := C) h (φ + (n : ℝ) + 1) (Y⟦(1 : ℤ)⟧) := by
          simpa [Y, Nat.cast_succ, add_assoc] using
            (phasePredicate (C := C) h (φ + ((n + 1 : ℕ) : ℝ))).prop_of_iso
              ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) (by omega)).app X) hX
        have h0 : phasePredicate (C := C) h (φ + (n : ℝ)) Y :=
          (phasePredicate_shift_iff (C := C) h (φ + (n : ℝ)) Y).mpr h1
        exact (ih φ X).mpr (by simpa [Y] using h0)
  | pred n ih =>
      constructor
      · intro hX
        let Y : C := X⟦(-(n : ℤ))⟧
        have h0 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ)) Y := by
          simpa [Y] using ((ih φ X).mp hX)
        have h0' :
            phasePredicate (C := C) h ((φ + (-(n : ℤ) : ℝ) - 1) + 1)
              ((Y⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) := by
          simpa [Y, sub_eq_add_neg, add_assoc] using
            (phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ))).prop_of_iso
              (shiftNegShift (X := Y) (i := (1 : ℤ))).symm h0
        have h1 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧) :=
          (phasePredicate_shift_iff (C := C) h (φ + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧)).mpr h0'
        have h2 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ) - 1)
            ((shiftFunctor C (Int.negSucc n)).obj X) :=
          (phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ) - 1)).prop_of_iso
            ((shiftFunctorAdd' C (-(n : ℤ)) (-1 : ℤ) (Int.negSucc n) (by omega)).app X).symm h1
        simpa [Y, Int.negSucc_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2
      · intro hX
        let Y : C := X⟦(-(n : ℤ))⟧
        have hX' : phasePredicate (C := C) h (φ + (Int.negSucc n : ℝ))
            ((shiftFunctor C (Int.negSucc n)).obj X) := by
          simpa [Int.negSucc_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hX
        have h1 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧) := by
          have h2 : phasePredicate (C := C) h (φ + (Int.negSucc n : ℝ))
              ((shiftFunctor C (-1 : ℤ)).obj Y) :=
            (phasePredicate (C := C) h (φ + (Int.negSucc n : ℝ))).prop_of_iso
              ((shiftFunctorAdd' C (-(n : ℤ)) (-1 : ℤ) (Int.negSucc n) (by omega)).app X) hX'
          simpa [Y, Int.negSucc_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2
        have h0' :
            phasePredicate (C := C) h ((φ + (-(n : ℤ) : ℝ) - 1) + 1)
              ((Y⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) :=
          (phasePredicate_shift_iff (C := C) h (φ + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧)).mp h1
        have h0 : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ)) Y := by
          have h0'' : phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ))
              ((shiftFunctor C (1 : ℤ)).obj ((shiftFunctor C (-1 : ℤ)).obj Y)) :=
            by
              simpa [sub_eq_add_neg, add_assoc] using h0'
          exact (phasePredicate (C := C) h (φ + (-(n : ℤ) : ℝ))).prop_of_iso
            (shiftNegShift (X := Y) (i := (1 : ℤ))) h0''
        exact (ih φ X).mpr (by simpa [Y] using h0)

private theorem phaseIndex_lt_phase
    (h : HeartStabilityData C) (φ : ℝ) :
    (phaseIndex (C := C) h φ : ℝ) < φ := by
  have hmem := phaseBase_mem (C := C) h φ
  have hpos : 0 < phaseBase (C := C) h φ := hmem.1
  nlinarith [phaseBase_add_phaseIndex (C := C) h φ]

private theorem phase_le_phaseIndex_add_one
    (h : HeartStabilityData C) (φ : ℝ) :
    φ ≤ (phaseIndex (C := C) h φ : ℝ) + 1 := by
  have hmem := phaseBase_mem (C := C) h φ
  have hle : phaseBase (C := C) h φ ≤ 1 := hmem.2
  nlinarith [phaseBase_add_phaseIndex (C := C) h φ]

private theorem phaseIndex_le_of_lt
    (h : HeartStabilityData C) {φ₁ φ₂ : ℝ} (hlt : φ₂ < φ₁) :
    phaseIndex (C := C) h φ₂ ≤ phaseIndex (C := C) h φ₁ := by
  by_contra hle
  have hgt : phaseIndex (C := C) h φ₁ < phaseIndex (C := C) h φ₂ := lt_of_not_ge hle
  have hstep : (phaseIndex (C := C) h φ₁ : ℝ) + 1 ≤ phaseIndex (C := C) h φ₂ := by
    exact_mod_cast (Int.add_one_le_iff.mpr hgt)
  linarith [phaseIndex_lt_phase (C := C) h φ₂, phase_le_phaseIndex_add_one (C := C) h φ₁]

private theorem phasePredicate_hom_zero
    (h : HeartStabilityData C)
    {φ₁ φ₂ : ℝ} {E F : C}
    (hE : phasePredicate (C := C) h φ₁ E)
    (hF : phasePredicate (C := C) h φ₂ F)
    (hgap : φ₂ < φ₁)
    (f : E ⟶ F) : f = 0 := by
  let n₁ := phaseIndex (C := C) h φ₁
  let n₂ := phaseIndex (C := C) h φ₂
  let ψ₁ := phaseBase (C := C) h φ₁
  let ψ₂ := phaseBase (C := C) h φ₂
  rcases hE with hEZ | ⟨hEheart, hEss, hEphase⟩
  · exact hEZ.eq_of_src f 0
  rcases hF with hFZ | ⟨hFheart, hFss, hFphase⟩
  · exact hFZ.eq_of_tgt f 0
  have hle : n₂ ≤ n₁ := phaseIndex_le_of_lt (C := C) h hgap
  by_cases hidx : n₂ = n₁
  · let EH : h.t.heart.FullSubcategory := ⟨E⟦(-n₁ : ℤ)⟧, by simpa [n₁] using hEheart⟩
    let FH : h.t.heart.FullSubcategory := ⟨F⟦(-n₁ : ℤ)⟧, by simpa [n₁, n₂, hidx] using hFheart⟩
    have hEss' : HeartSemistable (C := C) h EH := by
      simpa [EH, n₁] using hEss
    have hFss' : HeartSemistable (C := C) h FH := by
      simpa [FH, n₁, n₂, hidx] using hFss
    have hEphase' : HeartPhase (C := C) h EH = ψ₁ := by
      simpa [EH, ψ₁, n₁] using hEphase
    have hFphase' : HeartPhase (C := C) h FH = ψ₂ := by
      simpa [FH, ψ₂, n₁, n₂, hidx] using hFphase
    have hψ : ψ₂ < ψ₁ := by
      have hφ₂ : φ₂ = ψ₂ + (n₁ : ℝ) := by
        simpa [ψ₂, n₁, n₂, hidx] using (phaseBase_add_phaseIndex (C := C) h φ₂).symm
      have hφ₁ : φ₁ = ψ₁ + (n₁ : ℝ) := by
        simpa [ψ₁, n₁] using (phaseBase_add_phaseIndex (C := C) h φ₁).symm
      linarith [hgap, hφ₂, hφ₁]
    let g : EH.obj ⟶ FH.obj := (shiftFunctor C (-n₁ : ℤ)).map f
    have hg_zero :
        (ObjectProperty.homMk g : EH ⟶ FH) = 0 :=
      heart_hom_zero_of_semistable_phase_gt (C := C) h hEss' hFss' (by
        rw [hFphase', hEphase']
        exact hψ) (ObjectProperty.homMk g)
    have hmap : g = 0 := by
      exact congrArg InducedCategory.Hom.hom hg_zero
    exact (shiftFunctor C (-n₁ : ℤ)).map_injective (by simpa [g] using hmap)
  · let EH : h.t.heart.FullSubcategory := ⟨E⟦(-n₁ : ℤ)⟧, by simpa [n₁] using hEheart⟩
    let FH : h.t.heart.FullSubcategory := ⟨F⟦(-n₂ : ℤ)⟧, by simpa [n₂] using hFheart⟩
    let d : ℤ := n₁ - n₂
    have hdpos : 0 < d := by
      dsimp [d]
      omega
    let eE : EH.obj⟦d⟧ ≅ E⟦(-n₂ : ℤ)⟧ :=
      ((shiftFunctorAdd' C (-n₁ : ℤ) d (-n₂ : ℤ) (by
        dsimp [d]
        omega)).app E).symm
    let g : EH.obj⟦d⟧ ⟶ FH.obj := eE.hom ≫ (shiftFunctor C (-n₂ : ℤ)).map f
    haveI : h.t.IsLE EH.obj 0 := by
      exact (by simpa [EH, n₁] using hEheart.1 : h.t.IsLE EH.obj 0)
    haveI : h.t.IsGE FH.obj 0 := by
      exact (by simpa [FH, n₂] using hFheart.2 : h.t.IsGE FH.obj 0)
    haveI : h.t.IsLE (EH.obj⟦d⟧) (-d) :=
      h.t.isLE_shift EH.obj 0 d (-d) (by omega)
    have hg : g = 0 := by
      simpa using h.t.zero_of_isLE_of_isGE g (-d) 0 (by omega)
        (show h.t.IsLE (EH.obj⟦d⟧) (-d) by infer_instance)
        (show h.t.IsGE FH.obj 0 by infer_instance)
    have hshift : (shiftFunctor C (-n₂ : ℤ)).map f = 0 := by
      apply (cancel_epi eE.hom).mp
      simpa [g] using hg
    exact (shiftFunctor C (-n₂ : ℤ)).map_injective (by simpa using hshift)

/-- A local reverse-direction package: the induced phase family from heart stability
data, together with the pre-slicing axioms proved in this file. This isolates the
part of Bridgeland Proposition 5.3 already formalized here, before the ambient
central charge on `K₀ C` and the full HN existence for the induced slices are
packaged. -/
structure PreStabilityCondition where
  /-- The heart-side input data of Proposition 5.3. -/
  heartData : HeartStabilityData C
  /-- The induced phase predicate on the ambient triangulated category. -/
  P : ℝ → ObjectProperty C
  /-- The phase predicates are closed under isomorphism. -/
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  /-- The zero object lies in every phase. -/
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)
  /-- Shifting by `[1]` raises the phase by `1`. -/
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  /-- Morphisms from higher phase to lower phase vanish. -/
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0

/-- Forget the reverse-direction pre-slicing package back to the original heart data. -/
def PreStabilityCondition.toHeartStabilityData
    (σ : PreStabilityCondition C) : HeartStabilityData C :=
  σ.heartData

/-- **Proposition 5.3b / reverse direction, packaged so far.**
Heart stability data determines the ambient phase family `P(φ)` together with the
isomorphism, shift, and Hom-vanishing axioms of a Bridgeland slicing. The two
remaining reverse-direction steps, not yet packaged here, are:
1. constructing the ambient central charge `K₀ C →+ ℂ`;
2. proving HN existence for the induced phase family. -/
def HeartStabilityData.toPreStabilityCondition
    (h : HeartStabilityData C) : PreStabilityCondition C where
  heartData := h
  P := phasePredicate (C := C) h
  closedUnderIso := phasePredicate_closedUnderIso (C := C) h
  zero_mem := fun _ ↦ Or.inl (isZero_zero C)
  shift_iff := phasePredicate_shift_iff (C := C) h
  hom_vanishing := fun φ₁ φ₂ A B hlt hA hB f ↦
    phasePredicate_hom_zero (C := C) h hA hB hlt f

/-- The corresponding reverse-direction package extracted from an honest stability
condition. -/
def StabilityCondition.toPreStabilityCondition
    (σ : StabilityCondition C) : PreStabilityCondition C :=
  (σ.toHeartStabilityData C).toPreStabilityCondition C

/-- **Proposition 5.3c / left inverse, at the pre-stability level.**
Starting from a stability condition `σ`, extracting heart data, and reconstructing
the in-file reverse-direction pre-stability package agrees with the direct
definition of that package from `σ`. -/
theorem StabilityCondition.roundtrip
    (σ : StabilityCondition C) :
    (σ.toHeartStabilityData C).toPreStabilityCondition C = σ.toPreStabilityCondition C := by
  rfl

/-- **Proposition 5.3c / right inverse, at the heart-data level.**
For the in-file reverse-direction package, forgetting back to heart data recovers
the original input exactly. -/
theorem HeartStabilityData.roundtrip
    (h : HeartStabilityData C) :
    (h.toPreStabilityCondition C).toHeartStabilityData C = h := by
  rfl

end Proposition53

/-! ## §5: Lemma 5.2 consequences — P(φ) closure properties

### FALSE: P(φ) is NOT closed under subobjects in the heart

**Counterexample** (elliptic curve, standard stability condition `Z(E) = -deg(E) + i·rank(E)`):
Take `F` = semistable rank 2 bundle of degree 2 on an elliptic curve `E`.
Then `F ∈ P(3/4)` (since `arg(Z(F)) = arg(-2 + 2i) = 3π/4`).
A nonzero section `O_E → F` gives a sub-line-bundle `O_E ↪ F` in the heart `Coh(E)`.
But `O_E ∈ P(1/2)` (since `arg(Z(O_E)) = arg(i) = π/2`), so `O_E ∉ P(3/4)`.

**Why the see-saw argument fails**: For the triangle `A → E → Q → A⟦1⟧` with `E ∈ P(φ)`:
- `φ⁺(A) ≤ φ` (from `phiPlus_triangle_le`), so `Im(Z(A) · rot) ≤ 0`
- `φ⁻(Q) ≥ φ` (from `phiMinus_triangle_le`), so `Im(Z(Q) · rot) ≥ 0`
- Sum `= Im(Z(E) · rot) = 0` — but the terms have **opposite signs**, so sum `= 0`
  does NOT force each to be zero.

Compare with `P_phi_of_heart_triangle` (in `Deformation.lean`), which IS correct: it
requires BOTH `K` and `Q` to have phases `≤ φ` (and `> φ - 1`), ensuring same-sign
terms in the sum. -/

section PhaseSubcategoryProperties

variable [IsTriangulated C]

-- NOTE: The theorems `P_phi_closed_under_subobjects_in_heart` and
-- `P_phi_closed_under_quotients_in_heart` that were previously here are
-- MATHEMATICALLY FALSE and have been deleted. See the section comment above
-- for a counterexample.
--
-- The correct results for P(φ) closure are:
-- 1. `P_phi_of_heart_triangle` (Deformation.lean): if BOTH K and Q have
--    phases in (φ-1, φ], then K ∈ P(φ) and Q ∈ P(φ).
-- 2. For Bridgeland's arguments (Lemma 7.6, 7.7), the quasi-abelian
--    structure of P((a,b)) is needed. Strict subobjects in the quasi-abelian
--    category DO stay in the interval, but arbitrary heart-subobjects do NOT
--    stay in P(φ).

end PhaseSubcategoryProperties

/-! ## §7: Deformation infrastructure — heart SES bridge -/

section DeformationInfrastructure

variable [IsTriangulated C]

omit [IsTriangulated C] in
set_option backward.isDefEq.respectTransparency false in
/-- **Heart SES to distinguished triangle.**
Given a short exact sequence in the abelian heart (as objects and morphisms
in the ambient category `C` that lie in the heart), there is a distinguished
triangle extending it.

This is the fundamental bridge between abelian exact sequences in the heart
and triangulated exact triangles in the ambient category. It is used in
Lemma 7.6 (small-gap hom-vanishing) to translate kernel/image/cokernel
decompositions into phase bound arguments. -/
theorem TStructure.heart_shortExact_triangle
    (t : TStructure C) {A B Q : C}
    (hA : t.heart A) (hB : t.heart B) (hQ : t.heart Q)
    (f : A ⟶ B) (g : B ⟶ Q) (hfg : f ≫ g = 0)
    (hmono : Mono f) (hepi : Epi g)
    (hexact : ∀ {W : C} (α : W ⟶ B), α ≫ g = 0 →
      ∃ (β : W ⟶ A), β ≫ f = α) :
    ∃ (h : Q ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  -- Work in the heart abelian subcategory (letI for transparent instance reduction)
  letI := t.hasHeartFullSubcategory
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  let A' : t.heart.FullSubcategory := ⟨A, hA⟩
  let B' : t.heart.FullSubcategory := ⟨B, hB⟩
  let Q' : t.heart.FullSubcategory := ⟨Q, hQ⟩
  let f' : A' ⟶ B' := ObjectProperty.homMk f
  let g' : B' ⟶ Q' := ObjectProperty.homMk g
  -- g' is epi in the heart (faithful inclusion preserves the epi test)
  haveI : Epi g' := ⟨fun {Z} h₁ h₂ hh ↦ by
    ext; exact (cancel_epi g).mp (by
      simpa [ObjectProperty.FullSubcategory.comp_hom] using
        congr_arg InducedCategory.Hom.hom hh)⟩
  -- Get a distinguished triangle from the epi g' via the heart's abelian structure
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (heart_hι t) (heart_admissible t) g'
  -- hT : Triangle.mk (ι.map i) (ι.map g') δ ∈ distTriang C
  -- Factor ι.map i through f via hexact (i ≫ g' = 0 from the triangle)
  have h_ig : (ι.map i) ≫ g = 0 := by
    have := comp_distTriang_mor_zero₁₂ _ hT
    -- this : ι.map i ≫ ι.map g' = 0; ι.map g' =_def g
    change (ι.map i) ≫ g = 0 at this; exact this
  obtain ⟨β_hom, hβ_hom⟩ := hexact _ h_ig
  let β : K ⟶ A' := ObjectProperty.homMk β_hom
  have hβf : β ≫ f' = i := ι.map_injective (by
    rw [Functor.map_comp]; change β_hom ≫ f = ι.map i; exact hβ_hom)
  -- i is a kernel of g' in the heart (from the distinguished triangle)
  have hKer :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang (heart_hι t) i g' δ hT
  -- f' ≫ g' = 0 in the heart
  have hfg' : f' ≫ g' = 0 := ι.map_injective (by
    rw [Functor.map_comp, Functor.map_zero]; change f ≫ g = 0; exact hfg)
  -- Lift f' through the kernel i to get γ : A' ⟶ K with γ ≫ i = f'
  let γ : A' ⟶ K := hKer.lift (KernelFork.ofι f' hfg')
  have hγi : γ ≫ i = f' := Fork.IsLimit.lift_ι hKer
  -- β and γ are mutually inverse (both are kernel maps for g')
  have hβγ : β ≫ γ = 𝟙 K :=
    Fork.IsLimit.hom_ext hKer (by simp [hγi, hβf])
  have hγβ : γ ≫ β = 𝟙 A' := by
    haveI : Mono f' := ⟨fun {Z} h₁ h₂ hh ↦ by
      ext; exact (cancel_mono f).mp (by
        simpa [ObjectProperty.FullSubcategory.comp_hom] using
          congr_arg InducedCategory.Hom.hom hh)⟩
    rw [← cancel_mono f', Category.assoc, hβf, hγi, Category.id_comp]
  -- Construct the isomorphism K ≅ A' in the heart
  let eKA : K ≅ A' :=
    { hom := β, inv := γ, hom_inv_id := hβγ, inv_hom_id := hγβ }
  -- Transport the distinguished triangle via eKA
  -- T = Triangle.mk (ι.map i) (ι.map g') δ ∈ distTriang C
  -- T' = Triangle.mk f g h with h = δ ≫ (shiftFunctor C (1 : ℤ)).map (ι.map β)
  -- iso: T' ≅ T given by (ι.mapIso eKA.symm, id, id)
  refine ⟨δ ≫ ((shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)), ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (ι.mapIso eKA.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · -- comm₁: f ≫ 𝟙 = (ι.map γ) ≫ (ι.map i)
    simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom,
      Triangle.mk_mor₁]
    -- After simp: f = ι.map eKA.inv ≫ t.ιHeart.map i
    -- eKA.inv = γ and t.ιHeart = ι (via let), so:
    change f = ι.map γ ≫ ι.map i
    rw [← Functor.map_comp, hγi]; rfl
  · -- comm₂: g ≫ 𝟙 = 𝟙 ≫ (ι.map g')
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl
  · -- comm₃: (δ ≫ F.map (ι.map β)) ≫ F.map (ι.map γ) = 𝟙 ≫ δ
    simp only [Iso.refl_hom, Category.id_comp, Triangle.mk_mor₃, Functor.mapIso_hom,
      Iso.symm_hom]
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp, ← ι.map_comp, hβγ,
      ι.map_id, Functor.map_id, Category.comp_id]

end DeformationInfrastructure

end CategoryTheory.Triangulated
