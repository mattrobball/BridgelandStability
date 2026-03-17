/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.StabilityCondition
import Mathlib.CategoryTheory.Triangulated.StabilityFunction
import Mathlib.CategoryTheory.Triangulated.IntervalCategory
import Mathlib.CategoryTheory.Triangulated.TStructure.HeartAbelian
import Mathlib.CategoryTheory.Triangulated.Deformation.PPhiAbelian
import Mathlib.CategoryTheory.Triangulated.Deformation.PhaseArithmetic

/-!
# Heart Equivalence and Blueprint Scaffolding

This file captures the definitions and theorem statements from the Bridgeland
stability conditions blueprint (§§3–5) that are not yet present in the branch.
All nontrivial proofs are left as `sorry` to create a complete scaffolding.

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
* `HeartStabilityData.toStabilityCondition`: construct σ from heart data (5.3b).
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
open scoped ZeroObject

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
  /-- The abelian structure on the heart, default from `heartFullSubcategoryAbelian`. -/
  hAbelian : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  /-- The stability function on the heart. -/
  Z : @StabilityFunction t.heart.FullSubcategory _ hAbelian
  /-- The stability function has the HN property. -/
  hasHN : @StabilityFunction.HasHNProperty t.heart.FullSubcategory _ hAbelian Z

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

/-- **Proposition 5.3a / forward direction.**
Every stability condition `σ` determines heart stability data:
1. The t-structure is `σ.slicing.toTStructure`.
2. Boundedness follows from the HN filtration axiom.
3. The stability function on the heart `P((0, 1])` is the restriction of `Z`.
4. The HN property follows from local finiteness + `hasHN_of_finiteLength`.

The key identification is that semistable objects of phase `φ ∈ (0, 1]` in the
heart are exactly the objects of `P(φ)`, and the slicing's HN filtration of a
heart object is exactly an HN filtration in the sense of
`StabilityFunction`. -/
def StabilityCondition.toHeartStabilityData
    (σ : StabilityCondition C) : HeartStabilityData C where
  t := σ.slicing.toTStructure
  bounded := σ.slicing.toTStructure_bounded C
  Z := σ.stabilityFunctionOnHeart C
  hasHN := by sorry

/-- **Proposition 5.3b / reverse direction.**
Heart stability data determines a stability condition:
1. Define `P(φ)` for `φ ∈ (0, 1]` as the semistable objects of phase `φ` in
   the heart's stability function.
2. Extend by shifts: `P(φ + n) := P(φ)[n]` for `n ∈ ℤ`.
3. The central charge `Z : K₀ C →+ ℂ` is constructed by lifting the heart's
   `Zobj` through boundedness (every K₀ class decomposes into heart classes).
4. Hom-vanishing uses heart orthogonality (shifts of heart objects in different
   degrees have no morphisms) and phase monotonicity for semistable objects.
5. HN existence uses the bounded t-structure decomposition + the heart's HN
   property on each cohomology piece.
6. Compatibility with `Z` is direct from the construction.
7. Local finiteness follows from the HN property + finite length. -/
def HeartStabilityData.toStabilityCondition
    (h : HeartStabilityData C) : StabilityCondition C := by
  sorry

/-- **Proposition 5.3c / left inverse.**
Starting from a stability condition `σ`, extracting heart data, and
reconstructing a stability condition yields back `σ`. -/
theorem StabilityCondition.roundtrip
    (σ : StabilityCondition C) :
    (σ.toHeartStabilityData C).toStabilityCondition C = σ := by
  sorry

/-- **Proposition 5.3c / right inverse.**
Starting from heart stability data, constructing a stability condition, and
extracting heart data yields back the original data. -/
theorem HeartStabilityData.roundtrip
    (h : HeartStabilityData C) :
    (h.toStabilityCondition C).toHeartStabilityData C = h := by
  sorry

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
