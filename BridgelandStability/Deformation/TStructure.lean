/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.ExtensionClosure
public import BridgelandStability.Deformation.FiniteLengthHN
public import BridgelandStability.Deformation.HomVanishing
public import BridgelandStability.Deformation.HNFiltrationAssembly

/-!
# Deformation of Stability Conditions — TStructure

Q(>t), Q(≤t), orthogonality, HN splitting, deformedSlicing
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### Extension-closed subcategories Q(> t), Q(≤ t) (Node 7.8a) -/

variable [IsTriangulated C] in
/-- Auxiliary: any morphism from a `Q(ψ)`-semistable object to the `k`-th chain object of a
`Q`-HN filtration whose phases are all strictly less than `ψ` is zero. This is the direct
`deformedPred` analogue of `Slicing.chain_hom_eq_zero_of_gt`. -/
lemma chain_hom_eq_zero_of_gt_deformed
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {A E : C} {ψ : ℝ}
    (hA : σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ A)
    (F : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E)
    (hlt : ∀ i, F.φ i < ψ) :
    ∀ (k : ℕ) (hk : k < F.n + 1) (f : A ⟶ F.chain.obj ⟨k, hk⟩), f = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk f
      exact (F.base_isZero : IsZero F.chain.left).eq_of_tgt f 0
  | succ k ih =>
      intro hk f
      have hkn : k < F.n := by omega
      let T := F.triangle ⟨k, hkn⟩
      let e₁ := Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)
      let e₂ := Classical.choice (F.triangle_obj₂ ⟨k, hkn⟩)
      have hcomp : (f ≫ e₂.inv) ≫ T.mor₂ = 0 :=
        σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hε₀8 hsin
          hA (F.semistable ⟨k, hkn⟩) (hlt ⟨k, hkn⟩) _
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T
        (F.triangle_dist ⟨k, hkn⟩) (f ≫ e₂.inv) hcomp
      have hg0 : g ≫ e₁.hom = 0 := ih (by omega) (g ≫ e₁.hom)
      have hg_eq : g = 0 := by
        have : g = (g ≫ e₁.hom) ≫ e₁.inv := by
          rw [Category.assoc, e₁.hom_inv_id, Category.comp_id]
        rw [this, hg0, zero_comp]
      have hfe : f ≫ e₂.inv = 0 := by rw [hg, hg_eq, zero_comp]
      have : f = (f ≫ e₂.inv) ≫ e₂.hom := by
        rw [Category.assoc, e₂.inv_hom_id, Category.comp_id]
      rw [this, hfe, zero_comp]

variable [IsTriangulated C] in
/-- A morphism from a `Q(ψ)`-semistable object to an HN-filtered object whose phases are all
strictly less than `ψ` is zero. -/
lemma hom_eq_zero_of_gt_phases_deformed
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {A E : C} {ψ : ℝ}
    (hA : σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ A)
    (F : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E)
    (hlt : ∀ i, F.φ i < ψ) (f : A ⟶ E) : f = 0 := by
  let eE := Classical.choice F.top_iso
  have h1 : f ≫ eE.inv = 0 :=
    chain_hom_eq_zero_of_gt_deformed (C := C) (σ := σ) (W := W) (hW := hW)
      hε₀ hε₀2 hε₀8 hsin hA F hlt F.n (by omega) _
  have : f = (f ≫ eE.inv) ≫ eE.hom := by
    rw [Category.assoc, eE.inv_hom_id, Category.comp_id]
  rw [this, h1, zero_comp]

variable [IsTriangulated C] in
/-- Auxiliary: any morphism from the `k`-th chain object of a `Q`-HN filtration (with all
phases strictly greater than those of a second `Q`-HN filtration) to the target of the second
filtration is zero. This is the `deformedPred` analogue of
`Slicing.chain_hom_eq_zero_gap`. -/
lemma chain_hom_eq_zero_gap_deformed
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {X Y : C}
    (Fx : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) X)
    (Fy : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) Y)
    (hgap : ∀ i j, Fy.φ j < Fx.φ i) :
    ∀ (k : ℕ) (hk : k < Fx.n + 1) (f : Fx.chain.obj ⟨k, hk⟩ ⟶ Y), f = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk f
      exact (Fx.base_isZero : IsZero Fx.chain.left).eq_of_src f 0
  | succ k ih =>
      intro hk f
      have hkn : k < Fx.n := by omega
      let T := Fx.triangle ⟨k, hkn⟩
      let e₁ := Classical.choice (Fx.triangle_obj₁ ⟨k, hkn⟩)
      let e₂ := Classical.choice (Fx.triangle_obj₂ ⟨k, hkn⟩)
      have hmor1 : T.mor₁ ≫ (e₂.hom ≫ f) = 0 := by
        have h1 : e₁.inv ≫ (T.mor₁ ≫ (e₂.hom ≫ f)) = 0 := by
          simp only [← Category.assoc]
          exact ih (by omega) _
        have h2 :
            e₁.hom ≫ (e₁.inv ≫ (T.mor₁ ≫ (e₂.hom ≫ f))) =
              T.mor₁ ≫ (e₂.hom ≫ f) := by
          rw [← Category.assoc, e₁.hom_inv_id, Category.id_comp]
        rw [← h2, h1, comp_zero]
      obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T
        (Fx.triangle_dist ⟨k, hkn⟩) (e₂.hom ≫ f) hmor1
      have hg_eq : g = 0 :=
        hom_eq_zero_of_gt_phases_deformed (C := C) (σ := σ) (W := W) (hW := hW)
          hε₀ hε₀2 hε₀8 hsin (Fx.semistable ⟨k, hkn⟩) Fy
          (fun j ↦ hgap ⟨k, hkn⟩ j) g
      have hef : e₂.hom ≫ f = 0 := by rw [hg, hg_eq, comp_zero]
      have : f = e₂.inv ≫ (e₂.hom ≫ f) := by
        rw [← Category.assoc, e₂.inv_hom_id, Category.id_comp]
      rw [this, hef, comp_zero]

variable [IsTriangulated C] in
/-- Morphisms between `Q`-HN filtered objects with a phase gap are zero. -/
lemma hom_eq_zero_of_phase_gap_deformed
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {X Y : C}
    (Fx : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) X)
    (Fy : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) Y)
    (hgap : ∀ i j, Fy.φ j < Fx.φ i) (f : X ⟶ Y) : f = 0 := by
  let eX := Classical.choice Fx.top_iso
  have h1 : eX.hom ≫ f = 0 :=
    chain_hom_eq_zero_gap_deformed (C := C) (σ := σ) (W := W) (hW := hW)
      hε₀ hε₀2 hε₀8 hsin Fx Fy hgap Fx.n (by omega) _
  have : f = eX.inv ≫ (eX.hom ≫ f) := by
    rw [← Category.assoc, eX.inv_hom_id, Category.id_comp]
  rw [this, h1, comp_zero]

variable [IsTriangulated C] in
/-- Inside a thin interval whose `W`-phase window already sits `ε₀` away from the
boundaries, the Lemma 7.6 hom-vanishing theorem applies directly to the interval-semistable
objects, because they are `deformedPred` objects witnessed by that same interval. -/
theorem hom_eq_zero_of_enveloped_interval_semistable
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      a + ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b - ε₀)
    {E F : σ.slicing.IntervalCat C a b}
    (hE : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E.obj
      (wPhaseOf (W (K₀.of C E.obj)) ((a + b) / 2)))
    (hF : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C F.obj
      (wPhaseOf (W (K₀.of C F.obj)) ((a + b) / 2)))
    (hlt :
      wPhaseOf (W (K₀.of C F.obj)) ((a + b) / 2) <
        wPhaseOf (W (K₀.of C E.obj)) ((a + b) / 2))
    (f : E ⟶ F) :
    f = 0 := by
  have hEQ :
      σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin
        (wPhaseOf (W (K₀.of C E.obj)) ((a + b) / 2)) E.obj := by
    refine Or.inr ⟨a, b, hab, hthin, ?_, ?_, ?_⟩
    · exact le_of_lt (hWindow E.property hE.2.1).1
    · exact le_of_lt (hWindow E.property hE.2.1).2
    · simpa using hE
  have hFQ :
      σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin
        (wPhaseOf (W (K₀.of C F.obj)) ((a + b) / 2)) F.obj := by
    refine Or.inr ⟨a, b, hab, hthin, ?_, ?_, ?_⟩
    · exact le_of_lt (hWindow F.property hF.2.1).1
    · exact le_of_lt (hWindow F.property hF.2.1).2
    · simpa using hF
  have h0 : f.hom = 0 :=
    σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hε₀8 hsin hEQ hFQ hlt f.hom
  ext
  exact h0

variable [IsTriangulated C] in
/-- Lemma 7.7 packaged directly for the deformed slicing: if a thin interval carries the
strict finite-length input and every nonzero object has `W`-phase at least `ε₀` away from
the interval boundaries, then the thin-interval HN factors are already `Q`-factors, using
the same interval as the witness in `deformedPred`. -/
theorem exists_deformedHN_of_enveloped_interval
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      W (K₀.of C F) ≠ 0)
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      a + ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b - ε₀)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X) :
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) X.obj,
      ∀ j, a + ε₀ < G.φ j ∧ G.φ j < b - ε₀ := by
  let ssf : SkewedStabilityFunction C σ.slicing a b :=
    σ.skewedStabilityFunction_of_near C W hW hab
  obtain ⟨G, hGφ⟩ :=
    SkewedStabilityFunction.hn_exists_in_thin_interval
      (C := C) (σ := σ) (a := a) (b := b) (ssf := ssf) hFiniteLength
      (fun {F} hF hFne ↦ hW_interval hF hFne)
      (L := a + ε₀) (U := b - ε₀)
      (fun {F} hF hFne ↦ hWindow hF hFne)
      (by linarith [hthin])
      (fun {E F} hE hF hlt _hguard f ↦
        hom_eq_zero_of_enveloped_interval_semistable
          (C := C) (σ := σ) (W := W) (hW := hW) hab
          hε₀ hε₀2 hε₀8 hthin hsin hWindow hE hF hlt f)
      (fun {Y} _hY {A} hA_ss _hA_strict _hA_dest ↦ by
        simpa [ssf, StabilityCondition.skewedStabilityFunction_of_near] using
          (hWindow hA_ss.1 hA_ss.2.1).2)
      X hX
  let GQ : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) X.obj :=
    { n := G.n
      chain := G.chain
      triangle := G.triangle
      triangle_dist := G.triangle_dist
      triangle_obj₁ := G.triangle_obj₁
      triangle_obj₂ := G.triangle_obj₂
      base_isZero := G.base_isZero
      top_iso := G.top_iso
      zero_isZero := G.zero_isZero
      φ := G.φ
      hφ := G.hφ
      semistable := fun j ↦ by
        change IsZero (G.factor j) ∨
          ∃ (a' b' : ℝ) (hab' : a' < b') (_ : b' - a' + 2 * ε₀ < 1)
            (_ : a' + ε₀ ≤ G.φ j) (_ : G.φ j ≤ b' - ε₀),
            (σ.skewedStabilityFunction_of_near C W hW hab').Semistable C (G.factor j) (G.φ j)
        refine Or.inr ⟨a, b, hab, hthin, le_of_lt (hGφ j).1, le_of_lt (hGφ j).2, ?_⟩
        simpa [ssf] using G.semistable j }
  refine ⟨GQ, hGφ⟩

/-- **Generators of Q(> t)**: Q-semistable objects with some phase `ψ > t`
(Bridgeland Node 7.8a). -/
def StabilityCondition.deformedGtGen (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  fun E ↦ ∃ ψ, t < ψ ∧ σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ E

/-- **Generators of Q(≤ t)**: Q-semistable objects with some phase `ψ ≤ t`
(Bridgeland Node 7.8a). -/
def StabilityCondition.deformedLeGen (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  fun E ↦ ∃ ψ, ψ ≤ t ∧ σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ E

/-- **Generators of Q(< t)**: Q-semistable objects with some phase `ψ < t`
(Bridgeland Node 7.8a / 7.9). -/
def StabilityCondition.deformedLtGen (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  fun E ↦ ∃ ψ, ψ < t ∧ σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ E

/-- **Q(> t)**: the extension-closed subcategory generated by the `Q(ψ)` with `ψ > t`
(Bridgeland p.6, Node 7.8a). -/
def StabilityCondition.deformedGtPred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  (σ.deformedGtGen C W hW ε₀ hε₀ hε₀2 hsin t).ExtensionClosure

/-- **Q(≤ t)**: the extension-closed subcategory generated by the `Q(ψ)` with `ψ ≤ t`
(Bridgeland p.6, Node 7.8a). -/
def StabilityCondition.deformedLePred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  (σ.deformedLeGen C W hW ε₀ hε₀ hε₀2 hsin t).ExtensionClosure

/-- **Q(< t)**: the extension-closed subcategory generated by the `Q(ψ)` with `ψ < t`
(Bridgeland p.6, Node 7.8a / 7.9). -/
def StabilityCondition.deformedLtPred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  (σ.deformedLtGen C W hW ε₀ hε₀ hε₀2 hsin t).ExtensionClosure

variable [IsTriangulated C] in
/-- Monotonicity of the provisional `Q(≤ t)` predicate. -/
theorem StabilityCondition.deformedLePred_mono
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t₁ ≤
      σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t₂ :=
  ObjectProperty.ExtensionClosure.mono (fun E ⟨ψ, hψ, hP⟩ ↦ ⟨ψ, le_trans hψ ht, hP⟩)

variable [IsTriangulated C] in
/-- Monotonicity of the provisional `Q(< t)` predicate. -/
theorem StabilityCondition.deformedLtPred_mono
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin t₁ ≤
      σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin t₂ :=
  ObjectProperty.ExtensionClosure.mono (fun E ⟨ψ, hψ, hP⟩ ↦ ⟨ψ, lt_of_lt_of_le hψ ht, hP⟩)

variable [IsTriangulated C] in
/-- Any `Q(< t)`-object is in `Q(≤ t)`. -/
theorem StabilityCondition.deformedLePred_of_deformedLtPred
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {t : ℝ} :
    σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin t ≤
      σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t :=
  ObjectProperty.ExtensionClosure.mono (fun E ⟨ψ, hψ, hP⟩ ↦ ⟨ψ, le_of_lt hψ, hP⟩)

variable [IsTriangulated C] in
/-- Anti-monotonicity of `Q(> t)`: if `t₁ ≤ t₂` then `Q(> t₂) ⊆ Q(> t₁)`. -/
theorem StabilityCondition.deformedGtPred_anti
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t₂ ≤
      σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t₁ :=
  ObjectProperty.ExtensionClosure.mono (fun E ⟨ψ, hψ, hP⟩ ↦ ⟨ψ, lt_of_le_of_lt ht hψ, hP⟩)

variable [IsTriangulated C] in
/-- **Orthogonality of Q(> t) and Q(≤ t)** (**Node 7.8b**). Every morphism from a
`Q(> t)`-object to a `Q(≤ t)`-object is zero, by the sharp hom-vanishing (Node 7.6). -/
theorem StabilityCondition.hom_eq_zero_of_deformedGt_deformedLe
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E F : C} {t : ℝ}
    (hE : σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t E)
    (hF : σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t F)
    (f : E ⟶ F) : f = 0 :=
  ObjectProperty.ExtensionClosure.hom_eq_zero
    (fun E F ⟨ψ₁, hψ₁, hE'⟩ ⟨ψ₂, hψ₂, hF'⟩ f ↦
      σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hε₀8 hsin hE' hF' (by linarith) f)
    hE hF f

variable [IsTriangulated C] in
/-- Orthogonality of `Q(> t)` and `Q(< t)`. This is the strict version of Node 7.8b used
later for the strip categories `Q((t, t + δ))`. -/
theorem StabilityCondition.hom_eq_zero_of_deformedGt_deformedLt
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E F : C} {t : ℝ}
    (hE : σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t E)
    (hF : σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin t F)
    (f : E ⟶ F) : f = 0 :=
  ObjectProperty.ExtensionClosure.hom_eq_zero
    (fun E F ⟨ψ₁, hψ₁, hE'⟩ ⟨ψ₂, hψ₂, hF'⟩ f ↦
      σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hε₀8 hsin hE' hF' (by linarith) f)
    hE hF f
variable [IsTriangulated C] in
/-- A `Q`-HN filtration split at cutoff `t` gives the paper's truncation triangle whose two
pieces lie in `Q(> t)` and `Q(≤ t)`. -/
theorem exists_deformedGt_deformedLe_triangle_of_hn
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E : C}
    (G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E)
    (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t X ∧
      σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t Y := by
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hprops⟩ :=
    split_hn_filtration_at_cutoff (C := C) G t
  have hGX := And.left hprops; have hGY := And.left (And.right hprops)
  exact ⟨X, Y, f, g, h, hT,
    ObjectProperty.ExtensionClosure.of_postnikovTower GX.toPostnikovTower
      (fun j ↦ ⟨GX.φ j, hGX j, GX.semistable j⟩),
    ObjectProperty.ExtensionClosure.of_postnikovTower GY.toPostnikovTower
      (fun j ↦ ⟨GY.φ j, hGY j, GY.semistable j⟩)⟩

variable [IsTriangulated C] in
/-- A `Q`-HN filtration split at cutoff `t` also gives the strip-style truncation triangle
used in Node 7.9, with the right-hand term in `Q(< t + δ)` for any `δ > 0`. -/
theorem exists_deformedGt_deformedLt_triangle_of_hn
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E : C}
    (G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E)
    (t δ : ℝ) (hδ : 0 < δ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t X ∧
      σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin (t + δ) Y := by
  obtain ⟨X, Y, f, g, h, hT, hX, hY⟩ :=
    exists_deformedGt_deformedLe_triangle_of_hn C σ W hW hε₀ hε₀2 hsin G t
  exact ⟨X, Y, f, g, h, hT, hX,
    ObjectProperty.ExtensionClosure.mono (fun E ⟨ψ, hψ, hP⟩ ↦ ⟨ψ, by linarith, hP⟩) _ hY⟩

variable [IsTriangulated C] in
/-- Faithful Node 7.8c wrapper: once an object in a thin interval admits a `Q`-HN filtration
whose factors stay inside the same enveloping window, splitting that HN filtration at a cutoff
`t` gives the paper's `Q(> t) / Q(≤ t)` truncation triangle. -/
theorem exists_deformedGt_deformedLe_triangle_of_enveloped_interval
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      W (K₀.of C F) ≠ 0)
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      a + ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b - ε₀)
    {E : C} (hE : σ.slicing.intervalProp C a b E) (hEne : ¬IsZero E)
    (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t X ∧
      σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t Y := by
  let EI : σ.slicing.IntervalCat C a b := ⟨E, hE⟩
  have hEIne : ¬IsZero EI := by
    intro hZ
    exact hEne (((σ.slicing.intervalProp C a b).ι).map_isZero hZ)
  obtain ⟨G, _hGφ⟩ :=
    exists_deformedHN_of_enveloped_interval
      (C := C) (σ := σ) (W := W) (hW := hW) hab
      hFiniteLength hε₀ hε₀2 hε₀8 hthin hsin hW_interval hWindow
      (X := EI) hEIne
  exact exists_deformedGt_deformedLe_triangle_of_hn
    (C := C) (σ := σ) (W := W) (hW := hW) hε₀ hε₀2 hsin G t


end CategoryTheory.Triangulated
