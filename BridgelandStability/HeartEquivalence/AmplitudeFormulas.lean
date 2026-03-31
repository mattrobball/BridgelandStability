/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.HeartEquivalence.PureAdditivity

/-!
# Amplitude Formulas and Bounded Triangle Additivity

Specializations for objects of amplitude (-1, 0) and triangle additivity
with explicit bounds.
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

section Proposition53

variable [IsTriangulated C]

omit [IsTriangulated C] in
theorem TStructure.triangleLTGE_iso_of_amp_negOne_zero
    (t : TStructure C)
    {X K Q : C} (hK : t.heart K) (hQ : t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C) :
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

/-! The next two isomorphisms identify the only nonzero heart cohomology objects
of an object of amplitude `(-1, 0)` with the heart objects at the ends of a
distinguished triangle realizing that amplitude. -/

/-- For an object of amplitude `(-1, 0)` presented by a triangle
`K⟦1⟧ ⟶ X ⟶ Q ⟶ K⟦2⟧` with `K, Q` in the heart, the `(-1)`-st heart
cohomology of `X` is canonically isomorphic to `K`. -/
noncomputable def HeartStabilityData.heartCoh_negOne_iso_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsGE X (-1)] :
    h.heartCoh (C := C) (-1) X ≅ ⟨K, hK⟩ := by
  classical
  let hEx := TStructure.triangleLTGE_iso_of_amp_negOne_zero
    (C := C) (t := h.t) (X := X) (K := K) (Q := Q) hK hQ hT
  let eT := Classical.choose hEx
  let e₁ :
      ((h.t.truncGELE (-1) (-1)).obj X) ≅ ((h.t.truncGELT (-1) 0).obj X) :=
    (h.t.truncGELEIsoTruncGELT (-1) (-1) 0 rfl).app X
  let e₂ :
      ((h.t.truncGELT (-1) 0).obj X) ≅ (h.t.truncLT 0).obj X := by
      simpa [TStructure.truncGELT] using
        ((@asIso _ _ _ _ ((h.t.truncGEπ (-1)).app ((h.t.truncLT 0).obj X))
          (by
            infer_instance)).symm)
  let e₃ : (h.t.truncLT 0).obj X ≅ K⟦(1 : ℤ)⟧ :=
    (asIso eT.hom.hom₁).symm
  let e : ((h.t.truncGELE (-1) (-1)).obj X) ≅ K⟦(1 : ℤ)⟧ := e₁ ≪≫ e₂ ≪≫ e₃
  let e' : (h.heartCoh (C := C) (-1) X).obj ≅ K := by
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      ((shiftFunctor C (-1 : ℤ)).mapIso e ≪≫ shiftShiftNeg (X := K) (i := (1 : ℤ)))
  exact ObjectProperty.isoMk _ e'

/-- For an object of amplitude `(-1, 0)` presented by a triangle
`K⟦1⟧ ⟶ X ⟶ Q ⟶ K⟦2⟧` with `K, Q` in the heart, the `0`-th heart
cohomology of `X` is canonically isomorphic to `Q`. -/
noncomputable def HeartStabilityData.heartCoh_zero_iso_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] :
    h.heartCoh (C := C) 0 X ≅ ⟨Q, hQ⟩ := by
  classical
  let hEx := TStructure.triangleLTGE_iso_of_amp_negOne_zero
    (C := C) (t := h.t) (X := X) (K := K) (Q := Q) hK hQ hT
  let eT := Classical.choose hEx
  let e₁ :
      ((h.t.truncGELE 0 0).obj X) ≅ (h.t.truncGE 0).obj X := by
      refine ((h.t.truncGELEIsoLEGE 0 0).app X) ≪≫ ?_
      simpa [TStructure.truncLEGE] using
        (@asIso _ _ _ _ ((h.t.truncLEι 0).app ((h.t.truncGE 0).obj X))
          (by
            infer_instance))
  let e₂ : (h.t.truncGE 0).obj X ≅ Q :=
    (asIso eT.hom.hom₃).symm
  let e : ((h.t.truncGELE 0 0).obj X) ≅ Q := e₁ ≪≫ e₂
  let e' : (h.heartCoh (C := C) 0 X).obj ≅ Q := by
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      ((shiftFunctorZero C ℤ).app ((h.t.truncGELE 0 0).obj X) ≪≫ e)
  exact ObjectProperty.isoMk _ e'

theorem HeartStabilityData.heartCohClassSum_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] [h.t.IsGE X (-1)] :
    h.heartCohClassSum (C := C) (-1) 1 X =
      -HeartK0.of (C := C) h ⟨K, hK⟩ + HeartK0.of (C := C) h ⟨Q, hQ⟩ := by
  have hneg :
      HeartK0.of (C := C) h (h.heartCoh (C := C) (-1) X) =
        HeartK0.of (C := C) h ⟨K, hK⟩ :=
    HeartK0.of_iso (C := C) h
      (h.heartCoh_negOne_iso_of_amp_negOne_zero (C := C)
        (X := X) (K := K) (Q := Q) hK hQ hT)
  have hzero :
      HeartK0.of (C := C) h (h.heartCoh (C := C) 0 X) =
        HeartK0.of (C := C) h ⟨Q, hQ⟩ :=
    HeartK0.of_iso (C := C) h
      (h.heartCoh_zero_iso_of_amp_negOne_zero (C := C)
        (X := X) (K := K) (Q := Q) hK hQ hT)
  rw [HeartStabilityData.heartCohClassSum, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp [HeartStabilityData.heartCohClass, hneg, hzero]

theorem HeartStabilityData.ZOnHeartK0_heartCohClassSum_of_amp_negOne_zero
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

theorem HeartStabilityData.heartEulerClassObj_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] [h.t.IsGE X (-1)] :
    h.heartEulerClassObj (C := C) X =
      -HeartK0.of (C := C) h ⟨K, hK⟩ + HeartK0.of (C := C) h ⟨Q, hQ⟩ := by
  rw [h.heartEulerClassObj_eq_heartCohClassSum (C := C) (X := X) (b := -1) (a := 0)
    (by lia) inferInstance inferInstance]
  exact h.heartCohClassSum_of_amp_negOne_zero (C := C)
    (X := X) (K := K) (Q := Q) hK hQ hT

theorem HeartStabilityData.eulerZObj_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] [h.t.IsGE X (-1)] :
    h.eulerZObj (C := C) X =
      -HeartStabilityData.heartZObj (C := C) h ⟨K, hK⟩ +
        HeartStabilityData.heartZObj (C := C) h ⟨Q, hQ⟩ := by
  rw [HeartStabilityData.eulerZObj,
    h.heartEulerClassObj_eq_heartCohClassSum (C := C) (X := X) (b := -1) (a := 0)
      (by lia) inferInstance inferInstance]
  exact h.ZOnHeartK0_heartCohClassSum_of_amp_negOne_zero (C := C)
    (X := X) (K := K) (Q := Q) hK hQ hT

theorem HeartStabilityData.heartEulerClassObj_triangle_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] [h.t.IsGE X (-1)] :
    h.heartEulerClassObj (C := C) X =
      h.heartEulerClassObj (C := C) (K⟦(1 : ℤ)⟧) +
        h.heartEulerClassObj (C := C) Q := by
  have hK' :
      h.heartEulerClassObj (C := C) (K⟦(1 : ℤ)⟧) =
        -HeartK0.of (C := C) h ⟨K, hK⟩ := by
    simpa using h.heartEulerClassObj_of_heart_shift (C := C) ⟨K, hK⟩ (-1)
  have hQ' :
      h.heartEulerClassObj (C := C) Q =
        HeartK0.of (C := C) h ⟨Q, hQ⟩ := by
    simpa using h.heartEulerClassObj_of_heart (C := C) ⟨Q, hQ⟩
  rw [h.heartEulerClassObj_of_amp_negOne_zero (C := C) (X := X) (K := K) (Q := Q) hK hQ hT,
    hK', hQ']

theorem HeartStabilityData.eulerZObj_triangle_of_amp_negOne_zero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X K Q : C} (hK : h.t.heart K) (hQ : h.t.heart Q)
    {α : K⟦(1 : ℤ)⟧ ⟶ X} {β : X ⟶ Q} {γ : Q ⟶ (K⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C)
    [h.t.IsLE X 0] [h.t.IsGE X (-1)] :
    h.eulerZObj (C := C) X =
      h.eulerZObj (C := C) (K⟦(1 : ℤ)⟧) +
        h.eulerZObj (C := C) Q := by
  have hK' :
      h.eulerZObj (C := C) (K⟦(1 : ℤ)⟧) =
        -HeartStabilityData.heartZObj (C := C) h ⟨K, hK⟩ := by
    simpa using h.eulerZObj_of_heart_shift (C := C) ⟨K, hK⟩ (-1)
  have hQ' :
      h.eulerZObj (C := C) Q =
        HeartStabilityData.heartZObj (C := C) h ⟨Q, hQ⟩ := by
    simpa using h.eulerZObj_of_heart (C := C) ⟨Q, hQ⟩
  rw [h.eulerZObj_of_amp_negOne_zero (C := C) (X := X) (K := K) (Q := Q) hK hQ hT,
    hK', hQ']

theorem HeartStabilityData.heartEulerClassObj_triangle_of_bounds
    (h : HeartStabilityData C) [IsTriangulated C]
    [Functor.IsHomological (h.H0Functor (C := C))]
    (T : Triangle C) (hT : T ∈ distTriang C) {b a : ℤ} (hab : b ≤ a)
    (h₁LE : h.t.IsLE T.obj₁ (a + 1)) (h₁GE : h.t.IsGE T.obj₁ (b + 1))
    (h₂LE : h.t.IsLE T.obj₂ a) (h₂GE : h.t.IsGE T.obj₂ b)
    (h₃LE : h.t.IsLE T.obj₃ a) (h₃GE : h.t.IsGE T.obj₃ b) :
    h.heartEulerClassObj (C := C) T.obj₂ =
      h.heartEulerClassObj (C := C) T.obj₁ + h.heartEulerClassObj (C := C) T.obj₃ := by
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  let m : ℕ := Int.toNat (a - b)
  let imgTerm : ℤ → HeartK0 (C := C) h := fun n =>
    (((-1 : ℤ) ^ Int.natAbs n) •
      HeartK0.of (C := C) h
        (Limits.image (((h.H0Functor (C := C)).shift n).map T.mor₁)))
  have hm : b + (m : ℤ) = a := by
    dsimp [m]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    lia
  have hm_shift : Int.toNat ((a + 1) - (b + 1)) = m := by
    dsimp [m]
    lia
  have hstep (n : ℤ) :
      h.heartCohClass (C := C) n T.obj₂ -
          h.heartCohClass (C := C) n T.obj₃ -
            h.heartCohClass (C := C) (n + 1) T.obj₁ =
        imgTerm n - imgTerm (n + 1) := by
    simpa [imgTerm, sub_eq_add_neg, negOnePow_natAbs_succ, zsmul_neg] using
      h.heartCohClass_five_term_relation (C := C) T hT n
  have hsum :
      h.heartCohClassSum (C := C) b m T.obj₂ -
          h.heartCohClassSum (C := C) b m T.obj₃ -
            h.heartCohClassSum (C := C) (b + 1) m T.obj₁ =
        Finset.sum (Finset.range (m + 1))
          (fun j => imgTerm (b + (j : ℤ)) - imgTerm (b + (j : ℤ) + 1)) := by
    rw [HeartStabilityData.heartCohClassSum, HeartStabilityData.heartCohClassSum,
      HeartStabilityData.heartCohClassSum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    simpa [add_assoc, add_left_comm, add_comm] using hstep (b + (j : ℤ))
  have htel :
      Finset.sum (Finset.range (m + 1))
          (fun j => imgTerm (b + (j : ℤ)) - imgTerm (b + (j : ℤ) + 1)) =
        imgTerm b - imgTerm (b + ((m + 1 : ℕ) : ℤ)) := by
    let r : ℕ → HeartK0 (C := C) h := fun j => imgTerm (b + (j : ℤ))
    simpa [r, add_assoc] using (Finset.sum_range_sub' r (m + 1))
  have himg_b : imgTerm b = 0 := by
    have hzero :
        IsZero (((h.H0Functor (C := C)).shift b).obj T.obj₁) :=
      h.isZero_H0Functor_shift_obj_of_lt_bound (C := C) (X := T.obj₁)
        (m := b) (n := b + 1) (by lia) h₁GE
    have hmor_zero : (((h.H0Functor (C := C)).shift b).map T.mor₁) = 0 :=
      zero_of_source_iso_zero _ hzero.isoZero
    have hclass :
        HeartK0.of (C := C) h
            (Limits.image (((h.H0Functor (C := C)).shift b).map T.mor₁)) = 0 :=
      HeartK0.of_image_eq_zero (C := C) h hmor_zero
    simp [imgTerm, hclass]
  have himg_a1 : imgTerm (a + 1) = 0 := by
    have hzero :
        IsZero (((h.H0Functor (C := C)).shift (a + 1)).obj T.obj₂) :=
      h.isZero_H0Functor_shift_obj_of_gt_bound (C := C) (X := T.obj₂)
        (m := a + 1) (n := a) (by lia) h₂LE
    have hmor_zero : (((h.H0Functor (C := C)).shift (a + 1)).map T.mor₁) = 0 :=
      zero_of_target_iso_zero _ hzero.isoZero
    have hclass :
        HeartK0.of (C := C) h
            (Limits.image (((h.H0Functor (C := C)).shift (a + 1)).map T.mor₁)) = 0 :=
      HeartK0.of_image_eq_zero (C := C) h hmor_zero
    simp [imgTerm, hclass]
  have hm1 : b + ((m + 1 : ℕ) : ℤ) = a + 1 := by
    lia
  have hm1' : b + ((m : ℤ) + 1) = a + 1 := by
    lia
  have hsum_zero :
      h.heartCohClassSum (C := C) b m T.obj₂ -
          h.heartCohClassSum (C := C) b m T.obj₃ -
            h.heartCohClassSum (C := C) (b + 1) m T.obj₁ = 0 := by
    calc
      h.heartCohClassSum (C := C) b m T.obj₂ -
            h.heartCohClassSum (C := C) b m T.obj₃ -
              h.heartCohClassSum (C := C) (b + 1) m T.obj₁
          = Finset.sum (Finset.range (m + 1))
              (fun j => imgTerm (b + (j : ℤ)) - imgTerm (b + (j : ℤ) + 1)) :=
            hsum
      _ = imgTerm b - imgTerm (b + ((m + 1 : ℕ) : ℤ)) := htel
      _ = 0 := by rw [hm1]; simp [himg_b, himg_a1]
  have hsum_sub :
      h.heartCohClassSum (C := C) b m T.obj₂ -
          h.heartCohClassSum (C := C) b m T.obj₃ =
        h.heartCohClassSum (C := C) (b + 1) m T.obj₁ :=
    sub_eq_zero.mp hsum_zero
  have hsum_eq :
      h.heartCohClassSum (C := C) b m T.obj₂ =
        h.heartCohClassSum (C := C) (b + 1) m T.obj₁ +
          h.heartCohClassSum (C := C) b m T.obj₃ :=
    (sub_eq_iff_eq_add.mp hsum_sub).trans (by ac_rfl)
  calc
    h.heartEulerClassObj (C := C) T.obj₂ =
        h.heartCohClassSum (C := C) b m T.obj₂ := by
          simpa [m] using
            h.heartEulerClassObj_eq_heartCohClassSum (C := C)
              (X := T.obj₂) (b := b) (a := a) hab h₂LE h₂GE
    _ = h.heartCohClassSum (C := C) (b + 1) m T.obj₁ +
          h.heartCohClassSum (C := C) b m T.obj₃ := hsum_eq
    _ = h.heartEulerClassObj (C := C) T.obj₁ +
          h.heartEulerClassObj (C := C) T.obj₃ := by
          congr 1
          · symm
            simpa [hm_shift] using
              h.heartEulerClassObj_eq_heartCohClassSum (C := C)
                (X := T.obj₁) (b := b + 1) (a := a + 1) (by lia) h₁LE h₁GE
          · symm
            exact h.heartEulerClassObj_eq_heartCohClassSum (C := C)
              (X := T.obj₃) (b := b) (a := a) hab h₃LE h₃GE

instance HeartStabilityData.heartEulerClassObj_isTriangleAdditive
    (h : HeartStabilityData C) [IsTriangulated C]
    [Functor.IsHomological (h.H0Functor (C := C))] :
    IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E) where
  additive T hT := by
    let b : ℤ := min (h.lowerBound (C := C) T.obj₂)
      (min (h.lowerBound (C := C) T.obj₃) (h.lowerBound (C := C) T.obj₁ - 1))
    let a : ℤ := max (h.upperBound (C := C) T.obj₂)
      (max (h.upperBound (C := C) T.obj₃) (h.upperBound (C := C) T.obj₁ - 1))
    have hb₂ : b ≤ h.lowerBound (C := C) T.obj₂ := by
      dsimp [b]
      exact min_le_left _ _
    have hb₃ : b ≤ h.lowerBound (C := C) T.obj₃ := by
      dsimp [b]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hb₁ : b ≤ h.lowerBound (C := C) T.obj₁ - 1 := by
      dsimp [b]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have ha₂ : h.upperBound (C := C) T.obj₂ ≤ a := by
      dsimp [a]
      exact le_max_left _ _
    have ha₃ : h.upperBound (C := C) T.obj₃ ≤ a := by
      dsimp [a]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have ha₁ : h.upperBound (C := C) T.obj₁ - 1 ≤ a := by
      dsimp [a]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hab : b ≤ a :=
      le_trans hb₂ <|
        le_trans (h.lowerBound_le_upperBound (C := C) (E := T.obj₂)) ha₂
    have h₁LE : h.t.IsLE T.obj₁ (a + 1) := by
      letI : h.t.IsLE T.obj₁ (h.upperBound (C := C) T.obj₁) := h.isLE_upperBound (C := C) T.obj₁
      have : h.upperBound (C := C) T.obj₁ ≤ a + 1 := by lia
      exact h.t.isLE_of_le T.obj₁ (h.upperBound (C := C) T.obj₁) (a + 1) this
    have h₁GE : h.t.IsGE T.obj₁ (b + 1) := by
      letI : h.t.IsGE T.obj₁ (h.lowerBound (C := C) T.obj₁) := h.isGE_lowerBound (C := C) T.obj₁
      have : b + 1 ≤ h.lowerBound (C := C) T.obj₁ := by lia
      exact h.t.isGE_of_ge T.obj₁ (b + 1) (h.lowerBound (C := C) T.obj₁) this
    have h₂LE : h.t.IsLE T.obj₂ a := by
      letI : h.t.IsLE T.obj₂ (h.upperBound (C := C) T.obj₂) := h.isLE_upperBound (C := C) T.obj₂
      exact h.t.isLE_of_le T.obj₂ (h.upperBound (C := C) T.obj₂) a ha₂
    have h₂GE : h.t.IsGE T.obj₂ b := by
      letI : h.t.IsGE T.obj₂ (h.lowerBound (C := C) T.obj₂) := h.isGE_lowerBound (C := C) T.obj₂
      exact h.t.isGE_of_ge T.obj₂ b (h.lowerBound (C := C) T.obj₂) hb₂
    have h₃LE : h.t.IsLE T.obj₃ a := by
      letI : h.t.IsLE T.obj₃ (h.upperBound (C := C) T.obj₃) := h.isLE_upperBound (C := C) T.obj₃
      exact h.t.isLE_of_le T.obj₃ (h.upperBound (C := C) T.obj₃) a ha₃
    have h₃GE : h.t.IsGE T.obj₃ b := by
      letI : h.t.IsGE T.obj₃ (h.lowerBound (C := C) T.obj₃) := h.isGE_lowerBound (C := C) T.obj₃
      exact h.t.isGE_of_ge T.obj₃ b (h.lowerBound (C := C) T.obj₃) hb₃
    exact h.heartEulerClassObj_triangle_of_bounds (C := C) T hT hab
      h₁LE h₁GE h₂LE h₂GE h₃LE h₃GE

end Proposition53

end CategoryTheory.Triangulated
