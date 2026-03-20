/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.HeartEquivalence.EulerLift

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section Proposition53

variable [IsTriangulated C]


/-! ## Pure/Amplitude Formulas -/

theorem HeartStabilityData.heartCohClass_of_heart_shift
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : h.t.heart.FullSubcategory) (n : ℤ) :
    h.heartCohClass (C := C) n (E.obj⟦(-n : ℤ)⟧) =
      (((-1 : ℤ) ^ Int.natAbs n) • HeartK0.of (C := C) h E) := by
  rw [HeartStabilityData.heartCohClass]
  congr 1
  simpa using HeartK0.of_iso (C := C) h
    (ObjectProperty.isoMk _ (h.heartCohObjIsoOfHeartShift (C := C) E n))

noncomputable def HeartStabilityData.heartCohIso_of_truncLT
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : C) (n a : ℤ) (hna : n < a) :
    h.heartCoh (C := C) n ((h.t.truncLT a).obj E) ≅ h.heartCoh (C := C) n E := by
  have hIsoLE :
      IsIso ((h.t.truncLE n).map ((h.t.truncLTι a).app E)) := by
    simpa [TStructure.truncLE] using
      (h.t.isIso_truncLT_map_truncLTι_app (n + 1) a (by omega) E)
  haveI : IsIso ((h.t.truncGE n).map ((h.t.truncLE n).map ((h.t.truncLTι a).app E))) :=
    Functor.map_isIso (h.t.truncGE n) ((h.t.truncLE n).map ((h.t.truncLTι a).app E))
  have hIso :
      IsIso ((h.t.truncGELE n n).map ((h.t.truncLTι a).app E)) := by
    simpa [TStructure.truncGELE]
  refine ObjectProperty.isoMk _ ?_
  simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
    ((shiftFunctor C n).mapIso
      (asIso ((h.t.truncGELE n n).map ((h.t.truncLTι a).app E))))

theorem HeartStabilityData.heartCohClass_of_truncLT
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : C) (n a : ℤ) (hna : n < a) :
    h.heartCohClass (C := C) n ((h.t.truncLT a).obj E) =
      h.heartCohClass (C := C) n E := by
  rw [HeartStabilityData.heartCohClass]
  congr 1
  exact HeartK0.of_iso (C := C) h (h.heartCohIso_of_truncLT (C := C) E n a hna)

/-- On objects already lying in the heart, the Euler lift is the obvious heart
Grothendieck-group class. -/
theorem HeartStabilityData.heartEulerClassObj_of_heart
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
noncomputable def HeartStabilityData.eulerZObj
    (h : HeartStabilityData C) [IsTriangulated C] (E : C) : ℂ :=
  h.ZOnHeartK0 (C := C) (h.heartEulerClassObj (C := C) E)

theorem HeartStabilityData.eulerZObj_of_heart
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : h.t.heart.FullSubcategory) :
    h.eulerZObj (C := C) E.obj = HeartStabilityData.heartZObj (C := C) h E := by
  simp [HeartStabilityData.eulerZObj, h.heartEulerClassObj_of_heart (C := C) E]

noncomputable def HeartStabilityData.heartK0FromK0
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)] :
    K₀ C →+ HeartK0 (C := C) h :=
  K₀.lift C (fun E ↦ h.heartEulerClassObj (C := C) E)

@[simp]
theorem HeartStabilityData.heartK0FromK0_of
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)]
    (E : C) :
    h.heartK0FromK0 C (K₀.of C E) = h.heartEulerClassObj (C := C) E :=
  K₀.lift_of C (fun E ↦ h.heartEulerClassObj (C := C) E) E

theorem HeartStabilityData.heartK0ToK0_comp_heartK0FromK0
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)] :
    (h.heartK0ToK0 C).comp (h.heartK0FromK0 C) = AddMonoidHom.id (K₀ C) := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro E
  change ((h.heartK0ToK0 C).comp (h.heartK0FromK0 C)) (K₀.of C E) =
    (AddMonoidHom.id (K₀ C)) (K₀.of C E)
  rw [AddMonoidHom.comp_apply, h.heartK0FromK0_of (C := C), AddMonoidHom.id_apply]
  exact h.heartK0ToK0_heartEulerClassObj (C := C) E

theorem HeartStabilityData.heartK0FromK0_comp_heartK0ToK0
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)] :
    (h.heartK0FromK0 C).comp (h.heartK0ToK0 C) = AddMonoidHom.id (HeartK0 (C := C) h) := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro E
  change ((h.heartK0FromK0 C).comp (h.heartK0ToK0 C)) (HeartK0.of (C := C) h E) =
    (AddMonoidHom.id (HeartK0 (C := C) h)) (HeartK0.of (C := C) h E)
  rw [AddMonoidHom.comp_apply, h.heartK0ToK0_of (C := C), h.heartK0FromK0_of (C := C),
    AddMonoidHom.id_apply]
  exact h.heartEulerClassObj_of_heart (C := C) E

/-- If the Euler lift is triangle-additive, the canonical map
`K₀(heart(t)) → K₀(C)` is an equivalence. -/
noncomputable def HeartStabilityData.heartK0EquivK0
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)] :
    HeartK0 (C := C) h ≃+ K₀ C where
  toFun := h.heartK0ToK0 C
  invFun := h.heartK0FromK0 C
  left_inv x := by
    exact congrArg (fun f : HeartK0 (C := C) h →+ HeartK0 (C := C) h => f x)
      (h.heartK0FromK0_comp_heartK0ToK0 (C := C))
  right_inv x := by
    exact congrArg (fun f : K₀ C →+ K₀ C => f x)
      (h.heartK0ToK0_comp_heartK0FromK0 (C := C))
  map_add' x y := by
    simp

instance HeartStabilityData.eulerZObj_isTriangleAdditive
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)] :
    IsTriangleAdditive (fun E ↦ h.eulerZObj (C := C) E) where
  additive T hT := by
    simpa [HeartStabilityData.eulerZObj, map_add] using
      congrArg (h.ZOnHeartK0 (C := C))
        (IsTriangleAdditive.additive (f := fun E ↦ h.heartEulerClassObj (C := C) E) T hT)

/-- If the Euler lift is triangle-additive, the heart central charge extends to an
ambient homomorphism `K₀(C) →+ ℂ`. -/
noncomputable def HeartStabilityData.ambientZ
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)] :
    K₀ C →+ ℂ :=
  K₀.lift C (fun E ↦ h.eulerZObj (C := C) E)

@[simp]
theorem HeartStabilityData.ambientZ_of
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)]
    (E : C) :
    h.ambientZ C (K₀.of C E) = h.eulerZObj (C := C) E :=
  K₀.lift_of C (fun E ↦ h.eulerZObj (C := C) E) E

theorem HeartStabilityData.ambientZ_eq_ZOnHeartK0_comp_heartK0FromK0
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)] :
    h.ambientZ C = (h.ZOnHeartK0 (C := C)).comp (h.heartK0FromK0 C) := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro E
  change h.ambientZ C (K₀.of C E) =
    ((h.ZOnHeartK0 (C := C)).comp (h.heartK0FromK0 C)) (K₀.of C E)
  rw [h.ambientZ_of (C := C), AddMonoidHom.comp_apply, h.heartK0FromK0_of (C := C)]
  rfl

theorem HeartStabilityData.ambientZ_comp_heartK0ToK0
    (h : HeartStabilityData C) [IsTriangulated C]
    [IsTriangleAdditive (fun E ↦ h.heartEulerClassObj (C := C) E)] :
    (h.ambientZ C).comp (h.heartK0ToK0 C) = h.ZOnHeartK0 (C := C) := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro E
  change ((h.ambientZ C).comp (h.heartK0ToK0 C)) (HeartK0.of (C := C) h E) =
    (h.ZOnHeartK0 (C := C)) (HeartK0.of (C := C) h E)
  rw [AddMonoidHom.comp_apply, h.heartK0ToK0_of (C := C), h.ambientZ_of (C := C),
    h.eulerZObj_of_heart (C := C) E, h.ZOnHeartK0_of (C := C) E]

theorem HeartStabilityData.ZOnHeartK0_heartCohClass
    (h : HeartStabilityData C) [IsTriangulated C] (n : ℤ) (E : C) :
    h.ZOnHeartK0 (C := C) (h.heartCohClass (C := C) n E) =
      (((-1 : ℤ) ^ Int.natAbs n) •
        HeartStabilityData.heartZObj (C := C) h (h.heartCoh (C := C) n E)) := by
  rw [HeartStabilityData.heartCohClass, map_zsmul, h.ZOnHeartK0_of (C := C)]

/-- If a distinguished triangle is concentrated in a single `t`-degree `n`, then after
shifting by `n` it yields the expected short exact relation in the heart Grothendieck
group. -/
theorem HeartStabilityData.heartK0_relation_of_pure_distTriang
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

theorem HeartStabilityData.heartCohClass_eq_zero_of_lt_bound
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

theorem HeartStabilityData.heartCohClass_eq_zero_of_lt_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {m n : ℤ} (hmn : m < n)
    (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.heartCohClass (C := C) m X = 0 :=
  h.heartCohClass_eq_zero_of_lt_bound (C := C) hmn hGE

theorem HeartStabilityData.heartCohClass_eq_zero_of_gt_bound
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

theorem HeartStabilityData.heartCohClass_eq_zero_of_gt_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {m n : ℤ} (hmn : n < m)
    (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.heartCohClass (C := C) m X = 0 :=
  h.heartCohClass_eq_zero_of_gt_bound (C := C) hmn hLE

theorem HeartStabilityData.heartCohClassSum_eq_zero_of_lt_bound
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

theorem HeartStabilityData.heartCohClassSum_eq_zero_of_gt_bound
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

theorem HeartStabilityData.heartCohClass_eq_zero_of_isZero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} (hX : IsZero X) (n : ℤ) :
    h.heartCohClass (C := C) n X = 0 := by
  have hzeroObj : IsZero ((h.t.truncGELE n n).obj X) :=
    (h.t.truncGELE n n).map_isZero hX
  have hzeroHeart : IsZero (h.heartCoh (C := C) n X) := by
    refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      (shiftFunctor C n).map_isZero hzeroObj
  rw [HeartStabilityData.heartCohClass]
  simp [HeartK0.of_isZero (C := C) h hzeroHeart]

theorem HeartStabilityData.heartCohClassSum_eq_zero_of_isZero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} (hX : IsZero X) (b : ℤ) (n : ℕ) :
    h.heartCohClassSum (C := C) b n X = 0 := by
  rw [HeartStabilityData.heartCohClassSum]
  refine Finset.sum_eq_zero ?_
  intro j hj
  exact h.heartCohClass_eq_zero_of_isZero (C := C) hX _

  private theorem HeartStabilityData.heartCohClassSum_succ_lower
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {b a : ℤ} (hba : b < a) (hGE : h.t.IsGE X (b + 1)) :
    h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X =
      h.heartCohClassSum (C := C) (b + 1) (Int.toNat (a - (b + 1))) X := by
  have hnat : Int.toNat (a - b) = Int.toNat (a - (b + 1)) + 1 := by
    omega
  rw [hnat, HeartStabilityData.heartCohClassSum, Finset.sum_range_succ']
  have hzero : h.heartCohClass (C := C) b X = 0 := by
    exact h.heartCohClass_eq_zero_of_lt_bound (C := C) (X := X) (m := b) (n := b + 1)
      (by omega) hGE
  simp [HeartStabilityData.heartCohClassSum, hzero, add_assoc, add_left_comm, add_comm]

theorem HeartStabilityData.heartCohClassSum_pred_upper
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {b a : ℤ} (hba : b < a) (hLE : h.t.IsLE X (a - 1)) :
    h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X =
      h.heartCohClassSum (C := C) b (Int.toNat ((a - 1) - b)) X := by
  have hnat : Int.toNat (a - b) = Int.toNat ((a - 1) - b) + 1 := by
    omega
  have hdeg : b + (1 + max (a - 1 - b) 0) = a := by
    have hnonneg : 0 ≤ a - 1 - b := by omega
    rw [max_eq_left hnonneg]
    omega
  rw [hnat, HeartStabilityData.heartCohClassSum, Finset.sum_range_succ]
  have hzero : h.heartCohClass (C := C) a X = 0 := by
    exact h.heartCohClass_eq_zero_of_gt_bound (C := C) (X := X) (m := a) (n := a - 1)
      (by omega) hLE
  have hzero' :
      h.heartCohClass (C := C) (b + (max (a - 1 - b) 0 + 1)) X = 0 := by
    simpa [hdeg, add_assoc, add_left_comm, add_comm] using hzero
  simp [HeartStabilityData.heartCohClassSum, hzero']

theorem HeartStabilityData.heartCohClassSum_shrink_lower
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {c b a : ℤ} (hcb : c ≤ b) (hba : b ≤ a) (hGE : h.t.IsGE X b) :
    h.heartCohClassSum (C := C) c (Int.toNat (a - c)) X =
      h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X := by
  have hnonneg : 0 ≤ b - c := by omega
  let m : ℕ := Int.toNat (b - c)
  have hm : c + (m : ℤ) = b := by
    dsimp [m]
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  have haux :
      ∀ {d : ℤ} (n : ℕ), d + (n : ℤ) = b →
        h.heartCohClassSum (C := C) d (Int.toNat (a - d)) X =
          h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X := by
    intro d n
    induction n generalizing d with
    | zero =>
        intro hd
        have hEq : d = b := by omega
        subst hEq
        simp
    | succ n ihn =>
        intro hd
        have hlt : d < a := by omega
        have hGE' : h.t.IsGE X (d + 1) := h.t.isGE_of_ge X (d + 1) b (by omega)
        calc
          h.heartCohClassSum (C := C) d (Int.toNat (a - d)) X
              = h.heartCohClassSum (C := C) (d + 1) (Int.toNat (a - (d + 1))) X :=
                h.heartCohClassSum_succ_lower (C := C) (X := X) (b := d) (a := a) hlt hGE'
          _ = h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X :=
                ihn (by omega)
  exact haux m hm

theorem HeartStabilityData.heartCohClassSum_shrink_upper
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {b a c : ℤ} (hba : b ≤ a) (hac : a ≤ c) (hLE : h.t.IsLE X a) :
    h.heartCohClassSum (C := C) b (Int.toNat (c - b)) X =
      h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X := by
  have hnonneg : 0 ≤ c - a := by omega
  let m : ℕ := Int.toNat (c - a)
  have hm : a + (m : ℤ) = c := by
    dsimp [m]
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  have haux :
      ∀ {d : ℤ} (n : ℕ), a + (n : ℤ) = d →
        h.heartCohClassSum (C := C) b (Int.toNat (d - b)) X =
          h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X := by
    intro d n
    induction n generalizing d with
    | zero =>
        intro hd
        have hEq : d = a := by omega
        subst hEq
        simp
    | succ n ihn =>
        intro hd
        have hlt : b < d := by omega
        have hLE' : h.t.IsLE X (d - 1) := h.t.isLE_of_le X a (d - 1) (by omega)
        calc
          h.heartCohClassSum (C := C) b (Int.toNat (d - b)) X
              = h.heartCohClassSum (C := C) b (Int.toNat ((d - 1) - b)) X :=
                h.heartCohClassSum_pred_upper (C := C) (X := X) (b := b) (a := d) hlt hLE'
          _ = h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X :=
                ihn (by omega)
  exact haux m hm

theorem HeartStabilityData.heartCohClassSum_eq_of_bounds
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {b₁ a₁ b₂ a₂ : ℤ}
    (h₁ : b₁ ≤ a₁) (h₂ : b₂ ≤ a₂)
    (hLE₁ : h.t.IsLE X a₁) (hGE₁ : h.t.IsGE X b₁)
    (hLE₂ : h.t.IsLE X a₂) (hGE₂ : h.t.IsGE X b₂) :
    h.heartCohClassSum (C := C) b₁ (Int.toNat (a₁ - b₁)) X =
      h.heartCohClassSum (C := C) b₂ (Int.toNat (a₂ - b₂)) X := by
  let b := min b₁ b₂
  let a := max a₁ a₂
  have hb₁ : b ≤ b₁ := by dsimp [b]; exact min_le_left _ _
  have hb₂ : b ≤ b₂ := by dsimp [b]; exact min_le_right _ _
  have ha₁ : a₁ ≤ a := by dsimp [a]; exact le_max_left _ _
  have ha₂ : a₂ ≤ a := by dsimp [a]; exact le_max_right _ _
  have henv₁ :
      h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X =
        h.heartCohClassSum (C := C) b₁ (Int.toNat (a₁ - b₁)) X := by
    calc
      h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X
          = h.heartCohClassSum (C := C) b₁ (Int.toNat (a - b₁)) X :=
            h.heartCohClassSum_shrink_lower (C := C) (X := X) hb₁
              (show b₁ ≤ a by exact le_trans h₁ ha₁) hGE₁
      _ = h.heartCohClassSum (C := C) b₁ (Int.toNat (a₁ - b₁)) X :=
            h.heartCohClassSum_shrink_upper (C := C) (X := X) h₁ ha₁ hLE₁
  have henv₂ :
      h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X =
        h.heartCohClassSum (C := C) b₂ (Int.toNat (a₂ - b₂)) X := by
    calc
      h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X
          = h.heartCohClassSum (C := C) b₂ (Int.toNat (a - b₂)) X :=
            h.heartCohClassSum_shrink_lower (C := C) (X := X) hb₂
              (show b₂ ≤ a by exact le_trans h₂ ha₂) hGE₂
      _ = h.heartCohClassSum (C := C) b₂ (Int.toNat (a₂ - b₂)) X :=
            h.heartCohClassSum_shrink_upper (C := C) (X := X) h₂ ha₂ hLE₂
  exact henv₁.symm.trans henv₂

theorem HeartStabilityData.heartCohClassSum_of_truncLT
    (h : HeartStabilityData C) [IsTriangulated C]
    {E : C} {b a : ℤ} (hba : b < a) :
    h.heartCohClassSum (C := C) b (Int.toNat ((a - 1) - b)) ((h.t.truncLT a).obj E) =
      h.heartCohClassSum (C := C) b (Int.toNat ((a - 1) - b)) E := by
  have hnonneg : 0 ≤ (a - 1) - b := by omega
  rw [HeartStabilityData.heartCohClassSum, HeartStabilityData.heartCohClassSum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjle_nat : j ≤ Int.toNat ((a - 1) - b) :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjle' : (j : ℤ) ≤ Int.toNat ((a - 1) - b) := by
    exact_mod_cast hjle_nat
  have hjle : (j : ℤ) ≤ (a - 1) - b := by
    rw [Int.toNat_of_nonneg hnonneg] at hjle'
    exact hjle'
  have hjlt : b + (j : ℤ) < a := by omega
  simpa using h.heartCohClass_of_truncLT (C := C) E (b + (j : ℤ)) a hjlt

theorem HeartStabilityData.heartEulerClassObj_eq_heartCohClassSum
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {b a : ℤ} (hab : b ≤ a) (hLE : h.t.IsLE X a) (hGE : h.t.IsGE X b) :
    h.heartEulerClassObj (C := C) X =
      h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X := by
  classical
  let a₀ := h.upperBound (C := C) X
  let b₀ := h.lowerBound (C := C) X
  have hLE₀ : h.t.IsLE X a₀ := h.isLE_upperBound (C := C) X
  have hGE₀ : h.t.IsGE X b₀ := h.isGE_lowerBound (C := C) X
  by_cases h₀ : b₀ ≤ a₀
  · have hEq :=
      h.heartCohClassSum_eq_of_bounds (C := C) (X := X)
        (b₁ := b₀) (a₁ := a₀) (b₂ := b) (a₂ := a) h₀ hab hLE₀ hGE₀ hLE hGE
    simpa [HeartStabilityData.heartEulerClassObj, a₀, b₀, h₀] using hEq
  · have hzero : IsZero X := h.t.isZero X a₀ b₀ (by omega)
    rw [HeartStabilityData.heartEulerClassObj, dif_neg h₀]
    symm
    exact h.heartCohClassSum_eq_zero_of_isZero (C := C) hzero b (Int.toNat (a - b))

theorem HeartStabilityData.heartEulerClassObj_eq_zero_of_isZero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} (hX : IsZero X) :
    h.heartEulerClassObj (C := C) X = 0 := by
  have hLE : h.t.IsLE X 0 := h.t.isLE_of_isZero hX 0
  have hGE : h.t.IsGE X 0 := h.t.isGE_of_isZero hX 0
  rw [h.heartEulerClassObj_eq_heartCohClassSum (C := C) (X := X) (b := 0) (a := 0)
    le_rfl hLE hGE]
  simpa using h.heartCohClassSum_eq_zero_of_isZero (C := C) hX 0 0

theorem HeartStabilityData.eulerZObj_eq_zero_of_isZero
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} (hX : IsZero X) :
    h.eulerZObj (C := C) X = 0 := by
  rw [HeartStabilityData.eulerZObj, h.heartEulerClassObj_eq_zero_of_isZero (C := C) hX, map_zero]

theorem HeartStabilityData.heartEulerClassObj_eq_truncLT_add_heartCohClass
    (h : HeartStabilityData C) [IsTriangulated C]
    {E : C} {b a : ℤ} (hba : b < a) (hLE : h.t.IsLE E a) (hGE : h.t.IsGE E b) :
    h.heartEulerClassObj (C := C) E =
      h.heartEulerClassObj (C := C) ((h.t.truncLT a).obj E) +
        h.heartCohClass (C := C) a E := by
  have hnonneg : 0 ≤ (a - 1) - b := by omega
  have hnat : Int.toNat (a - b) = Int.toNat ((a - 1) - b) + 1 := by omega
  have hdeg' : b + (a - 1 - b + 1) = a := by omega
  calc
    h.heartEulerClassObj (C := C) E
        = h.heartCohClassSum (C := C) b (Int.toNat (a - b)) E := by
            exact h.heartEulerClassObj_eq_heartCohClassSum (C := C) (X := E)
              (show b ≤ a by omega) hLE hGE
    _ = h.heartCohClassSum (C := C) b (Int.toNat ((a - 1) - b)) E +
          h.heartCohClass (C := C) a E := by
            rw [hnat, HeartStabilityData.heartCohClassSum,
              HeartStabilityData.heartCohClassSum, Finset.sum_range_succ]
            simp [Int.toNat_of_nonneg hnonneg, hdeg']
    _ = h.heartCohClassSum (C := C) b (Int.toNat ((a - 1) - b)) ((h.t.truncLT a).obj E) +
          h.heartCohClass (C := C) a E := by
            rw [h.heartCohClassSum_of_truncLT (C := C) (E := E) hba]
    _ = h.heartEulerClassObj (C := C) ((h.t.truncLT a).obj E) +
          h.heartCohClass (C := C) a E := by
            congr 1
            exact (h.heartEulerClassObj_eq_heartCohClassSum (C := C)
              (X := (h.t.truncLT a).obj E) (b := b) (a := a - 1) (by omega)
              inferInstance inferInstance).symm

theorem HeartStabilityData.eulerZObj_eq_truncLT_add_heartCohClass
    (h : HeartStabilityData C) [IsTriangulated C]
    {E : C} {b a : ℤ} (hba : b < a) (hLE : h.t.IsLE E a) (hGE : h.t.IsGE E b) :
    h.eulerZObj (C := C) E =
      h.eulerZObj (C := C) ((h.t.truncLT a).obj E) +
        h.ZOnHeartK0 (C := C) (h.heartCohClass (C := C) a E) := by
  unfold HeartStabilityData.eulerZObj
  rw [h.heartEulerClassObj_eq_truncLT_add_heartCohClass (C := C) hba hLE hGE, map_add]

theorem HeartStabilityData.heartCohClassSum_eq_single_of_pure
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

theorem HeartStabilityData.heartCohClassSum_eq_top_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {a b : ℤ} (hab : b ≤ a)
    (hLE : h.t.IsLE X a) (hGE : h.t.IsGE X a) :
    h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X =
      h.heartCohClass (C := C) a X := by
  refine h.heartCohClassSum_eq_single_of_pure (C := C) (X := X) (n := a) (b := b)
    (m := Int.toNat (a - b)) hLE hGE hab ?_
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
  omega

theorem HeartStabilityData.ZOnHeartK0_heartCohClassSum_eq_top_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {a b : ℤ} (hab : b ≤ a)
    (hLE : h.t.IsLE X a) (hGE : h.t.IsGE X a) :
    h.ZOnHeartK0 (C := C) (h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X) =
      h.ZOnHeartK0 (C := C) (h.heartCohClass (C := C) a X) := by
  exact congrArg (h.ZOnHeartK0 (C := C))
    (h.heartCohClassSum_eq_top_of_pure (C := C) hab hLE hGE)

theorem HeartStabilityData.ZOnHeartK0_heartCohClassSum_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {a b : ℤ} (hab : b ≤ a)
    (hLE : h.t.IsLE X a) (hGE : h.t.IsGE X a) :
    h.ZOnHeartK0 (C := C) (h.heartCohClassSum (C := C) b (Int.toNat (a - b)) X) =
      (((-1 : ℤ) ^ Int.natAbs a) •
        HeartStabilityData.heartZObj (C := C) h (h.heartCoh (C := C) a X)) := by
  rw [h.ZOnHeartK0_heartCohClassSum_eq_top_of_pure (C := C) hab hLE hGE,
    h.ZOnHeartK0_heartCohClass (C := C) a X]

theorem HeartStabilityData.heartEulerClassObj_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {n : ℤ} (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.heartEulerClassObj (C := C) X = h.heartCohClass (C := C) n X := by
  rw [h.heartEulerClassObj_eq_heartCohClassSum (C := C) (X := X) (a := n) (b := n)
    le_rfl hLE hGE]
  simpa using h.heartCohClassSum_eq_top_of_pure (C := C) (X := X)
    (a := n) (b := n) le_rfl hLE hGE

noncomputable def HeartStabilityData.heartCohIso_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {n : ℤ} (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.heartCoh (C := C) n X ≅ h.heartShiftOfPure (C := C) n hLE hGE := by
  let eLE : (h.t.truncLE n).obj X ≅ X :=
    @asIso _ _ _ _ ((h.t.truncLEι n).app X) ((h.t.isLE_iff_isIso_truncLEι_app n X).mp hLE)
  let eGE : X ≅ (h.t.truncGE n).obj X :=
    @asIso _ _ _ _ ((h.t.truncGEπ n).app X) ((h.t.isGE_iff_isIso_truncGEπ_app n X).mp hGE)
  let e : (h.t.truncGELE n n).obj X ≅ X :=
    (h.t.truncGE n).mapIso eLE ≪≫ eGE.symm
  refine ObjectProperty.isoMk _ ?_
  simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
    ((shiftFunctor C n).mapIso e)

theorem HeartStabilityData.heartCohClass_eq_pureClass
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {n : ℤ} (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.heartCohClass (C := C) n X =
      (((-1 : ℤ) ^ Int.natAbs n) •
        HeartK0.of (C := C) h (h.heartShiftOfPure (C := C) n hLE hGE)) := by
  rw [HeartStabilityData.heartCohClass]
  congr 1
  exact HeartK0.of_iso (C := C) h (h.heartCohIso_of_pure (C := C) hLE hGE)

noncomputable def HeartStabilityData.heartCohIso_of_truncGE_of_isLE
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : C) (a : ℤ) (hLE : h.t.IsLE E a) :
    h.heartCoh (C := C) a ((h.t.truncGE a).obj E) ≅ h.heartCoh (C := C) a E := by
  let P := (h.t.truncGE a).obj E
  have hPLE : h.t.IsLE P a := by infer_instance
  have hIsoE :
      IsIso ((h.t.truncGE a).map ((h.t.truncLEι a).app E)) := by
    exact Functor.map_isIso (h.t.truncGE a) ((h.t.truncLEι a).app E)
  have hIsoP₁ :
      IsIso ((h.t.truncGE a).map ((h.t.truncLEι a).app P)) := by
    exact Functor.map_isIso (h.t.truncGE a) ((h.t.truncLEι a).app P)
  have hIsoP₂ :
      IsIso ((h.t.truncGE a).map ((h.t.truncGEπ a).app E)) := by
    infer_instance
  let eE : ((h.t.truncGELE a a).obj E) ≅ P := by
    simpa [P, TStructure.truncGELE] using
      (asIso ((h.t.truncGE a).map ((h.t.truncLEι a).app E)))
  let eP : ((h.t.truncGELE a a).obj P) ≅ P := by
    simpa [P, TStructure.truncGELE] using
      ((asIso ((h.t.truncGE a).map ((h.t.truncLEι a).app P))) ≪≫
        (asIso ((h.t.truncGE a).map ((h.t.truncGEπ a).app E))).symm)
  refine ObjectProperty.isoMk _ ?_
  simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure, P] using
    ((shiftFunctor C a).mapIso eP ≪≫ ((shiftFunctor C a).mapIso eE).symm)

theorem HeartStabilityData.heartCohClass_of_truncGE_of_isLE
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : C) (a : ℤ) (hLE : h.t.IsLE E a) :
    h.heartCohClass (C := C) a ((h.t.truncGE a).obj E) =
      h.heartCohClass (C := C) a E := by
  rw [HeartStabilityData.heartCohClass]
  congr 1
  exact HeartK0.of_iso (C := C) h
    (h.heartCohIso_of_truncGE_of_isLE (C := C) E a hLE)

theorem HeartStabilityData.heartEulerClassObj_of_truncGE_of_isLE
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : C) (a : ℤ) (hLE : h.t.IsLE E a) :
    h.heartEulerClassObj (C := C) ((h.t.truncGE a).obj E) =
      h.heartCohClass (C := C) a E := by
  let P := (h.t.truncGE a).obj E
  have hPLE : h.t.IsLE P a := by infer_instance
  have hPGE : h.t.IsGE P a := by infer_instance
  rw [h.heartEulerClassObj_of_pure (C := C) (X := P) hPLE hPGE,
    h.heartCohClass_of_truncGE_of_isLE (C := C) E a hLE]

theorem HeartStabilityData.heartEulerClassObj_eq_truncLT_add_truncGE
    (h : HeartStabilityData C) [IsTriangulated C]
    {E : C} {b a : ℤ} (hba : b < a) (hLE : h.t.IsLE E a) (hGE : h.t.IsGE E b) :
    h.heartEulerClassObj (C := C) E =
      h.heartEulerClassObj (C := C) ((h.t.truncLT a).obj E) +
        h.heartEulerClassObj (C := C) ((h.t.truncGE a).obj E) := by
  rw [h.heartEulerClassObj_eq_truncLT_add_heartCohClass (C := C) hba hLE hGE,
    h.heartEulerClassObj_of_truncGE_of_isLE (C := C) E a hLE]

theorem HeartStabilityData.eulerZObj_eq_truncLT_add_truncGE
    (h : HeartStabilityData C) [IsTriangulated C]
    {E : C} {b a : ℤ} (hba : b < a) (hLE : h.t.IsLE E a) (hGE : h.t.IsGE E b) :
    h.eulerZObj (C := C) E =
      h.eulerZObj (C := C) ((h.t.truncLT a).obj E) +
        h.eulerZObj (C := C) ((h.t.truncGE a).obj E) := by
  rw [h.eulerZObj_eq_truncLT_add_heartCohClass (C := C) hba hLE hGE]
  simp [HeartStabilityData.eulerZObj,
    h.heartEulerClassObj_of_truncGE_of_isLE (C := C) E a hLE]

theorem HeartStabilityData.heartEulerClassObj_of_heart_shift
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : h.t.heart.FullSubcategory) (n : ℤ) :
    h.heartEulerClassObj (C := C) (E.obj⟦(-n : ℤ)⟧) =
      (((-1 : ℤ) ^ Int.natAbs n) • HeartK0.of (C := C) h E) := by
  have hE' := (h.t.mem_heart_iff E.obj).mp E.property
  letI : h.t.IsLE E.obj 0 := hE'.1
  letI : h.t.IsGE E.obj 0 := hE'.2
  have hLE : h.t.IsLE (E.obj⟦(-n : ℤ)⟧) n := by
    simpa using (h.t.isLE_shift E.obj 0 (-n : ℤ) n (by omega))
  have hGE : h.t.IsGE (E.obj⟦(-n : ℤ)⟧) n := by
    simpa using (h.t.isGE_shift E.obj 0 (-n : ℤ) n (by omega))
  rw [h.heartEulerClassObj_of_pure (C := C) (X := E.obj⟦(-n : ℤ)⟧) hLE hGE]
  exact h.heartCohClass_of_heart_shift (C := C) E n

theorem HeartStabilityData.eulerZObj_of_pure
    (h : HeartStabilityData C) [IsTriangulated C]
    {X : C} {n : ℤ} (hLE : h.t.IsLE X n) (hGE : h.t.IsGE X n) :
    h.eulerZObj (C := C) X =
      (((-1 : ℤ) ^ Int.natAbs n) •
        HeartStabilityData.heartZObj (C := C) h (h.heartCoh (C := C) n X)) := by
  rw [HeartStabilityData.eulerZObj, h.heartEulerClassObj_of_pure (C := C) (X := X) hLE hGE,
    h.ZOnHeartK0_heartCohClass (C := C) n X]

theorem HeartStabilityData.heartEulerClassObj_triangle_of_pure_distTriang
    (h : HeartStabilityData C) [IsTriangulated C]
    {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧}
    (n : ℤ) (hT : Triangle.mk f g δ ∈ distTriang C)
    (h₁LE : h.t.IsLE X₁ n) (h₁GE : h.t.IsGE X₁ n)
    (h₂LE : h.t.IsLE X₂ n) (h₂GE : h.t.IsGE X₂ n)
    (h₃LE : h.t.IsLE X₃ n) (h₃GE : h.t.IsGE X₃ n) :
    h.heartEulerClassObj (C := C) X₂ =
      h.heartEulerClassObj (C := C) X₁ + h.heartEulerClassObj (C := C) X₃ := by
  rw [h.heartEulerClassObj_of_pure (C := C) (X := X₂) h₂LE h₂GE,
    h.heartCohClass_eq_pureClass (C := C) h₂LE h₂GE,
    h.heartEulerClassObj_of_pure (C := C) (X := X₁) h₁LE h₁GE,
    h.heartCohClass_eq_pureClass (C := C) h₁LE h₁GE,
    h.heartEulerClassObj_of_pure (C := C) (X := X₃) h₃LE h₃GE,
    h.heartCohClass_eq_pureClass (C := C) h₃LE h₃GE]
  exact h.heartK0_relation_of_pure_distTriang (C := C)
    (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) (f := f) (g := g) (δ := δ)
    n hT h₁LE h₁GE h₂LE h₂GE h₃LE h₃GE

theorem HeartStabilityData.eulerZObj_triangle_of_pure_distTriang
    (h : HeartStabilityData C) [IsTriangulated C]
    {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧}
    (n : ℤ) (hT : Triangle.mk f g δ ∈ distTriang C)
    (h₁LE : h.t.IsLE X₁ n) (h₁GE : h.t.IsGE X₁ n)
    (h₂LE : h.t.IsLE X₂ n) (h₂GE : h.t.IsGE X₂ n)
    (h₃LE : h.t.IsLE X₃ n) (h₃GE : h.t.IsGE X₃ n) :
    h.eulerZObj (C := C) X₂ =
      h.eulerZObj (C := C) X₁ + h.eulerZObj (C := C) X₃ := by
  rw [HeartStabilityData.eulerZObj, h.heartEulerClassObj_of_pure (C := C) (X := X₂) h₂LE h₂GE,
    h.heartCohClass_eq_pureClass (C := C) h₂LE h₂GE, map_zsmul,
    HeartStabilityData.eulerZObj, h.heartEulerClassObj_of_pure (C := C) (X := X₁) h₁LE h₁GE,
    h.heartCohClass_eq_pureClass (C := C) h₁LE h₁GE, map_zsmul,
    HeartStabilityData.eulerZObj, h.heartEulerClassObj_of_pure (C := C) (X := X₃) h₃LE h₃GE,
    h.heartCohClass_eq_pureClass (C := C) h₃LE h₃GE, map_zsmul]
  simpa [map_add] using congrArg (h.ZOnHeartK0 (C := C))
    (h.heartK0_relation_of_pure_distTriang (C := C)
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) (f := f) (g := g) (δ := δ)
      n hT h₁LE h₁GE h₂LE h₂GE h₃LE h₃GE)

theorem HeartStabilityData.eulerZObj_of_heart_shift
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : h.t.heart.FullSubcategory) (n : ℤ) :
    h.eulerZObj (C := C) (E.obj⟦(-n : ℤ)⟧) =
      (((-1 : ℤ) ^ Int.natAbs n) • HeartStabilityData.heartZObj (C := C) h E) := by
  rw [HeartStabilityData.eulerZObj, h.heartEulerClassObj_of_heart_shift (C := C) E n,
    map_zsmul, h.ZOnHeartK0_of (C := C)]

theorem HeartStabilityData.eulerZObj_additive_of_heart_shortExact
    (h : HeartStabilityData C) [IsTriangulated C]
    {S : ShortComplex h.t.heart.FullSubcategory} (hS : S.ShortExact) :
    h.eulerZObj (C := C) S.X₂.obj =
      h.eulerZObj (C := C) S.X₁.obj + h.eulerZObj (C := C) S.X₃.obj := by
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  rw [h.eulerZObj_of_heart (C := C) S.X₂, h.eulerZObj_of_heart (C := C) S.X₁,
    h.eulerZObj_of_heart (C := C) S.X₃]
  exact h.Z.additive S hS

theorem TStructure.triangleLTGE_iso_of_amp_negOne_zero
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

noncomputable def HeartStabilityData.heartCoh_negOne_iso_of_amp_negOne_zero
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

noncomputable def HeartStabilityData.heartCoh_zero_iso_of_amp_negOne_zero
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
    (by omega) inferInstance inferInstance]
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
      (by omega) inferInstance inferInstance]
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
    omega
  have hm_shift : Int.toNat ((a + 1) - (b + 1)) = m := by
    dsimp [m]
    omega
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
        (m := b) (n := b + 1) (by omega) h₁GE
    have hmor_zero : (((h.H0Functor (C := C)).shift b).map T.mor₁) = 0 := by
      exact zero_of_source_iso_zero _ hzero.isoZero
    have hclass :
        HeartK0.of (C := C) h
            (Limits.image (((h.H0Functor (C := C)).shift b).map T.mor₁)) = 0 :=
      HeartK0.of_image_eq_zero (C := C) h hmor_zero
    simp [imgTerm, hclass]
  have himg_a1 : imgTerm (a + 1) = 0 := by
    have hzero :
        IsZero (((h.H0Functor (C := C)).shift (a + 1)).obj T.obj₂) :=
      h.isZero_H0Functor_shift_obj_of_gt_bound (C := C) (X := T.obj₂)
        (m := a + 1) (n := a) (by omega) h₂LE
    have hmor_zero : (((h.H0Functor (C := C)).shift (a + 1)).map T.mor₁) = 0 := by
      exact zero_of_target_iso_zero _ hzero.isoZero
    have hclass :
        HeartK0.of (C := C) h
            (Limits.image (((h.H0Functor (C := C)).shift (a + 1)).map T.mor₁)) = 0 :=
      HeartK0.of_image_eq_zero (C := C) h hmor_zero
    simp [imgTerm, hclass]
  have hm1 : b + ((m + 1 : ℕ) : ℤ) = a + 1 := by
    omega
  have hm1' : b + ((m : ℤ) + 1) = a + 1 := by
    omega
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
      _ = 0 := by rw [hm1]; simpa [himg_b, himg_a1]
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
                (X := T.obj₁) (b := b + 1) (a := a + 1) (by omega) h₁LE h₁GE
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
    have hab : b ≤ a := by
      exact le_trans hb₂ <|
        le_trans (h.lowerBound_le_upperBound (C := C) (E := T.obj₂)) ha₂
    have h₁LE : h.t.IsLE T.obj₁ (a + 1) := by
      letI : h.t.IsLE T.obj₁ (h.upperBound (C := C) T.obj₁) := h.isLE_upperBound (C := C) T.obj₁
      have : h.upperBound (C := C) T.obj₁ ≤ a + 1 := by omega
      exact h.t.isLE_of_le T.obj₁ (h.upperBound (C := C) T.obj₁) (a + 1) this
    have h₁GE : h.t.IsGE T.obj₁ (b + 1) := by
      letI : h.t.IsGE T.obj₁ (h.lowerBound (C := C) T.obj₁) := h.isGE_lowerBound (C := C) T.obj₁
      have : b + 1 ≤ h.lowerBound (C := C) T.obj₁ := by omega
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
