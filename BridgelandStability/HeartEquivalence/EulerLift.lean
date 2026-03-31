/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.HeartEquivalence.H0Homological
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Euler Lift and K0 Isomorphism

The heartCohClass map, its five-term relation, the heartCohClassSum
telescoping, and the Euler class lift from the ambient K0 to the heart K0.
Establishes that heartK0ToK0 intertwines the Euler class with the
heart cohomology sum.
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


/-! ## Euler Lift and K₀ Isomorphism -/

/-- The `n`th heart cohomology class of `E`, weighted by the parity sign relating shifts in
`K₀(C)` to classes in `K₀(heart)`. -/
def HeartStabilityData.heartCohClass
    (h : HeartStabilityData C) (n : ℤ) (E : C) : HeartK0 (C := C) h :=
  (((-1 : ℤ) ^ Int.natAbs n) • HeartK0.of (C := C) h (h.heartCoh (C := C) n E))

theorem HeartStabilityData.heartCohClass_eq_H0FunctorShift
    (h : HeartStabilityData C) (n : ℤ) (X : C) :
    h.heartCohClass (C := C) n X =
      (((-1 : ℤ) ^ Int.natAbs n) •
        HeartK0.of (C := C) h (((h.H0Functor (C := C)).shift n).obj X)) := by
  have hIso :
      HeartK0.of (C := C) h (((h.H0Functor (C := C)).shift n).obj X) =
        HeartK0.of (C := C) h (h.heartCoh (C := C) n X) :=
    HeartK0.of_iso (C := C) h (h.H0FunctorShiftObjIsoHeartCoh (C := C) n X)
  rw [HeartStabilityData.heartCohClass, ← hIso]

theorem negOnePow_natAbs_succ (n : ℤ) :
    (-1 : ℤ) ^ Int.natAbs (n + 1) = -((-1 : ℤ) ^ Int.natAbs n) := by
  rw [← Int.coe_negOnePow ℤ (n + 1), Int.negOnePow_succ, ← Int.coe_negOnePow ℤ n]
  simp

theorem HeartStabilityData.heartCohClass_five_term_relation
    (h : HeartStabilityData C)
    [Abelian h.t.heart.FullSubcategory]
    [Functor.IsHomological (h.H0Functor (C := C))]
    (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) :
    h.heartCohClass (C := C) n T.obj₂ -
        h.heartCohClass (C := C) n T.obj₃ -
          h.heartCohClass (C := C) (n + 1) T.obj₁ =
      (((-1 : ℤ) ^ Int.natAbs n) •
        HeartK0.of (C := C) h
          (Limits.image (((h.H0Functor (C := C)).shift n).map T.mor₁))) +
      (((-1 : ℤ) ^ Int.natAbs n) •
        HeartK0.of (C := C) h
          (Limits.image (((h.H0Functor (C := C)).shift (n + 1)).map T.mor₁))) := by
  let s : ℤ := (-1 : ℤ) ^ Int.natAbs n
  have hrel := h.H0Functor_five_term_relation (C := C) T hT n
  have hrel' := congrArg (fun x : HeartK0 (C := C) h => s • x) hrel
  dsimp [s] at hrel'
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    HeartStabilityData.heartCohClass_eq_H0FunctorShift, negOnePow_natAbs_succ,
    zsmul_add, zsmul_neg] using hrel'

/-- The ambient image of the signed heart cohomology class is the class of the
pure truncation `τ^[n,n]E`. -/
theorem HeartStabilityData.heartK0ToK0_heartCohClass
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
      K₀.of C ((X⟦(n : ℤ)⟧)⟦(-n : ℤ)⟧) = K₀.of C (X⟦(0 : ℤ)⟧) :=
        (K₀.of_iso C ((shiftFunctorAdd' C (n : ℤ) (-n : ℤ) 0 (by lia)).app X)).symm
      _ = K₀.of C X := K₀.of_iso C ((shiftFunctorZero C ℤ).app X)
  rw [hX] at hshift
  simpa [X, H, HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure]
    using hshift.symm

/-- One-step telescoping for the bounded truncations: passing from `τ≤(n-1)E` to
`τ≤nE` adds exactly the degree-`n` pure truncation. -/
theorem HeartStabilityData.k0_truncLE_step
    (h : HeartStabilityData C) [IsTriangulated C] (n : ℤ) (E : C) :
    K₀.of C ((h.t.truncLE n).obj E) =
      K₀.of C ((h.t.truncLE (n - 1)).obj E) +
        h.heartK0ToK0 C (h.heartCohClass (C := C) n E) := by
  have htri :=
    K₀.of_triangle C ((h.t.triangleLTLTGELT n (n + 1) (by lia)).obj E)
      (h.t.triangleLTLTGELT_distinguished n (n + 1) (by lia) E)
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
def HeartStabilityData.heartCohClassSum
    (h : HeartStabilityData C) (b : ℤ) (n : ℕ) (E : C) : HeartK0 (C := C) h :=
  Finset.sum (Finset.range (n + 1)) (fun j =>
    h.heartCohClass (C := C) (b + (j : ℤ)) E)

@[simp]
theorem HeartStabilityData.heartCohClassSum_succ
    (h : HeartStabilityData C) (b : ℤ) (n : ℕ) (E : C) :
    h.heartCohClassSum (C := C) b (n + 1) E =
      h.heartCohClassSum (C := C) b n E +
        h.heartCohClass (C := C) (b + ((n + 1 : ℕ) : ℤ)) E := by
  rw [HeartStabilityData.heartCohClassSum, HeartStabilityData.heartCohClassSum,
    Finset.sum_range_succ]


/-- Telescoping formula for the classes of bounded truncations: if `E` is
concentrated in degrees `≥ b`, then `τ≤(b+n)E` is the sum of the heart
cohomology classes in degrees `b, …, b+n`. -/
theorem HeartStabilityData.heartK0ToK0_heartCohClassSum_truncLE
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
        exact h.t.isZero_truncLE_obj_of_isGE (b - 1) b (by lia) E
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
theorem HeartStabilityData.heartK0ToK0_heartCohClassSum
    (h : HeartStabilityData C) [IsTriangulated C]
    {E : C} (a b : ℤ) (hab : b ≤ a) (hLE : h.t.IsLE E a) (hGE : h.t.IsGE E b) :
    h.heartK0ToK0 C (h.heartCohClassSum (C := C) b (Int.toNat (a - b)) E) = K₀.of C E := by
  have hsum :=
    h.heartK0ToK0_heartCohClassSum_truncLE (C := C) b (Int.toNat (a - b)) (E := E) hGE
  have ha : b + (Int.toNat (a - b) : ℤ) = a := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    lia
  rw [ha] at hsum
  have hτ : K₀.of C ((h.t.truncLE a).obj E) = K₀.of C E := by
    have hIso : IsIso ((h.t.truncLEι a).app E) :=
      (h.t.isLE_iff_isIso_truncLEι_app a E).mp hLE
    let e : (h.t.truncLE a).obj E ≅ E := @asIso _ _ _ _ ((h.t.truncLEι a).app E) hIso
    exact K₀.of_iso C e
  exact hsum.trans hτ

/-- A classical choice of an upper bound for an object with respect to the bounded
t-structure. -/
noncomputable def HeartStabilityData.upperBound
    (h : HeartStabilityData C) (E : C) : ℤ := by
  classical
  exact if hE : h.t.heart E then 0 else Classical.choose (h.bounded E)

/-- A classical choice of a lower bound for an object with respect to the bounded
t-structure. -/
noncomputable def HeartStabilityData.lowerBound
    (h : HeartStabilityData C) (E : C) : ℤ := by
  classical
  exact if hE : h.t.heart E then 0 else Classical.choose (Classical.choose_spec (h.bounded E))

theorem HeartStabilityData.isLE_upperBound
    (h : HeartStabilityData C) (E : C) :
    h.t.IsLE E (h.upperBound (C := C) E) := by
  classical
  by_cases hE : h.t.heart E
  · simpa [HeartStabilityData.upperBound, hE] using ((h.t.mem_heart_iff E).mp hE).1
  · simpa [HeartStabilityData.upperBound, hE] using
      (⟨(Classical.choose_spec (Classical.choose_spec (h.bounded E))).1⟩ :
        h.t.IsLE E (Classical.choose (h.bounded E)))

theorem HeartStabilityData.isGE_lowerBound
    (h : HeartStabilityData C) (E : C) :
    h.t.IsGE E (h.lowerBound (C := C) E) := by
  classical
  by_cases hE : h.t.heart E
  · simpa [HeartStabilityData.lowerBound, hE] using ((h.t.mem_heart_iff E).mp hE).2
  · simpa [HeartStabilityData.lowerBound, hE] using
      (⟨(Classical.choose_spec (Classical.choose_spec (h.bounded E))).2⟩ :
        h.t.IsGE E (Classical.choose (Classical.choose_spec (h.bounded E))))

theorem HeartStabilityData.lowerBound_le_upperBound
    (h : HeartStabilityData C) (E : C) :
    h.lowerBound (C := C) E ≤ h.upperBound (C := C) E := by
  classical
  by_cases hE : h.t.heart E
  · simp [HeartStabilityData.lowerBound, HeartStabilityData.upperBound, hE]
  · by_contra hlt
    have hLE : h.t.IsLE E (h.upperBound (C := C) E) := h.isLE_upperBound (C := C) E
    have hGE : h.t.IsGE E (h.lowerBound (C := C) E) := h.isGE_lowerBound (C := C) E
    have hzero : IsZero E := h.t.isZero E (h.upperBound (C := C) E) (h.lowerBound (C := C) E)
      (by lia)
    have hzero_heart : h.t.heart E := by
      have h0 : h.t.heart (0 : C) := by
        rw [h.t.mem_heart_iff]
        constructor <;> infer_instance
      exact (h.t.heart).prop_of_iso hzero.isoZero.symm h0
    exact hE hzero_heart

/-- The canonical object-level lift of `[E]` to `K₀(heart)`, given by the
alternating sum of the chosen bounded heart cohomology classes. If the chosen
bounds are reversed, then `E` is zero and we return `0`. -/
noncomputable def HeartStabilityData.heartEulerClassObj
    (h : HeartStabilityData C) (E : C) : HeartK0 (C := C) h := by
  classical
  let a := h.upperBound (C := C) E
  let b := h.lowerBound (C := C) E
  by_cases hab : b ≤ a
  · exact h.heartCohClassSum (C := C) b (Int.toNat (a - b)) E
  · exact 0

/-- The canonical object-level lift maps to the ambient Grothendieck-group class
of the original object. -/
theorem HeartStabilityData.heartK0ToK0_heartEulerClassObj
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
  · have hzero : IsZero E := h.t.isZero E a b (by lia)
    rw [HeartStabilityData.heartEulerClassObj, dif_neg hab, map_zero, K₀.of_isZero C hzero]

/-- On an object already in the heart, the `H0` functor is canonically isomorphic to the
identity. -/
noncomputable def HeartStabilityData.H0FunctorObjIsoOfHeart
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) :
    (h.H0Functor (C := C)).obj E.obj ≅ E := by
  have hLE0 : h.t.IsLE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.1
  have hGE0 : h.t.IsGE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.2
  let eLE : (h.t.truncLE 0).obj E.obj ≅ E.obj :=
    @asIso _ _ _ _ ((h.t.truncLEι 0).app E.obj)
      ((h.t.isLE_iff_isIso_truncLEι_app 0 E.obj).mp hLE0)
  let eGE : E.obj ≅ (h.t.truncGE 0).obj E.obj :=
    @asIso _ _ _ _ ((h.t.truncGEπ 0).app E.obj)
      ((h.t.isGE_iff_isIso_truncGEπ_app 0 E.obj).mp hGE0)
  let e0 : (h.t.truncGELE 0 0).obj E.obj ≅ E.obj :=
    (h.t.truncGE 0).mapIso eLE ≪≫ eGE.symm
  let e0' : ((h.H0Functor (C := C)).obj E.obj).obj ≅ E.obj := by
    simpa [HeartStabilityData.H0Functor, HeartStabilityData.heartCohFunctor,
      HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      ((shiftFunctorZero C ℤ).app ((h.t.truncGELE 0 0).obj E.obj) ≪≫ e0)
  exact ObjectProperty.isoMk _ e0'

/-- The primed `H0` functor also restricts to the identity on heart objects. -/
noncomputable def HeartStabilityData.H0primeObjIsoOfHeart
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) :
    h.H0prime (C := C) E.obj ≅ E :=
  (h.H0ObjIsoH0prime (C := C) E.obj).symm ≪≫ h.H0FunctorObjIsoOfHeart (C := C) E

@[reassoc]
theorem HeartStabilityData.H0primeObjIsoOfHeart_inv_hom_comp_truncLEι
    (h : HeartStabilityData C) [IsTriangulated C]
    (E : h.t.heart.FullSubcategory) :
    ((h.H0primeObjIsoOfHeart (C := C) E).inv).hom ≫
        (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) =
      (h.t.truncGEπ 0).app E.obj := by
  have hLE0 : h.t.IsLE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.1
  haveI hIsoGEMapLE :
      IsIso ((h.t.truncGE 0).map ((h.t.truncLEι 0).app E.obj)) :=
    Functor.map_isIso (h.t.truncGE 0) ((h.t.truncLEι 0).app E.obj)
  let eLE : (h.t.truncLE 0).obj E.obj ≅ E.obj :=
    @asIso _ _ _ _ ((h.t.truncLEι 0).app E.obj)
      ((h.t.isLE_iff_isIso_truncLEι_app 0 E.obj).mp hLE0)
  let eGELE : (h.t.truncGELE 0 0).obj E.obj ≅ (h.t.truncGE 0).obj E.obj := by
    simpa [TStructure.truncGELE] using
      (asIso ((h.t.truncGE 0).map ((h.t.truncLEι 0).app E.obj)))
  have hpent :
      (h.t.truncGEπ 0).app ((h.t.truncLE 0).obj E.obj) ≫
          (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
            (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) =
        (h.t.truncLEι 0).app E.obj ≫ (h.t.truncGEπ 0).app E.obj := by
    simpa [HeartStabilityData.H0prime, TStructure.truncLE, TStructure.truncGELE,
      TStructure.truncLEGE, TStructure.truncGELEIsoLEGE] using
      h.t.truncGELTToLTGE_app_pentagon 0 1 E.obj
  have hnat :
      eLE.inv ≫ (h.t.truncGEπ 0).app ((h.t.truncLE 0).obj E.obj) =
        (h.t.truncGEπ 0).app E.obj ≫
          eGELE.inv := by
    apply (Iso.eq_comp_inv eGELE).2
    simpa [eLE, eGELE, Category.assoc] using
      (h.t.truncGEπ_naturality 0 ((h.t.truncLEι 0).app E.obj))
  have hmain :
      (h.t.truncGEπ 0).app E.obj ≫
          eGELE.inv ≫
            (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
              (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) =
        (h.t.truncGEπ 0).app E.obj := by
    have h' :
        eLE.inv ≫ (h.t.truncGEπ 0).app ((h.t.truncLE 0).obj E.obj) ≫
            (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
              (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) =
          eLE.inv ≫ (h.t.truncLEι 0).app E.obj ≫ (h.t.truncGEπ 0).app E.obj := by
      simpa [Category.assoc] using congrArg (fun k => eLE.inv ≫ k) hpent
    have h'' :
        (h.t.truncGEπ 0).app E.obj ≫ eGELE.inv ≫
            (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
              (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) =
          eLE.inv ≫ (h.t.truncLEι 0).app E.obj ≫ (h.t.truncGEπ 0).app E.obj := by
      have hstep :
          (h.t.truncGEπ 0).app E.obj ≫ eGELE.inv ≫
              (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
                (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) =
            eLE.inv ≫ (h.t.truncGEπ 0).app ((h.t.truncLE 0).obj E.obj) ≫
              (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
                (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) := by
        simpa [Category.assoc] using
          congrArg
            (fun k =>
              k ≫ (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
                (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj))
            hnat.symm
      exact hstep.trans (by simpa [Category.assoc] using h')
    simpa [Category.assoc, eLE] using h''
  have hmain' :
      (h.t.truncGEπ 0).app E.obj ≫ eGELE.inv ≫
          (shiftFunctorZero C ℤ).inv.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj E.obj)) ≫
            (shiftFunctorZero C ℤ).hom.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj E.obj)) ≫
              (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
                (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) =
        (h.t.truncGEπ 0).app E.obj := by
    calc
      (h.t.truncGEπ 0).app E.obj ≫ eGELE.inv ≫
            (shiftFunctorZero C ℤ).inv.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj E.obj)) ≫
              (shiftFunctorZero C ℤ).hom.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj E.obj)) ≫
                (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
                  (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) =
          (h.t.truncGEπ 0).app E.obj ≫ eGELE.inv ≫
            (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
              (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k =>
                      (h.t.truncGEπ 0).app E.obj ≫ eGELE.inv ≫ k ≫
                        (h.t.truncGELEIsoLEGE 0 0).hom.app E.obj ≫
                          (h.t.truncLEι 0).app ((h.t.truncGE 0).obj E.obj))
                    ((shiftFunctorZero C ℤ).inv_hom_id_app
                      ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj E.obj)))
      _ = (h.t.truncGEπ 0).app E.obj := hmain
  simpa [HeartStabilityData.H0primeObjIsoOfHeart, HeartStabilityData.H0FunctorObjIsoOfHeart,
    HeartStabilityData.H0ObjIsoH0prime, HeartStabilityData.H0Functor,
    HeartStabilityData.heartCohFunctor, HeartStabilityData.heartCoh,
    HeartStabilityData.heartShiftOfPure, HeartStabilityData.H0prime, TStructure.truncGELE,
    TStructure.truncLEGE, eGELE, Category.assoc] using hmain'

@[reassoc]
  private theorem HeartStabilityData.H0primeObjIsoOfHeart_inv_comp_H0primeFunctor_map
    (h : HeartStabilityData C) [IsTriangulated C]
    (A : h.t.heart.FullSubcategory) {X : C} (f : A.obj ⟶ X) :
    (h.H0primeObjIsoOfHeart (C := C) A).inv ≫ (h.H0primeFunctor (C := C)).map f =
      h.toH0primeHom (C := C) A f := by
  apply h.hom_ext_toH0prime (C := C) A
  change
    (((h.H0primeObjIsoOfHeart (C := C) A).inv).hom ≫
        ((h.H0primeFunctor (C := C)).map f).hom) ≫
          (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) =
      (h.toH0primeHom (C := C) A f).hom ≫
        (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X)
  rw [Category.assoc, h.toH0primeHom_hom (C := C) A f]
  have hstep₁ :
      ((h.H0primeObjIsoOfHeart (C := C) A).inv).hom ≫
            ((h.H0primeFunctor (C := C)).map f).hom ≫
              (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) =
          ((h.H0primeObjIsoOfHeart (C := C) A).inv).hom ≫
            (h.t.truncLEι 0).app ((h.t.truncGE 0).obj A.obj) ≫
              (h.t.truncGE 0).map f := by
    simpa [Category.assoc, HeartStabilityData.H0prime, TStructure.truncLEGE] using
      congrArg
        (fun k => ((h.H0primeObjIsoOfHeart (C := C) A).inv).hom ≫ k)
        (NatTrans.naturality (h.t.truncLEι 0) ((h.t.truncGE 0).map f))
  have hstep₂ :
      ((h.H0primeObjIsoOfHeart (C := C) A).inv).hom ≫
            (h.t.truncLEι 0).app ((h.t.truncGE 0).obj A.obj) ≫
              (h.t.truncGE 0).map f =
          (h.t.truncGEπ 0).app A.obj ≫ (h.t.truncGE 0).map f := by
    simpa [Category.assoc] using
      congrArg (fun k => k ≫ (h.t.truncGE 0).map f)
        (h.H0primeObjIsoOfHeart_inv_hom_comp_truncLEι (C := C) A)
  exact hstep₁.trans (hstep₂.trans (by simpa using h.t.truncGEπ_naturality 0 f))

/-- The short complex in the heart obtained by applying `H0'` to a triangle whose source lies in
the heart. -/
noncomputable def HeartStabilityData.heartSourceH0primeShortComplex
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    (f : A.obj ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : f ≫ g = 0) :
    ShortComplex h.t.heart.FullSubcategory :=
  ShortComplex.mk
    ((h.H0primeObjIsoOfHeart (C := C) A).inv ≫ (h.H0primeFunctor (C := C)).map f)
    ((h.H0primeFunctor (C := C)).map g)
    (by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg ((h.H0primeFunctor (C := C)).map) hfg)

@[simp]
theorem HeartStabilityData.heartSourceH0primeShortComplex_f_eq_toH0primeHom
    (h : HeartStabilityData C) [IsTriangulated C]
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    (f : A.obj ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : f ≫ g = 0) :
    (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f =
      h.toH0primeHom (C := C) A f :=
  h.H0primeObjIsoOfHeart_inv_comp_H0primeFunctor_map (C := C) A f

/-- Comparison isomorphism between the heart-source `H0'` short complex and the image of the
ambient distinguished-triangle short complex under `H0'`. -/
noncomputable def HeartStabilityData.heartSourceH0primeShortComplexIso
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    h.heartSourceH0primeShortComplex (C := C) A f g (comp_distTriang_mor_zero₁₂ _ hT) ≅
      (shortComplexOfDistTriangle (Triangle.mk f g δ) hT).map
        (h.H0primeFunctor (C := C)) := by
  refine ShortComplex.isoMk
    (h.H0primeObjIsoOfHeart (C := C) A).symm
    (Iso.refl _)
    (Iso.refl _)
    ?_
    ?_
  · change
      (h.H0primeObjIsoOfHeart (C := C) A).inv ≫ (h.H0primeFunctor (C := C)).map f =
        ((h.H0primeObjIsoOfHeart (C := C) A).inv ≫
          (h.H0primeFunctor (C := C)).map f) ≫ 𝟙 _
    simp
  · simp [HeartStabilityData.heartSourceH0primeShortComplex, shortComplexOfDistTriangle]

theorem HeartStabilityData.heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_iff
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C)
    (E : h.t.heart.FullSubcategory) :
    ((shortComplexOfDistTriangle (Triangle.mk f g δ) hT).map
      (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact ↔
      ((h.heartSourceH0primeShortComplex (C := C) A f g
        (comp_distTriang_mor_zero₁₂ _ hT)).map
        (preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
  simpa [ShortComplex.map_comp] using
    (ShortComplex.exact_iff_of_iso
      ((preadditiveCoyoneda.obj (Opposite.op E)).mapShortComplex.mapIso
        (h.heartSourceH0primeShortComplexIso (C := C) A hT))).symm

theorem HeartStabilityData.heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_of_f_is_kernel
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} (hfg : f ≫ g = 0)
    (hKer :
      IsLimit (KernelFork.ofι
        (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f
        (h.heartSourceH0primeShortComplex (C := C) A f g hfg).zero))
    (E : h.t.heart.FullSubcategory) :
    ((h.heartSourceH0primeShortComplex (C := C) A f g hfg).map
      (preadditiveCoyoneda.obj (Opposite.op E))).Exact :=
  ShortComplex.preadditiveCoyoneda_exact_of_f_is_kernel hKer E

/-- The canonical map from the cokernel of the heart-source `H0'` short complex to `H0' X₃`. -/
noncomputable def HeartStabilityData.heartSourceH0primeShortComplex_cokernelDesc
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    (f : A.obj ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : f ≫ g = 0) :
    cokernel (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f ⟶
      h.H0prime (C := C) X₃ :=
  cokernel.desc
    (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f
    (h.heartSourceH0primeShortComplex (C := C) A f g hfg).g
    (h.heartSourceH0primeShortComplex (C := C) A f g hfg).zero

@[reassoc (attr := simp)]
theorem HeartStabilityData.heartSourceH0primeShortComplex_cokernelπ_comp_cokernelDesc
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    (f : A.obj ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : f ≫ g = 0) :
    cokernel.π (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f ≫
      h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g hfg =
        (h.heartSourceH0primeShortComplex (C := C) A f g hfg).g :=
  cokernel.π_desc
    (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f
    (h.heartSourceH0primeShortComplex (C := C) A f g hfg).g
    (h.heartSourceH0primeShortComplex (C := C) A f g hfg).zero

/-- In the heart-source `H0'` short complex induced by a distinguished triangle, the first map is
a kernel. -/
noncomputable def HeartStabilityData.heartSourceH0primeShortComplex_f_is_kernel_of_distTriang
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} (hfg : f ≫ g = 0)
    {δ : (h.H0prime (C := C) X₃).obj ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT :
      Triangle.mk
          (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f.hom
          (h.heartSourceH0primeShortComplex (C := C) A f g hfg).g.hom
          δ ∈ distTriang C) :
    IsLimit (KernelFork.ofι
      (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f
      (h.heartSourceH0primeShortComplex (C := C) A f g hfg).zero) := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  letI : IsNormalMonoCategory h.t.heart.FullSubcategory := Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory h.t.heart.FullSubcategory := Abelian.toIsNormalEpiCategory
  letI : Balanced h.t.heart.FullSubcategory := by infer_instance
  have hSE :
      (h.heartSourceH0primeShortComplex (C := C) A f g hfg).ShortExact := by
    refine TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) h.t (A := A)
      (B := h.H0prime (C := C) X₂) (Q := h.H0prime (C := C) X₃)
      (f := (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f)
      (g := (h.heartSourceH0primeShortComplex (C := C) A f g hfg).g)
      (δ := δ) hT
  exact hSE.fIsKernel

theorem HeartStabilityData.H0Functor_isHomological_of_eval_of_heartSourceH0primeShortComplex
    (h : HeartStabilityData C)
    (hHeart :
      ∀ (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
        {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
        (hT : Triangle.mk f g δ ∈ distTriang C) (E : h.t.heart.FullSubcategory),
        ((h.heartSourceH0primeShortComplex (C := C) A f g
          (comp_distTriang_mor_zero₁₂ _ hT)).map
          (preadditiveCoyoneda.obj (Opposite.op E))).Exact) :
    Functor.IsHomological (h.H0Functor (C := C)) := by
  apply h.H0Functor_isHomological_of_eval_of_heart_case (C := C)
  intro A X₂ X₃ f g δ hT E
  exact (h.heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_iff
    (C := C) A hT E).mpr (hHeart A hT E)

theorem HeartStabilityData.H0Functor_isHomological_of_heartSourceH0primeShortComplex_f_is_kernel
    (h : HeartStabilityData C)
    (hKer :
      ∀ (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
        {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
        (hT : Triangle.mk f g δ ∈ distTriang C),
        IsLimit (KernelFork.ofι
          (h.heartSourceH0primeShortComplex (C := C) A f g
            (comp_distTriang_mor_zero₁₂ _ hT)).f
          (h.heartSourceH0primeShortComplex (C := C) A f g
            (comp_distTriang_mor_zero₁₂ _ hT)).zero)) :
    Functor.IsHomological (h.H0Functor (C := C)) := by
  apply h.H0Functor_isHomological_of_eval_of_heartSourceH0primeShortComplex (C := C)
  intro A X₂ X₃ f g δ hT E
  exact h.heartSourceH0primeShortComplex_preadditiveCoyoneda_exact_of_f_is_kernel
    (C := C) A (comp_distTriang_mor_zero₁₂ _ hT) (hKer A hT) E

theorem HeartStabilityData.H0Functor_isHomological_of_heartSourceH0primeShortComplex_distTriang
    (h : HeartStabilityData C)
    (hTri :
      ∀ (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
        {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
        (hT : Triangle.mk f g δ ∈ distTriang C),
        Σ' δ' : (h.H0prime (C := C) X₃).obj ⟶ A.obj⟦(1 : ℤ)⟧,
          Triangle.mk
            (h.heartSourceH0primeShortComplex (C := C) A f g
              (comp_distTriang_mor_zero₁₂ _ hT)).f.hom
            (h.heartSourceH0primeShortComplex (C := C) A f g
              (comp_distTriang_mor_zero₁₂ _ hT)).g.hom
            δ' ∈ distTriang C) :
    Functor.IsHomological (h.H0Functor (C := C)) := by
  apply h.H0Functor_isHomological_of_heartSourceH0primeShortComplex_f_is_kernel (C := C)
  intro A X₂ X₃ f g δ hT
  let hδ' := hTri A hT
  exact h.heartSourceH0primeShortComplex_f_is_kernel_of_distTriang
    (C := C) A (comp_distTriang_mor_zero₁₂ _ hT) hδ'.2

/-- The morphism from the `(-1,0)` truncation of `X₃` to `A[1]` induced by a morphism
`X₃ ⟶ A[1]` with `A` in the heart. -/
noncomputable def HeartStabilityData.heartSourceNegOneToAShiftHom
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₃ : C}
    (δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧) :
    (h.t.truncGELT (-1) 0).obj X₃ ⟶ A.obj⟦(1 : ℤ)⟧ := by
  let s : (h.t.truncLT 0).obj X₃ ⟶ A.obj⟦(1 : ℤ)⟧ := (h.t.truncLTι 0).app X₃ ≫ δ
  have hnegLe : (-1 : ℤ) ≤ 0 := by lia
  have hs :
      (h.t.natTransTruncLTOfLE (-1) 0 hnegLe).app X₃ ≫ s = 0 := by
    have hs' :
        (h.t.natTransTruncLTOfLE (-1) 0 hnegLe).app X₃ ≫ s =
          (h.t.truncLTι (-1)).app X₃ ≫ δ := by
      calc
        (h.t.natTransTruncLTOfLE (-1) 0 hnegLe).app X₃ ≫ s
            = ((h.t.natTransTruncLTOfLE (-1) 0 hnegLe).app X₃ ≫ (h.t.truncLTι 0).app X₃) ≫ δ := by
                dsimp [s]
                rw [Category.assoc]
        _ = (h.t.truncLTι (-1)).app X₃ ≫ δ := by
              rw [h.t.natTransTruncLTOfLE_ι_app (-1) 0 hnegLe X₃]
    rw [hs']
    letI : h.t.IsGE A.obj 0 := (h.t.mem_heart_iff A.obj).mp A.property |>.2
    letI : h.t.IsLE ((h.t.truncLT (-1)).obj X₃) (-2) := h.t.isLE_truncLT_obj ..
    letI : h.t.IsGE (A.obj⟦(1 : ℤ)⟧) (-1) := h.t.isGE_shift _ 0 1 (-1)
    exact h.t.zero _ (-2) (-1) (by lia)
  exact Triangle.yoneda_exact₂ _
    (h.t.triangleLTLTGELT_distinguished (-1) 0 (by lia) X₃) s hs |>.choose

@[reassoc]
theorem HeartStabilityData.truncLT_map_truncGEπ_comp_heartSourceNegOneToAShiftHom
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₃ : C}
    (δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧) :
    (h.t.truncGEπ (-1)).app ((h.t.truncLT 0).obj X₃) ≫
        h.heartSourceNegOneToAShiftHom (C := C) A δ =
      (h.t.truncLTι 0).app X₃ ≫ δ := by
  let s : (h.t.truncLT 0).obj X₃ ⟶ A.obj⟦(1 : ℤ)⟧ := (h.t.truncLTι 0).app X₃ ≫ δ
  have hnegLe : (-1 : ℤ) ≤ 0 := by lia
  have hs :
      (h.t.natTransTruncLTOfLE (-1) 0 hnegLe).app X₃ ≫ s = 0 := by
    have hs' :
        (h.t.natTransTruncLTOfLE (-1) 0 hnegLe).app X₃ ≫ s =
          (h.t.truncLTι (-1)).app X₃ ≫ δ := by
      calc
        (h.t.natTransTruncLTOfLE (-1) 0 hnegLe).app X₃ ≫ s
            = ((h.t.natTransTruncLTOfLE (-1) 0 hnegLe).app X₃ ≫ (h.t.truncLTι 0).app X₃) ≫ δ := by
                dsimp [s]
                rw [Category.assoc]
        _ = (h.t.truncLTι (-1)).app X₃ ≫ δ := by
              rw [h.t.natTransTruncLTOfLE_ι_app (-1) 0 hnegLe X₃]
    rw [hs']
    letI : h.t.IsGE A.obj 0 := (h.t.mem_heart_iff A.obj).mp A.property |>.2
    letI : h.t.IsLE ((h.t.truncLT (-1)).obj X₃) (-2) := h.t.isLE_truncLT_obj ..
    letI : h.t.IsGE (A.obj⟦(1 : ℤ)⟧) (-1) := h.t.isGE_shift _ 0 1 (-1)
    exact h.t.zero _ (-2) (-1) (by lia)
  exact (Triangle.yoneda_exact₂ _
    (h.t.triangleLTLTGELT_distinguished (-1) 0 (by lia) X₃) s hs).choose_spec.symm

/-- After shifting back by `-1`, `heartSourceNegOneToAShiftHom` becomes a morphism from
`H^{-1}(X₃)` to the heart object `A`. -/
noncomputable def HeartStabilityData.heartSourceNegOneToAHom
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₃ : C}
    (δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧) :
    h.heartCoh (C := C) (-1) X₃ ⟶ A := by
  let e :
      ((h.t.truncGELE (-1) (-1)).obj X₃)⟦(-1 : ℤ)⟧ ≅
        ((h.t.truncGELT (-1) 0).obj X₃)⟦(-1 : ℤ)⟧ :=
    (shiftFunctor C (-1)).mapIso
      ((h.t.truncGELEIsoTruncGELT (-1) (-1) 0 rfl).app X₃)
  refine ObjectProperty.homMk (e.hom ≫
    (shiftFunctor C (-1)).map (h.heartSourceNegOneToAShiftHom (C := C) A δ) ≫
      (shiftShiftNeg (X := A.obj) (i := (1 : ℤ))).hom)

theorem HeartStabilityData.exists_heartSourceNegOneToAShiftHom_comp_shift_map_factor
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    ∃ φ : ((h.t.truncLT (-1)).obj X₃)⟦(1 : ℤ)⟧ ⟶ X₂⟦(1 : ℤ)⟧,
      h.heartSourceNegOneToAShiftHom (C := C) A δ ≫ (shiftFunctor C (1 : ℤ)).map f =
        (h.t.truncGELTδLT (-1) 0).app X₃ ≫ φ := by
  have hzero :
      (h.t.truncGEπ (-1)).app ((h.t.truncLT 0).obj X₃) ≫
          h.heartSourceNegOneToAShiftHom (C := C) A δ ≫
            (shiftFunctor C (1 : ℤ)).map f = 0 := by
    calc
      (h.t.truncGEπ (-1)).app ((h.t.truncLT 0).obj X₃) ≫
          h.heartSourceNegOneToAShiftHom (C := C) A δ ≫
            (shiftFunctor C (1 : ℤ)).map f =
        (h.t.truncLTι 0).app X₃ ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map f := by
          simpa [Category.assoc] using
            congrArg (fun k => k ≫ (shiftFunctor C (1 : ℤ)).map f)
              (h.truncLT_map_truncGEπ_comp_heartSourceNegOneToAShiftHom (C := C) A δ)
      _ = (h.t.truncLTι 0).app X₃ ≫ 0 := by
          simpa [Category.assoc] using
            congrArg (fun k => (h.t.truncLTι 0).app X₃ ≫ k) (comp_distTriang_mor_zero₃₁ _ hT)
      _ = 0 := comp_zero
  obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₃ _
    (h.t.triangleLTLTGELT_distinguished (-1) 0 (by lia) X₃)
    (h.heartSourceNegOneToAShiftHom (C := C) A δ ≫ (shiftFunctor C (1 : ℤ)).map f)
    hzero
  exact ⟨φ, by simpa [TStructure.triangleLTLTGELT] using hφ⟩

theorem HeartStabilityData.exists_comp_heartSourceNegOneToAShiftHom_eq_of_comp_truncGEπ_zero
    (h : HeartStabilityData C)
    (E A : h.t.heart.FullSubcategory) {X₃ : C}
    (δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧) (m : E.obj ⟶ X₃)
    (hm : m ≫ (h.t.truncGEπ 0).app X₃ = 0) :
    ∃ u : E.obj ⟶ (h.t.truncGELT (-1) 0).obj X₃,
      u ≫ h.heartSourceNegOneToAShiftHom (C := C) A δ = m ≫ δ := by
  obtain ⟨u₀, hu₀⟩ := Triangle.coyoneda_exact₂ _
    (h.t.triangleLTGE_distinguished 0 X₃) m hm
  change E.obj ⟶ (h.t.truncLT 0).obj X₃ at u₀
  refine ⟨u₀ ≫ (h.t.truncGEπ (-1)).app ((h.t.truncLT 0).obj X₃), ?_⟩
  calc
    (u₀ ≫ (h.t.truncGEπ (-1)).app ((h.t.truncLT 0).obj X₃)) ≫
          h.heartSourceNegOneToAShiftHom (C := C) A δ =
        u₀ ≫ (h.t.truncLTι 0).app X₃ ≫ δ := by
          simpa [Category.assoc] using
            congrArg (fun k => u₀ ≫ k)
              (h.truncLT_map_truncGEπ_comp_heartSourceNegOneToAShiftHom (C := C) A δ)
    _ = m ≫ δ := by
          simpa [Category.assoc] using congrArg (fun k => k ≫ δ) hu₀.symm

theorem HeartStabilityData.exists_comp_heartSourceNegOneToAShiftHom_eq_of_toH0prime_comp_kernel
    (h : HeartStabilityData C)
    (E A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    (f : E.obj ⟶ X₂) (g : X₂ ⟶ X₃)
    {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hfg :
      h.toH0primeHom (C := C) E f ≫ (h.H0primeFunctor (C := C)).map g = 0) :
    ∃ u : E.obj ⟶ (h.t.truncGELT (-1) 0).obj X₃,
      u ≫ h.heartSourceNegOneToAShiftHom (C := C) A δ =
        f ≫ g ≫ δ := by
  have hzeroTo : h.toH0primeHom (C := C) E (f ≫ g) = 0 := by
    calc
      h.toH0primeHom (C := C) E (f ≫ g) =
          h.toH0primeHom (C := C) E f ≫ (h.H0primeFunctor (C := C)).map g := by
            symm
            exact h.toH0primeHom_comp_H0primeFunctor_map (C := C) E f g
      _ = 0 := hfg
  have hfgπ : f ≫ g ≫ (h.t.truncGEπ 0).app X₃ = 0 := by
    simpa [Category.assoc] using
      (h.toH0primeHom_eq_zero_iff (C := C) E (f ≫ g)).mp hzeroTo
  simpa [Category.assoc] using
    h.exists_comp_heartSourceNegOneToAShiftHom_eq_of_comp_truncGEπ_zero
      (C := C) E A δ
      (f ≫ g) (by simpa [Category.assoc] using hfgπ)

omit [IsTriangulated C] in
theorem TStructure.comp_shift_truncGEπ_zero_of_truncLT_negOne
    (t : TStructure C) {X₂ X₃ : C}
    (φ : ((t.truncLT (-1)).obj X₃)⟦(1 : ℤ)⟧ ⟶ X₂⟦(1 : ℤ)⟧) :
    φ ≫ (shiftFunctor C (1 : ℤ)).map ((t.truncGEπ 0).app X₂) = 0 := by
  letI : t.IsLE ((t.truncLT (-1)).obj X₃) (-1) := t.isLE_truncLT_obj ..
  letI : t.IsLE (((t.truncLT (-1)).obj X₃)⟦(1 : ℤ)⟧) (-2) := by
    simpa using t.isLE_shift ((t.truncLT (-1)).obj X₃) (-1) 1 (-2) (by lia)
  letI : t.IsGE ((t.truncGE 0).obj X₂) 0 := t.isGE_truncGE_obj ..
  letI : t.IsGE (((t.truncGE 0).obj X₂)⟦(1 : ℤ)⟧) (-1 : ℤ) := by
    simpa using t.isGE_shift ((t.truncGE 0).obj X₂) 0 1 (-1) (by lia)
  exact t.zero (φ ≫ (shiftFunctor C (1 : ℤ)).map ((t.truncGEπ 0).app X₂)) (-2) (-1) (by
    norm_num)

/-- The underlying object of `heartCoh n (E[-n])` is canonically isomorphic to `E` when `E`
already lies in the heart. -/
noncomputable def HeartStabilityData.heartCohObjIsoOfHeartShift
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) (n : ℤ) :
    (h.heartCoh (C := C) n (E.obj⟦(-n : ℤ)⟧)).obj ≅ E.obj := by
  let X : C := E.obj⟦(-n : ℤ)⟧
  have hE' := (h.t.mem_heart_iff E.obj).mp E.property
  letI : h.t.IsLE E.obj 0 := hE'.1
  letI : h.t.IsGE E.obj 0 := hE'.2
  have hLE : h.t.IsLE X n := by
    simpa [X] using (h.t.isLE_shift E.obj 0 (-n : ℤ) n (by lia))
  have hGE : h.t.IsGE X n := by
    simpa [X] using (h.t.isGE_shift E.obj 0 (-n : ℤ) n (by lia))
  letI := hLE
  letI := hGE
  let eLE : (h.t.truncLE n).obj X ≅ X :=
    @asIso _ _ _ _ ((h.t.truncLEι n).app X) ((h.t.isLE_iff_isIso_truncLEι_app n X).mp hLE)
  let eGE : X ≅ (h.t.truncGE n).obj X :=
    @asIso _ _ _ _ ((h.t.truncGEπ n).app X) ((h.t.isGE_iff_isIso_truncGEπ_app n X).mp hGE)
  let e0 : (h.t.truncGELE n n).obj X ≅ X :=
    (h.t.truncGE n).mapIso eLE ≪≫ eGE.symm
  simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure, X] using
    ((shiftFunctor C n).mapIso e0 ≪≫ shiftNegShift (X := E.obj) (i := n))

theorem HeartStabilityData.heartCohClass_zero_of_heart
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) :
    h.heartCohClass (C := C) 0 E.obj = HeartK0.of (C := C) h E := by
  simpa [HeartStabilityData.heartCohClass, HeartStabilityData.heartCoh] using
    HeartK0.of_iso (C := C) h (h.H0FunctorObjIsoOfHeart (C := C) E)


end Proposition53

end CategoryTheory.Triangulated
