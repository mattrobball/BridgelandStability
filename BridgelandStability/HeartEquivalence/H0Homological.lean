/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.HeartEquivalence.H0Functor

/-!
# H0 Homological Properties

Exactness properties of the H0' functor: preadditive Yoneda exactness
for octahedral splits, vanishing outside the amplitude range, and the
five-term exact sequence for heart cohomology.
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


/-! ## H0 Homological Properties -/

/-- Shifting `τ≥n X` by `n` identifies it with `τ≥0 (X⟦n⟧)`. -/
noncomputable def TStructure.truncGEObjShiftIso
    (t : TStructure C) (n : ℤ) (X : C) :
    ((t.truncGE n).obj X)⟦(n : ℤ)⟧ ≅ (t.truncGE 0).obj (X⟦(n : ℤ)⟧) := by
  classical
  let T₁ := (Triangle.shiftFunctor C n).obj ((t.triangleLTGE n).obj X)
  let T₂ := (t.triangleLTGE 0).obj (X⟦(n : ℤ)⟧)
  have hT₁ : T₁ ∈ distTriang C := by
    dsimp [T₁]
    exact Triangle.shift_distinguished _ (t.triangleLTGE_distinguished n X) n
  have hT₂ : T₂ ∈ distTriang C := by
    dsimp [T₂]
    exact t.triangleLTGE_distinguished 0 (X⟦(n : ℤ)⟧)
  let eEx := t.triangle_iso_exists hT₁ hT₂ (Iso.refl _) (-1) 0
    (by
      dsimp [T₁]
      simpa using t.isLE_shift ((t.truncLT n).obj X) (n - 1) n (-1) (by grind))
    (by
      dsimp [T₁]
      simpa using t.isGE_shift ((t.truncGE n).obj X) n n 0 (by grind))
    (by
      dsimp [T₂]
      simpa using t.isLE_truncLT_obj ((X⟦(n : ℤ)⟧)) 0 (-1) (by grind))
    (by
      dsimp [T₂]
      infer_instance)
    (by grind)
  let e := Classical.choose eEx
  exact Triangle.π₃.mapIso e

/-- Shifting `τ≤n X` by `n` identifies it with `τ≤0 (X⟦n⟧)`. -/
noncomputable def TStructure.truncLEObjShiftIso
    (t : TStructure C) (n : ℤ) (X : C) :
    ((t.truncLE n).obj X)⟦(n : ℤ)⟧ ≅ (t.truncLE 0).obj (X⟦(n : ℤ)⟧) := by
  classical
  let T₁ := (Triangle.shiftFunctor C n).obj ((t.triangleLEGE n (n + 1) rfl).obj X)
  let T₂ := (t.triangleLEGE 0 1 rfl).obj (X⟦(n : ℤ)⟧)
  have hT₁ : T₁ ∈ distTriang C := by
    dsimp [T₁]
    exact Triangle.shift_distinguished _ (t.triangleLEGE_distinguished n (n + 1) rfl X) n
  have hT₂ : T₂ ∈ distTriang C := by
    dsimp [T₂]
    exact t.triangleLEGE_distinguished 0 1 rfl (X⟦(n : ℤ)⟧)
  let eEx := t.triangle_iso_exists hT₁ hT₂ (Iso.refl _) 0 1
    (by
      dsimp [T₁]
      simpa using t.isLE_shift ((t.truncLE n).obj X) n n 0 (by grind))
    (by
      dsimp [T₁]
      simpa using t.isGE_shift ((t.truncGE (n + 1)).obj X) (n + 1) n 1 (by grind))
    (by
      dsimp [T₂]
      infer_instance)
    (by
      dsimp [T₂]
      infer_instance)
    (by grind)
  let e := Classical.choose eEx
  exact Triangle.π₁.mapIso e

/-- Shifting the pure truncation `τ^[n,n] X` by `n` identifies it with
`τ^[0,0] (X⟦n⟧)`. -/
noncomputable def TStructure.truncGELEObjShiftIso
    (t : TStructure C) (n : ℤ) (X : C) :
    ((t.truncGELE n n).obj X)⟦(n : ℤ)⟧ ≅ (t.truncGELE 0 0).obj (X⟦(n : ℤ)⟧) := by
  let e₁ :
      ((t.truncGELE n n).obj X)⟦(n : ℤ)⟧ ≅
        (t.truncGE 0).obj (((t.truncLE n).obj X)⟦(n : ℤ)⟧) := by
    simpa [TStructure.truncGELE] using
      TStructure.truncGEObjShiftIso (C := C) t n ((t.truncLE n).obj X)
  let e₂ :
      (t.truncGE 0).obj (((t.truncLE n).obj X)⟦(n : ℤ)⟧) ≅
        (t.truncGELE 0 0).obj (X⟦(n : ℤ)⟧) := by
      simpa [TStructure.truncGELE] using
        (t.truncGE 0).mapIso (TStructure.truncLEObjShiftIso (C := C) t n X)
  exact e₁ ≪≫ e₂

/-- The shifted `H⁰_t` object of `X` agrees with the degree-`n` heart cohomology
object `heartCoh n X`. -/
noncomputable def HeartStabilityData.H0FunctorShiftObjIsoHeartCoh
    (h : HeartStabilityData C) (n : ℤ) (X : C) :
    ((h.H0Functor (C := C)).shift n).obj X ≅ h.heartCoh (C := C) n X := by
  let e₂ : (h.H0Functor (C := C)).obj (X⟦(n : ℤ)⟧) ≅ h.heartCoh (C := C) n X := by
    refine ObjectProperty.isoMk _ ?_
    simpa [HeartStabilityData.H0Functor, HeartStabilityData.heartCohFunctor,
      HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      (((shiftFunctorZero C ℤ).app ((h.t.truncGELE 0 0).obj (X⟦(n : ℤ)⟧))) ≪≫
        (TStructure.truncGELEObjShiftIso (C := C) h.t n X).symm)
  exact ((Functor.isoShift (h.H0Functor (C := C)) n).app X).symm ≪≫ e₂

theorem TStructure.isIso_truncLT_pred_map_of_isGE
    (t : TStructure C)
    {a : ℤ} {A Z X₃ : C} [t.IsGE A a]
    {m₁ : A ⟶ Z} {m₃ : Z ⟶ X₃} {δ : X₃ ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk m₁ m₃ δ ∈ distTriang C) :
    IsIso ((t.truncLT (a - 1)).map m₃) := by
  let T : Triangle C := Triangle.mk m₁ m₃ δ
  have hrot : T.rotate ∈ distTriang C := by
    simpa [T] using rot_of_distTriang _ hT
  have hGE : t.IsGE (T.rotate.obj₃) (a - 1) := by
    change t.IsGE (A⟦(1 : ℤ)⟧) (a - 1)
    simpa [T] using t.isGE_shift A a 1 (a - 1) (by grind)
  simpa [T] using t.isIso₁_truncLT_map_of_isGE T.rotate hrot (a - 1) hGE

theorem TStructure.exists_truncLT_octahedral_split
    (t : TStructure C)
    {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) (a : ℤ) :
    ∃ (Z : C) (v : X₂ ⟶ Z) (w : Z ⟶ ((t.truncLT a).obj X₁)⟦(1 : ℤ)⟧)
      (m₁ : (t.truncGE a).obj X₁ ⟶ Z) (m₃ : Z ⟶ X₃),
      Triangle.mk ((t.truncLTι a).app X₁ ≫ f) v w ∈ distTriang C ∧
      Triangle.mk m₁ m₃
        (δ ≫ ((shiftFunctor C (1 : ℤ)).map ((t.truncGEπ a).app X₁))) ∈ distTriang C ∧
      ((t.truncGEπ a).app X₁) ≫ m₁ = f ≫ v ∧
      m₁ ≫ w = (t.truncGEδLT a).app X₁ ∧
      v ≫ m₃ = g := by
  obtain ⟨Z, v, w, h13⟩ := distinguished_cocone_triangle ((t.truncLTι a).app X₁ ≫ f)
  let oct := Triangulated.someOctahedron rfl (t.triangleLTGE_distinguished a X₁) hT h13
  refine ⟨Z, v, w, oct.m₁, oct.m₃, h13, ?_, oct.comm₁, oct.comm₂, oct.comm₃⟩
  simpa using oct.mem

/-- If the lower obstruction term vanishes, a map into `H0prime X` lifts to a
map into `X` itself. -/
noncomputable def TStructure.shortComplexOfDistTriangle_map_truncGEIsoOfSplit
    (t : TStructure C) [IsTriangulated C]
    {X₁ X₂ X₃ Z : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧}
    {v : X₂ ⟶ Z} {m₁ : (t.truncGE 0).obj X₁ ⟶ Z} {m₃ : Z ⟶ X₃}
    (hT : Triangle.mk f g δ ∈ distTriang C)
    (hT' :
      Triangle.mk m₁ m₃
        (δ ≫ ((shiftFunctor C (1 : ℤ)).map ((t.truncGEπ 0).app X₁))) ∈ distTriang C)
    (hm₁ : ((t.truncGEπ 0).app X₁) ≫ m₁ = f ≫ v)
    (hm₃ : v ≫ m₃ = g)
    (hvIso : IsIso ((t.truncGE 0).map v)) :
    ((shortComplexOfDistTriangle (Triangle.mk f g δ) hT).map (t.truncGE 0)) ≅
      ((shortComplexOfDistTriangle
        (Triangle.mk m₁ m₃
          (δ ≫ ((shiftFunctor C (1 : ℤ)).map ((t.truncGEπ 0).app X₁)))) hT').map
        (t.truncGE 0)) := by
  let e₁ : (t.truncGE 0).obj X₁ ≅ (t.truncGE 0).obj ((t.truncGE 0).obj X₁) :=
    @asIso _ _ _ _ ((t.truncGE 0).map ((t.truncGEπ 0).app X₁))
      (t.isIso_truncGE_map_truncGEπ_app 0 0 (by grind) X₁)
  let e₂ : (t.truncGE 0).obj X₂ ≅ (t.truncGE 0).obj Z :=
    @asIso _ _ _ _ ((t.truncGE 0).map v) hvIso
  refine ShortComplex.isoMk
    e₁
    e₂
    (Iso.refl _) ?_ ?_
  · simpa [Functor.map_comp] using congrArg ((t.truncGE 0).map) hm₁
  · simpa [Functor.map_comp] using congrArg ((t.truncGE 0).map) hm₃

theorem HeartStabilityData.truncGE_preadditiveCoyoneda_exact_iff_of_split
    (h : HeartStabilityData C) [IsTriangulated C]
    {X₁ X₂ X₃ Z : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧}
    {v : X₂ ⟶ Z} {m₁ : (h.t.truncGE 0).obj X₁ ⟶ Z} {m₃ : Z ⟶ X₃}
    (hT : Triangle.mk f g δ ∈ distTriang C)
    (hT' :
      Triangle.mk m₁ m₃
        (δ ≫ ((shiftFunctor C (1 : ℤ)).map ((h.t.truncGEπ 0).app X₁))) ∈ distTriang C)
    (hm₁ : ((h.t.truncGEπ 0).app X₁) ≫ m₁ = f ≫ v)
    (hm₃ : v ≫ m₃ = g)
    (hvIso : IsIso ((h.t.truncGE 0).map v))
    (E : h.t.heart.FullSubcategory) :
    ((shortComplexOfDistTriangle (Triangle.mk f g δ) hT).map
      (h.t.truncGE 0 ⋙ preadditiveCoyoneda.obj (Opposite.op E.obj))).Exact ↔
      ((shortComplexOfDistTriangle
        (Triangle.mk m₁ m₃
          (δ ≫ ((shiftFunctor C (1 : ℤ)).map ((h.t.truncGEπ 0).app X₁)))) hT').map
        (h.t.truncGE 0 ⋙ preadditiveCoyoneda.obj (Opposite.op E.obj))).Exact := by
  let e :=
    h.t.shortComplexOfDistTriangle_map_truncGEIsoOfSplit (C := C) hT hT' hm₁ hm₃ hvIso
  simpa [ShortComplex.map_comp] using
    ShortComplex.exact_iff_of_iso
      ((preadditiveCoyoneda.obj (Opposite.op E.obj)).mapShortComplex.mapIso e)

theorem HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_iff_octahedral_split
    (h : HeartStabilityData C) [IsTriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) (E : h.t.heart.FullSubcategory) :
    ∃ (Z : C) (v : T.obj₂ ⟶ Z) (w : Z ⟶ ((h.t.truncLT 0).obj T.obj₁)⟦(1 : ℤ)⟧)
      (m₁ : (h.t.truncGE 0).obj T.obj₁ ⟶ Z) (m₃ : Z ⟶ T.obj₃)
      (_h13 : Triangle.mk ((h.t.truncLTι 0).app T.obj₁ ≫ T.mor₁) v w ∈ distTriang C)
      (h23 : Triangle.mk m₁ m₃
        (T.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map ((h.t.truncGEπ 0).app T.obj₁))) ∈ distTriang C),
      ((h.t.truncGEπ 0).app T.obj₁) ≫ m₁ = T.mor₁ ≫ v ∧
      m₁ ≫ w = (h.t.truncGEδLT 0).app T.obj₁ ∧
      v ≫ m₃ = T.mor₂ ∧
      (((shortComplexOfDistTriangle T hT).map
        (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact ↔
        ((shortComplexOfDistTriangle
          (Triangle.mk m₁ m₃
            (T.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map ((h.t.truncGEπ 0).app T.obj₁))))
          h23).map
          (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact) := by
  obtain ⟨Z, v, w, m₁, m₃, h13, h23, hm₁, hmw, hm₃⟩ :=
    h.t.exists_truncLT_octahedral_split (C := C) hT 0
  have hvIso : IsIso ((h.t.truncGE 0).map v) := by
    exact h.t.isIso₂_truncGE_map_of_isLE _ h13 (-1) 0 rfl
      (h.t.isLE_truncLT_obj T.obj₁ 0 (-1) (by grind))
  refine ⟨Z, v, w, m₁, m₃, h13, h23, hm₁, hmw, hm₃, ?_⟩
  rw [h.H0primeFunctor_preadditiveCoyoneda_exact_iff_truncGE (C := C) T hT E]
  exact (h.truncGE_preadditiveCoyoneda_exact_iff_of_split
      (C := C) hT h23 hm₁ hm₃ hvIso E).trans
    (h.H0primeFunctor_preadditiveCoyoneda_exact_iff_truncGE (C := C)
      (Triangle.mk m₁ m₃
        (T.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map ((h.t.truncGEπ 0).app T.obj₁)))) h23 E).symm

theorem HeartStabilityData.exists_toH0primeHom_eq_of_obstruction_zero
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C}
    (β : E ⟶ h.H0prime (C := C) X)
    (hβ :
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫
          (h.t.truncGEδLT 0).app X = 0) :
    ∃ f : E.obj ⟶ X, β = h.toH0primeHom (C := C) E f := by
  let b : E.obj ⟶ (h.t.truncGE 0).obj X :=
    β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X)
  have hb : b ≫ (h.t.truncGEδLT 0).app X = 0 := by
    simpa [b, Category.assoc] using hβ
  obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₃ _ (h.t.triangleLTGE_distinguished 0 X) b hb
  refine ⟨f, h.toH0primeHom_eq (C := C) E f β ?_⟩
  simpa [b] using hf

theorem HeartStabilityData.comp_H0primeFunctor_map_eq_zero_iff
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X Y : C}
    (β : E ⟶ h.H0prime (C := C) X) (g : X ⟶ Y) :
    β ≫ (h.H0primeFunctor (C := C)).map g = 0 ↔
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫
        (h.t.truncGE 0).map g = 0 := by
  constructor
  · intro hβ
    have hβ' : β.hom ≫ (h.t.truncLE 0).map ((h.t.truncGE 0).map g) = 0 := by
      simpa [HeartStabilityData.H0primeFunctor, HeartStabilityData.H0prime,
        TStructure.truncLEGE] using congrArg (fun f => f.hom) hβ
    have hβ'' :
        β.hom ≫ (h.t.truncLE 0).map ((h.t.truncGE 0).map g) ≫
          (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Y) = 0 := by
      simpa [Category.assoc] using
        congrArg (fun k => k ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Y)) hβ'
    calc
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫ (h.t.truncGE 0).map g =
          β.hom ≫ (h.t.truncLE 0).map ((h.t.truncGE 0).map g) ≫
            (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Y) := by
              simpa [Category.assoc] using
                congrArg (fun k => β.hom ≫ k)
                  (((h.t.truncLEι 0).naturality ((h.t.truncGE 0).map g)).symm)
      _ = 0 := hβ''
  · intro hβ
    apply h.hom_ext_toH0prime (C := C) E
    have hcomp :
        (β ≫ (h.H0primeFunctor (C := C)).map g).hom ≫
            (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Y) =
          β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫
            (h.t.truncGE 0).map g := by
      simpa [HeartStabilityData.H0primeFunctor, HeartStabilityData.H0prime,
        TStructure.truncLEGE, Category.assoc] using
        congrArg (fun k => β.hom ≫ k)
          ((h.t.truncLEι 0).naturality ((h.t.truncGE 0).map g))
    have hzero :
        β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫
            (h.t.truncGE 0).map g =
          0 ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Y) := by
      simpa [hβ]
    exact hcomp.trans hzero

theorem HeartStabilityData.toH0primeHom_eq_zero_iff
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} (f : E.obj ⟶ X) :
    h.toH0primeHom (C := C) E f = 0 ↔ f ≫ (h.t.truncGEπ 0).app X = 0 := by
  constructor
  · intro hf
    simpa [hf] using (h.toH0primeHom_hom (C := C) E f).symm
  · intro hf
    apply h.hom_ext_toH0prime (C := C) E
    simpa [hf] using h.toH0primeHom_hom (C := C) E f

theorem HeartStabilityData.isZero_H0prime_of_isGE_one
    (h : HeartStabilityData C) [inst : IsTriangulated C]
    {X : C} [h.t.IsGE X 1] :
    IsZero (@HeartStabilityData.H0prime C _ _ _ _ _ _ inst h X) := by
  letI := inst
  refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
  change IsZero ((h.t.truncLE 0).obj ((h.t.truncGE 0).obj X))
  exact h.t.isZero_truncLE_obj_of_isGE 0 1 rfl ((h.t.truncGE 0).obj X)

theorem HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_isIso_truncLT_map
    (h : HeartStabilityData C)
    {A Z X₃ : C}
    {m₁ : A ⟶ Z} {m₃ : Z ⟶ X₃} {δ : X₃ ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk m₁ m₃ δ ∈ distTriang C)
    (hm₃LT : IsIso ((h.t.truncLT 0).map m₃))
    (E : h.t.heart.FullSubcategory) :
    ((shortComplexOfDistTriangle (Triangle.mk m₁ m₃ δ) hT).map
      (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro β hβ
  letI := hm₃LT
  have hkernel :
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Z) ≫
          (h.t.truncGE 0).map m₃ = 0 :=
    (h.comp_H0primeFunctor_map_eq_zero_iff (C := C) E β m₃).mp hβ
  have hkernel' :
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Z) ≫
          (h.t.truncGE 0).map m₃ ≫ (h.t.truncGEδLT 0).app X₃ = 0 := by
    simpa [Category.assoc] using
      congrArg (fun k => k ≫ (h.t.truncGEδLT 0).app X₃) hkernel
  have hobsComp :
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Z) ≫
          (h.t.truncGEδLT 0).app Z ≫ ((h.t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' = 0 := by
    calc
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Z) ≫
          (h.t.truncGEδLT 0).app Z ≫ ((h.t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' =
        β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Z) ≫
          (h.t.truncGE 0).map m₃ ≫ (h.t.truncGEδLT 0).app X₃ := by
            simpa [Category.assoc] using
              congrArg
                (fun k =>
                  β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Z) ≫ k)
                ((h.t.truncGEδLT 0).naturality m₃).symm
      _ = 0 := hkernel'
  have hobs :
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Z) ≫
          (h.t.truncGEδLT 0).app Z = 0 := by
    have hobsComp' :
        β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Z) ≫
            (h.t.truncGEδLT 0).app Z ≫ ((h.t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' =
          0 ≫ ((h.t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' := by
      simpa using hobsComp
    have hobsComp'' :
        (β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Z) ≫
            (h.t.truncGEδLT 0).app Z) ≫ ((h.t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' =
          0 ≫ ((h.t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' := by
      simpa [Category.assoc] using hobsComp'
    exact (cancel_mono (((h.t.truncLT 0).map m₃)⟦(1 : ℤ)⟧')).1 hobsComp''
  obtain ⟨f, hfβ⟩ := h.exists_toH0primeHom_eq_of_obstruction_zero (C := C) E β hobs
  change E.obj ⟶ Z at f
  have hfm₃π :
      f ≫ m₃ ≫ (h.t.truncGEπ 0).app X₃ = 0 := by
    have hβ' : h.toH0primeHom (C := C) E f ≫ (h.H0primeFunctor (C := C)).map m₃ = 0 := by
      simpa [hfβ] using hβ
    have hzeroTo : h.toH0primeHom (C := C) E (f ≫ m₃) = 0 := by
      calc
        h.toH0primeHom (C := C) E (f ≫ m₃) =
            h.toH0primeHom (C := C) E f ≫ (h.H0primeFunctor (C := C)).map m₃ := by
              symm
              exact h.toH0primeHom_comp_H0primeFunctor_map (C := C) E f m₃
        _ = 0 := hβ'
    simpa [Category.assoc] using (h.toH0primeHom_eq_zero_iff (C := C) E (f ≫ m₃)).mp hzeroTo
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ _ (h.t.triangleLTGE_distinguished 0 X₃) (f ≫ m₃)
    (by simpa using hfm₃π)
  change E.obj ⟶ (h.t.truncLT 0).obj X₃ at u
  let u' : E.obj ⟶ (h.t.truncLT 0).obj Z := u ≫ inv ((h.t.truncLT 0).map m₃)
  have hu' :
      u' ≫ (h.t.truncLTι 0).app Z ≫ m₃ = f ≫ m₃ := by
    have hu₁ :
        u' ≫ (h.t.truncLTι 0).app Z ≫ m₃ =
          u' ≫ (h.t.truncLT 0).map m₃ ≫ (h.t.truncLTι 0).app X₃ := by
      simpa [Category.assoc] using
        congrArg (fun k => u' ≫ k) ((h.t.truncLTι 0).naturality m₃).symm
    have hu₂ :
        u' ≫ (h.t.truncLT 0).map m₃ ≫ (h.t.truncLTι 0).app X₃ =
          u ≫ (h.t.truncLTι 0).app X₃ := by
      simp [u', Category.assoc]
    have hu₃ : u ≫ (h.t.truncLTι 0).app X₃ = f ≫ m₃ := by
      simpa using hu.symm
    exact hu₁.trans (hu₂.trans hu₃)
  let n : E.obj ⟶ Z := u' ≫ (h.t.truncLTι 0).app Z
  have hn : n ≫ m₃ = f ≫ m₃ := by
    simpa [n] using hu'
  let f' : E.obj ⟶ Z := f + (-n)
  have hf'm₃ : f' ≫ m₃ = 0 := by
    simp [f', hn]
  have hu'zero :
      h.toH0primeHom (C := C) E n = 0 := by
    have hz :
        (h.t.truncLTι 0).app Z ≫ (h.t.truncGEπ 0).app Z = 0 :=
      comp_distTriang_mor_zero₁₂ _ (h.t.triangleLTGE_distinguished 0 Z)
    apply (h.toH0primeHom_eq_zero_iff (C := C) E n).2
    simpa [n, Category.assoc] using congrArg (fun k => u' ≫ k) hz
  have hnegzero :
      h.toH0primeHom (C := C) E (-n) = 0 := by
    apply (h.toH0primeHom_eq_zero_iff (C := C) E (-n)).2
    simpa using congrArg Neg.neg
      ((h.toH0primeHom_eq_zero_iff (C := C) E n).mp hu'zero)
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ _ hT f' hf'm₃
  have hf'Eq :
      h.toH0primeHom (C := C) E f' = h.toH0primeHom (C := C) E f := by
    simp [f', hnegzero]
  have hfβ' : h.toH0primeHom (C := C) E f = β := by
    simpa using hfβ.symm
  have hcomp₁ :
      h.toH0primeHom (C := C) E a ≫ (h.H0primeFunctor (C := C)).map m₁ =
        h.toH0primeHom (C := C) E (a ≫ m₁) := by
    exact h.toH0primeHom_comp_H0primeFunctor_map (C := C) E a m₁
  have hcomp₂ :
      h.toH0primeHom (C := C) E (a ≫ m₁) = h.toH0primeHom (C := C) E f' := by
    simpa using congrArg (h.toH0primeHom (C := C) E) ha.symm
  refine ⟨h.toH0primeHom (C := C) E a, ?_⟩
  exact hcomp₁.trans (hcomp₂.trans (hf'Eq.trans hfβ'))

theorem HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_one
    (h : HeartStabilityData C) [IsTriangulated C]
    {A Z X₃ : C} [h.t.IsGE A 1]
    {m₁ : A ⟶ Z} {m₃ : Z ⟶ X₃} {δ : X₃ ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk m₁ m₃ δ ∈ distTriang C)
    (E : h.t.heart.FullSubcategory) :
    ((shortComplexOfDistTriangle (Triangle.mk m₁ m₃ δ) hT).map
      (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
  letI : h.t.IsGE A 0 := h.t.isGE_of_ge A 0 1 (by grind)
  have hm₃LT : IsIso ((h.t.truncLT 0).map m₃) := by
    let T : Triangle C := Triangle.mk m₁ m₃ δ
    have hrot : T.rotate ∈ distTriang C := by
      simpa [T] using rot_of_distTriang _ hT
    have hGE : h.t.IsGE (T.rotate.obj₃) 0 := by
      change h.t.IsGE (A⟦(1 : ℤ)⟧) 0
      simpa [T] using h.t.isGE_shift A 1 1 0 (by grind)
    simpa [T] using h.t.isIso₁_truncLT_map_of_isGE T.rotate hrot 0 hGE
  exact h.H0primeFunctor_preadditiveCoyoneda_exact_of_isIso_truncLT_map
    (C := C) hT hm₃LT E

theorem HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_split_one
    (h : HeartStabilityData C)
    {A X₂ X₃ Z : C}
    {f : A ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A⟦(1 : ℤ)⟧}
    {v : X₂ ⟶ Z} {w : Z ⟶ ((h.t.truncLT 1).obj A)⟦(1 : ℤ)⟧}
    {m₁ : (h.t.truncGE 1).obj A ⟶ Z} {m₃ : Z ⟶ X₃}
    (E : h.t.heart.FullSubcategory)
    (hT : Triangle.mk f g δ ∈ distTriang C)
    (h13 : Triangle.mk ((h.t.truncLTι 1).app A ≫ f) v w ∈ distTriang C)
    (h23 :
      Triangle.mk m₁ m₃
        (δ ≫ ((shiftFunctor C (1 : ℤ)).map ((h.t.truncGEπ 1).app A))) ∈ distTriang C)
    (hm₃ : v ≫ m₃ = g)
    (hex13 :
      ((shortComplexOfDistTriangle
        (Triangle.mk ((h.t.truncLTι 1).app A ≫ f) v w) h13).map
        (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact)
    :
    ((shortComplexOfDistTriangle (Triangle.mk f g δ) hT).map
      (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro β hβ
  have hex23 :=
    h.H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_one (C := C) h23 E
  rw [ShortComplex.ab_exact_iff] at hex23 hex13
  have hβ' : β ≫ (h.H0primeFunctor (C := C)).map (v ≫ m₃) = 0 := by
    simpa [hm₃] using hβ
  have hβvm₃ :
      (β ≫ (h.H0primeFunctor (C := C)).map v) ≫
          (h.H0primeFunctor (C := C)).map m₃ = 0 := by
    simpa [Functor.map_comp, Category.assoc] using hβ'
  obtain ⟨a, ha⟩ := hex23 (β ≫ (h.H0primeFunctor (C := C)).map v) hβvm₃
  have ha_zero : a = 0 := by
    exact IsZero.eq_of_tgt (h.isZero_H0prime_of_isGE_one (C := C)
      (X := (h.t.truncGE 1).obj A)) a 0
  have ha_m₁_zero : a ≫ (h.H0primeFunctor (C := C)).map m₁ = 0 := by
    cases ha_zero
    exact zero_comp
  have hβv_zero : β ≫ (h.H0primeFunctor (C := C)).map v = 0 := by
    calc
      β ≫ (h.H0primeFunctor (C := C)).map v =
          a ≫ (h.H0primeFunctor (C := C)).map m₁ := by
            simpa using ha.symm
      _ = 0 := ha_m₁_zero
  obtain ⟨a', ha'⟩ := hex13 β hβv_zero
  refine ⟨a' ≫ (h.H0primeFunctor (C := C)).map ((h.t.truncLTι 1).app A), ?_⟩
  calc
    (a' ≫ (h.H0primeFunctor (C := C)).map ((h.t.truncLTι 1).app A)) ≫
        (h.H0primeFunctor (C := C)).map f =
      a' ≫ (h.H0primeFunctor (C := C)).map (((h.t.truncLTι 1).app A) ≫ f) := by
        simp [Functor.map_comp, Category.assoc]
    _ = a' ≫
        (h.H0primeFunctor (C := C)).map (((h.t.truncLTι 1).app A) ≫ f) := by rfl
    _ = β := by simpa [Functor.map_comp] using ha'

theorem HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_zero_of_heart_case
    (h : HeartStabilityData C) [IsTriangulated C]
    {A X₂ X₃ : C} [h.t.IsGE A 0]
    {f : A ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C)
    (E : h.t.heart.FullSubcategory)
    (hHeart :
      ∀ (A0 : h.t.heart.FullSubcategory) {Y₂ Y₃ : C}
        {f0 : A0.obj ⟶ Y₂} {g0 : Y₂ ⟶ Y₃} {δ0 : Y₃ ⟶ A0.obj⟦(1 : ℤ)⟧}
        (hT0 : Triangle.mk f0 g0 δ0 ∈ distTriang C),
        ((shortComplexOfDistTriangle (Triangle.mk f0 g0 δ0) hT0).map
          (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact) :
    ((shortComplexOfDistTriangle (Triangle.mk f g δ) hT).map
      (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
  let A0 : h.t.heart.FullSubcategory :=
    ⟨(h.t.truncLT 1).obj A, (h.t.mem_heart_iff _).mpr
      ⟨h.t.isLE_truncLT_obj A 1 0 (by grind), inferInstance⟩⟩
  obtain ⟨Z, v, w, m₁, m₃, h13, h23, hm₁, hmw, hm₃⟩ :=
    h.t.exists_truncLT_octahedral_split (C := C) hT 1
  have hex13 :
      ((shortComplexOfDistTriangle
        (Triangle.mk ((h.t.truncLTι 1).app A ≫ f) v w) h13).map
        (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
    simpa [A0] using hHeart A0 h13
  exact h.H0primeFunctor_preadditiveCoyoneda_exact_of_split_one
    (C := C) (A := A) (X₂ := X₂) (X₃ := X₃) (Z := Z) (f := f) (g := g) (δ := δ)
    (v := v) (w := w) (m₁ := m₁) (m₃ := m₃) E hT h13 h23 hm₃ hex13

theorem TStructure.isIso_truncLT_negOne_map_of_heart_source
    (t : TStructure C)
    (A : t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    IsIso ((t.truncLT (-1)).map g) := by
  let T : Triangle C := Triangle.mk f g δ
  have hrot : T.rotate ∈ distTriang C := by
    simpa [T] using rot_of_distTriang _ hT
  have hGE : t.IsGE (T.rotate.obj₃) (-1) := by
    change t.IsGE (A.obj⟦(1 : ℤ)⟧) (-1)
    letI : t.IsGE A.obj 0 := (t.mem_heart_iff A.obj).mp A.property |>.2
    simpa [T] using t.isGE_shift A.obj 0 1 (-1)
  simpa [T] using t.isIso₁_truncLT_map_of_isGE T.rotate hrot (-1) hGE

theorem HeartStabilityData.isZero_H0Functor_shift_obj_of_lt_bound
    (h : HeartStabilityData C) [inst : IsTriangulated C]
    {X : C} {m n : ℤ} (hmn : m < n) (hGE : h.t.IsGE X n) :
    IsZero (((@HeartStabilityData.H0Functor C _ _ _ _ _ _ inst h).shift m).obj X) := by
  letI := inst
  have hGE' : h.t.IsGE X (m + 1) := h.t.isGE_of_ge X (m + 1) n (by grind)
  have hzeroObj : IsZero ((h.t.truncGELE m m).obj X) := by
    dsimp [TStructure.truncGELE]
    exact Functor.map_isZero (h.t.truncGE m)
      (h.t.isZero_truncLE_obj_of_isGE m (m + 1) (by grind) X)
  have hzeroHeart : IsZero (h.heartCoh (C := C) m X) := by
    refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      (shiftFunctor C m).map_isZero hzeroObj
  exact IsZero.of_iso hzeroHeart (h.H0FunctorShiftObjIsoHeartCoh (C := C) m X)

theorem HeartStabilityData.isZero_H0Functor_shift_obj_of_gt_bound
    (h : HeartStabilityData C) [inst : IsTriangulated C]
    {X : C} {m n : ℤ} (hmn : n < m) (hLE : h.t.IsLE X n) :
    IsZero (((@HeartStabilityData.H0Functor C _ _ _ _ _ _ inst h).shift m).obj X) := by
  letI := inst
  have hLE' : h.t.IsLE X (m - 1) := h.t.isLE_of_le X n (m - 1) (by grind)
  have hzeroObj : IsZero ((h.t.truncGELE m m).obj X) := by
    dsimp [TStructure.truncGELE]
    letI : h.t.IsLE ((h.t.truncLE m).obj X) (m - 1) := by
      have hm : h.t.IsLE X m := h.t.isLE_of_le X n m (by grind)
      let e : (h.t.truncLE m).obj X ≅ X :=
        @asIso _ _ _ _ ((h.t.truncLEι m).app X) ((h.t.isLE_iff_isIso_truncLEι_app m X).mp hm)
      exact h.t.isLE_of_iso e.symm (m - 1)
    exact h.t.isZero_truncGE_obj_of_isLE (m - 1) m (by grind) ((h.t.truncLE m).obj X)
  have hzeroHeart : IsZero (h.heartCoh (C := C) m X) := by
    refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
    simpa [HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
      (shiftFunctor C m).map_isZero hzeroObj
  exact IsZero.of_iso hzeroHeart (h.H0FunctorShiftObjIsoHeartCoh (C := C) m X)

theorem eq_zero_congr_hasZeroMorphisms
    {D : Type*} [Category D] (I J : HasZeroMorphisms D)
    {X Y : D} {f : X ⟶ Y}
    (h : by
      letI : HasZeroMorphisms D := I
      exact f = 0) : by
      letI : HasZeroMorphisms D := J
      exact f = 0 := by
  cases Subsingleton.elim I J
  simpa using h

theorem shortComplex_exact_congr_hasZeroMorphisms
    {D : Type*} [Category D] (I J : HasZeroMorphisms D)
    {X₁ X₂ X₃ : D} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
    {wI : by
      letI : HasZeroMorphisms D := I
      exact f ≫ g = 0}
    {wJ : by
      letI : HasZeroMorphisms D := J
      exact f ≫ g = 0}
    (h : by
      letI : HasZeroMorphisms D := I
      exact (ShortComplex.mk f g wI).Exact) : by
      letI : HasZeroMorphisms D := J
      exact (ShortComplex.mk f g wJ).Exact := by
  cases Subsingleton.elim I J
  cases Subsingleton.elim wI wJ
  simpa using h

theorem ShortComplex.exact_of_eval
    {J : Type*} [Category J] {A : Type*} [Category A] [Abelian A]
    (S : ShortComplex (J ⥤ A))
    (hS : ∀ j : J, (S.map ((evaluation J A).obj j)).Exact) :
    S.Exact := by
  letI : Abelian (J ⥤ A) := inferInstance
  letI : S.HasHomology := inferInstance
  have hzeroEval (j : J) :
      ((evaluation J A).obj j).map S.f ≫ ((evaluation J A).obj j).map S.g = 0 := by
    change (S.f ≫ S.g).app j = 0
    exact NatTrans.congr_app S.zero j
  rw [S.exact_iff_epi_kernel_lift]
  rw [NatTrans.epi_iff_epi_app]
  intro j
  let E : (J ⥤ A) ⥤ A := (evaluation J A).obj j
  let φ : S.X₁ ⟶ kernel S.g := kernel.lift S.g S.f S.zero
  have hφ :
      E.map φ ≫ kernelComparison S.g E =
        kernel.lift (E.map S.g) (E.map S.f) (by
          simpa [E] using hzeroEval j) := by
    simpa [E, φ] using
      (map_lift_kernelComparison (G := E) (f := S.g) (h := S.f) S.zero)
  have hExact : (S.map E).Exact := hS j
  have hEpi :
      Epi (kernel.lift (E.map S.g) (E.map S.f) (by
        simpa [E] using hzeroEval j)) :=
    hExact.epi_kernelLift
  have hCompEpi : Epi (E.map φ ≫ kernelComparison S.g E) := by
    rw [hφ]
    infer_instance
  exact (epi_comp_iff_of_isIso (E.map φ) (kernelComparison S.g E)).mp hCompEpi

theorem ShortComplex.preadditiveCoyoneda_exact_of_f_is_kernel
    {D : Type*} [Category D] [Preadditive D] {S : ShortComplex D}
    (hS : IsLimit (KernelFork.ofι S.f S.zero)) (E : D) :
    (S.map (preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro β hβ
  refine ⟨hS.lift (KernelFork.ofι β ?_), hS.fac _ WalkingParallelPair.zero⟩
  simpa using hβ

theorem HeartStabilityData.H0primeFunctor_comp_preadditiveYoneda_eval
    (h : HeartStabilityData C) (E : h.t.heart.FullSubcategory) :
    (h.H0primeFunctor (C := C) ⋙
        (preadditiveYoneda :
          h.t.heart.FullSubcategory ⥤ h.t.heart.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat)) ⋙
      (evaluation h.t.heart.FullSubcategoryᵒᵖ AddCommGrpCat).obj (Opposite.op E) =
        h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E) := by
  rfl

theorem HeartStabilityData.H0primeFunctor_preadditiveYoneda_isHomological_of_eval
    (h : HeartStabilityData C)
    (hExact :
      ∀ (T : Triangle C) (hT : T ∈ distTriang C) (E : h.t.heart.FullSubcategory),
        ((shortComplexOfDistTriangle T hT).map
          (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact) :
    Functor.IsHomological
      (h.H0primeFunctor (C := C) ⋙
        (preadditiveYoneda :
          h.t.heart.FullSubcategory ⥤ h.t.heart.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat)) := by
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  refine ⟨fun T hT ↦ ?_⟩
  apply ShortComplex.exact_of_eval
  intro E
  simpa [HeartStabilityData.H0primeFunctor_comp_preadditiveYoneda_eval] using
    hExact T hT (Opposite.unop E)

theorem HeartStabilityData.H0primeFunctor_isHomological_of_preadditiveYoneda
    (h : HeartStabilityData C) [IsTriangulated C]
    [Functor.IsHomological
      (h.H0primeFunctor (C := C) ⋙
        (preadditiveYoneda :
          h.t.heart.FullSubcategory ⥤ h.t.heart.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat))] :
    Functor.IsHomological (h.H0primeFunctor (C := C)) := by
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  refine ⟨fun T hT ↦ ?_⟩
  let S := (shortComplexOfDistTriangle T hT).map (h.H0primeFunctor (C := C))
  have hS :
      (S.map
        (preadditiveYoneda :
          h.t.heart.FullSubcategory ⥤ h.t.heart.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat)).Exact := by
    simpa [S] using
      (Functor.map_distinguished_exact
        (F := h.H0primeFunctor (C := C) ⋙
          (preadditiveYoneda :
            h.t.heart.FullSubcategory ⥤ h.t.heart.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat))
        T hT)
  exact Functor.reflects_exact_of_faithful
    (preadditiveYoneda :
      h.t.heart.FullSubcategory ⥤ h.t.heart.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat) S hS

theorem HeartStabilityData.H0Functor_isHomological_of_H0primeFunctor
    (h : HeartStabilityData C)
    [Functor.IsHomological (h.H0primeFunctor (C := C))] :
    Functor.IsHomological (h.H0Functor (C := C)) :=
  Functor.IsHomological.of_iso (h.H0FunctorIsoH0primeFunctor (C := C)).symm

theorem HeartStabilityData.H0Functor_isHomological_of_eval
    (h : HeartStabilityData C) [IsTriangulated C]
    (hExact :
      ∀ (T : Triangle C) (hT : T ∈ distTriang C) (E : h.t.heart.FullSubcategory),
        ((shortComplexOfDistTriangle T hT).map
          (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact) :
    Functor.IsHomological (h.H0Functor (C := C)) := by
  letI :
      Functor.IsHomological
        (h.H0primeFunctor (C := C) ⋙
          (preadditiveYoneda :
            h.t.heart.FullSubcategory ⥤ h.t.heart.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat)) :=
    h.H0primeFunctor_preadditiveYoneda_isHomological_of_eval (C := C) hExact
  letI : Functor.IsHomological (h.H0primeFunctor (C := C)) :=
    h.H0primeFunctor_isHomological_of_preadditiveYoneda (C := C)
  exact h.H0Functor_isHomological_of_H0primeFunctor (C := C)

theorem HeartStabilityData.H0Functor_isHomological_of_eval_of_heart_case
    (h : HeartStabilityData C) [IsTriangulated C]
    (hHeart :
      ∀ (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
        {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
        (hT : Triangle.mk f g δ ∈ distTriang C) (E : h.t.heart.FullSubcategory),
        ((shortComplexOfDistTriangle (Triangle.mk f g δ) hT).map
          (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact) :
    Functor.IsHomological (h.H0Functor (C := C)) := by
  apply h.H0Functor_isHomological_of_eval (C := C)
  intro T hT E
  obtain ⟨Z, v, w, m₁, m₃, h13, h23, hm₁, hmw, hm₃, hiff⟩ :=
    h.H0primeFunctor_preadditiveCoyoneda_exact_iff_octahedral_split (C := C) T hT E
  have h23Exact :
      ((shortComplexOfDistTriangle
        (Triangle.mk m₁ m₃
          (T.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map ((h.t.truncGEπ 0).app T.obj₁)))) h23).map
        (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
    exact h.H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_zero_of_heart_case
      (C := C) (A := (h.t.truncGE 0).obj T.obj₁) (X₂ := Z) (X₃ := T.obj₃)
      (f := m₁) (g := m₃)
      (δ := T.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map ((h.t.truncGEπ 0).app T.obj₁)))
      h23 E (fun A {X₂} {X₃} {f} {g} {δ} hT ↦ hHeart A hT E)
  exact hiff.mpr h23Exact

/-- A homological functor on a triangulated category induces a spectral object by
applying the long exact homology sequence to each distinguished triangle. -/
noncomputable def SpectralObject.mapHomologicalFunctor
    {ι : Type*} [Category ι] {A : Type*} [Category A] [Abelian A]
    (X : Triangulated.SpectralObject C ι) (F : C ⥤ A)
    [F.IsHomological] [F.ShiftSequence ℤ] :
    Abelian.SpectralObject A ι where
  H n := X.ω₁ ⋙ F.shift n
  δ' n₀ n₁ h :=
    { app := fun D => F.homologySequenceδ (X.ω₂.obj D) n₀ n₁ h
      naturality := by
        intro D D' φ
        simpa using
          F.homologySequenceδ_naturality (X.ω₂.obj D) (X.ω₂.obj D') (X.ω₂.map φ) n₀ n₁ h }
  exact₁' n₀ n₁ h D := by
    let hEx := F.homologySequence_exact₁ (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n₀ n₁ h
    simpa using hEx.exact_toComposableArrows
  exact₂' n D := by
    let hEx := F.homologySequence_exact₂ (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n
    simpa using hEx.exact_toComposableArrows
  exact₃' n₀ n₁ h D := by
    let hEx := F.homologySequence_exact₃ (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n₀ n₁ h
    simpa using hEx.exact_toComposableArrows

/-- The five-term exact segment in the long exact sequence of a homological
`H⁰_t` yields the corresponding Grothendieck-group relation in the heart. -/
theorem HeartStabilityData.H0Functor_five_term_relation
    (h : HeartStabilityData C)
    [Abelian h.t.heart.FullSubcategory]
    [Functor.IsHomological (h.H0Functor (C := C))]
    (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) :
    HeartK0.of (C := C) h (((h.H0Functor (C := C)).shift n).obj T.obj₂) -
        HeartK0.of (C := C) h (((h.H0Functor (C := C)).shift n).obj T.obj₃) +
          HeartK0.of (C := C) h (((h.H0Functor (C := C)).shift (n + 1)).obj T.obj₁) =
      HeartK0.of (C := C) h
          (Limits.image (((h.H0Functor (C := C)).shift n).map T.mor₁)) +
        HeartK0.of (C := C) h
          (Limits.image (((h.H0Functor (C := C)).shift (n + 1)).map T.mor₁)) := by
  let A : Abelian h.t.heart.FullSubcategory := inferInstance
  let P : Preadditive h.t.heart.FullSubcategory := A.toPreadditive
  let J : HasZeroMorphisms h.t.heart.FullSubcategory :=
    h.t.heart.instHasZeroMorphismsFullSubcategory
  have hw₀ :
      ((h.H0Functor (C := C)).shift n).map T.mor₁ ≫
          ((h.H0Functor (C := C)).shift n).map T.mor₂ = 0 :=
    eq_zero_congr_hasZeroMorphisms
      (@Preadditive.preadditiveHasZeroMorphisms _ _ P) J
      ((h.H0Functor (C := C)).homologySequence_comp T hT n)
  have hw₁ :
      ((h.H0Functor (C := C)).shift n).map T.mor₂ ≫
          (h.H0Functor (C := C)).homologySequenceδ T n (n + 1) rfl = 0 :=
    eq_zero_congr_hasZeroMorphisms
      (@Preadditive.preadditiveHasZeroMorphisms _ _ P) J
      ((h.H0Functor (C := C)).comp_homologySequenceδ T hT n (n + 1) rfl)
  have hw₂ :
      (h.H0Functor (C := C)).homologySequenceδ T n (n + 1) rfl ≫
          ((h.H0Functor (C := C)).shift (n + 1)).map T.mor₁ = 0 :=
    eq_zero_congr_hasZeroMorphisms
      (@Preadditive.preadditiveHasZeroMorphisms _ _ P) J
      ((h.H0Functor (C := C)).homologySequenceδ_comp T hT n (n + 1) rfl)
  have hex₀ :
      (ShortComplex.mk (((h.H0Functor (C := C)).shift n).map T.mor₁)
        (((h.H0Functor (C := C)).shift n).map T.mor₂) hw₀).Exact :=
    shortComplex_exact_congr_hasZeroMorphisms
      (@Preadditive.preadditiveHasZeroMorphisms _ _ P) J
      ((h.H0Functor (C := C)).homologySequence_exact₂ T hT n)
  have hex₁ :
      (ShortComplex.mk (((h.H0Functor (C := C)).shift n).map T.mor₂)
        ((h.H0Functor (C := C)).homologySequenceδ T n (n + 1) rfl) hw₁).Exact :=
    shortComplex_exact_congr_hasZeroMorphisms
      (@Preadditive.preadditiveHasZeroMorphisms _ _ P) J
      ((h.H0Functor (C := C)).homologySequence_exact₃ T hT n (n + 1) rfl)
  have hex₂ :
      (ShortComplex.mk ((h.H0Functor (C := C)).homologySequenceδ T n (n + 1) rfl)
        (((h.H0Functor (C := C)).shift (n + 1)).map T.mor₁) hw₂).Exact :=
    shortComplex_exact_congr_hasZeroMorphisms
      (@Preadditive.preadditiveHasZeroMorphisms _ _ P) J
      ((h.H0Functor (C := C)).homologySequence_exact₁ T hT n (n + 1) rfl)
  exact HeartK0.of_exact_five (C := C) h hw₀ hw₁ hw₂ hex₀ hex₁ hex₂


end Proposition53

end CategoryTheory.Triangulated
