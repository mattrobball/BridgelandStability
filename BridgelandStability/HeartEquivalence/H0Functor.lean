/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.HeartEquivalence.Basic

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


/-! ## H0 Functor Construction -/

/-- The degree-`n` heart cohomology object of `E`, realized as the pure
truncation `τ^[n,n]E` shifted into the heart. -/
def HeartStabilityData.heartCoh
    (h : HeartStabilityData C) (n : ℤ) (E : C) :
    h.t.heart.FullSubcategory :=
  h.heartShiftOfPure (C := C) (X := (h.t.truncGELE n n).obj E) n inferInstance inferInstance

/-- The degree-`n` heart cohomology object assembled into a functor
`C ⥤ heart(t)`. This packages the object-level construction
`HeartStabilityData.heartCoh` so later arguments can use functoriality directly. -/
noncomputable def HeartStabilityData.heartCohFunctor
    (h : HeartStabilityData C) (n : ℤ) : C ⥤ h.t.heart.FullSubcategory :=
  ObjectProperty.lift _ (((h.t.truncGELE n n) ⋙ shiftFunctor C n))
    (fun E ↦ by
      rw [h.t.mem_heart_iff]
      constructor
      · simpa using (h.t.isLE_shift ((h.t.truncGELE n n).obj E) n n 0 (by omega))
      · simpa using (h.t.isGE_shift ((h.t.truncGELE n n).obj E) n n 0 (by omega)))

instance HeartStabilityData.heartCohFunctor_additive
    (h : HeartStabilityData C) (n : ℤ) :
    Functor.Additive (h.heartCohFunctor (C := C) n) where
  map_add := by
    intro X Y f g
    ext
    change (shiftFunctor C n).map ((h.t.truncGE n).map ((h.t.truncLE n).map (f + g))) =
      (shiftFunctor C n).map ((h.t.truncGE n).map ((h.t.truncLE n).map f)) +
        (shiftFunctor C n).map ((h.t.truncGE n).map ((h.t.truncLE n).map g))
    simp [Functor.map_add]

@[simp]
theorem HeartStabilityData.heartCohFunctor_obj
    (h : HeartStabilityData C) (n : ℤ) (E : C) :
    (h.heartCohFunctor (C := C) n).obj E = h.heartCoh (C := C) n E := rfl

/-- Degree-zero heart cohomology as a functor `C ⥤ heart(t)`. -/
noncomputable abbrev HeartStabilityData.H0Functor
    (h : HeartStabilityData C) : C ⥤ h.t.heart.FullSubcategory :=
  h.heartCohFunctor (C := C) 0

instance HeartStabilityData.H0Functor_additive
    (h : HeartStabilityData C) :
    Functor.Additive (h.H0Functor (C := C)) := by
  dsimp [HeartStabilityData.H0Functor]
  infer_instance

/-- The tautological shift-sequence structure on `H⁰_t`, used later to compare the
generic homological-functor API with the explicit `heartCoh n` objects already defined
in this file. -/
noncomputable instance HeartStabilityData.H0Functor_shiftSequence
    (h : HeartStabilityData C) :
    (h.H0Functor (C := C)).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

/-- The degree-zero cohomology object, written in the alternative normal form
`τ≤0(τ≥0 X)`. This is often a more convenient target for maps out of `H⁰(X)`. -/
def HeartStabilityData.H0prime
    (h : HeartStabilityData C) (X : C) : h.t.heart.FullSubcategory :=
  ⟨(h.t.truncLEGE 0 0).obj X, by
    rw [h.t.mem_heart_iff]
    constructor
    · exact show h.t.IsLE ((h.t.truncLE 0).obj ((h.t.truncGE 0).obj X)) 0 by infer_instance
    · letI : h.t.IsGE ((h.t.truncGE 0).obj X) 0 := by infer_instance
      exact show h.t.IsGE ((h.t.truncLE 0).obj ((h.t.truncGE 0).obj X)) 0 by infer_instance⟩

/-- The degree-zero cohomology object in the normal form `τ≤0(τ≥0 X)` assembled
into a functor `C ⥤ heart(t)`. -/
noncomputable def HeartStabilityData.H0primeFunctor
    (h : HeartStabilityData C) : C ⥤ h.t.heart.FullSubcategory where
  obj := h.H0prime (C := C)
  map {X Y} f := ObjectProperty.homMk ((h.t.truncLEGE 0 0).map f)
  map_id X := by
    ext
    simp [HeartStabilityData.H0prime, TStructure.truncLEGE]
  map_comp f g := by
    ext
    simp [HeartStabilityData.H0prime, TStructure.truncLEGE]

instance HeartStabilityData.H0primeFunctor_additive
    (h : HeartStabilityData C) :
    Functor.Additive (h.H0primeFunctor (C := C)) where
  map_add := by
    intro X Y f g
    ext
    change (h.t.truncLE 0).map ((h.t.truncGE 0).map (f + g)) =
      (h.t.truncLE 0).map ((h.t.truncGE 0).map f) +
        (h.t.truncLE 0).map ((h.t.truncGE 0).map g)
    simp [Functor.map_add]

/-- The two standard normal forms `τ≥0(τ≤0 X)` and `τ≤0(τ≥0 X)` for `H⁰(X)` agree. -/
noncomputable def HeartStabilityData.H0ObjIsoH0prime
    (h : HeartStabilityData C) (X : C) :
    (h.H0Functor (C := C)).obj X ≅ h.H0prime (C := C) X := by
  refine ObjectProperty.isoMk _ ?_
  simpa [HeartStabilityData.H0Functor, HeartStabilityData.heartCohFunctor,
    HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure,
    HeartStabilityData.H0prime] using
      ((shiftFunctorZero C ℤ).app ((h.t.truncGELE 0 0).obj X) ≪≫
        (h.t.truncGELEIsoLEGE 0 0).app X)

@[reassoc]
theorem HeartStabilityData.H0ObjIsoH0prime_hom_naturality
    (h : HeartStabilityData C) {X Y : C} (f : X ⟶ Y) :
    (h.H0Functor (C := C)).map f ≫ (h.H0ObjIsoH0prime (C := C) Y).hom =
      (h.H0ObjIsoH0prime (C := C) X).hom ≫
        (ObjectProperty.homMk ((h.t.truncLEGE 0 0).map f) :
          h.H0prime (C := C) X ⟶ h.H0prime (C := C) Y) := by
  ext
  change
    (shiftFunctor C 0).map ((h.t.truncGE 0).map ((h.t.truncLE 0).map f)) ≫
        (shiftFunctorZero C ℤ).hom.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj Y)) ≫
          (h.t.truncGELEIsoLEGE 0 0).hom.app Y =
      ((shiftFunctorZero C ℤ).hom.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj X)) ≫
          (h.t.truncGELEIsoLEGE 0 0).hom.app X) ≫
        (h.t.truncLE 0).map ((h.t.truncGE 0).map f)
  calc
    (shiftFunctor C 0).map ((h.t.truncGE 0).map ((h.t.truncLE 0).map f)) ≫
          (shiftFunctorZero C ℤ).hom.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj Y)) ≫
            (h.t.truncGELEIsoLEGE 0 0).hom.app Y
        =
          ((shiftFunctorZero C ℤ).hom.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj X)) ≫
            (h.t.truncGE 0).map ((h.t.truncLE 0).map f)) ≫
              (h.t.truncGELEIsoLEGE 0 0).hom.app Y := by
                rw [← Category.assoc]
                simpa using
                  congrArg (fun k =>
                    k ≫ (h.t.truncGELEIsoLEGE 0 0).hom.app Y)
                    (NatTrans.naturality (shiftFunctorZero C ℤ).hom
                      ((h.t.truncGE 0).map ((h.t.truncLE 0).map f)))
    _ =
          ((shiftFunctorZero C ℤ).hom.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj X)) ≫
            (h.t.truncGELEIsoLEGE 0 0).hom.app X) ≫
              (h.t.truncLE 0).map ((h.t.truncGE 0).map f) := by
                simpa [TStructure.truncGELE, TStructure.truncLEGE, Category.assoc] using
                  congrArg (fun k =>
                    (shiftFunctorZero C ℤ).hom.app ((h.t.truncGE 0).obj ((h.t.truncLE 0).obj X)) ≫
                      k)
                    (NatTrans.naturality ((h.t.truncGELEIsoLEGE 0 0).hom) f)

/-- The normal forms `τ≥0(τ≤0 X)` and `τ≤0(τ≥0 X)` assemble into a natural isomorphism
of functors `C ⥤ heart(t)`. -/
noncomputable def HeartStabilityData.H0FunctorIsoH0primeFunctor
    (h : HeartStabilityData C) : h.H0Functor (C := C) ≅ h.H0primeFunctor (C := C) :=
  NatIso.ofComponents (fun X ↦ h.H0ObjIsoH0prime (C := C) X) fun f ↦
    h.H0ObjIsoH0prime_hom_naturality (C := C) f

section

omit [IsTriangulated C]

@[reassoc]
theorem TStructure.truncGE_map_comp_descTruncGE
    (t : TStructure C)
    {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) (n : ℤ) [t.IsGE Z n] :
    (t.truncGE n).map g ≫ t.descTruncGE f n = t.descTruncGE (g ≫ f) n := by
  apply t.from_truncGE_obj_ext
  rw [← Category.assoc, t.truncGEπ_naturality]
  have h₁ : (g ≫ (t.truncGEπ n).app Y) ≫ t.descTruncGE f n = g ≫ f := by
    simpa [Category.assoc] using
      congrArg (fun k => g ≫ k) (t.π_descTruncGE (f := f) (n := n))
  exact h₁.trans (t.π_descTruncGE (f := g ≫ f) (n := n)).symm

omit [IsTriangulated C] in
@[simp]
theorem TStructure.descTruncGE_zero
    (t : TStructure C)
    {X Y : C} (n : ℤ) [t.IsGE Y n] :
    t.descTruncGE (0 : X ⟶ Y) n = 0 := by
  apply t.from_truncGE_obj_ext
  rw [t.π_descTruncGE]
  simp

omit [IsTriangulated C] in
@[simp]
theorem TStructure.descTruncGE_add
    (t : TStructure C)
    {X Y : C} (f g : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
    t.descTruncGE (f + g) n = t.descTruncGE f n + t.descTruncGE g n := by
  apply t.from_truncGE_obj_ext
  rw [t.π_descTruncGE, CategoryTheory.Preadditive.comp_add, t.π_descTruncGE, t.π_descTruncGE]
  rfl

end

/-- A morphism from a heart object into `X` factors canonically through the
degree-zero normal form `H0prime X = τ≤0(τ≥0 X)`. -/
noncomputable def HeartStabilityData.toH0primeHom
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} (f : E.obj ⟶ X) :
    E ⟶ h.H0prime (C := C) X :=
  letI : h.t.IsLE E.obj 0 := (h.t.mem_heart_iff _).mp E.property |>.1
  ObjectProperty.homMk (h.t.liftTruncLE (f ≫ (h.t.truncGEπ 0).app X) 0)

@[reassoc (attr := simp)]
theorem HeartStabilityData.toH0primeHom_hom
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} (f : E.obj ⟶ X) :
    (h.toH0primeHom (C := C) E f).hom ≫
        (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) =
      f ≫ (h.t.truncGEπ 0).app X := by
  letI : h.t.IsLE E.obj 0 := (h.t.mem_heart_iff _).mp E.property |>.1
  change h.t.liftTruncLE (f ≫ (h.t.truncGEπ 0).app X) 0 ≫
      (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) =
    f ≫ (h.t.truncGEπ 0).app X
  simpa using h.t.liftTruncLE_ι (f ≫ (h.t.truncGEπ 0).app X) 0

theorem HeartStabilityData.hom_ext_toH0prime
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C}
    {β₁ β₂ : E ⟶ h.H0prime (C := C) X}
    (hβ :
      β₁.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) =
        β₂.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X)) :
    β₁ = β₂ := by
  letI : h.t.IsLE E.obj 0 := (h.t.mem_heart_iff _).mp E.property |>.1
  ext
  exact h.t.to_truncLE_obj_ext hβ

theorem HeartStabilityData.toH0primeHom_eq
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} (f : E.obj ⟶ X)
    (β : E ⟶ h.H0prime (C := C) X)
    (hβ :
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) =
        f ≫ (h.t.truncGEπ 0).app X) :
    β = h.toH0primeHom (C := C) E f := by
  apply h.hom_ext_toH0prime (C := C) E
  rw [hβ, h.toH0primeHom_hom (C := C) E f]

@[reassoc]
theorem HeartStabilityData.toH0primeHom_comp_H0primeFunctor_map
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X Y : C} (f : E.obj ⟶ X) (g : X ⟶ Y) :
    h.toH0primeHom (C := C) E f ≫ (h.H0primeFunctor (C := C)).map g =
      h.toH0primeHom (C := C) E (f ≫ g) := by
  apply h.hom_ext_toH0prime (C := C) E
  rw [h.toH0primeHom_hom (C := C) E (f ≫ g)]
  let lhs :=
    (h.toH0primeHom (C := C) E f).hom ≫
      (h.t.truncLE 0).map ((h.t.truncGE 0).map g) ≫
        (h.t.truncLEι 0).app ((h.t.truncGE 0).obj Y)
  let mid :=
    (h.toH0primeHom (C := C) E f).hom ≫
      (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫
        (h.t.truncGE 0).map g
  let rhs :=
    f ≫ (h.t.truncGEπ 0).app X ≫ (h.t.truncGE 0).map g
  have h₁ : lhs = mid := by
    exact
      (by
        simpa only [lhs, mid, Category.assoc] using
          congrArg
            (fun k => (h.toH0primeHom (C := C) E f).hom ≫ k)
            ((h.t.truncLEι 0).naturality ((h.t.truncGE 0).map g))
        : lhs = mid)
  have h₂ : mid = rhs := by
    dsimp [mid, rhs]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun k => k ≫ (h.t.truncGE 0).map g)
      (h.toH0primeHom_hom (C := C) E f)
  have h₃ : rhs = f ≫ g ≫ (h.t.truncGEπ 0).app Y := by
    exact
      (by
        simpa only [rhs, Category.assoc] using
          congrArg (fun k => f ≫ k) (h.t.truncGEπ_naturality 0 g)
        : rhs = f ≫ g ≫ (h.t.truncGEπ 0).app Y)
  simpa [HeartStabilityData.H0primeFunctor, TStructure.truncLEGE, Category.assoc, lhs] using
    h₁.trans (h₂.trans h₃)

@[simp]
theorem HeartStabilityData.toH0primeHom_zero
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} :
    h.toH0primeHom (C := C) E (0 : E.obj ⟶ X) = 0 := by
  apply h.hom_ext_toH0prime (C := C) E
  rw [h.toH0primeHom_hom (C := C) E (0 : E.obj ⟶ X)]
  simp

@[simp]
theorem HeartStabilityData.toH0primeHom_add
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} (f g : E.obj ⟶ X) :
    h.toH0primeHom (C := C) E (f + g) =
      h.toH0primeHom (C := C) E f + h.toH0primeHom (C := C) E g := by
  apply h.hom_ext_toH0prime (C := C) E
  rw [h.toH0primeHom_hom (C := C) E (f + g)]
  rw [CategoryTheory.Preadditive.add_comp]
  change
    f ≫ (h.t.truncGEπ 0).app X + g ≫ (h.t.truncGEπ 0).app X =
      ((h.toH0primeHom (C := C) E f).hom + (h.toH0primeHom (C := C) E g).hom) ≫
        (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X)
  rw [CategoryTheory.Preadditive.add_comp]
  rw [h.toH0primeHom_hom (C := C) E f, h.toH0primeHom_hom (C := C) E g]
  rfl

/-- For a heart object `E`, maps `E.obj ⟶ X` in the ambient triangulated category induce
maps `E ⟶ H⁰'(X)` in the heart, naturally in `X`. -/
noncomputable def HeartStabilityData.toH0primeNatTrans
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) :
    preadditiveCoyoneda.obj (Opposite.op E.obj) ⟶
      h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E) where
  app X := AddCommGrpCat.ofHom
    { toFun := fun f => h.toH0primeHom (C := C) E f
      map_zero' := h.toH0primeHom_zero (C := C) E (X := X)
      map_add' := fun f g => h.toH0primeHom_add (C := C) E f g }
  naturality {X Y} g := by
    ext f
    simpa [Functor.comp_map] using
      (h.toH0primeHom_comp_H0primeFunctor_map (C := C) E f g).symm

/-- If `X ∈ t.≥0`, a morphism into `H0prime X` can be read as a morphism into
`X` by composing with the canonical map `τ≥0 X ⟶ X`. -/
noncomputable def HeartStabilityData.fromH0primeHom_of_isGE
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} [h.t.IsGE X 0]
    (β : E ⟶ h.H0prime (C := C) X) :
    E.obj ⟶ X :=
  β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫ (asIso ((h.t.truncGEπ 0).app X)).inv

@[reassoc (attr := simp)]
theorem HeartStabilityData.fromH0primeHom_of_isGE_hom
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} [h.t.IsGE X 0]
    (β : E ⟶ h.H0prime (C := C) X) :
    h.fromH0primeHom_of_isGE (C := C) E β ≫ (h.t.truncGEπ 0).app X =
      β.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) := by
  simp [HeartStabilityData.fromH0primeHom_of_isGE, Category.assoc]

theorem HeartStabilityData.toH0primeHom_fromH0primeHom_of_isGE
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} [h.t.IsGE X 0]
    (β : E ⟶ h.H0prime (C := C) X) :
    h.toH0primeHom (C := C) E (h.fromH0primeHom_of_isGE (C := C) E β) = β := by
  symm
  exact h.toH0primeHom_eq (C := C) E
    (h.fromH0primeHom_of_isGE (C := C) E β) β
    (by simpa using h.fromH0primeHom_of_isGE_hom (C := C) E β)

theorem HeartStabilityData.fromH0primeHom_of_isGE_toH0primeHom
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} [h.t.IsGE X 0]
    (f : E.obj ⟶ X) :
    h.fromH0primeHom_of_isGE (C := C) E (h.toH0primeHom (C := C) E f) = f := by
  apply (cancel_mono ((h.t.truncGEπ 0).app X)).1
  exact
    (h.fromH0primeHom_of_isGE_hom (C := C) E (h.toH0primeHom (C := C) E f)).trans
      (h.toH0primeHom_hom (C := C) E f)

@[simp]
theorem HeartStabilityData.fromH0primeHom_of_isGE_zero
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} [h.t.IsGE X 0] :
    h.fromH0primeHom_of_isGE (C := C) E (0 : E ⟶ h.H0prime (C := C) X) = 0 := by
  simp [HeartStabilityData.fromH0primeHom_of_isGE]

theorem HeartStabilityData.fromH0primeHom_of_isGE_add
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X : C} [h.t.IsGE X 0]
    (β₁ β₂ : E ⟶ h.H0prime (C := C) X) :
    h.fromH0primeHom_of_isGE (C := C) E (β₁ + β₂) =
      h.fromH0primeHom_of_isGE (C := C) E β₁ +
        h.fromH0primeHom_of_isGE (C := C) E β₂ := by
  change
    (β₁.hom + β₂.hom) ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫
        (asIso ((h.t.truncGEπ 0).app X)).inv =
      β₁.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫
          (asIso ((h.t.truncGEπ 0).app X)).inv +
        β₂.hom ≫ (h.t.truncLEι 0).app ((h.t.truncGE 0).obj X) ≫
          (asIso ((h.t.truncGEπ 0).app X)).inv
  repeat rw [CategoryTheory.Preadditive.add_comp]

/-- For `X ∈ t.≥0`, morphisms from a heart object to `X` are additively equivalent
to morphisms into `H0prime X`. -/
noncomputable def HeartStabilityData.toH0primeIsoOfIsGE
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) (X : C) [h.t.IsGE X 0] :
    (E.obj ⟶ X) ≃+ (E ⟶ h.H0prime (C := C) X) where
  toFun := h.toH0primeHom (C := C) E
  invFun := h.fromH0primeHom_of_isGE (C := C) E
  left_inv := h.fromH0primeHom_of_isGE_toH0primeHom (C := C) E
  right_inv := h.toH0primeHom_fromH0primeHom_of_isGE (C := C) E
  map_add' := h.toH0primeHom_add (C := C) E

/-- `H0prime X` is canonically unchanged by replacing `X` with its truncation
`τ≥0 X`. -/
noncomputable def HeartStabilityData.H0primeObjIsoTruncGE
    (h : HeartStabilityData C) (X : C) :
    h.H0prime (C := C) X ≅ h.H0prime (C := C) ((h.t.truncGE 0).obj X) := by
  refine ObjectProperty.isoMk _ ?_
  simpa [HeartStabilityData.H0prime] using
    (h.t.truncLE 0).mapIso (asIso ((h.t.truncGE 0).map ((h.t.truncGEπ 0).app X)))

@[reassoc]
theorem HeartStabilityData.H0primeObjIsoTruncGE_hom_naturality
    (h : HeartStabilityData C) {X Y : C} (g : X ⟶ Y) :
    (h.H0primeObjIsoTruncGE (C := C) X).hom ≫
        (h.H0primeFunctor (C := C)).map ((h.t.truncGE 0).map g) =
      (h.H0primeFunctor (C := C)).map g ≫
        (h.H0primeObjIsoTruncGE (C := C) Y).hom := by
  ext
  simpa [HeartStabilityData.H0primeObjIsoTruncGE, HeartStabilityData.H0primeFunctor,
    HeartStabilityData.H0prime, TStructure.truncLEGE, Functor.map_comp] using
    congrArg ((h.t.truncLE 0).map)
      (congrArg ((h.t.truncGE 0).map) (h.t.truncGEπ_naturality 0 g))

@[reassoc]
theorem HeartStabilityData.H0primeObjIsoTruncGE_inv_naturality
    (h : HeartStabilityData C) {X Y : C} (g : X ⟶ Y) :
    (h.H0primeObjIsoTruncGE (C := C) X).inv ≫ (h.H0primeFunctor (C := C)).map g =
      (h.H0primeFunctor (C := C)).map ((h.t.truncGE 0).map g) ≫
        (h.H0primeObjIsoTruncGE (C := C) Y).inv := by
  apply (Iso.eq_comp_inv (h.H0primeObjIsoTruncGE (C := C) Y)).2
  calc
    ((h.H0primeObjIsoTruncGE (C := C) X).inv ≫ (h.H0primeFunctor (C := C)).map g) ≫
        (h.H0primeObjIsoTruncGE (C := C) Y).hom =
      (h.H0primeObjIsoTruncGE (C := C) X).inv ≫
        ((h.H0primeFunctor (C := C)).map g ≫
          (h.H0primeObjIsoTruncGE (C := C) Y).hom) := by
            simp [Category.assoc]
    _ = (h.H0primeFunctor (C := C)).map ((h.t.truncGE 0).map g) := by
      simpa using
        (Iso.inv_comp_eq (h.H0primeObjIsoTruncGE (C := C) X)).2
          ((h.H0primeObjIsoTruncGE_hom_naturality (C := C) g).symm)

/-- Transport the comparison for `τ≥0 X` along `H0prime X ≅ H0prime (τ≥0 X)` to
compare morphisms into `τ≥0 X` with morphisms into `H0prime X`. -/
noncomputable def HeartStabilityData.toH0primeIsoViaTruncGE
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) (X : C) :
    (E.obj ⟶ (h.t.truncGE 0).obj X) ≃+ (E ⟶ h.H0prime (C := C) X) where
  toFun := fun f =>
    (h.toH0primeIsoOfIsGE (C := C) E ((h.t.truncGE 0).obj X)) f ≫
      (h.H0primeObjIsoTruncGE (C := C) X).inv
  invFun := fun β =>
    (h.toH0primeIsoOfIsGE (C := C) E ((h.t.truncGE 0).obj X)).symm
      (β ≫ (h.H0primeObjIsoTruncGE (C := C) X).hom)
  left_inv := by
    intro f
    simp
  right_inv := by
    intro β
    simp
  map_add' := by
    intro f g
    simp

-- `docBlame` currently misses the attached docstrings on these public
-- `noncomputable def`s, even though `findDocString?` and hover both see them.
attribute [nolint docBlame]
  HeartStabilityData.toH0primeHom
  HeartStabilityData.fromH0primeHom_of_isGE
  HeartStabilityData.toH0primeIsoOfIsGE
  HeartStabilityData.H0primeObjIsoTruncGE
  HeartStabilityData.toH0primeIsoViaTruncGE

theorem HeartStabilityData.toH0primeIsoViaTruncGE_naturality
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) {X Y : C}
    (f : E.obj ⟶ (h.t.truncGE 0).obj X) (g : X ⟶ Y) :
    h.toH0primeIsoViaTruncGE (C := C) E Y (f ≫ (h.t.truncGE 0).map g) =
      h.toH0primeIsoViaTruncGE (C := C) E X f ≫ (h.H0primeFunctor (C := C)).map g := by
  simp [HeartStabilityData.toH0primeIsoViaTruncGE, Category.assoc,
    h.H0primeObjIsoTruncGE_inv_naturality (C := C) g]
  change h.toH0primeHom (C := C) E (f ≫ (h.t.truncGE 0).map g) ≫
      (h.H0primeObjIsoTruncGE (C := C) Y).inv =
    h.toH0primeHom (C := C) E f ≫
      (h.H0primeFunctor (C := C)).map ((h.t.truncGE 0).map g) ≫
        (h.H0primeObjIsoTruncGE (C := C) Y).inv
  rw [← Category.assoc,
    h.toH0primeHom_comp_H0primeFunctor_map (C := C) E f ((h.t.truncGE 0).map g)]
  rfl

/-- For a heart object `E`, the `H0prime`-evaluation functor is naturally isomorphic
to evaluation of the ambient `τ≥0` truncation functor at `E.obj`. -/
noncomputable def HeartStabilityData.toH0primeNatIsoViaTruncGE
    (h : HeartStabilityData C)
    (E : h.t.heart.FullSubcategory) :
    h.t.truncGE 0 ⋙ preadditiveCoyoneda.obj (Opposite.op E.obj) ≅
      h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E) :=
  NatIso.ofComponents
    (fun X => AddEquiv.toAddCommGrpIso (h.toH0primeIsoViaTruncGE (C := C) E X))
    (fun g => by
      ext f
      exact h.toH0primeIsoViaTruncGE_naturality (C := C) E f g)

theorem HeartStabilityData.H0primeFunctor_preadditiveCoyoneda_exact_iff_truncGE
    (h : HeartStabilityData C)
    (T : Triangle C) (hT : T ∈ distTriang C) (E : h.t.heart.FullSubcategory) :
    ((shortComplexOfDistTriangle T hT).map
      (h.H0primeFunctor (C := C) ⋙ preadditiveCoyoneda.obj (Opposite.op E))).Exact ↔
      ((shortComplexOfDistTriangle T hT).map
        (h.t.truncGE 0 ⋙ preadditiveCoyoneda.obj (Opposite.op E.obj))).Exact := by
  simpa using
    ShortComplex.exact_iff_of_iso
      (((shortComplexOfDistTriangle T hT).mapNatIso
        (h.toH0primeNatIsoViaTruncGE (C := C) E)).symm)


end Proposition53

end CategoryTheory.Triangulated
