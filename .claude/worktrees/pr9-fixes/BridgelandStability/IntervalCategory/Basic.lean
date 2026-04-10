/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Slicing.TStructureConstruction
public import BridgelandStability.GrothendieckGroup.Basic
public import BridgelandStability.QuasiAbelian.Basic
public import BridgelandStability.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategoryLimits
public import BridgelandStability.TStructure.HeartAbelian
public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.Complex.Basic

/-!
# Interval Subcategories of Slicings

Given a slicing `s` on a pretriangulated category `C` and an open interval `(a, b) ⊂ ℝ`,
we define the interval subcategory `P((a, b))` as the full subcategory of `C` on objects
whose HN phases all lie in `(a, b)`.

These interval subcategories play a central role in Bridgeland's deformation theorem (§7):
when `b - a` is small enough (relative to the local finiteness parameter), objects in
`P((a,b))` have finite length in the quasi-abelian sense, i.e. well-founded chains of
strict subobjects and strict quotients, enabling HN filtration arguments within thin
subcategories.

## Main definitions

* `CategoryTheory.Triangulated.Slicing.IntervalCat`: the full subcategory `P((a, b))`
* `CategoryTheory.Triangulated.Slicing.intervalFiniteLength`: objects in thin intervals
  have well-founded subobject lattices

## Main results

* `CategoryTheory.Triangulated.Slicing.intervalHom_eq_zero`: hom-vanishing between
  objects in disjoint intervals
* `CategoryTheory.Triangulated.Slicing.intervalProp_of_semistable`: semistable objects
  with phase in `(a, b)` lie in `P((a, b))`

## References

* Bridgeland, "Stability conditions on triangulated categories", §4, §7
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

/-! ### Interval subcategory -/

/-- The interval subcategory `P((a, b))` of a slicing, defined as the full subcategory
on objects whose HN phases all lie in `(a, b)`. An object `E` belongs to `P((a, b))` if
it is zero or admits an HN filtration with all phases in `(a, b)`.

This is **Bridgeland's Definition 4.1** specialized to open intervals. -/
abbrev Slicing.IntervalCat (s : Slicing C) (a b : ℝ) :=
  (s.intervalProp C a b).FullSubcategory

/-- The inclusion functor from the interval subcategory to the ambient category. -/
abbrev Slicing.IntervalCat.ι (s : Slicing C) (a b : ℝ) :
    s.IntervalCat C a b ⥤ C :=
  (s.intervalProp C a b).ι

/-- Any zero object lies in every interval subcategory. -/
lemma Slicing.intervalProp_of_isZero (s : Slicing C) {E : C} (hE : IsZero E)
    (a b : ℝ) : s.intervalProp C a b E :=
  Or.inl hE

/-- The interval property contains the zero object. -/
instance Slicing.intervalProp_containsZero (s : Slicing C) (a b : ℝ) :
    (s.intervalProp C a b).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, s.intervalProp_of_isZero C (isZero_zero C) a b⟩

/-- If the underlying object of an interval object is zero in `C`, then the interval
object itself is zero. -/
theorem Slicing.IntervalCat.isZero_of_obj_isZero (s : Slicing C) {a b : ℝ}
    {X : s.IntervalCat C a b} (hX : IsZero X.obj) : IsZero X := by
  let Z : s.IntervalCat C a b := 0
  have hZ : IsZero Z.obj :=
    ((Slicing.IntervalCat.ι (C := C) (s := s) a b).map_isZero (isZero_zero _))
  let e : X.obj ≅ Z.obj := hX.iso hZ
  let e' : X ≅ Z := by
    refine ⟨ObjectProperty.homMk e.hom, ObjectProperty.homMk e.inv, ?_, ?_⟩
    · ext
      change e.hom ≫ e.inv = 𝟙 X.obj
      exact e.hom_inv_id
    · ext
      change e.inv ≫ e.hom = 𝟙 Z.obj
      exact e.inv_hom_id
  exact (show IsZero Z from isZero_zero _).of_iso e'

/-! ### Finite length in thin intervals -/

/-- **Finite subobject lattice in thin intervals**. For any object `E` in `P((a, b))` with
`b - a ≤ 2η`, if all objects in `η`-intervals have finite subobject lattices, then
`E` does too.

This is an older stronger helper; the paper-faithful local-finiteness hypothesis below
uses strict-subobject finite length instead. -/
theorem Slicing.intervalFiniteLength (s : Slicing C)
    {a b : ℝ} {E : C} (hI : s.intervalProp C a b E) :
    ∀ {η : ℝ}, b - a ≤ 2 * η →
      (∀ t : ℝ, ∀ (F : C), s.intervalProp C (t - η) (t + η) F →
        Finite (Subobject F)) →
      Finite (Subobject E) := by
  intro η hwidth hlf
  -- Choose t = (a + b) / 2, then (a, b) ⊆ (t - η, t + η)
  set t := (a + b) / 2
  apply hlf t E
  rcases hI with hEZ | ⟨F, hF⟩
  · exact Or.inl hEZ
  · right
    exact ⟨F, fun i ↦ by
      have h1 := (hF i).1
      have h2 := (hF i).2
      have ht : t = (a + b) / 2 := rfl
      constructor
      · -- t - η ≤ a < F.φ i
        by_contra h
        push Not at h
        linarith
      · -- F.φ i < b ≤ t + η
        by_contra h
        push Not at h
        linarith⟩

/-! ### Interval containment -/

/-- A semistable object of phase `φ ∈ (a, b)` lies in `P((a, b))`. -/
lemma Slicing.intervalProp_of_semistable (s : Slicing C)
    {E : C} {φ : ℝ} (hP : (s.P φ) E) {a b : ℝ}
    (ha : a < φ) (hb : φ < b) :
    s.intervalProp C a b E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  · right
    have ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C s hE
    have ⟨hpP, hpM⟩ := s.phiPlus_eq_phiMinus_of_semistable C hP hE
    exact ⟨F, fun i ↦ by
      constructor
      · calc a < φ := ha
          _ = s.phiMinus C E hE := hpM.symm
          _ = F.φ ⟨F.n - 1, by lia⟩ :=
              s.phiMinus_eq C E hE F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
              F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = s.phiPlus C E hE :=
              (s.phiPlus_eq C E hE F hn hfirst).symm
          _ = φ := hpP
          _ < b := hb⟩

/-- Narrower intervals are contained in wider ones. -/
lemma Slicing.intervalProp_mono (s : Slicing C) {E : C}
    {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b')
    (hI : s.intervalProp C a b E) :
    s.intervalProp C a' b' E := by
  rcases hI with hEZ | ⟨F, hF⟩
  · exact Or.inl hEZ
  · right
    exact ⟨F, fun i ↦ ⟨by grind, by grind⟩⟩

/-- The inclusion functor between nested interval subcategories. -/
abbrev Slicing.IntervalCat.inclusion (s : Slicing C)
    {a₁ b₁ a₂ b₂ : ℝ} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    s.IntervalCat C a₁ b₁ ⥤ s.IntervalCat C a₂ b₂ :=
  ObjectProperty.ιOfLE (fun _ hX ↦ s.intervalProp_mono C ha hb hX)

/-- The interval property is closed under isomorphisms. -/
instance Slicing.intervalProp_closedUnderIso (s : Slicing C) (a b : ℝ) :
    (s.intervalProp C a b).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    rcases hE with hZ | ⟨F, hF⟩
    · exact Or.inl (IsZero.of_iso hZ e.symm)
    · exact Or.inr ⟨F.ofIso C e, hF⟩

instance Slicing.intervalProp_stableUnderRetracts (s : Slicing C) (a b : ℝ) :
    CategoryTheory.ObjectProperty.IsStableUnderRetracts (s.intervalProp C a b) where
  of_retract {X Y} h hY := by
    by_cases hX : IsZero X
    · exact Or.inl hX
    · obtain ⟨FX, hnX, hneX⟩ := HNFiltration.exists_nonzero_first C s hX
      have hX_lt : s.phiPlus C X hX < b := by
        rw [s.phiPlus_eq C X hX FX hnX hneX]
        by_contra hle
        push Not at hle
        have hzeroY : ∀ α : (FX.triangle ⟨0, hnX⟩).obj₃ ⟶ Y, α = 0 := by
          intro α
          by_cases hY0 : IsZero Y
          · exact hY0.eq_of_tgt α 0
          · obtain ⟨FY, hnY, hneY⟩ := HNFiltration.exists_nonzero_first C s hY0
            have hgap : ∀ j : Fin FY.n, FY.φ j < FX.φ ⟨0, hnX⟩ := by
              intro j
              have h1 : FY.φ j ≤ FY.φ ⟨0, hnY⟩ := by
                apply FY.hφ.antitone
                simp only [Fin.le_def]
                lia
              have h2 : FY.φ ⟨0, hnY⟩ = s.phiPlus C Y hY0 :=
                (s.phiPlus_eq C Y hY0 FY hnY hneY).symm
              have h3 : s.phiPlus C Y hY0 < b := s.phiPlus_lt_of_intervalProp C hY0 hY
              linarith
            exact s.hom_eq_zero_of_gt_phases C (FX.semistable ⟨0, hnX⟩) FY hgap α
        have hzeroX : ∀ α : (FX.triangle ⟨0, hnX⟩).obj₃ ⟶ X, α = 0 := by
          intro α
          have hαi : α ≫ h.i = 0 := hzeroY (α ≫ h.i)
          calc α = (α ≫ h.i) ≫ h.r := by simp [h.retract]
          _ = 0 := by rw [hαi, zero_comp]
        exact hneX (FX.isZero_factor_zero_of_hom_eq_zero C s hnX hzeroX)
      obtain ⟨GX, hnX', hneX'⟩ := HNFiltration.exists_nonzero_last C s hX
      have hX_gt : a < s.phiMinus C X hX := by
        rw [s.phiMinus_eq C X hX GX hnX' hneX']
        by_contra hge
        push Not at hge
        have hzeroY : ∀ β : Y ⟶ (GX.triangle ⟨GX.n - 1, by lia⟩).obj₃, β = 0 := by
          intro β
          by_cases hY0 : IsZero Y
          · exact hY0.eq_of_src β 0
          · obtain ⟨GY, hnY, hneY⟩ := HNFiltration.exists_nonzero_last C s hY0
            have hgap : ∀ j : Fin GY.n, GX.φ ⟨GX.n - 1, by lia⟩ < GY.φ j := by
              intro j
              have h1 : GY.φ ⟨GY.n - 1, by lia⟩ ≤ GY.φ j := by
                apply GY.hφ.antitone
                simp only [Fin.le_def]
                lia
              have h2 : s.phiMinus C Y hY0 = GY.φ ⟨GY.n - 1, by lia⟩ :=
                s.phiMinus_eq C Y hY0 GY hnY hneY
              have h3 : a < s.phiMinus C Y hY0 := s.phiMinus_gt_of_intervalProp C hY0 hY
              linarith
            exact s.hom_eq_zero_of_lt_phases C (GX.semistable ⟨GX.n - 1, by lia⟩) GY hgap β
        have hzeroX : ∀ β : X ⟶ (GX.triangle ⟨GX.n - 1, by lia⟩).obj₃, β = 0 := by
          intro β
          have hrβ : h.r ≫ β = 0 := hzeroY (h.r ≫ β)
          calc β = (𝟙 X) ≫ β := by simp
          _ = h.i ≫ (h.r ≫ β) := by rw [← h.retract]; simp
          _ = 0 := by rw [hrβ, comp_zero]
        exact hneX' (GX.isZero_factor_last_of_hom_eq_zero C s hnX' hzeroX)
      exact s.intervalProp_of_intrinsic_phases C hX hX_gt hX_lt

section FiniteProducts

variable [IsTriangulated C]

omit [IsTriangulated C] in
/-- The interval property is closed under binary products. -/
lemma Slicing.intervalProp_biprod (s : Slicing C) {a b : ℝ} {X Y : C}
    (hX : s.intervalProp C a b X) (hY : s.intervalProp C a b Y) :
    s.intervalProp C a b (X ⊞ Y) :=
  s.intervalProp_of_triangle C hX hY (binaryBiproductTriangle_distinguished X Y)

/-- The interval property is closed under binary products. -/
instance Slicing.intervalProp_closedUnderBinaryProducts (s : Slicing C) (a b : ℝ) :
    (s.intervalProp C a b).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    exact (s.intervalProp C a b).prop_of_iso
      ((biprod.isoProd (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) ≪≫
        (HasLimit.isoOfNatIso (Discrete.natIso (fun ⟨j⟩ ↦ match j with
          | WalkingPair.left => Iso.refl _
          | WalkingPair.right => Iso.refl _))).symm)
      (s.intervalProp_biprod C (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))

/-- The interval property is closed under finite products. -/
instance Slicing.intervalProp_closedUnderFiniteProducts (s : Slicing C) (a b : ℝ) :
    (s.intervalProp C a b).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- Thin interval subcategories have finite products. -/
noncomputable instance Slicing.intervalCat_hasFiniteProducts (s : Slicing C) (a b : ℝ) :
    HasFiniteProducts (s.IntervalCat C a b) :=
  hasFiniteProducts_of_has_binary_and_terminal

end FiniteProducts

/-! ### Hom-vanishing between disjoint intervals -/

/-- **Hom-vanishing between disjoint intervals**. If `A ∈ P((a₁, b₁))` and
`B ∈ P((a₂, b₂))` with `b₂ ≤ a₁` (so all phases of `A` are strictly above all phases
of `B`), then `Hom(A, B) = 0`.

This follows from the existing hom-vanishing for semistable objects applied factorwise
through HN filtrations. -/
theorem Slicing.intervalHom_eq_zero (s : Slicing C) {A B : C}
    {a₁ b₁ a₂ b₂ : ℝ} (hA : s.intervalProp C a₁ b₁ A)
    (hB : s.intervalProp C a₂ b₂ B)
    (hgap : b₂ ≤ a₁)
    (f : A ⟶ B) : f = 0 := by
  rcases hA with hAZ | ⟨FA, hFA⟩
  · exact hAZ.eq_of_src f 0
  rcases hB with hBZ | ⟨FB, hFB⟩
  · exact hBZ.eq_of_tgt f 0
  exact s.hom_eq_zero_of_phase_gap C FA FB
    (fun i j ↦ by grind) f

end CategoryTheory.Triangulated
