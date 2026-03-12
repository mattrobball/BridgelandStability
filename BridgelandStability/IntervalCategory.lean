/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Slicing
import Mathlib.CategoryTheory.Triangulated.GrothendieckGroup
import Mathlib.CategoryTheory.Triangulated.Strict
import Mathlib.CategoryTheory.Triangulated.TStructure.HeartAbelian
import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Data.Complex.Basic

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
  have hZ : IsZero Z.obj := ((Slicing.IntervalCat.ι (C := C) (s := s) a b).map_isZero (isZero_zero _))
  let e : X.obj ≅ Z.obj := hX.iso hZ
  let e' : X ≅ Z := by
    refine ⟨ObjectProperty.homMk e.hom, ObjectProperty.homMk e.inv, ?_, ?_⟩
    · ext
      simpa using congrArg InducedCategory.Hom.hom e.hom_inv_id
    · ext
      simpa using congrArg InducedCategory.Hom.hom e.inv_hom_id
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
        push_neg at h
        linarith
      · -- F.φ i < b ≤ t + η
        by_contra h
        push_neg at h
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
          _ = F.φ ⟨F.n - 1, by omega⟩ :=
              s.phiMinus_eq C E hE F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
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
    exact ⟨F, fun i ↦ ⟨by linarith [(hF i).1], by linarith [(hF i).2]⟩⟩

/-- The inclusion functor between nested interval subcategories. -/
abbrev Slicing.IntervalCat.inclusion (s : Slicing C)
    {a₁ b₁ a₂ b₂ : ℝ} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    s.IntervalCat C a₁ b₁ ⥤ s.IntervalCat C a₂ b₂ :=
  ObjectProperty.ιOfLE (fun X hX ↦ s.intervalProp_mono C ha hb hX)

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
        push_neg at hle
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
                omega
              have h2 : FY.φ ⟨0, hnY⟩ = s.phiPlus C Y hY0 := by
                exact (s.phiPlus_eq C Y hY0 FY hnY hneY).symm
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
        push_neg at hge
        have hzeroY : ∀ β : Y ⟶ (GX.triangle ⟨GX.n - 1, by omega⟩).obj₃, β = 0 := by
          intro β
          by_cases hY0 : IsZero Y
          · exact hY0.eq_of_src β 0
          · obtain ⟨GY, hnY, hneY⟩ := HNFiltration.exists_nonzero_last C s hY0
            have hgap : ∀ j : Fin GY.n, GX.φ ⟨GX.n - 1, by omega⟩ < GY.φ j := by
              intro j
              have h1 : GY.φ ⟨GY.n - 1, by omega⟩ ≤ GY.φ j := by
                apply GY.hφ.antitone
                simp only [Fin.le_def]
                omega
              have h2 : s.phiMinus C Y hY0 = GY.φ ⟨GY.n - 1, by omega⟩ := by
                exact s.phiMinus_eq C Y hY0 GY hnY hneY
              have h3 : a < s.phiMinus C Y hY0 := s.phiMinus_gt_of_intervalProp C hY0 hY
              linarith
            exact s.hom_eq_zero_of_lt_phases C (GX.semistable ⟨GX.n - 1, by omega⟩) GY hgap β
        have hzeroX : ∀ β : X ⟶ (GX.triangle ⟨GX.n - 1, by omega⟩).obj₃, β = 0 := by
          intro β
          have hrβ : h.r ≫ β = 0 := hzeroY (h.r ≫ β)
          calc β = (𝟙 X) ≫ β := by simp
          _ = h.i ≫ (h.r ≫ β) := by rw [← h.retract]; simp [Category.assoc]
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
    (fun i j ↦ by linarith [(hFB j).2, (hFA i).1]) f

/-! ### Heart containment — Two-heart embedding (Lemma 4.3 foundations)

Objects in a thin interval `P((a, b))` with `b - a ≤ 1` lie in two different abelian hearts:
* **Left heart** `P((a, a+1])` — the heart of the slicing shifted by `a`.
  Controls kernels and images.
* **Right heart** `P((b-1, b])` — the heart of the slicing shifted by `b-1`.
  Controls cokernels and coimages.

This is the foundation of Bridgeland's Lemma 4.3 and is why the interval category
is quasi-abelian: one heart cannot handle both kernels and cokernels, but together
the two hearts make up for each other's deficiencies.
-/

section TwoHeartEmbedding

variable [IsTriangulated C]

omit [IsTriangulated C] in
/-- **Interval to gtProp.** If all HN phases lie in `(a, b)`, then phiMinus > `a`. -/
lemma Slicing.gtProp_of_intervalProp (s : Slicing C) {a b : ℝ} {E : C}
    (hE : s.intervalProp C a b E) : s.gtProp C a E := by
  rcases hE with hZ | ⟨F, hF⟩
  · exact Or.inl hZ
  · by_cases hn : 0 < F.n
    · exact Or.inr ⟨F, hn, (hF ⟨F.n - 1, by omega⟩).1⟩
    · exact Or.inl (F.toPostnikovTower.zero_isZero (by omega))

omit [IsTriangulated C] in
/-- **Interval to leProp.** If all HN phases lie in `(a, b)`, then phiPlus ≤ `b`. -/
lemma Slicing.leProp_of_intervalProp (s : Slicing C) {a b : ℝ} {E : C}
    (hE : s.intervalProp C a b E) : s.leProp C b E := by
  rcases hE with hZ | ⟨F, hF⟩
  · exact Or.inl hZ
  · by_cases hn : 0 < F.n
    · exact Or.inr ⟨F, hn, le_of_lt (hF ⟨0, hn⟩).2⟩
    · exact Or.inl (F.toPostnikovTower.zero_isZero (by omega))

/-- **Left heart containment (Lemma 4.3a).** If `b - a ≤ 1` and `E ∈ P((a, b))`,
then `E` lies in the heart of the t-structure induced by the slicing shifted by `a`.
This heart is the half-open interval `P((a, a+1])`.

The proof is immediate: phases in `(a, b)` satisfy `> a` (for `gtProp`) and
`< b ≤ a + 1` (for `leProp`). -/
theorem Slicing.intervalProp_implies_leftHeart (s : Slicing C) {a b : ℝ}
    (hab : b - a ≤ 1) {E : C} (hE : s.intervalProp C a b E) :
    ((s.phaseShift C a).toTStructure).heart E := by
  rw [(s.phaseShift C a).toTStructure_heart_iff]
  constructor
  · -- gtProp C 0 for shifted slicing ↔ gtProp C a for original
    rw [s.phaseShift_gtProp_zero]
    exact s.gtProp_of_intervalProp C hE
  · -- leProp C 1 for shifted slicing: construct shifted HN filtration
    rcases hE with hZ | ⟨F, hF⟩
    · exact Or.inl hZ
    · by_cases hn : 0 < F.n
      · right
        refine ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - a,
          fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hn, ?_⟩
        · change s.P (F.φ j - a + a) _
          rw [show F.φ j - a + a = F.φ j from by ring]
          exact F.semistable j
        · dsimp [HNFiltration.phiPlus]
          linarith [(hF ⟨0, hn⟩).2]
      · exact Or.inl (F.toPostnikovTower.zero_isZero (by omega))

/-- **Right heart containment (Lemma 4.3b).** If `b - a ≤ 1` and `E ∈ P((a, b))`,
then `E` lies in the heart of the dual half-open t-structure induced by the slicing
shifted by `b - 1`. This heart is the half-open interval `P([b-1, b))`.

Together with `intervalProp_implies_leftHeart`, this establishes the two-heart
embedding: every object in a thin interval lies in both an abelian heart that
controls kernels (left heart) and one that controls cokernels (right heart). -/
theorem Slicing.intervalProp_implies_rightHeart (s : Slicing C) {a b : ℝ}
    (hab : b - a ≤ 1) {E : C} (hE : s.intervalProp C a b E) :
    ((s.phaseShift C (b - 1)).toTStructureGE).heart E := by
  rw [(s.phaseShift C (b - 1)).toTStructureGE_heart_iff]
  constructor
  · rw [s.phaseShift_geProp_zero]
    have hgt : s.gtProp C a E := s.gtProp_of_intervalProp C hE
    have hge : s.geProp C a E := (s.geProp_of_gtProp (C := C) (t := a)) E hgt
    exact (s.geProp_anti (C := C) (t₁ := b - 1) (t₂ := a) (by linarith)) E hge
  · rw [s.phaseShift_ltProp]
    simpa [show 1 + (b - 1) = b by ring] using s.ltProp_of_intervalProp C hE

/-- The fully faithful embedding of `P((a,b))` into the left heart `P((a,a+1])`. -/
abbrev Slicing.IntervalCat.toLeftHeart (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤ ((s.phaseShift C a).toTStructure).heart.FullSubcategory where
  obj X := ⟨X.obj, s.intervalProp_implies_leftHeart C hab X.property⟩
  map f := ObjectProperty.homMk f.hom

instance Slicing.IntervalCat.toLeftHeart_full (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    Functor.Full (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_surjective {X Y} f := ⟨ObjectProperty.homMk f.hom, rfl⟩

instance Slicing.IntervalCat.toLeftHeart_faithful (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Faithful (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_injective := by
    intro X Y f g h
    cases f
    cases g
    cases h
    rfl

/-- The fully faithful embedding of `P((a,b))` into the right heart `P([b-1,b))`. -/
abbrev Slicing.IntervalCat.toRightHeart (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤ ((s.phaseShift C (b - 1)).toTStructureGE).heart.FullSubcategory where
  obj X := ⟨X.obj, s.intervalProp_implies_rightHeart C hab X.property⟩
  map f := ObjectProperty.homMk f.hom

instance Slicing.IntervalCat.toRightHeart_full (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    Functor.Full (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_surjective {X Y} f := ⟨ObjectProperty.homMk f.hom, rfl⟩

instance Slicing.IntervalCat.toRightHeart_faithful (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Faithful (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_injective := by
    intro X Y f g h
    cases f
    cases g
    cases h
    rfl

omit [IsTriangulated C] in
/-- **Right-window bounds.** If `b - a ≤ 1` and `E ∈ P((a, b))`, then `E` satisfies
the phase-window conditions `geProp (b - 1)` and `ltProp b`.

This is the half-open interval `[b - 1, b)` needed for the future right-heart
convention controlling cokernels. -/
theorem Slicing.intervalProp_implies_rightWindow (s : Slicing C) {a b : ℝ}
    (hab : b - a ≤ 1) {E : C} (hE : s.intervalProp C a b E) :
    s.geProp C (b - 1) E ∧ s.ltProp C b E := by
  constructor
  · have hgt : s.gtProp C a E := s.gtProp_of_intervalProp C hE
    have hge : s.geProp C a E := (s.geProp_of_gtProp (C := C) (t := a)) E hgt
    exact (s.geProp_anti (C := C) (t₁ := b - 1) (t₂ := a) (by linarith)) E hge
  · exact s.ltProp_of_intervalProp C hE

/-! ### Phase bounds for triangles with semistable middle term

For a distinguished triangle `K → F → Q → K⟦1⟧` where `F ∈ P(φ)` is σ-semistable
and `K, Q ∈ P((a, b))` lie in a thin interval containing `φ`, Lemma 3.4 gives:
- `φ⁺(K) ≤ φ` (the top phase of K is bounded by F's phase)
- `φ⁻(Q) ≥ φ` (the bottom phase of Q is bounded below by F's phase)

These are the foundational phase bounds for the deformation theorem's triangle test.
Combined with interval membership, they give:
- K has all σ-phases in `(a, φ]`
- Q has all σ-phases in `[φ, b)`

The Z-ray consequence (Im(Z(K)·rot) ≤ 0 and Im(Z(Q)·rot) ≥ 0) does NOT suffice
to force K, Q ∈ P(φ) — the terms have opposite signs, so sum = 0 allows both nonzero.
See the counterexample in `HeartEquivalence.lean`. The full triangle test requires
the quasi-abelian theory or W-semistability arguments.
-/

omit [IsTriangulated C] in
/-- **Phase upper bound from Lemma 3.4.** In a triangle `K → F → Q → K⟦1⟧` with
`F ∈ P(φ)` σ-semistable and `K, Q` in a thin interval `P((a, b))` with `b ≤ a + 1`
and `φ ∈ (a, b)`, if `K` is nonzero then `φ⁺(K) ≤ φ`. -/
theorem Slicing.phiPlus_le_of_semistable_triangle (s : Slicing C) {φ : ℝ}
    {K F Q : C} {f₁ : K ⟶ F} {f₂ : F ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C)
    (hPφ : (s.P φ) F) (hFne : ¬IsZero F) (hKne : ¬IsZero K)
    {a b : ℝ} (hab : b ≤ a + 1)
    (hKI : s.intervalProp C a b K) (hQI : s.intervalProp C a b Q) :
    s.phiPlus C K hKne ≤ φ := by
  have hFplus : s.phiPlus C F hFne = φ :=
    (s.phiPlus_eq_phiMinus_of_semistable C hPφ hFne).1
  rw [← hFplus]
  exact s.phiPlus_triangle_le C hKne hFne hab hKI hQI hT

omit [IsTriangulated C] in
/-- **Phase lower bound from Lemma 3.4.** In a triangle `K → F → Q → K⟦1⟧` with
`F ∈ P(φ)` σ-semistable and `K, Q` in a thin interval `P((a, b))` with `b ≤ a + 1`,
if `Q` is nonzero then `φ ≤ φ⁻(Q)`. -/
theorem Slicing.phiMinus_ge_of_semistable_triangle (s : Slicing C) {φ : ℝ}
    {K F Q : C} {f₁ : K ⟶ F} {f₂ : F ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C)
    (hPφ : (s.P φ) F) (hFne : ¬IsZero F) (hQne : ¬IsZero Q)
    {a b : ℝ} (hab : b ≤ a + 1)
    (hKI : s.intervalProp C a b K) (hQI : s.intervalProp C a b Q) :
    φ ≤ s.phiMinus C Q hQne := by
  have hFminus : s.phiMinus C F hFne = φ :=
    (s.phiPlus_eq_phiMinus_of_semistable C hPφ hFne).2
  rw [← hFminus]
  exact s.phiMinus_triangle_le C hQne hFne hab hKI hQI hT

/-! ### One-sided phase bounds for triangles (generalizing Lemma 3.4)

These lemmas generalize `phiPlus_triangle_le` and `phiMinus_triangle_le` by replacing
the `intervalProp` condition on one vertex with a weaker `leProp` or `gtProp` condition.
The key application is kernel/image containment: when a morphism `f : E → F` between
interval objects has its kernel/image computed in an abelian heart, the heart membership
gives only a `leProp`/`gtProp` bound, not full `intervalProp`. These lemmas recover
the full interval containment from the weaker one-sided bound.
-/

omit [IsTriangulated C] in
/-- **Phase upper bound from one-sided containment.** In a triangle `K → E → Q → K⟦1⟧`,
if `E` has `φ⁺(E) < b` and `Q` satisfies `leProp c` (all phases ≤ c) with `c < b + 1`,
then if `K` is nonzero, `φ⁺(K) < b`.

This strengthens `phiPlus_triangle_le` by requiring only a `leProp` bound on `Q` rather
than full `intervalProp`. The condition `c < b + 1` ensures `Q⟦-1⟧` has all phases
`≤ c - 1 < b`, providing the hom-vanishing gap for the coyoneda factoring argument.

**Key application**: kernel containment in the left heart. If `f : E → F` with both
in `P((a, b))`, the heart's SES `ker(f) → E → im(f)` gives a triangle where `im(f)`
is in the heart with `leProp (a + 1)`. Since `a + 1 < b + 1`, this lemma bounds
`φ⁺(ker(f)) < b`, placing the kernel in `P((a, b))`. -/
theorem Slicing.phiPlus_lt_of_triangle_with_leProp (s : Slicing C)
    {K E Q : C} (hK : ¬IsZero K) {b : ℝ}
    (hE_lt : ∀ (hE : ¬IsZero E), s.phiPlus C E hE < b)
    {c : ℝ} (hQ_le : s.leProp C c Q) (hcb : c < b + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.phiPlus C K hK < b := by
  obtain ⟨FK, hnK, hneK⟩ := HNFiltration.exists_nonzero_first C s hK
  rw [s.phiPlus_eq C K hK FK hnK hneK]
  by_contra hge
  push_neg at hge
  -- hge : b ≤ FK.φ ⟨0, hnK⟩ (top factor has phase ≥ b)
  -- Show all maps from FK's top factor to K are zero
  have hK_factor_zero : ∀ α : (FK.triangle ⟨0, hnK⟩).obj₃ ⟶ K, α = 0 := by
    intro α
    -- Step 1: α ≫ f₁ = 0 (top factor → E is zero by hom-vanishing)
    have hαf : α ≫ f₁ = 0 := by
      by_cases hEZ : IsZero E
      · exact hEZ.eq_of_tgt (α ≫ f₁) 0
      · obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_first C s hEZ
        have hE_gap : ∀ j : Fin FE.n, FE.φ j < FK.φ ⟨0, hnK⟩ := fun j ↦ by
          have h1 : FE.φ j ≤ FE.φ ⟨0, hnE⟩ := by
            apply FE.hφ.antitone; simp only [Fin.le_def]; omega
          have h2 : FE.φ ⟨0, hnE⟩ = s.phiPlus C E hEZ :=
            (s.phiPlus_eq C E hEZ FE hnE hneE).symm
          linarith [hE_lt hEZ]
        exact s.hom_eq_zero_of_gt_phases C (FK.semistable ⟨0, hnK⟩) FE hE_gap _
    -- Step 2: By coyoneda on invRotate, α factors through Q⟦-1⟧
    let T := Triangle.mk f₁ f₂ f₃
    obtain ⟨β, hβ⟩ := Triangle.coyoneda_exact₂ T.invRotate
      (inv_rot_of_distTriang _ hT) α hαf
    -- Step 3: β = 0 (top factor → Q⟦-1⟧ is zero by hom-vanishing)
    suffices hβ0 : β = 0 by rw [hβ, hβ0, zero_comp]; rfl
    by_cases hQZ : IsZero Q
    · exact ((shiftFunctor C (-1 : ℤ)).map_isZero hQZ).eq_of_tgt β 0
    · rcases hQ_le with hQZ' | ⟨GQ, hnQ, hGQ_le⟩
      · exact absurd hQZ' hQZ
      · -- Shift GQ by -1 to get filtration of Q⟦-1⟧
        let GQs := GQ.shiftHN C s (-1 : ℤ)
        -- GQs.φ(j) = GQ.φ(j) - 1 ≤ c - 1 < b ≤ FK.φ(0)
        have hQs_gap : ∀ j : Fin GQs.n, GQs.φ j < FK.φ ⟨0, hnK⟩ := by
          intro j
          change GQ.φ j + ((-1 : ℤ) : ℝ) < FK.φ ⟨0, hnK⟩
          have h1 : GQ.φ j ≤ GQ.φ ⟨0, hnQ⟩ := by
            apply GQ.hφ.antitone; simp only [Fin.le_def]; omega
          have h2 : GQ.φ ⟨0, hnQ⟩ ≤ c := by
            have := hGQ_le; change GQ.phiPlus C hnQ ≤ c at this; exact this
          have h3 : ((-1 : ℤ) : ℝ) = -1 := by norm_num
          linarith
        exact s.hom_eq_zero_of_gt_phases C (FK.semistable ⟨0, hnK⟩) GQs hQs_gap β
  -- Top factor is zero — contradiction
  exact hneK (FK.isZero_factor_zero_of_hom_eq_zero C s hnK hK_factor_zero)

omit [IsTriangulated C] in
/-- **Phase lower bound from one-sided containment** (dual of
`phiPlus_lt_of_triangle_with_leProp`). In a triangle `K → E → Q → K⟦1⟧`,
if `E` has `φ⁻(E) > a` and `K` satisfies `gtProp c` (all phases > c) with `a < c + 1`,
then if `Q` is nonzero, `a < φ⁻(Q)`.

**Key application**: cokernel/quotient lower bound. In a heart SES, the quotient object
satisfies `gtProp` from heart membership, and this lemma gives the lower phase bound
needed for interval containment. -/
theorem Slicing.phiMinus_gt_of_triangle_with_gtProp (s : Slicing C)
    {K E Q : C} (hQ : ¬IsZero Q) {a : ℝ}
    (hE_gt : ∀ (hE : ¬IsZero E), a < s.phiMinus C E hE)
    {c : ℝ} (hK_gt : s.gtProp C c K) (hca : a < c + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    a < s.phiMinus C Q hQ := by
  obtain ⟨FQ, hnQ, hneQ⟩ := HNFiltration.exists_nonzero_last C s hQ
  rw [s.phiMinus_eq C Q hQ FQ hnQ hneQ]
  by_contra hle
  push_neg at hle
  -- hle : FQ.φ ⟨FQ.n - 1, _⟩ ≤ a (bottom factor has phase ≤ a)
  -- Show all maps from Q to FQ's bottom factor are zero
  have hQ_factor_zero :
      ∀ β : Q ⟶ (FQ.triangle ⟨FQ.n - 1, by omega⟩).obj₃, β = 0 := by
    intro β
    -- Step 1: f₂ ≫ β = 0 (E → bottom_factor is zero by hom-vanishing)
    have hfβ : f₂ ≫ β = 0 := by
      by_cases hEZ : IsZero E
      · exact hEZ.eq_of_src (f₂ ≫ β) 0
      · obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_last C s hEZ
        have hE_gap : ∀ j : Fin FE.n,
            FQ.φ ⟨FQ.n - 1, by omega⟩ < FE.φ j := fun j ↦ by
          have h1 : a < FE.φ ⟨FE.n - 1, by omega⟩ := by
            have := hE_gt hEZ
            rw [s.phiMinus_eq C E hEZ FE hnE hneE] at this; exact this
          have h2 : FE.φ ⟨FE.n - 1, by omega⟩ ≤ FE.φ j := by
            apply FE.hφ.antitone; simp only [Fin.le_def]; omega
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FQ.semistable ⟨FQ.n - 1, by omega⟩) FE hE_gap _
    -- Step 2: By yoneda_exact₃, β factors through K⟦1⟧
    obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₃ (Triangle.mk f₁ f₂ f₃) hT β hfβ
    -- Step 3: γ = 0 (K⟦1⟧ → bottom_factor is zero by hom-vanishing)
    suffices hγ0 : γ = 0 by rw [hγ, hγ0]; exact comp_zero
    by_cases hKZ : IsZero K
    · exact ((shiftFunctor C (1 : ℤ)).map_isZero hKZ).eq_of_src γ 0
    · rcases hK_gt with hKZ' | ⟨GK, hnGK, hGK_gt⟩
      · exact absurd hKZ' hKZ
      · -- Shift GK by 1 to get filtration of K⟦1⟧
        let GKs := GK.shiftHN C s (1 : ℤ)
        -- GKs.φ(j) = GK.φ(j) + 1 > c + 1 > a ≥ FQ.φ(n-1)
        have hKs_gap : ∀ j : Fin GKs.n,
            FQ.φ ⟨FQ.n - 1, by omega⟩ < GKs.φ j := by
          intro j
          change FQ.φ ⟨FQ.n - 1, by omega⟩ < GK.φ j + ((1 : ℤ) : ℝ)
          have h1 : GK.φ ⟨GK.n - 1, by omega⟩ ≤ GK.φ j := by
            apply GK.hφ.antitone
            change j.val ≤ GK.n - 1
            have := j.isLt; have : GKs.n = GK.n := rfl; omega
          have h2 : c < GK.φ ⟨GK.n - 1, by omega⟩ := hGK_gt
          have h3 : ((1 : ℤ) : ℝ) = 1 := by norm_num
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FQ.semistable ⟨FQ.n - 1, by omega⟩) GKs hKs_gap γ
  -- Bottom factor is zero — contradiction
  exact hneQ (FQ.isZero_factor_last_of_hom_eq_zero C s hnQ hQ_factor_zero)

/-! ### Kernel and image containment in thin intervals (Lemma 4.3 consequences)

In a thin interval `P((a, b))` with `b - a ≤ 1`, the left heart `P((a, a+1])` computes
kernels and images of morphisms between interval objects. The resulting kernels and images
**stay in the interval** `P((a, b))`:

* **Upper bound** (`phiPlus < b`): from `phiPlus_lt_of_triangle_with_leProp`, using
  that the third vertex of the heart SES triangle has `leProp(a+1)` from heart membership.
* **Lower bound** (`phiMinus > a`): directly from left heart membership, since all
  phases in `P((a, a+1])` are `> a`.

This does NOT extend to cokernels in the left heart: a quotient of an interval object
in the left heart can have phases up to `a + 1 > b`. For cokernels, the right heart
`P((b-1, b])` is needed, and the strict upper bound `phiPlus < b` requires the
quasi-abelian theory (Bridgeland §4).
-/

omit [IsTriangulated C] in
/-- **Kernel/image containment in thin intervals.** In a distinguished triangle
`K → E → Q → K[1]` where `E ∈ P((a,b))` and both `K` and `Q` satisfy basic phase
bounds (`gtProp a` and `leProp (a+1)`), then `K ∈ P((a, b))`.

The upper bound `phiPlus(K) < b` comes from `phiPlus_lt_of_triangle_with_leProp`.
The lower bound `phiMinus(K) > a` comes from `gtProp a`.

**Key applications**:
* **Kernels**: In the heart SES `0 → ker(f) → E → im(f) → 0`, both `ker(f)` and
  `im(f)` are in the left heart, hence satisfy `gtProp a` and `leProp (a+1)`.
* **Images**: In the heart SES `0 → im(f) → F → coker(f) → 0`, similarly. -/
theorem Slicing.first_intervalProp_of_triangle (s : Slicing C)
    {a b : ℝ} (hab' : a < b)
    {K E Q : C}
    (hE : s.intervalProp C a b E)
    (hQ_le : s.leProp C (a + 1) Q)
    (hK_gt : s.gtProp C a K)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.intervalProp C a b K := by
  by_cases hK : IsZero K
  · exact Or.inl hK
  · -- phiPlus(K) < b: from phiPlus_lt_of_triangle_with_leProp
    have hK_lt : s.phiPlus C K hK < b :=
      s.phiPlus_lt_of_triangle_with_leProp C hK
        (fun hE' ↦ s.phiPlus_lt_of_intervalProp C hE' hE)
        hQ_le (by linarith) hT
    -- phiMinus(K) > a: from gtProp via phiMinus_gt_of_gtProp
    have hK_minus : a < s.phiMinus C K hK :=
      s.phiMinus_gt_of_gtProp C hK hK_gt
    -- Combine: K has all phases in (a, b)
    obtain ⟨FK, hnK, hfirstK, hlastK⟩ := HNFiltration.exists_both_nonzero C s hK
    right
    exact ⟨FK, fun i ↦ by
      constructor
      · calc a < s.phiMinus C K hK := hK_minus
          _ = FK.φ ⟨FK.n - 1, by omega⟩ := s.phiMinus_eq C K hK FK hnK hlastK
          _ ≤ FK.φ i := FK.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
      · calc FK.φ i ≤ FK.φ ⟨0, hnK⟩ :=
              FK.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = s.phiPlus C K hK := (s.phiPlus_eq C K hK FK hnK hfirstK).symm
          _ < b := hK_lt⟩

omit [IsTriangulated C] in
/-- **Extension closure for thin intervals.** In a distinguished triangle
`A → E → B → A[1]` where `A` and `B` are in `P((a, b))` with `b - a ≤ 1`,
then `E ∈ P((a, b))`.

This follows from `phiPlus_lt_of_triangle` and `phiMinus_gt_of_triangle`. It shows
that `P((a, b))` is extension-closed in the triangulated category when `b - a ≤ 1`.
This is a special case of the general extension closure for interval categories. -/
theorem Slicing.intervalProp_extension_closed (s : Slicing C)
    {a b : ℝ}
    {A E B : C}
    (hA : s.intervalProp C a b A) (hB : s.intervalProp C a b B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a b E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  · right
    have hPlus : s.phiPlus C E hE < b :=
      s.phiPlus_lt_of_triangle C hE
        (fun hA' ↦ s.phiPlus_lt_of_intervalProp C hA' hA)
        (fun hB' ↦ s.phiPlus_lt_of_intervalProp C hB' hB) hT
    have hMinus : a < s.phiMinus C E hE :=
      s.phiMinus_gt_of_triangle C hE
        (fun hA' ↦ s.phiMinus_gt_of_intervalProp C hA' hA)
        (fun hB' ↦ s.phiMinus_gt_of_intervalProp C hB' hB) hT
    obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C s hE
    exact ⟨F, fun i ↦ by
      constructor
      · calc a < s.phiMinus C E hE := hMinus
          _ = F.φ ⟨F.n - 1, by omega⟩ := s.phiMinus_eq C E hE F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
      · calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
              F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = s.phiPlus C E hE := (s.phiPlus_eq C E hE F hn hfirst).symm
          _ < b := hPlus⟩

/-! ### Cokernel/quotient containment via the right heart (Lemma 4.3 dual)

In a thin interval `P((a, b))` with `b - a ≤ 1`, the **right heart** `P([b-1, b))` controls
cokernels. Objects in the right heart satisfy `geProp(b-1)` (phases ≥ b-1) and `ltProp(b)`
(phases < b). The key property is:

Given a triangle `K → E → Q → K[1]` with `E ∈ P((a, b))`, if `K` has `geProp(b-1)` (so
`K[1]` has phases ≥ b) and `Q` has `ltProp(b)` (phases < b), then `Q ∈ P((a, b))`.

* **Upper bound** (`φ⁺(Q) < b`): immediate from the `ltProp(b)` hypothesis.
* **Lower bound** (`φ⁻(Q) > a`): by contradiction. If Q has a bottom factor with phase ≤ a,
  then f₂ ≫ β = 0 by hom-vanishing (E phases > a), and β factors through K[1] via
  yoneda_exact₃. Since K[1] has phases ≥ b > a, the factoring morphism vanishes too.
-/

omit [IsTriangulated C] in
/-- **Phase lower bound from non-strict one-sided containment.** In a triangle
`K → E → Q → K[1]`, if `E` has `φ⁻(E) > a` and `K` satisfies `geProp c` (all phases ≥ c)
with `a < c + 1`, then if `Q` is nonzero, `a < φ⁻(Q)`.

This generalizes `phiMinus_gt_of_triangle_with_gtProp` by replacing `gtProp` (strict)
with `geProp` (non-strict). The key application is cokernel containment via the right
heart, where objects satisfy `geProp(b-1)` rather than `gtProp(b-1)`. -/
theorem Slicing.phiMinus_gt_of_triangle_with_geProp (s : Slicing C)
    {K E Q : C} (hQ : ¬IsZero Q) {a : ℝ}
    (hE_gt : ∀ (hE : ¬IsZero E), a < s.phiMinus C E hE)
    {c : ℝ} (hK_ge : s.geProp C c K) (hca : a < c + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    a < s.phiMinus C Q hQ := by
  obtain ⟨FQ, hnQ, hneQ⟩ := HNFiltration.exists_nonzero_last C s hQ
  rw [s.phiMinus_eq C Q hQ FQ hnQ hneQ]
  by_contra hle
  push_neg at hle
  -- hle : FQ.φ ⟨FQ.n - 1, _⟩ ≤ a (bottom factor has phase ≤ a)
  have hQ_factor_zero :
      ∀ β : Q ⟶ (FQ.triangle ⟨FQ.n - 1, by omega⟩).obj₃, β = 0 := by
    intro β
    -- Step 1: f₂ ≫ β = 0 (E → bottom_factor is zero by hom-vanishing)
    have hfβ : f₂ ≫ β = 0 := by
      by_cases hEZ : IsZero E
      · exact hEZ.eq_of_src (f₂ ≫ β) 0
      · obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_last C s hEZ
        have hE_gap : ∀ j : Fin FE.n,
            FQ.φ ⟨FQ.n - 1, by omega⟩ < FE.φ j := fun j ↦ by
          have h1 : a < FE.φ ⟨FE.n - 1, by omega⟩ := by
            have := hE_gt hEZ
            rw [s.phiMinus_eq C E hEZ FE hnE hneE] at this; exact this
          have h2 : FE.φ ⟨FE.n - 1, by omega⟩ ≤ FE.φ j :=
            FE.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FQ.semistable ⟨FQ.n - 1, by omega⟩) FE hE_gap _
    -- Step 2: By yoneda_exact₃, β factors through K⟦1⟧
    obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₃ (Triangle.mk f₁ f₂ f₃) hT β hfβ
    -- Step 3: γ = 0 (K⟦1⟧ → bottom_factor is zero by hom-vanishing)
    suffices hγ0 : γ = 0 by rw [hγ, hγ0]; exact comp_zero
    by_cases hKZ : IsZero K
    · exact ((shiftFunctor C (1 : ℤ)).map_isZero hKZ).eq_of_src γ 0
    · rcases hK_ge with hKZ' | ⟨GK, hnGK, hGK_ge⟩
      · exact absurd hKZ' hKZ
      · -- Shift GK by 1 to get filtration of K⟦1⟧
        let GKs := GK.shiftHN C s (1 : ℤ)
        -- GKs.φ(j) = GK.φ(j) + 1 ≥ c + 1 > a ≥ FQ.φ(n-1)
        have hKs_gap : ∀ j : Fin GKs.n,
            FQ.φ ⟨FQ.n - 1, by omega⟩ < GKs.φ j := by
          intro j
          change FQ.φ ⟨FQ.n - 1, by omega⟩ < GK.φ j + ((1 : ℤ) : ℝ)
          have h1 : GK.φ ⟨GK.n - 1, by omega⟩ ≤ GK.φ j := by
            apply GK.hφ.antitone
            change j.val ≤ GK.n - 1
            have := j.isLt; have : GKs.n = GK.n := rfl; omega
          have h2 : c ≤ GK.φ ⟨GK.n - 1, by omega⟩ := hGK_ge
          have h3 : ((1 : ℤ) : ℝ) = 1 := by norm_num
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FQ.semistable ⟨FQ.n - 1, by omega⟩) GKs hKs_gap γ
  -- Bottom factor is zero — contradiction
  exact hneQ (FQ.isZero_factor_last_of_hom_eq_zero C s hnQ hQ_factor_zero)

omit [IsTriangulated C] in
/-- **Cokernel/quotient containment in thin intervals (Lemma 4.3 dual).** In a
distinguished triangle `K → E → Q → K[1]` where `E ∈ P((a,b))` and `K` has
`geProp(b-1)` (from right heart membership) and `Q` has `ltProp(b)` (from right
heart membership), then `Q ∈ P((a, b))`.

This is the key property that ensures cokernels computed in the right heart
`P([b-1, b))` stay in the interval `P((a, b))`. Together with
`first_intervalProp_of_triangle` (kernel containment via the left heart), this
establishes that `P((a, b))` is quasi-abelian (Bridgeland Lemma 4.3). -/
theorem Slicing.third_intervalProp_of_triangle (s : Slicing C)
    {a b : ℝ} (hab' : a < b)
    {K E Q : C}
    (hE : s.intervalProp C a b E)
    (hK_ge : s.geProp C (b - 1) K)
    (hQ_lt : s.ltProp C b Q)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.intervalProp C a b Q := by
  by_cases hQ : IsZero Q
  · exact Or.inl hQ
  · -- φ⁺(Q) < b: from ltProp(b) hypothesis
    have hQ_plus : s.phiPlus C Q hQ < b := s.phiPlus_lt_of_ltProp C hQ hQ_lt
    -- φ⁻(Q) > a: from phiMinus_gt_of_triangle_with_geProp
    have hQ_minus : a < s.phiMinus C Q hQ :=
      s.phiMinus_gt_of_triangle_with_geProp C hQ
        (fun hE' ↦ s.phiMinus_gt_of_intervalProp C hE' hE)
        hK_ge (by linarith) hT
    exact s.intervalProp_of_intrinsic_phases C hQ hQ_minus hQ_plus

/-- If `f : X ⟶ Y` is a monomorphism in the left heart `P((a, a + 1])` and `Y` lies in the
thin interval `P((a, b))`, then `X` also lies in `P((a, b))`. This is the concrete
kernel-side closure condition from Bridgeland Lemma 4.2. -/
theorem Slicing.intervalProp_of_mono_leftHeart (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : ((s.phaseShift C a).toTStructure).heart.FullSubcategory}
    (hY : s.intervalProp C a b Y.obj) (f : X ⟶ Y) [Mono f] :
    s.intervalProp C a b X.obj := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let q : Y ⟶ cokernel f := cokernel.π f
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) q
  have hKGtShift :
      (s.phaseShift C a).gtProp C 0 K.obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a) K.obj).mp
      K.property |>.1
  have hKGt : s.gtProp C a K.obj := (s.phaseShift_gtProp_zero C a K.obj).mp hKGtShift
  have hQLeShift :
      (s.phaseShift C a).leProp C 1 (cokernel f).obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a)
      (cokernel f).obj).mp
      (cokernel f).property |>.2
  have hQLe : s.leProp C (a + 1) (cokernel f).obj := by
    simpa [add_comm] using
      (s.phaseShift_leProp C a 1 (cokernel f).obj).mp hQLeShift
  have hT' : Pretriangulated.Triangle.mk i.hom q.hom δ ∈ distTriang C := by
    simpa using hT
  have hK_mem_aux : s.intervalProp C a b K.obj :=
    s.first_intervalProp_of_triangle C (Fact.out : a < b) hY hQLe hKGt hT'
  have hKer : IsLimit (KernelFork.ofι f (cokernel.condition f)) :=
    Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ q (cokernel.condition f))
      (cokernelIsCokernel f)
  let e : X ≅ K := IsLimit.conePointUniqueUpToIso hKer
    (Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i q δ hT)
  exact (s.intervalProp C a b).prop_of_iso
    ⟨e.inv.hom, e.hom.hom,
      by simpa using congrArg InducedCategory.Hom.hom e.inv_hom_id,
      by simpa using congrArg InducedCategory.Hom.hom e.hom_inv_id⟩
    hK_mem_aux

/-- If `f : X ⟶ Y` is an epimorphism in the right heart `P([b - 1, b))` and `X` lies in the
thin interval `P((a, b))`, then `Y` also lies in `P((a, b))`. This is the concrete
cokernel-side closure condition from Bridgeland Lemma 4.2. -/
theorem Slicing.intervalProp_of_epi_rightHeart (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : ((s.phaseShift C (b - 1)).toTStructureGE).heart.FullSubcategory}
    (hX : s.intervalProp C a b X.obj) (f : X ⟶ Y) [Epi f] :
    s.intervalProp C a b Y.obj := by
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) f
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property |>.1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hYLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 Y.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) Y.obj).mp
      Y.property |>.2
  have hYLt : s.ltProp C b Y.obj := by
    simpa [show 1 + (b - 1) = b by ring] using
      (s.phaseShift_ltProp C (b - 1) 1 Y.obj).mp hYLtShift
  have hT' : Pretriangulated.Triangle.mk i.hom f.hom δ ∈ distTriang C := by
    simpa using hT
  exact s.third_intervalProp_of_triangle C (Fact.out : a < b) hX hKGe hYLt hT'

end TwoHeartEmbedding

section Preabelian

variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The left ambient abelian heart `P((a,a+1])`. -/
abbrev Slicing.LeftHeart (s : Slicing C) (a : ℝ) :=
  ((s.phaseShift C a).toTStructure).heart.FullSubcategory

/-- The right ambient abelian heart `P([b-1,b))`. -/
abbrev Slicing.RightHeart (s : Slicing C) (b : ℝ) :=
  ((s.phaseShift C (b - 1)).toTStructureGE).heart.FullSubcategory

noncomputable def Slicing.intervalCat_hasKernel (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) : HasKernel f := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (s := s) (C := C) a b hab
  let XH : t.heart.FullSubcategory := FL.obj X
  let YH : t.heart.FullSubcategory := FL.obj Y
  let fH : XH ⟶ YH := FL.map f
  let π : XH ⟶ cokernel (kernel.ι fH) := cokernel.π (kernel.ι fH)
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) π
  have hKπ :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i π δ hT
  have hKerπ : IsLimit (KernelFork.ofι (kernel.ι fH) (cokernel.condition _)) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  let eK : K ≅ kernel fH := IsLimit.conePointUniqueUpToIso hKπ hKerπ
  have hKGtShift :
      (s.phaseShift C a).gtProp C 0 K.obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a) K.obj).mp
      K.property |>.1
  have hKGt : s.gtProp C a K.obj := (s.phaseShift_gtProp_zero C a K.obj).mp hKGtShift
  have hQLeShift :
      (s.phaseShift C a).leProp C 1 (cokernel (kernel.ι fH)).obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a)
      (cokernel (kernel.ι fH)).obj).mp
      (cokernel (kernel.ι fH)).property |>.2
  have hQLe : s.leProp C (a + 1) (cokernel (kernel.ι fH)).obj :=
    by simpa [add_comm] using
      (s.phaseShift_leProp C a 1 (cokernel (kernel.ι fH)).obj).mp hQLeShift
  have hT' : Triangle.mk i.hom π.hom δ ∈ distTriang C := by
    simpa using hT
  have hK_mem_aux : s.intervalProp C a b K.obj :=
    s.first_intervalProp_of_triangle C hab' X.property hQLe hKGt hT'
  let eK0 : K.obj ≅ (kernel fH).obj :=
    ⟨eK.hom.hom, eK.inv.hom,
      by simpa using congrArg InducedCategory.Hom.hom eK.hom_inv_id,
      by simpa using congrArg InducedCategory.Hom.hom eK.inv_hom_id⟩
  have hKer_mem : s.intervalProp C a b (kernel fH).obj :=
    (s.intervalProp C a b).prop_of_iso eK0 hK_mem_aux
  let KI : s.IntervalCat C a b := ⟨(kernel fH).obj, hKer_mem⟩
  let k : KI ⟶ X := ObjectProperty.homMk (kernel.ι fH).hom
  have hk_zero : k ≫ f = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι fH ≫ fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition fH)
  refine ⟨⟨KernelFork.ofι k hk_zero, ?_⟩⟩
  refine KernelFork.IsLimit.ofι _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
    (fun {W'} g hg m hm ↦ ?_)
  · let WH : t.heart.FullSubcategory := FL.obj W'
    let ι' : WH ⟶ XH := FL.map g
    have hι' : ι' ≫ fH = 0 := by
      apply ((t.heart).ι).map_injective
      simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
    exact ObjectProperty.homMk (kernel.lift fH ι' hι').hom
  · let WH : t.heart.FullSubcategory := FL.obj W'
    let ι' : WH ⟶ XH := FL.map g
    have hι' : ι' ≫ fH = 0 := by
      apply ((t.heart).ι).map_injective
      simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = g.hom
    rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
      exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
    rfl
  · let WH : t.heart.FullSubcategory := FL.obj W'
    let ι' : WH ⟶ XH := FL.map g
    have hι' : ι' ≫ fH = 0 := by
      apply ((t.heart).ι).map_injective
      simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
    let mH : WH ⟶ kernel fH := ObjectProperty.homMk m.hom
    have hm' : mH ≫ kernel.ι fH = kernel.lift fH ι' hι' ≫ kernel.ι fH := by
      apply ((t.heart).ι).map_injective
      change m.hom ≫ (kernel.ι fH).hom =
        (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom
      rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
      simpa [mH, k] using congrArg InducedCategory.Hom.hom hm
    have hmEq : mH = kernel.lift fH ι' hι' :=
      Fork.IsLimit.hom_ext (kernelIsKernel fH) hm'
    apply ((s.intervalProp C a b).ι).map_injective
    change m.hom = (kernel.lift fH ι' hι').hom
    simpa [mH] using congrArg InducedCategory.Hom.hom hmEq

noncomputable instance Slicing.intervalCat_hasKernels (s : Slicing C) :
    HasKernels (s.IntervalCat C a b) :=
  ⟨fun {X Y} f ↦ Slicing.intervalCat_hasKernel (C := C) (s := s)
    (a := a) (b := b) (X := X) (Y := Y) f⟩

noncomputable def Slicing.intervalCat_hasCokernel (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) : HasCokernel f := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (s := s) (C := C) a b hab
  let XH : t.heart.FullSubcategory := FR.obj X
  let YH : t.heart.FullSubcategory := FR.obj Y
  let fH : XH ⟶ YH := FR.map f
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) (cokernel.π fH)
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property |>.1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hQLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 (cokernel fH).obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1))
      (cokernel fH).obj).mp
      (cokernel fH).property |>.2
  have hQLt : s.ltProp C b (cokernel fH).obj := by
    simpa [show 1 + (b - 1) = b by ring] using
      (s.phaseShift_ltProp C (b - 1) 1 (cokernel fH).obj).mp hQLtShift
  have hT' : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := by
    simpa using hT
  have hCoker_mem : s.intervalProp C a b (cokernel fH).obj :=
    s.third_intervalProp_of_triangle C hab' Y.property hKGe hQLt hT'
  let QI : s.IntervalCat C a b := ⟨(cokernel fH).obj, hCoker_mem⟩
  let p : Y ⟶ QI := ObjectProperty.homMk (cokernel.π fH).hom
  have hp_zero : f ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (fH ≫ cokernel.π fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition fH)
  refine ⟨⟨CokernelCofork.ofπ p hp_zero, ?_⟩⟩
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
    (fun {W'} g hg m hm ↦ ?_)
  · let WH : t.heart.FullSubcategory := FR.obj W'
    let π' : YH ⟶ WH := FR.map g
    have hπ' : fH ≫ π' = 0 := by
      apply ((t.heart).ι).map_injective
      simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
    exact ObjectProperty.homMk (cokernel.desc fH π' hπ').hom
  · let WH : t.heart.FullSubcategory := FR.obj W'
    let π' : YH ⟶ WH := FR.map g
    have hπ' : fH ≫ π' = 0 := by
      apply ((t.heart).ι).map_injective
      simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
    apply ((s.intervalProp C a b).ι).map_injective
    change (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = g.hom
    rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
      exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
    rfl
  · let WH : t.heart.FullSubcategory := FR.obj W'
    let π' : YH ⟶ WH := FR.map g
    have hπ' : fH ≫ π' = 0 := by
      apply ((t.heart).ι).map_injective
      simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
    let mH : cokernel fH ⟶ WH := ObjectProperty.homMk m.hom
    have hm' : cokernel.π fH ≫ mH = cokernel.π fH ≫ cokernel.desc fH π' hπ' := by
      apply ((t.heart).ι).map_injective
      change (cokernel.π fH).hom ≫ m.hom =
        (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom
      rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
      simpa [mH, p] using congrArg InducedCategory.Hom.hom hm
    have hmEq : mH = cokernel.desc fH π' hπ' :=
      Cofork.IsColimit.hom_ext (cokernelIsCokernel fH) hm'
    apply ((s.intervalProp C a b).ι).map_injective
    change m.hom = (cokernel.desc fH π' hπ').hom
    simpa [mH] using congrArg InducedCategory.Hom.hom hmEq

noncomputable instance Slicing.intervalCat_hasCokernels (s : Slicing C) :
    HasCokernels (s.IntervalCat C a b) :=
  ⟨fun {X Y} f ↦ Slicing.intervalCat_hasCokernel (C := C) (s := s)
    (a := a) (b := b) (X := X) (Y := Y) f⟩

/-- The cokernel of a morphism in `P((a,b))` is computed by the right heart
`P([b - 1, b))`. -/
noncomputable def Slicing.IntervalCat.toRightHeartCokernelIso (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C (b - 1)).toTStructureGE
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    FR.obj (cokernel f) ≅ cokernel (FR.map f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FR.obj X
  let YH : t.heart.FullSubcategory := FR.obj Y
  let fH : XH ⟶ YH := FR.map f
  classical
  let h₀ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) (cokernel.π fH)
  let K := Classical.choose h₀
  let h₁ := Classical.choose_spec h₀
  let i := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let δ := Classical.choose h₂
  let hT : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := Classical.choose_spec h₂
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property |>.1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hQLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 (cokernel fH).obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1))
      (cokernel fH).obj).mp
      (cokernel fH).property |>.2
  have hQLt : s.ltProp C b (cokernel fH).obj := by
    simpa [show 1 + (b - 1) = b by ring] using
      (s.phaseShift_ltProp C (b - 1) 1 (cokernel fH).obj).mp hQLtShift
  have hT' : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := by
    simpa using hT
  have hCoker_mem : s.intervalProp C a b (cokernel fH).obj :=
    s.third_intervalProp_of_triangle C hab' Y.property hKGe hQLt hT'
  let QI : s.IntervalCat C a b := ⟨(cokernel fH).obj, hCoker_mem⟩
  let p : Y ⟶ QI := ObjectProperty.homMk (cokernel.π fH).hom
  have hp_zero : f ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (fH ≫ cokernel.π fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition fH)
  let hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (cokernel.desc fH π' hπ').hom
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = g.hom
      rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
      rfl
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      let mH : cokernel fH ⟶ WH := ObjectProperty.homMk m.hom
      have hm' : cokernel.π fH ≫ mH = cokernel.π fH ≫ cokernel.desc fH π' hπ' := by
        apply ((t.heart).ι).map_injective
        change (cokernel.π fH).hom ≫ m.hom =
          (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom
        rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
          exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
        simpa [mH, p] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = cokernel.desc fH π' hπ' :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel fH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (cokernel.desc fH π' hπ').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : QI ≅ cokernel f := IsColimit.coconePointUniqueUpToIso hp_colim (colimit.isColimit _)
  let eH : FR.obj (cokernel f) ≅ FR.obj QI := FR.mapIso e.symm
  let j : FR.obj QI ≅ cokernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  exact eH ≪≫ j

theorem Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C (b - 1)).toTStructureGE
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    FR.map (cokernel.π f) ≫
      (Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s)
        (a := a) (b := b) f).hom =
      cokernel.π (FR.map f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FR.obj X
  let YH : t.heart.FullSubcategory := FR.obj Y
  let fH : XH ⟶ YH := FR.map f
  classical
  let h₀ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) (cokernel.π fH)
  let K := Classical.choose h₀
  let h₁ := Classical.choose_spec h₀
  let i := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let δ := Classical.choose h₂
  let hT : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := Classical.choose_spec h₂
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property |>.1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hQLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 (cokernel fH).obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1))
      (cokernel fH).obj).mp
      (cokernel fH).property |>.2
  have hQLt : s.ltProp C b (cokernel fH).obj := by
    simpa [show 1 + (b - 1) = b by ring] using
      (s.phaseShift_ltProp C (b - 1) 1 (cokernel fH).obj).mp hQLtShift
  have hT' : Triangle.mk i.hom (cokernel.π fH).hom δ ∈ distTriang C := by
    simpa using hT
  have hCoker_mem : s.intervalProp C a b (cokernel fH).obj :=
    s.third_intervalProp_of_triangle C hab' Y.property hKGe hQLt hT'
  let QI : s.IntervalCat C a b := ⟨(cokernel fH).obj, hCoker_mem⟩
  let p : Y ⟶ QI := ObjectProperty.homMk (cokernel.π fH).hom
  have hp_zero : f ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (fH ≫ cokernel.π fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition fH)
  let hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (cokernel.desc fH π' hπ').hom
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = g.hom
      rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
      rfl
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : fH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', fH] using congrArg InducedCategory.Hom.hom hg
      let mH : cokernel fH ⟶ WH := ObjectProperty.homMk m.hom
      have hm' : cokernel.π fH ≫ mH = cokernel.π fH ≫ cokernel.desc fH π' hπ' := by
        apply ((t.heart).ι).map_injective
        change (cokernel.π fH).hom ≫ m.hom =
          (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom
        rw [show (cokernel.π fH ≫ cokernel.desc fH π' hπ').hom = π'.hom by
          exact congrArg InducedCategory.Hom.hom (cokernel.π_desc fH π' hπ')]
        simpa [mH, p] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = cokernel.desc fH π' hπ' :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel fH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (cokernel.desc fH π' hπ').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : QI ≅ cokernel f := IsColimit.coconePointUniqueUpToIso hp_colim (colimit.isColimit _)
  let eH : FR.obj (cokernel f) ≅ FR.obj QI := FR.mapIso e.symm
  let j : FR.obj QI ≅ cokernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  have he :
      p ≫ e.hom = cokernel.π f := by
    simpa [e, CokernelCofork.ofπ] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hp_colim (colimit.isColimit _)
        Limits.WalkingParallelPair.one
  have hp_eq : FR.map p ≫ (FR.mapIso e).hom = FR.map (cokernel.π f) := by
    simpa [e] using congrArg FR.map he
  have hp_eq' : FR.map (cokernel.π f) ≫ eH.hom = FR.map p := by
    apply (cancel_mono (FR.mapIso e).hom).1
    simpa [eH] using hp_eq.symm
  have hj_map : FR.map p ≫ j.hom = cokernel.π fH := by
    apply ((t.heart).ι).map_injective
    change (FR.map p).hom ≫ (j.hom).hom = (cokernel.π fH).hom
    have hmap : (FR.map p).hom = (cokernel.π fH).hom := by
      change p.hom = (cokernel.π fH).hom
      rfl
    rw [hmap]
    simp [j]
  change FR.map (cokernel.π f) ≫ (eH.hom ≫ j.hom) = cokernel.π fH
  rw [← Category.assoc, hp_eq', hj_map]

/-- A strict epimorphism in `P((a, b))` becomes an epimorphism in the right heart
`P([b - 1, b))`. -/
theorem Slicing.IntervalCat.epi_toRightHeart_of_strictEpi (s : Slicing C)
    {X Y : s.IntervalCat C a b} (g : X ⟶ Y) (hg : IsStrictEpi g) :
    Epi ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map g) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FR.obj (kernel g)
  let YH : t.heart.FullSubcategory := FR.obj X
  let k : kernel g ⟶ X := kernel.ι g
  let kH : XH ⟶ YH := FR.map k
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) (cokernel.π kH)
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property |>.1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hQLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 (cokernel kH).obj := by
    exact (Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1))
      (cokernel kH).obj).mp
      (cokernel kH).property |>.2
  have hQLt : s.ltProp C b (cokernel kH).obj := by
    simpa [show 1 + (b - 1) = b by ring] using
      (s.phaseShift_ltProp C (b - 1) 1 (cokernel kH).obj).mp hQLtShift
  have hT' : Pretriangulated.Triangle.mk i.hom (cokernel.π kH).hom δ ∈ distTriang C := by
    simpa using hT
  have hCoker_mem : s.intervalProp C a b (cokernel kH).obj :=
    s.third_intervalProp_of_triangle C hab' X.property hKGe hQLt hT'
  let QI : s.IntervalCat C a b := ⟨(cokernel kH).obj, hCoker_mem⟩
  let p : X ⟶ QI := ObjectProperty.homMk (cokernel.π kH).hom
  have hp_zero : k ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kH ≫ cokernel.π kH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition kH)
  have hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (cokernel.desc kH π' hπ').hom
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = g.hom
      rw [show (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc kH π' hπ')]
      rfl
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let π' : YH ⟶ WH := FR.map g
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg
      let mH : cokernel kH ⟶ WH := ObjectProperty.homMk m.hom
      have hm' : cokernel.π kH ≫ mH = cokernel.π kH ≫ cokernel.desc kH π' hπ' := by
        apply ((t.heart).ι).map_injective
        change (cokernel.π kH).hom ≫ m.hom =
          (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom
        rw [show (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = π'.hom by
          exact congrArg InducedCategory.Hom.hom (cokernel.π_desc kH π' hπ')]
        simpa [mH, p] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = cokernel.desc kH π' hπ' :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel kH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (cokernel.desc kH π' hπ').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : QI ≅ Y := IsColimit.coconePointUniqueUpToIso hp_colim (hg.isColimitCokernelCofork)
  have he : p ≫ e.hom = g := by
    simpa [p, e, CokernelCofork.ofπ] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hp_colim (hg.isColimitCokernelCofork)
        Limits.WalkingParallelPair.one
  let j : FR.obj QI ≅ cokernel kH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;> ext <;> simp
  have hj : FR.map p ≫ j.hom = cokernel.π kH := by
    apply ((t.heart).ι).map_injective
    change (FR.map p).hom ≫ (j.hom).hom = (cokernel.π kH).hom
    have hmap : (FR.map p).hom = (cokernel.π kH).hom := by
      change p.hom = (cokernel.π kH).hom
      rfl
    rw [hmap]
    simp [j]
  have hp_eq : FR.map p = cokernel.π kH ≫ j.inv := by
    letI : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
    letI : Mono j.hom := by infer_instance
    exact (cancel_mono j.hom).1 (by simpa [Category.assoc] using hj)
  have hp_epi : Epi (FR.map p) := by
    letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
    haveI : Epi (cokernel.π kH ≫ j.inv) := inferInstance
    simpa [hp_eq]
  let eH : FR.obj QI ≅ FR.obj Y := FR.mapIso e
  have hmapg : FR.map p ≫ eH.hom = FR.map g := by
    simpa [eH] using congrArg FR.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  haveI : Epi (FR.map p ≫ eH.hom) := inferInstance
  simpa [hmapg]

/-- A strict monomorphism in `P((a, b))` becomes a monomorphism in the left heart
`P((a, a + 1])`. -/
theorem Slicing.IntervalCat.mono_toLeftHeart_of_strictMono (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictMono f) :
    Mono ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let YH : t.heart.FullSubcategory := FL.obj Y
  let ZH : t.heart.FullSubcategory := FL.obj (cokernel f)
  let q : Y ⟶ cokernel f := cokernel.π f
  let qH : YH ⟶ ZH := FL.map q
  let π : YH ⟶ cokernel (kernel.ι qH) := cokernel.π (kernel.ι qH)
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) π
  have hKGtShift :
      (s.phaseShift C a).gtProp C 0 K.obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a) K.obj).mp
      K.property |>.1
  have hKGt : s.gtProp C a K.obj := (s.phaseShift_gtProp_zero C a K.obj).mp hKGtShift
  have hQLeShift :
      (s.phaseShift C a).leProp C 1 (cokernel (kernel.ι qH)).obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a)
      (cokernel (kernel.ι qH)).obj).mp
      (cokernel (kernel.ι qH)).property |>.2
  have hQLe : s.leProp C (a + 1) (cokernel (kernel.ι qH)).obj := by
    simpa [add_comm] using
      (s.phaseShift_leProp C a 1 (cokernel (kernel.ι qH)).obj).mp hQLeShift
  have hT' : Pretriangulated.Triangle.mk i.hom π.hom δ ∈ distTriang C := by
    simpa using hT
  have hK_mem_aux : s.intervalProp C a b K.obj :=
    s.first_intervalProp_of_triangle C hab' Y.property hQLe hKGt hT'
  have hKerπ : IsLimit (KernelFork.ofι (kernel.ι qH) (cokernel.condition _)) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  let eK : K ≅ kernel qH := IsLimit.conePointUniqueUpToIso
    (Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i π δ hT) hKerπ
  let eK0 : K.obj ≅ (kernel qH).obj :=
    ⟨eK.hom.hom, eK.inv.hom,
      by simpa using congrArg InducedCategory.Hom.hom eK.hom_inv_id,
      by simpa using congrArg InducedCategory.Hom.hom eK.inv_hom_id⟩
  have hKer_mem : s.intervalProp C a b (kernel qH).obj :=
    (s.intervalProp C a b).prop_of_iso eK0 hK_mem_aux
  let KI : s.IntervalCat C a b := ⟨(kernel qH).obj, hKer_mem⟩
  let k : KI ⟶ Y := ObjectProperty.homMk (kernel.ι qH).hom
  have hk_zero : k ≫ q = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι qH ≫ qH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition qH)
  let hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ YH := FL.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (kernel.lift qH ι' hι').hom
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ YH := FL.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = g.hom
      rw [show (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι qH ι' hι')]
      rfl
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ YH := FL.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      let mH : WH ⟶ kernel qH := ObjectProperty.homMk m.hom
      have hm' : mH ≫ kernel.ι qH = kernel.lift qH ι' hι' ≫ kernel.ι qH := by
        apply ((t.heart).ι).map_injective
        change m.hom ≫ (kernel.ι qH).hom = (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom
        rw [show (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = ι'.hom by
          exact congrArg InducedCategory.Hom.hom (kernel.lift_ι qH ι' hι')]
        simpa [mH, k] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = kernel.lift qH ι' hι' :=
        Fork.IsLimit.hom_ext (kernelIsKernel qH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (kernel.lift qH ι' hι').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : X ≅ KI := IsLimit.conePointUniqueUpToIso (hf.isLimitKernelFork) hk_limit
  have he : e.hom ≫ k = f := by
    simpa [k, e, KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_hom_comp (hf.isLimitKernelFork) hk_limit
        Limits.WalkingParallelPair.zero
  let j : kernel qH ≅ FL.obj KI := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;> ext <;> simp
  have hj : j.hom ≫ FL.map k = kernel.ι qH := by
    apply ((t.heart).ι).map_injective
    change (j.hom).hom ≫ (FL.map k).hom = (kernel.ι qH).hom
    have hmap : (FL.map k).hom = (kernel.ι qH).hom := by
      change k.hom = (kernel.ι qH).hom
      rfl
    rw [hmap]
    simp [j]
  have hk_eq : FL.map k = j.inv ≫ kernel.ι qH := by
    letI : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
    letI : Epi j.hom := by infer_instance
    exact (cancel_epi j.hom).1 (by simpa [Category.assoc] using hj)
  have hk_mono : Mono (FL.map k) := by
    letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
    haveI : Mono (j.inv ≫ kernel.ι qH) := inferInstance
    simpa [hk_eq]
  let eH : FL.obj X ≅ FL.obj KI := FL.mapIso e
  have hmapf : eH.hom ≫ FL.map k = FL.map f := by
    simpa [eH] using congrArg FL.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  haveI : Mono (eH.hom ≫ FL.map k) := inferInstance
  simpa [hmapf]

/-- A strict monomorphism in `P((a, b))` becomes a monomorphism in the right heart
`P([b - 1, b))`. -/
theorem Slicing.IntervalCat.mono_toRightHeart_of_strictMono (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictMono f) :
    Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f) := by
  have hab : b - a ≤ 1 := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let q : Y ⟶ cokernel f := cokernel.π f
  let qH : FR.obj Y ⟶ FR.obj (cokernel f) := FR.map q
  let eQ := Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s) (a := a) (b := b) f
  have hqHeq : qH ≫ eQ.hom = cokernel.π (FR.map f) := by
    simpa [qH, FR, eQ] using Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
      (C := C) (s := s) (a := a) (b := b) f
  have himage_zero : Abelian.image.ι (FR.map f) ≫ qH = 0 := by
    apply (cancel_mono eQ.hom).1
    simpa [Category.assoc, hqHeq] using kernel.condition (cokernel.π (FR.map f))
  have himage_kernel : IsLimit
      (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero) := by
    exact isKernelOfComp (f := qH) eQ.hom (cokernel.π (FR.map f))
      (kernelIsKernel (cokernel.π (FR.map f))) himage_zero hqHeq
  have hkernel_qH : IsLimit (KernelFork.ofι (kernel.ι qH) (kernel.condition qH)) := by
    simpa using kernelIsKernel qH
  let eKh : Abelian.image (FR.map f) ⟶ kernel qH :=
    hkernel_qH.lift (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero)
  have heKh : eKh ≫ kernel.ι qH = Abelian.image.ι (FR.map f) := by
    simpa [eKh, KernelFork.ofι] using
      hkernel_qH.fac (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero)
        Limits.WalkingParallelPair.zero
  let eKi : kernel qH ⟶ Abelian.image (FR.map f) :=
    himage_kernel.lift (KernelFork.ofι (kernel.ι qH) (kernel.condition qH))
  have heKi : eKi ≫ Abelian.image.ι (FR.map f) = kernel.ι qH := by
    simpa [eKi, KernelFork.ofι] using
      himage_kernel.fac (KernelFork.ofι (kernel.ι qH) (kernel.condition qH))
        Limits.WalkingParallelPair.zero
  let eK : Abelian.image (FR.map f) ≅ kernel qH := by
    refine ⟨eKh, eKi, ?_, ?_⟩
    · apply (cancel_mono (Abelian.image.ι (FR.map f))).1
      simpa [Category.assoc, heKh, heKi]
    · apply (cancel_mono (kernel.ι qH)).1
      simpa [Category.assoc, heKh, heKi]
  have heK : eK.hom ≫ kernel.ι qH = Abelian.image.ι (FR.map f) := by
    exact heKh
  let iH : FR.obj X ⟶ kernel qH := Abelian.factorThruImage (FR.map f) ≫ eK.hom
  have hiH : iH ≫ kernel.ι qH = FR.map f := by
    change (Abelian.factorThruImage (FR.map f) ≫ eK.hom) ≫ kernel.ι qH = FR.map f
    rw [Category.assoc, heK, Abelian.image.fac]
  haveI : Epi iH := by
    letI : IsIso eK.hom := ⟨⟨eK.inv, eK.hom_inv_id, eK.inv_hom_id⟩⟩
    exact CategoryTheory.epi_comp'
      (CategoryTheory.Abelian.instEpiFactorThruImage (f := FR.map f)) inferInstance
  have hK_mem : s.intervalProp C a b (kernel qH).obj := by
    exact s.intervalProp_of_epi_rightHeart (C := C) (a := a) (b := b)
      X.property iH
  let KI : s.IntervalCat C a b := ⟨(kernel qH).obj, hK_mem⟩
  let k : KI ⟶ Y := ObjectProperty.homMk (kernel.ι qH).hom
  let i : X ⟶ KI := ObjectProperty.homMk iH.hom
  have hk_zero : k ≫ q = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι qH ≫ qH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition qH)
  have hi : i ≫ k = f := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (iH ≫ kernel.ι qH).hom = (FR.map f).hom
    simpa [hiH]
  have hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let ι' : WH ⟶ FR.obj Y := FR.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (kernel.lift qH ι' hι').hom
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let ι' : WH ⟶ FR.obj Y := FR.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = g.hom
      rw [show (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι qH ι' hι')]
      rfl
    · let WH : t.heart.FullSubcategory := FR.obj W'
      let ι' : WH ⟶ FR.obj Y := FR.map g
      have hι' : ι' ≫ qH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', qH] using congrArg InducedCategory.Hom.hom hg
      let mH : WH ⟶ kernel qH := ObjectProperty.homMk m.hom
      have hm' : mH ≫ kernel.ι qH = kernel.lift qH ι' hι' ≫ kernel.ι qH := by
        apply ((t.heart).ι).map_injective
        change m.hom ≫ (kernel.ι qH).hom = (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom
        rw [show (kernel.lift qH ι' hι' ≫ kernel.ι qH).hom = ι'.hom by
          exact congrArg InducedCategory.Hom.hom (kernel.lift_ι qH ι' hι')]
        simpa [mH, k] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = kernel.lift qH ι' hι' :=
        Fork.IsLimit.hom_ext (kernelIsKernel qH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (kernel.lift qH ι' hι').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : X ≅ KI := IsLimit.conePointUniqueUpToIso (hf.isLimitKernelFork) hk_limit
  have he : e.hom ≫ k = f := by
    simpa [k, e, KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_hom_comp (hf.isLimitKernelFork) hk_limit
        Limits.WalkingParallelPair.zero
  let j : kernel qH ≅ FR.obj KI := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;> ext <;> simp
  have hk_map : j.inv ≫ kernel.ι qH = FR.map k := by
    apply ((t.heart).ι).map_injective
    change (j.inv ≫ kernel.ι qH).hom = (FR.map k).hom
    simp [FR, k, j]
  have hk_eq : FR.map k = j.inv ≫ kernel.ι qH := hk_map.symm
  let eH : FR.obj X ≅ FR.obj KI := FR.mapIso e
  have hmapf : eH.hom ≫ FR.map k = FR.map f := by
    simpa [eH] using congrArg FR.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
  haveI : Mono (eH.hom ≫ (j.inv ≫ kernel.ι qH)) := inferInstance
  have hfac : FR.map f ≫ 𝟙 _ = eH.hom ≫ (j.inv ≫ kernel.ι qH) := by
    simpa [Category.comp_id, hk_eq, Category.assoc] using hmapf.symm
  exact mono_of_mono_fac hfac

/-- If a morphism in `P((a, b))` becomes a monomorphism in the right heart
`P([b - 1, b))`, then it is a strict monomorphism in `P((a, b))`. -/
theorem Slicing.IntervalCat.strictMono_of_mono_toRightHeart (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y)
    [Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f)] :
    IsStrictMono f := by
  have hab : b - a ≤ 1 := Fact.out
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab
  let eQ := Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s) (a := a) (b := b) f
  let eDiag :
      parallelPair (FR.map (cokernel.π f)) 0 ≅ parallelPair (cokernel.π (FR.map f)) 0 :=
    parallelPair.ext (Iso.refl _) eQ
      (by
        simpa [FR, eQ] using Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
          (C := C) (s := s) (a := a) (b := b) f)
      (by simp)
  have hlim' :
      IsLimit
        (KernelFork.ofι (FR.map f) (by
          apply ((t.heart).ι).map_injective
          change (f ≫ cokernel.π f).hom = 0
          exact congrArg InducedCategory.Hom.hom (cokernel.condition f)) :
          Fork (FR.map (cokernel.π f)) 0) := by
    let c :
        Fork (cokernel.π (FR.map f)) 0 :=
      KernelFork.ofι (FR.map f) (cokernel.condition (FR.map f))
    let s :
        Cofork (FR.map f) 0 :=
      CokernelCofork.ofπ (cokernel.π (FR.map f)) (cokernel.condition (FR.map f))
    have hcanon : IsLimit c :=
      Abelian.monoIsKernelOfCokernel s (cokernelIsCokernel (FR.map f))
    let htrans := (IsLimit.postcomposeInvEquiv eDiag c).symm hcanon
    exact IsLimit.ofIsoLimit htrans <|
      Fork.ext (Iso.refl _) (by
        have hι : c.ι = Fork.ι ((Cones.postcompose eDiag.inv).obj c) := by
          change c.ι = c.ι ≫ eDiag.inv.app WalkingParallelPair.zero
          simp [eDiag]
        simpa [c] using hι)
  have hmap :
      IsLimit (FR.mapCone (KernelFork.ofι f (cokernel.condition f))) :=
    (isLimitMapConeForkEquiv' FR (cokernel.condition f)).symm hlim'
  have hlim : IsLimit (KernelFork.ofι f (cokernel.condition f)) :=
    isLimitOfReflects FR hmap
  exact isStrictMono_of_isLimitKernelFork hlim

/-- The kernel of a morphism in `P((a,b))` is computed by the left heart
`P((a,a+1])`. -/
noncomputable def Slicing.IntervalCat.toLeftHeartKernelIso (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C a).toTStructure
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    FL.obj (kernel f) ≅ kernel (FL.map f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FL.obj X
  let YH : t.heart.FullSubcategory := FL.obj Y
  let fH : XH ⟶ YH := FL.map f
  let π : XH ⟶ cokernel (kernel.ι fH) := cokernel.π (kernel.ι fH)
  classical
  let h₀ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) π
  let K := Classical.choose h₀
  let h₁ := Classical.choose_spec h₀
  let i := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let δ := Classical.choose h₂
  let hT : Triangle.mk i.hom π.hom δ ∈ distTriang C := Classical.choose_spec h₂
  have hKπ :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i π δ hT
  have hKerπ : IsLimit (KernelFork.ofι (kernel.ι fH) (cokernel.condition _)) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  let eK : K ≅ kernel fH := IsLimit.conePointUniqueUpToIso hKπ hKerπ
  have hKGtShift :
      (s.phaseShift C a).gtProp C 0 K.obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a) K.obj).mp
      K.property |>.1
  have hKGt : s.gtProp C a K.obj := (s.phaseShift_gtProp_zero C a K.obj).mp hKGtShift
  have hQLeShift :
      (s.phaseShift C a).leProp C 1 (cokernel (kernel.ι fH)).obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a)
      (cokernel (kernel.ι fH)).obj).mp
      (cokernel (kernel.ι fH)).property |>.2
  have hQLe : s.leProp C (a + 1) (cokernel (kernel.ι fH)).obj :=
    by simpa [add_comm] using
      (s.phaseShift_leProp C a 1 (cokernel (kernel.ι fH)).obj).mp hQLeShift
  have hT' : Triangle.mk i.hom π.hom δ ∈ distTriang C := by
    simpa using hT
  have hK_mem_aux : s.intervalProp C a b K.obj :=
    s.first_intervalProp_of_triangle C hab' X.property hQLe hKGt hT'
  let eK0 : K.obj ≅ (kernel fH).obj :=
    ⟨eK.hom.hom, eK.inv.hom,
      by simpa using congrArg InducedCategory.Hom.hom eK.hom_inv_id,
      by simpa using congrArg InducedCategory.Hom.hom eK.inv_hom_id⟩
  have hKer_mem : s.intervalProp C a b (kernel fH).obj :=
    (s.intervalProp C a b).prop_of_iso eK0 hK_mem_aux
  let KI : s.IntervalCat C a b := ⟨(kernel fH).obj, hKer_mem⟩
  let k : KI ⟶ X := ObjectProperty.homMk (kernel.ι fH).hom
  have hk_zero : k ≫ f = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι fH ≫ fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition fH)
  let hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (kernel.lift fH ι' hι').hom
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = g.hom
      rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
      rfl
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      let mH : WH ⟶ kernel fH := ObjectProperty.homMk m.hom
      have hm' : mH ≫ kernel.ι fH = kernel.lift fH ι' hι' ≫ kernel.ι fH := by
        apply ((t.heart).ι).map_injective
        change m.hom ≫ (kernel.ι fH).hom = (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom
        rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
          exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
        simpa [mH, k] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = kernel.lift fH ι' hι' :=
        Fork.IsLimit.hom_ext (kernelIsKernel fH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (kernel.lift fH ι' hι').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : kernel f ≅ KI := IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk_limit
  let j : FL.obj KI ≅ kernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  exact FL.mapIso e ≪≫ j

theorem Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C a).toTStructure
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    (Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s)
      (a := a) (b := b) f).hom ≫ kernel.ι (FL.map f) = FL.map (kernel.ι f) := by
  have hab : b - a ≤ 1 := Fact.out
  have hab' : a < b := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let XH : t.heart.FullSubcategory := FL.obj X
  let YH : t.heart.FullSubcategory := FL.obj Y
  let fH : XH ⟶ YH := FL.map f
  let π : XH ⟶ cokernel (kernel.ι fH) := cokernel.π (kernel.ι fH)
  classical
  let h₀ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) π
  let K := Classical.choose h₀
  let h₁ := Classical.choose_spec h₀
  let i := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let δ := Classical.choose h₂
  let hT : Triangle.mk i.hom π.hom δ ∈ distTriang C := Classical.choose_spec h₂
  have hKπ :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i π δ hT
  have hKerπ : IsLimit (KernelFork.ofι (kernel.ι fH) (cokernel.condition _)) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  let eK : K ≅ kernel fH := IsLimit.conePointUniqueUpToIso hKπ hKerπ
  have hKGtShift :
      (s.phaseShift C a).gtProp C 0 K.obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a) K.obj).mp
      K.property |>.1
  have hKGt : s.gtProp C a K.obj := (s.phaseShift_gtProp_zero C a K.obj).mp hKGtShift
  have hQLeShift :
      (s.phaseShift C a).leProp C 1 (cokernel (kernel.ι fH)).obj := by
    exact (Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a)
      (cokernel (kernel.ι fH)).obj).mp
      (cokernel (kernel.ι fH)).property |>.2
  have hQLe : s.leProp C (a + 1) (cokernel (kernel.ι fH)).obj :=
    by simpa [add_comm] using
      (s.phaseShift_leProp C a 1 (cokernel (kernel.ι fH)).obj).mp hQLeShift
  have hT' : Triangle.mk i.hom π.hom δ ∈ distTriang C := by
    simpa using hT
  have hK_mem_aux : s.intervalProp C a b K.obj :=
    s.first_intervalProp_of_triangle C hab' X.property hQLe hKGt hT'
  let eK0 : K.obj ≅ (kernel fH).obj :=
    ⟨eK.hom.hom, eK.inv.hom,
      by simpa using congrArg InducedCategory.Hom.hom eK.hom_inv_id,
      by simpa using congrArg InducedCategory.Hom.hom eK.inv_hom_id⟩
  have hKer_mem : s.intervalProp C a b (kernel fH).obj :=
    (s.intervalProp C a b).prop_of_iso eK0 hK_mem_aux
  let KI : s.IntervalCat C a b := ⟨(kernel fH).obj, hKer_mem⟩
  let k : KI ⟶ X := ObjectProperty.homMk (kernel.ι fH).hom
  have hk_zero : k ≫ f = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι fH ≫ fH).hom = 0
    exact congrArg InducedCategory.Hom.hom (kernel.condition fH)
  let hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W'} g hg ↦ ?_) (fun {W'} g hg ↦ ?_)
      (fun {W'} g hg m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      exact ObjectProperty.homMk (kernel.lift fH ι' hι').hom
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = g.hom
      rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
        exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
      rfl
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let ι' : WH ⟶ XH := FL.map g
      have hι' : ι' ≫ fH = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [ι', fH] using congrArg InducedCategory.Hom.hom hg
      let mH : WH ⟶ kernel fH := ObjectProperty.homMk m.hom
      have hm' : mH ≫ kernel.ι fH = kernel.lift fH ι' hι' ≫ kernel.ι fH := by
        apply ((t.heart).ι).map_injective
        change m.hom ≫ (kernel.ι fH).hom = (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom
        rw [show (kernel.lift fH ι' hι' ≫ kernel.ι fH).hom = ι'.hom by
          exact congrArg InducedCategory.Hom.hom (kernel.lift_ι fH ι' hι')]
        simpa [mH, k] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = kernel.lift fH ι' hι' :=
        Fork.IsLimit.hom_ext (kernelIsKernel fH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (kernel.lift fH ι' hι').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : kernel f ≅ KI := IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk_limit
  let j : FL.obj KI ≅ kernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  have hk_map : j.hom ≫ kernel.ι fH = FL.map k := by
    apply ((t.heart).ι).map_injective
    change (j.hom ≫ kernel.ι fH).hom = (FL.map k).hom
    simp [FL, k, j]
  have he : e.hom ≫ k = kernel.ι f := by
    simpa [e, KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel f) hk_limit
        Limits.WalkingParallelPair.zero
  ext
  let hgoal := congrArg InducedCategory.Hom.hom he
  convert hgoal using 1
  · change (((FL.mapIso e).hom ≫ j.hom) ≫ kernel.ι fH).hom = (e.hom ≫ k).hom
    rw [Category.assoc, hk_map]
    rfl

/-- A strict epimorphism in `P((a, b))` becomes an epimorphism in the left heart
`P((a, a + 1])`. -/
theorem Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi (s : Slicing C)
    {X Y : s.IntervalCat C a b} (g : X ⟶ Y) (hg : IsStrictEpi g) :
    Epi ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map g) := by
  have hab : b - a ≤ 1 := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let k : kernel g ⟶ X := kernel.ι g
  let kH : FL.obj (kernel g) ⟶ FL.obj X := FL.map k
  let eK := Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s) (a := a) (b := b) g
  let eQ : cokernel kH ≅ cokernel (kernel.ι (FL.map g)) :=
    cokernel.mapIso kH (kernel.ι (FL.map g)) eK (Iso.refl _)
      (by
        simpa [kH, FL] using
          (Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
            (C := C) (s := s) (a := a) (b := b) g).symm)
  let d : cokernel kH ⟶ FL.obj Y := eQ.hom ≫ Abelian.factorThruCoimage (FL.map g)
  have hd : cokernel.π kH ≫ d = FL.map g := by
    calc
      cokernel.π kH ≫ d
          = cokernel.π kH ≫ eQ.hom ≫ Abelian.factorThruCoimage (FL.map g) := by
            simp [d, Category.assoc]
      _ = cokernel.π (kernel.ι (FL.map g)) ≫ Abelian.factorThruCoimage (FL.map g) := by
            simp [eQ, Category.assoc]
      _ = FL.map g := Abelian.coimage.fac (FL.map g)
  haveI : Mono d := by
    letI : CategoryTheory.NonPreadditiveAbelian t.heart.FullSubcategory :=
      CategoryTheory.Abelian.nonPreadditiveAbelian (C := t.heart.FullSubcategory)
    letI : IsIso eQ.hom := ⟨⟨eQ.inv, eQ.hom_inv_id, eQ.inv_hom_id⟩⟩
    letI : Mono eQ.hom := by infer_instance
    change Mono (eQ.hom ≫ Abelian.factorThruCoimage (FL.map g))
    exact CategoryTheory.mono_comp'
      (hg := inferInstance)
      (hf := CategoryTheory.Abelian.instMonoFactorThruCoimage (f := FL.map g))
  have hQ_mem : s.intervalProp C a b (cokernel kH).obj :=
    s.intervalProp_of_mono_leftHeart (C := C) (a := a) (b := b) Y.property d
  let QI : s.IntervalCat C a b := ⟨(cokernel kH).obj, hQ_mem⟩
  let p : X ⟶ QI := ObjectProperty.homMk (cokernel.π kH).hom
  have hp_zero : k ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kH ≫ cokernel.π kH).hom = 0
    exact congrArg InducedCategory.Hom.hom (cokernel.condition kH)
  have hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W'} g' hg' ↦ ?_) (fun {W'} g' hg' ↦ ?_)
      (fun {W'} g' hg' m hm ↦ ?_)
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let π' : FL.obj X ⟶ WH := FL.map g'
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg'
      exact ObjectProperty.homMk (cokernel.desc kH π' hπ').hom
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let π' : FL.obj X ⟶ WH := FL.map g'
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg'
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = g'.hom
      rw [show (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = π'.hom by
        exact congrArg InducedCategory.Hom.hom (cokernel.π_desc kH π' hπ')]
      rfl
    · let WH : t.heart.FullSubcategory := FL.obj W'
      let π' : FL.obj X ⟶ WH := FL.map g'
      have hπ' : kH ≫ π' = 0 := by
        apply ((t.heart).ι).map_injective
        simpa [π', kH] using congrArg InducedCategory.Hom.hom hg'
      let mH : cokernel kH ⟶ WH := ObjectProperty.homMk m.hom
      have hm' : cokernel.π kH ≫ mH = cokernel.π kH ≫ cokernel.desc kH π' hπ' := by
        apply ((t.heart).ι).map_injective
        change (cokernel.π kH).hom ≫ m.hom =
          (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom
        rw [show (cokernel.π kH ≫ cokernel.desc kH π' hπ').hom = π'.hom by
          exact congrArg InducedCategory.Hom.hom (cokernel.π_desc kH π' hπ')]
        simpa [mH, p] using congrArg InducedCategory.Hom.hom hm
      have hmEq : mH = cokernel.desc kH π' hπ' :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel kH) hm'
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (cokernel.desc kH π' hπ').hom
      simpa [mH] using congrArg InducedCategory.Hom.hom hmEq
  let e : QI ≅ Y := IsColimit.coconePointUniqueUpToIso hp_colim (hg.isColimitCokernelCofork)
  have he : p ≫ e.hom = g := by
    simpa [p, e, CokernelCofork.ofπ] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hp_colim (hg.isColimitCokernelCofork)
        Limits.WalkingParallelPair.one
  let j : FL.obj QI ≅ cokernel kH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;> ext <;> simp
  have hj : FL.map p ≫ j.hom = cokernel.π kH := by
    apply ((t.heart).ι).map_injective
    change (FL.map p).hom ≫ (j.hom).hom = (cokernel.π kH).hom
    have hmap : (FL.map p).hom = (cokernel.π kH).hom := by
      change p.hom = (cokernel.π kH).hom
      rfl
    rw [hmap]
    simp [j]
  have hp_eq : FL.map p = cokernel.π kH ≫ j.inv := by
    letI : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
    letI : Mono j.hom := by infer_instance
    exact (cancel_mono j.hom).1 (by simpa [Category.assoc] using hj)
  have hp_epi : Epi (FL.map p) := by
    letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
    haveI : Epi (cokernel.π kH ≫ j.inv) := inferInstance
    simpa [hp_eq]
  let eH : FL.obj QI ≅ FL.obj Y := FL.mapIso e
  have hmapg : FL.map p ≫ eH.hom = FL.map g := by
    simpa [eH] using congrArg FL.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  haveI : Epi (FL.map p ≫ eH.hom) := inferInstance
  simpa [hmapg]

/-- If a morphism in `P((a, b))` becomes an epimorphism in the left heart
`P((a, a + 1])`, then it is a strict epimorphism in `P((a, b))`. -/
theorem Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart (s : Slicing C)
    {X Y : s.IntervalCat C a b} (g : X ⟶ Y)
    [Epi ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map g)] :
    IsStrictEpi g := by
  have hab : b - a ≤ 1 := Fact.out
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab
  let eK := Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s) (a := a) (b := b) g
  let eDiag :
      parallelPair (FL.map (kernel.ι g)) 0 ≅ parallelPair (kernel.ι (FL.map g)) 0 :=
    parallelPair.ext eK (Iso.refl _)
      (by
        simpa [FL, eK] using (Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
          (C := C) (s := s) (a := a) (b := b) g).symm)
      (by simp)
  have hcolim' :
      IsColimit
        (CokernelCofork.ofπ (FL.map g) (by
          apply ((t.heart).ι).map_injective
          change (kernel.ι g ≫ g).hom = 0
          exact congrArg InducedCategory.Hom.hom (kernel.condition g)) :
          Cofork (FL.map (kernel.ι g)) 0) := by
    let c :
        Cofork (kernel.ι (FL.map g)) 0 :=
      CokernelCofork.ofπ (FL.map g) (kernel.condition (FL.map g))
    have hcanon : IsColimit c :=
      Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι (FL.map g))
        (kernel.condition (FL.map g))) (kernelIsKernel (FL.map g))
    let htrans := (IsColimit.precomposeHomEquiv eDiag c).symm hcanon
    exact IsColimit.ofIsoColimit htrans <|
      Cofork.ext (Iso.refl _) (by
        have hπ :
            Cofork.π ((Cocones.precompose eDiag.hom).obj c) =
              eDiag.hom.app WalkingParallelPair.one ≫ c.π := by
          change eDiag.hom.app WalkingParallelPair.one ≫ c.π =
            eDiag.hom.app WalkingParallelPair.one ≫ c.π
          rfl
        have h₁ :
            Cofork.π ((Cocones.precompose eDiag.hom).obj c) ≫
                (Iso.refl ((Cocones.precompose eDiag.hom).obj c).pt).hom =
              eDiag.hom.app WalkingParallelPair.one ≫ c.π := by
          simpa [Category.assoc] using congrArg
            (fun k => k ≫ (Iso.refl ((Cocones.precompose eDiag.hom).obj c).pt).hom) hπ
        have h₂ : eDiag.hom.app WalkingParallelPair.one ≫ c.π = FL.map g := by
          simp [c, eDiag]
        exact h₁.trans h₂)
  have hmap :
      IsColimit (FL.mapCocone (CokernelCofork.ofπ g (kernel.condition g))) :=
    (isColimitMapCoconeCoforkEquiv' FL (kernel.condition g)).symm hcolim'
  have hcolim : IsColimit (CokernelCofork.ofπ g (kernel.condition g)) :=
    isColimitOfReflects FL hmap
  exact isStrictEpi_of_isColimitCokernelCofork hcolim

instance Slicing.IntervalCat.toLeftHeart_additive (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Additive (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_add := by
    intro X Y f g
    rfl

instance Slicing.IntervalCat.toRightHeart_additive (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Additive (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_add := by
    intro X Y f g
    rfl

noncomputable instance Slicing.IntervalCat.toLeftHeart_preservesKernel (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0)
      (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  change IsLimit (FL.mapCone (KernelFork.ofι (kernel.ι f) (kernel.condition f)))
  exact (isLimitMapConeForkEquiv' FL (kernel.condition f)).symm <|
    IsLimit.ofIsoLimit (kernelIsKernel (FL.map f)) <|
      Fork.ext ((Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s)
        (a := a) (b := b) f).symm) <| by
          have hι :
              (Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s)
                (a := a) (b := b) f).hom ≫ kernel.ι (FL.map f) =
                FL.map (kernel.ι f) := by
            simpa [FL] using Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
              (C := C) (s := s) (a := a) (b := b) f
          change
            (Iso.symm (Slicing.IntervalCat.toLeftHeartKernelIso (C := C) (s := s)
              (a := a) (b := b) f)).hom ≫ FL.map (kernel.ι f) =
              kernel.ι (FL.map f)
          rw [← hι]
          simp [Category.assoc]

noncomputable instance Slicing.IntervalCat.toRightHeart_preservesCokernel (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0)
      (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  change IsColimit (FR.mapCocone (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)))
  exact (isColimitMapCoconeCoforkEquiv' FR (cokernel.condition f)).symm <|
    IsColimit.ofIsoColimit (cokernelIsCokernel (FR.map f)) <|
      Cofork.ext ((Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s)
        (a := a) (b := b) f).symm) <| by
          have hπ :
              FR.map (cokernel.π f) ≫
                (Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s)
                  (a := a) (b := b) f).hom =
                cokernel.π (FR.map f) := by
            simpa [FR] using Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
              (C := C) (s := s) (a := a) (b := b) f
          change
            cokernel.π (FR.map f) ≫
              (Iso.symm (Slicing.IntervalCat.toRightHeartCokernelIso (C := C) (s := s)
                (a := a) (b := b) f)).hom =
              FR.map (cokernel.π f)
          rw [← hπ]
          simp [Category.assoc]

noncomputable instance Slicing.intervalCat_hasBinaryBiproducts (s : Slicing C) :
    HasBinaryBiproducts (s.IntervalCat C a b) :=
  HasBinaryBiproducts.of_hasBinaryProducts

noncomputable instance Slicing.intervalCat_hasEqualizers (s : Slicing C) :
    HasEqualizers (s.IntervalCat C a b) :=
  Preadditive.hasEqualizers_of_hasKernels

noncomputable instance Slicing.intervalCat_hasCoequalizers (s : Slicing C) :
    HasCoequalizers (s.IntervalCat C a b) :=
  Preadditive.hasCoequalizers_of_hasCokernels

noncomputable instance Slicing.intervalCat_hasFiniteCoproducts (s : Slicing C) :
    HasFiniteCoproducts (s.IntervalCat C a b) :=
  hasFiniteCoproducts_of_has_binary_and_initial

noncomputable instance Slicing.intervalCat_hasPullbacks (s : Slicing C) :
    HasPullbacks (s.IntervalCat C a b) := by
  exact Limits.hasPullbacks_of_hasBinaryProducts_of_hasEqualizers _

noncomputable instance Slicing.intervalCat_hasPushouts (s : Slicing C) :
    HasPushouts (s.IntervalCat C a b) := by
  exact Limits.hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers _

noncomputable instance Slicing.IntervalCat.toLeftHeart_preservesFiniteLimits (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] :
    PreservesFiniteLimits
      (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  exact Functor.preservesFiniteLimits_of_preservesKernels FL

noncomputable instance Slicing.IntervalCat.toRightHeart_preservesFiniteColimits (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] :
    PreservesFiniteColimits
      (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  exact Functor.preservesFiniteColimits_of_preservesCokernels FR

/-- Finite subobjects in the left heart transfer to finite subobjects in `P((a,b))`
via the fully faithful left-heart embedding. -/
theorem Slicing.IntervalCat.finite_subobject_of_leftHeart (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b}
    (hX : Finite (Subobject ((Slicing.IntervalCat.toLeftHeart
      (C := C) (s := s) a b (Fact.out : b - a ≤ 1)).obj X))) :
    Finite (Subobject X) := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  exact Finite.subobject_of_faithful_preservesMono
    (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)) hX

/-- Strict epimorphisms in `P((a,b))` are closed under composition. -/
theorem Slicing.IntervalCat.comp_strictEpi (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y Z : s.IntervalCat C a b} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsStrictEpi f) (hg : IsStrictEpi g) :
    IsStrictEpi (f ≫ g) := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  haveI : Epi (FL.map f) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
      (C := C) (s := s) (a := a) (b := b) f hf
  haveI : Epi (FL.map g) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
      (C := C) (s := s) (a := a) (b := b) g hg
  haveI : Epi (FL.map (f ≫ g)) := by
    simpa using (show Epi (FL.map f ≫ FL.map g) by infer_instance)
  exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) (f ≫ g)

/-- Strict monomorphisms in `P((a,b))` are closed under composition. -/
theorem Slicing.IntervalCat.comp_strictMono (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y Z : s.IntervalCat C a b} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsStrictMono f) (hg : IsStrictMono g) :
    IsStrictMono (f ≫ g) := by
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  haveI : Mono (FR.map f) :=
    Slicing.IntervalCat.mono_toRightHeart_of_strictMono
      (C := C) (s := s) (a := a) (b := b) f hf
  haveI : Mono (FR.map g) :=
    Slicing.IntervalCat.mono_toRightHeart_of_strictMono
      (C := C) (s := s) (a := a) (b := b) g hg
  haveI : Mono (FR.map (f ≫ g)) := by
    simpa using (show Mono (FR.map f ≫ FR.map g) by infer_instance)
  exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart
    (C := C) (s := s) (a := a) (b := b) (f ≫ g)

noncomputable instance Slicing.intervalCat_quasiAbelian (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] :
    QuasiAbelian (s.IntervalCat C a b) where
  pullback_strictEpi := by
    intro X Y Z f g hg
    let t := (s.phaseShift C a).toTStructure
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
    haveI : Epi (FL.map g) :=
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) g hg
    have hpb :
        IsLimit
          (PullbackCone.mk
            (FL.map (pullback.fst f g))
            (FL.map (pullback.snd f g))
            (by
              simpa using congrArg FL.map (pullback.condition (f := f) (g := g))) :
            PullbackCone (FL.map f) (FL.map g)) :=
      isLimitOfHasPullbackOfPreservesLimit FL f g
    haveI : Epi (FL.map (pullback.fst f g)) :=
      CategoryTheory.Abelian.epi_fst_of_isLimit (f := FL.map f) (g := FL.map g) hpb
    exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
      (C := C) (s := s) (a := a) (b := b) (pullback.fst f g)
  pushout_strictMono := by
    intro X Y Z f g hf
    let t := (s.phaseShift C (b - 1)).toTStructureGE
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
    let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
    haveI : Mono (FR.map f) :=
      Slicing.IntervalCat.mono_toRightHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) f hf
    have hpo :
        IsColimit
          (PushoutCocone.mk
            (FR.map (pushout.inl f g))
            (FR.map (pushout.inr f g))
            (by
              simpa using congrArg FR.map (pushout.condition (f := f) (g := g))) :
            PushoutCocone (FR.map f) (FR.map g)) :=
      isColimitOfHasPushoutOfPreservesColimit FR f g
    haveI : Mono (FR.map (pushout.inr f g)) :=
      CategoryTheory.Abelian.mono_inr_of_isColimit (f := FR.map f) (g := FR.map g) hpo
    exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) (pushout.inr f g)

/-! ### Local finiteness in thin interval categories -/

omit [IsTriangulated C] in
/-- A slicing is locally finite if there exists `η > 0` with `η < 1/2` such that every
object in each thin interval category `P((t-η, t+η))` has finite length in the
quasi-abelian sense, i.e. ACC/DCC on strict subobjects.

The extra bound `η < 1/2` is a harmless normalization: any Bridgeland witness may be
shrunk to such an `η`, and then the width `2η` is at most `1`, so the thin interval
category carries the exact / quasi-abelian structure proved above. -/
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  intervalFinite : ∃ η : ℝ, ∃ hη : 0 < η, ∃ hη' : η < 1 / 2, ∀ t : ℝ,
    let a := t - η
    let b := t + η
    letI : Fact (a < b) := ⟨by
      dsimp [a, b]
      linarith⟩
    letI : Fact (b - a ≤ 1) := ⟨by
      dsimp [a, b]
      linarith⟩
    ∀ (E : s.IntervalCat C a b),
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E

/-- If a short complex in `P((a,b))` is short exact after embedding into both hearts,
then its left map is a strict monomorphism and its right map is a strict epimorphism
in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictMono_strictEpi_of_shortExact_toLeftRightHearts (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hL :
      (S.map (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1))).ShortExact)
    (hR :
      (S.map (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1))).ShortExact) :
    IsStrictMono S.f ∧ IsStrictEpi S.g := by
  let tL := (s.phaseShift C a).toTStructure
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := tL.heartFullSubcategoryAbelian
  letI : CategoryWithHomology tL.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := tL.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  letI : CategoryWithHomology tR.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := tR.heart.FullSubcategory)
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  letI : Mono (FR.map S.f) := hR.mono_f
  letI : Epi (FL.map S.g) := hL.epi_g
  have hf : IsStrictMono S.f :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) S.f
  have hg : IsStrictEpi S.g :=
    Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
      (C := C) (s := s) (a := a) (b := b) S.g
  exact ⟨hf, hg⟩

/-- A distinguished triangle in `C` whose three vertices lie in `P((a,b))`
forces the first map to be a strict monomorphism and the second to be a strict epimorphism
in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictMono_strictEpi_of_distTriang (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    {δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C) :
    IsStrictMono S.f ∧ IsStrictEpi S.g := by
  let tL := (s.phaseShift C a).toTStructure
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := tL.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιL := tL.ιHeart (H := tL.heart.FullSubcategory)
  have hTL :
      Triangle.mk (ιL.map ((S.map FL).f)) (ιL.map ((S.map FL).g)) δ ∈ distTriang C := by
    simpa [FL] using hT
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := by
    simpa using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι tL) ((S.map FL).f) ((S.map FL).g) δ hTL
  have hCokL :
      IsColimit (CokernelCofork.ofπ ((S.map FL).g) (S.map FL).zero) := by
    simpa using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι tL) ((S.map FL).f) ((S.map FL).g) δ hTL
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExactL : (S.map FL).Exact := by
    exact ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKerL
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExactL (Fork.IsLimit.mono hKerL) (Cofork.IsColimit.epi hCokL)
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιR := tR.ιHeart (H := tR.heart.FullSubcategory)
  have hTR :
      Triangle.mk (ιR.map ((S.map FR).f)) (ιR.map ((S.map FR).g)) δ ∈ distTriang C := by
    simpa [FR] using hT
  have hKerR :
      IsLimit (KernelFork.ofι ((S.map FR).f) (S.map FR).zero) := by
    simpa using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι tR) ((S.map FR).f) ((S.map FR).g) δ hTR
  have hCokR :
      IsColimit (CokernelCofork.ofπ ((S.map FR).g) (S.map FR).zero) := by
    simpa using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι tR) ((S.map FR).f) ((S.map FR).g) δ hTR
  letI : (S.map FR).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FR))
  have hExactR : (S.map FR).Exact := by
    exact ShortComplex.exact_of_f_is_kernel (S := S.map FR) hKerR
  have hR : (S.map FR).ShortExact :=
    ShortComplex.ShortExact.mk' hExactR (Fork.IsLimit.mono hKerR) (Cofork.IsColimit.epi hCokR)
  exact Slicing.IntervalCat.strictMono_strictEpi_of_shortExact_toLeftRightHearts
    (C := C) (s := s) (a := a) (b := b) hL hR

/-- A short exact sequence in the left heart `P((a,a+1])` with vertices in `P((a,b))`
extends to a distinguished triangle in `C`. -/
theorem Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hL :
      (S.map (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1))).ShortExact) :
    ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧), Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : IsNormalMonoCategory t.heart.FullSubcategory := Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory t.heart.FullSubcategory := Abelian.toIsNormalEpiCategory
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  letI : Balanced t.heart.FullSubcategory := by infer_instance
  letI : Epi ((S.map FL).g) := hL.epi_g
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) ((S.map FL).g)
  have hKer :
      IsLimit (KernelFork.ofι i (show i ≫ (S.map FL).g = 0 by
        exact ι.map_injective (comp_distTriang_mor_zero₁₂ _ hT))) :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i ((S.map FL).g) δ hT
  have hLfIsKernel : IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := hL.fIsKernel
  let eKA : K ≅ FL.obj S.X₁ := IsLimit.conePointUniqueUpToIso hKer hLfIsKernel
  refine ⟨δ ≫ ((shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)), ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (ι.mapIso eKA.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · simp only [Iso.refl_hom, Functor.mapIso_hom, Iso.symm_hom, Triangle.mk_mor₁]
    have hcomp : ι.map eKA.inv ≫ ι.map i = S.f.hom := by
      simpa [Functor.map_comp] using
        congrArg (fun k => ι.map k)
        (IsLimit.conePointUniqueUpToIso_inv_comp hKer hLfIsKernel
          Limits.WalkingParallelPair.zero)
    change S.f.hom ≫ 𝟙 S.X₂.obj = ι.map eKA.inv ≫ t.ιHeart.map i
    simpa [FL] using hcomp.symm
  · have hmap : t.ιHeart.map ((S.map FL).g) = S.g.hom := rfl
    simp only [Iso.refl_hom, Triangle.mk_mor₂, Triangle.mk_obj₂, Triangle.mk_obj₃]
    rw [hmap]
    convert (rfl : S.g.hom = S.g.hom) using 1
    · exact Category.comp_id S.g.hom
    · exact Category.id_comp S.g.hom
  · simp only [Iso.refl_hom, Triangle.mk_mor₃, Functor.mapIso_hom, Iso.symm_hom]
    change (δ ≫ (shiftFunctor C (1 : ℤ)).map (ι.map eKA.hom)) ≫
        (shiftFunctor C (1 : ℤ)).map (ι.map eKA.inv) = 𝟙 _ ≫ δ
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp, ← ι.map_comp, eKA.hom_inv_id,
      ι.map_id, Functor.map_id]
    simp

/-- A strict short exact sequence in `P((a,b))` extends to a distinguished triangle in `C`. -/
theorem Slicing.IntervalCat.exists_distTriang_of_strictShortExact (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hS : StrictShortExact S) :
    ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧), Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := t.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have := hS.shortExact.mono_f
  have := hS.shortExact.epi_g
  let h := hS.shortExact.exact.condition.choose
  let eHi : kernel S.g ≅ h.left.K :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.left.hi
  have heHi : eHi.inv ≫ kernel.ι S.g = h.left.i := by
    simpa [KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) h.left.hi
        Limits.WalkingParallelPair.zero
  haveI : Epi h.left.f' := hS.shortExact.exact.epi_f' h.left
  have hFRMono : Mono (FR.map h.left.f') := by
    haveI : Mono (FR.map S.f) :=
      Slicing.IntervalCat.mono_toRightHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) S.f
        ⟨inferInstance, hS.strict_f⟩
    have hFRComp : FR.map h.left.f' ≫ FR.map h.left.i = FR.map S.f := by
      calc
        FR.map h.left.f' ≫ FR.map h.left.i = FR.map (h.left.f' ≫ h.left.i) := by
          rw [← FR.map_comp]
        _ = FR.map S.f := by
          simp [h.left.f'_i]
    haveI : Mono (FR.map h.left.f' ≫ FR.map h.left.i) := by
      rw [hFRComp]
      infer_instance
    exact mono_of_mono (FR.map h.left.f') (FR.map h.left.i)
  have hf'Strict : IsStrictMono h.left.f' :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) h.left.f'
  haveI : IsIso h.left.f' := hf'Strict.isIso
  let eK : S.X₁ ≅ kernel S.g := asIso h.left.f' ≪≫ eHi.symm
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    refine kernel.isoKernel S.g S.f eK ?_
    calc
      eK.hom ≫ kernel.ι S.g = h.left.f' ≫ h.left.i := by
          simp [eK, heHi, Category.assoc]
      _ = S.f := h.left.f'_i
  have hEpi : Epi (FL.map S.g) := by
    letI : Epi (FL.map S.g) :=
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) S.g
        ⟨inferInstance, hS.strict_g⟩
    infer_instance
  have hKer :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  have hExact : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKer
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
  exact Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) hL

/-- A distinguished triangle in `C` whose three vertices lie in `P((a,b))`
defines a strict short exact sequence in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictShortExact_of_distTriang (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    {δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C) :
    StrictShortExact S := by
  let tL := (s.phaseShift C a).toTStructure
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := tL.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιL := tL.ιHeart (H := tL.heart.FullSubcategory)
  have hTL :
      Triangle.mk (ιL.map ((S.map FL).f)) (ιL.map ((S.map FL).g)) δ ∈ distTriang C := by
    simpa [FL] using hT
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := by
    simpa using Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι tL) ((S.map FL).f) ((S.map FL).g) δ hTL
  have hKerMap :
      IsLimit (FL.mapCone (KernelFork.ofι S.f S.zero)) :=
    (isLimitMapConeForkEquiv' FL S.zero).symm hKerL
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimitOfReflects FL hKerMap
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ιR := tR.ιHeart (H := tR.heart.FullSubcategory)
  have hTR :
      Triangle.mk (ιR.map ((S.map FR).f)) (ιR.map ((S.map FR).g)) δ ∈ distTriang C := by
    simpa [FR] using hT
  have hCokR :
      IsColimit (CokernelCofork.ofπ ((S.map FR).g) (S.map FR).zero) := by
    simpa using Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (TStructure.heart_hι tR) ((S.map FR).f) ((S.map FR).g) δ hTR
  have hCokMap :
      IsColimit (FR.mapCocone (CokernelCofork.ofπ S.g S.zero)) :=
    (isColimitMapCoconeCoforkEquiv' FR S.zero).symm hCokR
  have hCok : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    isColimitOfReflects FR hCokMap
  obtain ⟨hf, hg⟩ := Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
    (C := C) (s := s) (a := a) (b := b) hT
  let eK' : kernel S.g ≅ S.X₁ :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hKer
  let eK : S.X₁ ≅ kernel S.g := eK'.symm
  have heK : eK.hom ≫ kernel.ι S.g = S.f := by
    simpa [KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) hKer
        Limits.WalkingParallelPair.zero
  have hLift : kernel.lift S.g S.f S.zero = eK.hom := by
    apply (cancel_mono (kernel.ι S.g)).1
    simpa [heK] using kernel.lift_ι S.g S.f S.zero
  have hKernelComp : kernel.ι S.g ≫ cokernel.π S.f = 0 := by
    have hιEq : kernel.ι S.g = eK.inv ≫ S.f := by
      apply (cancel_epi eK.hom).1
      simp [Category.assoc, heK]
    rw [hιEq, Category.assoc, cokernel.condition]
    simp
  let eQ : cokernel S.f ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hCok
  have heQ : cokernel.π S.f ≫ eQ.hom = S.g := by
    simpa [CokernelCofork.ofπ] using
      IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel S.f) hCok
        Limits.WalkingParallelPair.one
  have hDesc : cokernel.desc S.f S.g S.zero = eQ.hom := by
    apply (cancel_epi (cokernel.π S.f)).1
    simpa [heQ] using cokernel.π_desc S.f S.g S.zero
  let hLeft : S.LeftHomologyData := ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S
  let hRight : S.RightHomologyData := ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel S
  have hLeftZero : IsZero hLeft.H := by
    haveI : IsIso (kernel.lift S.g S.f S.zero) := by rw [hLift]; infer_instance
    haveI : Epi (kernel.lift S.g S.f S.zero) := by infer_instance
    dsimp [hLeft]
    simpa [hLift] using isZero_cokernel_of_epi (kernel.lift S.g S.f S.zero)
  have hRightZero : IsZero hRight.H := by
    haveI : IsIso (cokernel.desc S.f S.g S.zero) := by rw [hDesc]; infer_instance
    haveI : Mono (cokernel.desc S.f S.g S.zero) := by infer_instance
    dsimp [hRight]
    simpa [hDesc] using isZero_kernel_of_mono (cokernel.desc S.f S.g S.zero)
  have hComp : hLeft.i ≫ hRight.p = 0 := by
    dsimp [hLeft, hRight]
    exact hKernelComp
  have hExact : S.Exact := by
    let hData : S.HomologyData :=
      { left := hLeft
        right := hRight
        iso := IsZero.iso hLeftZero hRightZero
        comm := by
          have hπZero : hLeft.π = 0 := hLeftZero.eq_of_tgt _ _
          simpa [hπZero, Category.assoc] using hComp.symm }
    exact ⟨⟨hData, hLeftZero⟩⟩
  have hShortExact : S.ShortExact :=
    ShortComplex.ShortExact.mk' hExact hf.mono hg.epi
  refine
    { shortExact := hShortExact
      strict_f := hf.strict
      strict_g := hg.strict }

/-- A strict short exact sequence in a smaller interval remains strict in any larger thin
interval containing it. This is the inclusion-case transport used in the deformation
theorem's interval-independence step. -/
theorem Slicing.IntervalCat.strictShortExact_inclusion (s : Slicing C)
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)] [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂)
    {S : ShortComplex (s.IntervalCat C a₁ b₁)} (hS : StrictShortExact S) :
    StrictShortExact (S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)) := by
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := s) (a := a₁) (b := b₁) hS
  have hT' :
      Triangle.mk ((S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)).f.hom)
        ((S.map (Slicing.IntervalCat.inclusion (C := C) (s := s) ha hb)).g.hom) δ ∈ distTriang C := by
    simpa [Slicing.IntervalCat.inclusion] using hT
  exact Slicing.IntervalCat.strictShortExact_of_distTriang
    (C := C) (s := s) (a := a₂) (b := b₂) hT'

/-- Strict short exact sequences in `P((a,b))` are exactly the distinguished triangles
in `C` whose three vertices lie in `P((a,b))`. -/
theorem Slicing.IntervalCat.strictShortExact_iff_exists_distTriang (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)} :
    StrictShortExact S ↔
      ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧), Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  constructor
  · exact Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := s) (a := a) (b := b)
  · rintro ⟨δ, hT⟩
    exact Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := s) (a := a) (b := b) hT

/-- A strict short exact sequence in `P((a,b))` yields the expected `K₀` relation
in the ambient triangulated category. -/
theorem Slicing.IntervalCat.K0_of_strictShortExact (s : Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)] {S : ShortComplex (s.IntervalCat C a b)}
    (hS : StrictShortExact S) :
    K₀.of C S.X₂.obj = K₀.of C S.X₁.obj + K₀.of C S.X₃.obj := by
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := s) (a := a) (b := b) hS
  simpa using K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT

/-- Append a semistable strict quotient in `P((a,b))` to an HN filtration of the
kernel. This packages `appendFactor` with the strict short exact sequence to triangle
bridge for interval categories. -/
noncomputable def HNFiltration.appendStrictFactor {P : ℝ → ObjectProperty C}
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {S : ShortComplex (s.IntervalCat C a b)}
    (G : HNFiltration C P S.X₁.obj)
    (hS : StrictShortExact S) (ψ : ℝ) (hψ : P ψ S.X₃.obj)
    (hψ_lt : ∀ j : Fin G.n, ψ < G.φ j) :
    HNFiltration C P S.X₂.obj := by
  let hδ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := s) (a := a) (b := b) hS
  let δ := Classical.choose hδ
  have hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := Classical.choose_spec hδ
  exact G.appendFactor C (Triangle.mk S.f.hom S.g.hom δ) hT
    (Iso.refl _) (Iso.refl _) ψ hψ hψ_lt

end Preabelian

/-! ### Skewed stability functions (Definition 4.4) -/

/-- A *skewed stability function* on a thin subcategory `P((a, b))` with `b - a ≤ 1`.
This is a group homomorphism `W : K₀ C →+ ℂ` together with a real parameter `α ∈ (a, b)`
such that for every nonzero semistable object `E` of phase `φ ∈ (a, b)`, `W([E]) ≠ 0`.

In the deformation theorem, `W` is a perturbation of the central charge `Z` of a
stability condition, and `α` is chosen so that `W`-phases are well-defined in
`(α - 1/2, α + 1/2)` for objects in `P((a, b))`. -/
structure SkewedStabilityFunction (s : Slicing C) (a b : ℝ) where
  /-- The group homomorphism (typically a perturbation of the central charge). -/
  W : K₀ C →+ ℂ
  /-- The skewing parameter, lying in the interval `(a, b)`. -/
  α : ℝ
  /-- The skewing parameter lies in the interval. -/
  hα_mem : a < α ∧ α < b
  /-- For every nonzero semistable object of phase `φ ∈ (a, b)`, the central charge
  `W([E])` is nonzero. -/
  nonzero : ∀ (E : C) (φ : ℝ), a < φ → φ < b →
    (s.P φ) E → ¬IsZero E → W (K₀.of C E) ≠ 0

variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The central charge of a `SkewedStabilityFunction` is additive on strict short exact
sequences in the thin interval category. -/
theorem SkewedStabilityFunction.strict_additive {s : Slicing C}
    (ssf : SkewedStabilityFunction C s a b)
    {S : ShortComplex (s.IntervalCat C a b)} (hS : StrictShortExact S) :
    ssf.W (K₀.of C S.X₂.obj) = ssf.W (K₀.of C S.X₁.obj) + ssf.W (K₀.of C S.X₃.obj) := by
  rw [Slicing.IntervalCat.K0_of_strictShortExact (C := C) (s := s) (a := a) (b := b) hS,
    map_add]

end CategoryTheory.Triangulated
