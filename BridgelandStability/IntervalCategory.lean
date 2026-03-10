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
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.Data.Complex.Basic

/-!
# Interval Subcategories of Slicings

Given a slicing `s` on a pretriangulated category `C` and an open interval `(a, b) ⊂ ℝ`,
we define the interval subcategory `P((a, b))` as the full subcategory of `C` on objects
whose HN phases all lie in `(a, b)`.

These interval subcategories play a central role in Bridgeland's deformation theorem (§7):
when `b - a` is small enough (relative to the local finiteness parameter), objects in
`P((a,b))` have well-founded subobject lattices, enabling HN filtration arguments within
thin subcategories.

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

/-! ### Finite length in thin intervals -/

/-- **Finite subobject lattice in thin intervals**. For any object `E` in `P((a, b))` with
`b - a ≤ 2η`, if all objects in `η`-intervals have finite subobject lattices, then
`E` does too. -/
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

/-- Simplified version: if `s` is locally finite, the finiteness parameter can be
extracted automatically. -/
theorem Slicing.intervalFiniteLength' (s : Slicing C) (hLF : s.IsLocallyFinite C)
    {a b : ℝ} {E : C} (hI : s.intervalProp C a b E) :
    ∃ (η : ℝ), 0 < η ∧ (b - a ≤ 2 * η →
      Finite (Subobject E)) := by
  obtain ⟨w, hw, hlf⟩ := hLF.intervalFinite
  exact ⟨w, hw, fun hwidth ↦ s.intervalFiniteLength C hI hwidth hlf⟩

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

/-- The interval property is closed under isomorphisms. -/
instance Slicing.intervalProp_closedUnderIso (s : Slicing C) (a b : ℝ) :
    (s.intervalProp C a b).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    rcases hE with hZ | ⟨F, hF⟩
    · exact Or.inl (IsZero.of_iso hZ e.symm)
    · exact Or.inr ⟨F.ofIso C e, hF⟩

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
  have hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
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

noncomputable instance Slicing.intervalCat_hasBinaryBiproducts (s : Slicing C) :
    HasBinaryBiproducts (s.IntervalCat C a b) :=
  HasBinaryBiproducts.of_hasBinaryProducts

noncomputable instance Slicing.intervalCat_hasEqualizers (s : Slicing C) :
    HasEqualizers (s.IntervalCat C a b) :=
  Preadditive.hasEqualizers_of_hasKernels

noncomputable instance Slicing.intervalCat_hasCoequalizers (s : Slicing C) :
    HasCoequalizers (s.IntervalCat C a b) :=
  Preadditive.hasCoequalizers_of_hasCokernels

noncomputable instance Slicing.intervalCat_hasPullbacks (s : Slicing C) :
    HasPullbacks (s.IntervalCat C a b) := by
  exact Limits.hasPullbacks_of_hasBinaryProducts_of_hasEqualizers _

noncomputable instance Slicing.intervalCat_hasPushouts (s : Slicing C) :
    HasPushouts (s.IntervalCat C a b) := by
  exact Limits.hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers _

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

end CategoryTheory.Triangulated
