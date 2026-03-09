/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Slicing
import Mathlib.CategoryTheory.Triangulated.GrothendieckGroup
import Mathlib.CategoryTheory.Triangulated.Strict
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
  obtain ⟨η, hη, hlf⟩ := hLF
  exact ⟨η, hη, fun hwidth ↦ s.intervalFiniteLength C hI hwidth hlf⟩

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
