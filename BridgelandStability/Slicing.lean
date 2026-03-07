/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.PostnikovTower
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Data.Real.Basic

/-!
# Bridgeland Slicings on Triangulated Categories

We define slicings, Harder-Narasimhan filtrations, and local finiteness conditions
following Bridgeland's "Stability conditions on triangulated categories" (2007).

## Main definitions

* `CategoryTheory.Triangulated.HNFiltration`: Harder-Narasimhan filtration data, built
  as a `PostnikovTower` equipped with phases on the factors
* `CategoryTheory.Triangulated.Slicing`: a slicing of a triangulated category, using
  `ObjectProperty C` for each phase slice
* `CategoryTheory.Triangulated.Slicing.intervalProp`: the interval subcategory predicate
* `CategoryTheory.Triangulated.Slicing.IsLocallyFinite`: the local finiteness condition

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

section Slicing

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A Harder-Narasimhan (HN) filtration of an object `E` with respect to a phase
predicate `P`. This extends a `PostnikovTower` with phase data: each factor is
semistable with a given phase, and the phases are strictly decreasing. -/
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C) extends PostnikovTower C E where
  /-- The phases of the semistable factors, in strictly decreasing order. -/
  φ : Fin n → ℝ
  /-- The phases are strictly decreasing (higher phase factors appear first). -/
  hφ : StrictAnti φ
  /-- Each factor is semistable of the given phase. -/
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j)

/-- A slicing of a pretriangulated category `C`, as defined in
Bridgeland (2007), Definition 5.1. A slicing assigns to each real number `φ`
a full subcategory of semistable objects `P(φ)` (as an `ObjectProperty`),
subject to shift, Hom-vanishing, and Harder-Narasimhan existence axioms.

Each `P(φ)` is an `ObjectProperty C`, enabling use of the `ObjectProperty` API
(e.g. `FullSubcategory`, shift stability, closure properties). -/
structure Slicing where
  /-- For each phase `φ ∈ ℝ`, the property of semistable objects of phase `φ`. -/
  P : ℝ → ObjectProperty C
  /-- Each phase slice is closed under isomorphisms. -/
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  /-- The zero object satisfies every phase predicate. -/
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)
  /-- Shifting by `[1]` increases the phase by 1, and conversely. -/
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  /-- Morphisms from higher-phase to lower-phase nonzero semistable objects vanish. -/
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0
  /-- Every object has a Harder-Narasimhan filtration. -/
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)

attribute [instance] Slicing.closedUnderIso

/-- Zero objects satisfy every phase predicate. -/
lemma Slicing.zero_mem' (s : Slicing C) (φ : ℝ) (X : C) (hX : IsZero X) : (s.P φ) X :=
  ObjectProperty.prop_of_iso _ ((isZero_zero C).iso hX) (s.zero_mem φ)

/-- Shifting by `[1]` increases the phase by 1. -/
lemma Slicing.shift (s : Slicing C) (φ : ℝ) (X : C) (h : (s.P φ) X) :
    (s.P (φ + 1)) (X⟦(1 : ℤ)⟧) :=
  (s.shift_iff φ X).mp h

/-- The inverse of the shift axiom. -/
lemma Slicing.shift_inv (s : Slicing C) (φ : ℝ) (X : C)
    (h : (s.P (φ + 1)) (X⟦(1 : ℤ)⟧)) : (s.P φ) X :=
  (s.shift_iff φ X).mpr h

instance (s : Slicing C) (φ : ℝ) : (s.P φ).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, s.zero_mem φ⟩

/-! ### Phase bounds and interval subcategories -/

/-- The highest phase `φ⁺` of a nonzero object, extracted from a given HN filtration. -/
def HNFiltration.phiPlus {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) : ℝ :=
  F.φ ⟨0, h⟩

/-- The lowest phase `φ⁻` of a nonzero object, extracted from a given HN filtration. -/
def HNFiltration.phiMinus {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) : ℝ :=
  F.φ ⟨F.n - 1, by omega⟩

/-- The interval subcategory predicate `P((a,b))`: an object `E` belongs to the
interval subcategory if it is zero or all phases in its HN filtration lie in `(a,b)`. -/
def Slicing.intervalProp (s : Slicing C) (a b : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E), ∀ i, a < F.φ i ∧ F.φ i < b

/-- A slicing is locally finite if there exists `η > 0` such that for every `t`,
every object in the interval subcategory `P((t-η, t+η))` has well-founded
subobject lattice (both ascending and descending chains stabilize).

This uses `WellFoundedLT` and `WellFoundedGT` on `Subobject E`, matching the
pattern used by Mathlib's `IsArtinianObject` and `IsNoetherianObject`. -/
def Slicing.IsLocallyFinite (s : Slicing C) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ,
    ∀ (E : C), s.intervalProp C (t - η) (t + η) E →
      WellFoundedLT (Subobject E) ∧ WellFoundedGT (Subobject E)

/-! ### Phase bound properties -/

/-- The highest phase is at least the lowest phase. -/
lemma HNFiltration.phiMinus_le_phiPlus {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) :
    F.phiMinus C h ≤ F.phiPlus C h := by
  simp only [HNFiltration.phiMinus, HNFiltration.phiPlus]
  exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))

/-- All phases lie between phiMinus and phiPlus. -/
lemma HNFiltration.phase_mem_range {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) (i : Fin F.n) :
    F.phiMinus C h ≤ F.φ i ∧ F.φ i ≤ F.phiPlus C h := by
  constructor
  · exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
  · exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))

/-! ### Subcategory predicates from slicings -/

/-- The subcategory predicate `P(≤ t)`: an object `E` satisfies this if it is zero or
all phases in some HN filtration of `E` are `≤ t`. -/
def Slicing.leProp (s : Slicing C) (t : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E) (h : 0 < F.n),
    F.phiPlus C h ≤ t

/-- The subcategory predicate `P(> t)`: an object `E` satisfies this if it is zero or
all phases in some HN filtration of `E` are `> t`. -/
def Slicing.gtProp (s : Slicing C) (t : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E) (h : 0 < F.n),
    t < F.phiMinus C h

end Slicing

end CategoryTheory.Triangulated
