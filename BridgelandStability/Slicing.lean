/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.PostnikovTower
import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Data.Real.Basic

/-!
# Bridgeland Slicings on Triangulated Categories

We define slicings, Harder-Narasimhan filtrations, quasi-abelian categories, and local
finiteness conditions following Bridgeland's "Stability conditions on triangulated
categories" (2007).

## Main definitions

* `CategoryTheory.Triangulated.QuasiAbelian`: a quasi-abelian category, using Mathlib's
  `NormalMono`/`NormalEpi` instead of ad-hoc strict morphism definitions
* `CategoryTheory.Triangulated.HNFiltration`: Harder-Narasimhan filtration data, built
  as a `PostnikovTower` equipped with phases on the factors
* `CategoryTheory.Triangulated.Slicing`: a slicing of a triangulated category
* `CategoryTheory.Triangulated.Slicing.intervalProp`: the interval subcategory predicate
* `CategoryTheory.Triangulated.Slicing.IsLocallyFinite`: the local finiteness condition,
  using `WellFoundedLT`/`WellFoundedGT` on `Subobject` (matching Mathlib's
  `ArtinianObject`/`NoetherianObject` pattern)

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v v' u u'

namespace CategoryTheory.Triangulated

/-! ### Quasi-abelian categories -/

/-- A preadditive category with kernels, cokernels, pullbacks, and pushouts is
quasi-abelian if pullbacks of normal epimorphisms are normal epimorphisms and
pushouts of normal monomorphisms are normal monomorphisms.

This uses Mathlib's `NormalMono`/`NormalEpi` from
`CategoryTheory.Limits.Shapes.NormalMono.Basic`. -/
class QuasiAbelian (A : Type u') [Category.{v'} A] [Preadditive A]
    [HasKernels A] [HasCokernels A] [HasPullbacks A] [HasPushouts A] : Prop where
  /-- The pullback of a normal epimorphism along any morphism is a normal epimorphism. -/
  pullback_normalEpi : ∀ {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z),
    Nonempty (NormalEpi g) → Nonempty (NormalEpi (pullback.fst f g))
  /-- The pushout of a normal monomorphism along any morphism is a normal monomorphism. -/
  pushout_normalMono : ∀ {X Y Z : A} (f : Z ⟶ X) (g : Z ⟶ Y),
    Nonempty (NormalMono f) → Nonempty (NormalMono (pushout.inr f g))

/-! ### HN filtrations and slicings -/

section Slicing

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A Harder-Narasimhan (HN) filtration of an object `E` with respect to a phase
predicate `P`. This extends a `PostnikovTower` with phase data: each factor is
semistable with a given phase, and the phases are strictly decreasing. -/
structure HNFiltration (P : ℝ → C → Prop) (E : C) extends PostnikovTower C E where
  /-- The phases of the semistable factors, in strictly decreasing order. -/
  φ : Fin n → ℝ
  /-- The phases are strictly decreasing (higher phase factors appear first). -/
  hφ : StrictAnti φ
  /-- Each factor is semistable of the given phase. -/
  semistable : ∀ j, P (φ j) (toPostnikovTower.factor j)

/-- A slicing of a pretriangulated category `C`, as defined in
Bridgeland (2007), Definition 5.1. A slicing assigns to each real number `φ`
a class of semistable objects `P(φ)`, subject to shift, Hom-vanishing,
and Harder-Narasimhan existence axioms. -/
structure Slicing where
  /-- For each phase `φ ∈ ℝ`, the predicate of semistable objects of phase `φ`. -/
  P : ℝ → C → Prop
  /-- The semistable predicate is closed under isomorphism. -/
  closedUnderIso : ∀ (φ : ℝ) {X Y : C}, P φ X → (X ≅ Y) → P φ Y
  /-- Shifting by `[1]` increases the phase by 1. -/
  shift : ∀ (φ : ℝ) (X : C), P φ X → P (φ + 1) (X⟦(1 : ℤ)⟧)
  /-- Inverse of the shift axiom. -/
  shift_inv : ∀ (φ : ℝ) (X : C), P (φ + 1) (X⟦(1 : ℤ)⟧) → P φ X
  /-- Morphisms from higher-phase to lower-phase semistable objects vanish. -/
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ (f : A ⟶ B), f = 0
  /-- Every object has a Harder-Narasimhan filtration. -/
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)

/-! ### Phase bounds and interval subcategories -/

/-- The highest phase `φ⁺` of a nonzero object, extracted from a given HN filtration. -/
def HNFiltration.phiPlus {P : ℝ → C → Prop} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) : ℝ :=
  F.φ ⟨0, h⟩

/-- The lowest phase `φ⁻` of a nonzero object, extracted from a given HN filtration. -/
def HNFiltration.phiMinus {P : ℝ → C → Prop} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) : ℝ :=
  F.φ ⟨F.n - 1, by omega⟩

/-- The interval subcategory predicate `P((a,b))`: an object `E` belongs to the
interval subcategory if it is zero or all phases in its HN filtration lie in `(a,b)`. -/
def Slicing.intervalProp (s : Slicing C) (a b : ℝ) : C → Prop :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E), ∀ i, a < F.φ i ∧ F.φ i < b

/-- A slicing is locally finite if there exists `η > 0` such that for every `t`,
every object in the interval subcategory `P((t-η, t+η))` has well-founded
subobject lattice (both ascending and descending chains stabilize).

This uses `WellFoundedLT` and `WellFoundedGT` on `Subobject E`, matching the
pattern used by Mathlib's `ArtinianObject` and `NoetherianObject`. -/
def Slicing.IsLocallyFinite (s : Slicing C) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ,
    ∀ (E : C), s.intervalProp C (t - η) (t + η) E →
      WellFoundedLT (Subobject E) ∧ WellFoundedGT (Subobject E)

end Slicing

end CategoryTheory.Triangulated
