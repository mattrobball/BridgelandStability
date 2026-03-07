/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.PostnikovTower
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

/-- Each phase slice of a slicing contains the zero object. -/
instance (s : Slicing C) (φ : ℝ) : (s.P φ).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, s.zero_mem φ⟩

/-- Forward shift by a natural number: if `(P φ) X` then `(P (φ + n)) (X⟦n⟧)`. -/
private lemma Slicing.shift_nat (s : Slicing C) (φ : ℝ) (X : C) (n : ℕ) :
    (s.P φ) X → (s.P (φ + (n : ℝ))) (X⟦(n : ℤ)⟧) := by
  induction n with
  | zero =>
    intro h
    simp only [Nat.cast_zero, add_zero]
    exact (s.P φ).prop_of_iso ((shiftFunctorZero C ℤ).app X).symm h
  | succ n ih =>
    intro h
    have h1 := (s.shift_iff (φ + ↑n) ((shiftFunctor C (↑n : ℤ)).obj X)).mp (ih h)
    have hc : φ + ↑n + 1 = φ + (↑(n + 1) : ℝ) := by push_cast; ring
    rw [hc] at h1
    exact (s.P _).prop_of_iso
      ((shiftFunctorAdd' C (↑n : ℤ) 1 ((↑n : ℤ) + 1) (by omega)).app X).symm h1

/-- Backward shift by a natural number: if `(P (φ + n)) (X⟦n⟧)` then `(P φ) X`. -/
private lemma Slicing.unshift_nat (s : Slicing C) (φ : ℝ) (X : C) (n : ℕ) :
    (s.P (φ + (n : ℝ))) (X⟦(n : ℤ)⟧) → (s.P φ) X := by
  induction n with
  | zero =>
    intro h
    simp only [Nat.cast_zero, add_zero] at h
    exact (s.P φ).prop_of_iso ((shiftFunctorZero C ℤ).app X) h
  | succ n ih =>
    intro h
    apply ih
    have hc : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
    rw [hc] at h
    have h1 := (s.P _).prop_of_iso
      ((shiftFunctorAdd' C (↑n : ℤ) 1 ((↑n : ℤ) + 1) (by omega)).app X) h
    rw [← add_assoc] at h1
    exact (s.shift_iff (φ + ↑n) ((shiftFunctor C (↑n : ℤ)).obj X)).mpr h1

/-- Generalized shift: shifting by `n : ℤ` adds `n` to the phase. -/
lemma Slicing.shift_int (s : Slicing C) (φ : ℝ) (X : C) (n : ℤ) :
    (s.P φ) X ↔ (s.P (φ + ↑n)) (X⟦n⟧) := by
  cases n with
  | ofNat m => exact ⟨s.shift_nat C φ X m, s.unshift_nat C φ X m⟩
  | negSucc m =>
    -- shiftFunctorAdd' gives X⟦0⟧ ≅ X⟦negSucc m⟧⟦↑(m+1)⟧
    have addIso :=
      (shiftFunctorAdd' C (Int.negSucc m) ((m + 1 : ℕ) : ℤ) 0 (by omega)).app X
    -- shiftFunctorZero gives X⟦0⟧ ≅ X
    have zeroIso := (shiftFunctorZero C ℤ).app X
    constructor
    · intro h
      -- Transfer: X → X⟦0⟧ → X⟦negSucc m⟧⟦↑(m+1)⟧, then unshift by (m+1)
      have h0 := (s.P φ).prop_of_iso zeroIso.symm h
      have h1 := (s.P _).prop_of_iso addIso h0
      have phase_eq : φ = φ + ↑(Int.negSucc m) + ((m + 1 : ℕ) : ℝ) := by
        simp [Int.negSucc_eq]; ring
      rw [phase_eq] at h1
      exact s.unshift_nat C _ _ (m + 1) h1
    · intro h
      -- Shift by (m+1), then transfer: X⟦negSucc m⟧⟦↑(m+1)⟧ → X⟦0⟧ → X
      have h1 := s.shift_nat C _ _ (m + 1) h
      have phase_eq : φ + ↑(Int.negSucc m) + ((m + 1 : ℕ) : ℝ) = φ := by
        simp [Int.negSucc_eq]; ring
      rw [phase_eq] at h1
      have h2 := (s.P φ).prop_of_iso addIso.symm h1
      exact (s.P φ).prop_of_iso zeroIso h2

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

/-! ### Properties of subcategory predicates -/

/-- Zero objects are in `P(≤ t)` for all `t`. -/
lemma Slicing.leProp_zero (s : Slicing C) (t : ℝ) :
    s.leProp C t (0 : C) :=
  Or.inl (isZero_zero C)

/-- Zero objects are in `P(> t)` for all `t`. -/
lemma Slicing.gtProp_zero (s : Slicing C) (t : ℝ) :
    s.gtProp C t (0 : C) :=
  Or.inl (isZero_zero C)

/-- `P(≤ t₁) ≤ P(≤ t₂)` when `t₁ ≤ t₂`. -/
lemma Slicing.leProp_mono (s : Slicing C) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    s.leProp C t₁ ≤ s.leProp C t₂ := by
  intro E hE
  rcases hE with hZ | ⟨F, hF, hle⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨F, hF, le_trans hle h⟩

/-- `P(> t₂) ≤ P(> t₁)` when `t₁ ≤ t₂`. -/
lemma Slicing.gtProp_anti (s : Slicing C) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    s.gtProp C t₂ ≤ s.gtProp C t₁ := by
  intro E hE
  rcases hE with hZ | ⟨F, hF, hgt⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨F, hF, lt_of_le_of_lt h hgt⟩

/-! ### Hom-vanishing for HN-filtered objects

These lemmas extend the pointwise hom-vanishing axiom of a slicing to
Harder-Narasimhan-filtered objects, using the coYoneda and Yoneda exact sequences
from the distinguished triangles in the Postnikov tower.
-/

/-- Auxiliary: any morphism from a semistable object of phase `ψ` to the `k`-th chain
object of an HN filtration (with all phases strictly less than `ψ`) is zero.
Proved by induction on `k`, using the coYoneda exact sequence. -/
private lemma chain_hom_eq_zero_of_gt (s : Slicing C) {A E : C} {ψ : ℝ}
    (hA : (s.P ψ) A) (F : HNFiltration C s.P E) (hlt : ∀ i, F.φ i < ψ) :
    ∀ (k : ℕ) (hk : k < F.n + 1) (f : A ⟶ F.chain.obj ⟨k, hk⟩), f = 0 := by
  intro k
  induction k with
  | zero =>
    intro hk f
    exact (F.base_isZero : IsZero F.chain.left).eq_of_tgt f 0
  | succ k ih =>
    intro hk f
    have hkn : k < F.n := by omega
    let T := F.triangle ⟨k, hkn⟩
    let e₁ := Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)
    let e₂ := Classical.choice (F.triangle_obj₂ ⟨k, hkn⟩)
    have hcomp : (f ≫ e₂.inv) ≫ T.mor₂ = 0 :=
      s.hom_vanishing ψ (F.φ ⟨k, hkn⟩) A T.obj₃
        (hlt ⟨k, hkn⟩) hA (F.semistable ⟨k, hkn⟩) _
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T
      (F.triangle_dist ⟨k, hkn⟩) (f ≫ e₂.inv) hcomp
    have hg0 : g ≫ e₁.hom = 0 := ih (by omega) (g ≫ e₁.hom)
    have hg_eq : g = 0 := by
      have : g = (g ≫ e₁.hom) ≫ e₁.inv := by
        rw [Category.assoc, e₁.hom_inv_id, Category.comp_id]
      rw [this, hg0, zero_comp]
    have hfe : f ≫ e₂.inv = 0 := by rw [hg, hg_eq, zero_comp]
    have : f = (f ≫ e₂.inv) ≫ e₂.hom := by
      rw [Category.assoc, e₂.inv_hom_id, Category.comp_id]
    rw [this, hfe, zero_comp]

/-- A morphism from a semistable object of phase `ψ` to an HN-filtered object whose
phases are all strictly less than `ψ` is zero. -/
lemma Slicing.hom_eq_zero_of_gt_phases (s : Slicing C) {A E : C} {ψ : ℝ}
    (hA : (s.P ψ) A) (F : HNFiltration C s.P E) (hlt : ∀ i, F.φ i < ψ)
    (f : A ⟶ E) : f = 0 := by
  let eE := Classical.choice F.top_iso
  have h1 : f ≫ eE.inv = 0 :=
    chain_hom_eq_zero_of_gt C s hA F hlt F.n (by omega) _
  have : f = (f ≫ eE.inv) ≫ eE.hom := by
    rw [Category.assoc, eE.inv_hom_id, Category.comp_id]
  rw [this, h1, zero_comp]

/-- Auxiliary: any morphism from the `k`-th chain object of an HN filtration (with all
phases strictly greater than those of another filtration) to the target of the second
filtration is zero. Uses the Yoneda exact sequence and `hom_eq_zero_of_gt_phases`. -/
private lemma chain_hom_eq_zero_gap (s : Slicing C) {X Y : C}
    (Fx : HNFiltration C s.P X) (Fy : HNFiltration C s.P Y)
    (hgap : ∀ i j, Fy.φ j < Fx.φ i) :
    ∀ (k : ℕ) (hk : k < Fx.n + 1) (f : Fx.chain.obj ⟨k, hk⟩ ⟶ Y), f = 0 := by
  intro k
  induction k with
  | zero =>
    intro hk f
    exact (Fx.base_isZero : IsZero Fx.chain.left).eq_of_src f 0
  | succ k ih =>
    intro hk f
    have hkn : k < Fx.n := by omega
    let T := Fx.triangle ⟨k, hkn⟩
    let e₁ := Classical.choice (Fx.triangle_obj₁ ⟨k, hkn⟩)
    let e₂ := Classical.choice (Fx.triangle_obj₂ ⟨k, hkn⟩)
    -- T.mor₁ ≫ (e₂.hom ≫ f) : T.obj₁ → Y is zero via e₁ and IH
    have hmor1 : T.mor₁ ≫ (e₂.hom ≫ f) = 0 := by
      have h1 : e₁.inv ≫ (T.mor₁ ≫ (e₂.hom ≫ f)) = 0 := by
        simp only [← Category.assoc]; exact ih (by omega) _
      have h2 : e₁.hom ≫ (e₁.inv ≫ (T.mor₁ ≫ (e₂.hom ≫ f))) =
          T.mor₁ ≫ (e₂.hom ≫ f) := by
        rw [← Category.assoc, e₁.hom_inv_id, Category.id_comp]
      rw [← h2, h1, comp_zero]
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T
      (Fx.triangle_dist ⟨k, hkn⟩) (e₂.hom ≫ f) hmor1
    -- g : T.obj₃ → Y, factor ∈ P(φ_k), all Fy phases < φ_k
    have hg_eq : g = 0 :=
      s.hom_eq_zero_of_gt_phases C (Fx.semistable ⟨k, hkn⟩) Fy
        (fun j ↦ hgap ⟨k, hkn⟩ j) g
    have hef : e₂.hom ≫ f = 0 := by rw [hg, hg_eq, comp_zero]
    have : f = e₂.inv ≫ (e₂.hom ≫ f) := by
      rw [← Category.assoc, e₂.inv_hom_id, Category.id_comp]
    rw [this, hef, comp_zero]

/-- Morphisms between HN-filtered objects with a phase gap are zero: if every phase
of `Fx` is strictly greater than every phase of `Fy`, then `Hom(X, Y) = 0`. -/
lemma Slicing.hom_eq_zero_of_phase_gap (s : Slicing C) {X Y : C}
    (Fx : HNFiltration C s.P X) (Fy : HNFiltration C s.P Y)
    (hgap : ∀ i j, Fy.φ j < Fx.φ i) (f : X ⟶ Y) : f = 0 := by
  let eX := Classical.choice Fx.top_iso
  have h1 : eX.hom ≫ f = 0 :=
    chain_hom_eq_zero_gap C s Fx Fy hgap Fx.n (by omega) _
  have : f = eX.inv ≫ (eX.hom ≫ f) := by
    rw [← Category.assoc, eX.inv_hom_id, Category.id_comp]
  rw [this, h1, comp_zero]

/-- Auxiliary: any morphism from the `k`-th chain object of an HN filtration to a
semistable object of phase `ψ` (with all HN phases strictly greater than `ψ`) is zero.
Proved by induction on `k`, using the Yoneda exact sequence. -/
private lemma chain_hom_eq_zero_of_lt (s : Slicing C) {B E : C} {ψ : ℝ}
    (hB : (s.P ψ) B) (F : HNFiltration C s.P E) (hgt : ∀ i, ψ < F.φ i) :
    ∀ (k : ℕ) (hk : k < F.n + 1) (f : F.chain.obj ⟨k, hk⟩ ⟶ B), f = 0 := by
  intro k
  induction k with
  | zero =>
    intro hk f
    exact (F.base_isZero : IsZero F.chain.left).eq_of_src f 0
  | succ k ih =>
    intro hk f
    have hkn : k < F.n := by omega
    let T := F.triangle ⟨k, hkn⟩
    let e₁ := Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)
    let e₂ := Classical.choice (F.triangle_obj₂ ⟨k, hkn⟩)
    -- T.mor₁ ≫ (e₂.hom ≫ f) : T.obj₁ → B via e₁ and IH
    have hmor1 : T.mor₁ ≫ (e₂.hom ≫ f) = 0 := by
      have h1 : e₁.inv ≫ (T.mor₁ ≫ (e₂.hom ≫ f)) = 0 := by
        simp only [← Category.assoc]; exact ih (by omega) _
      have h2 : e₁.hom ≫ (e₁.inv ≫ (T.mor₁ ≫ (e₂.hom ≫ f))) =
          T.mor₁ ≫ (e₂.hom ≫ f) := by
        rw [← Category.assoc, e₁.hom_inv_id, Category.id_comp]
      rw [← h2, h1, comp_zero]
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T
      (F.triangle_dist ⟨k, hkn⟩) (e₂.hom ≫ f) hmor1
    -- g : factor(k) → B, with factor(k) ∈ P(φ(k)) and φ(k) > ψ
    have hg_eq : g = 0 :=
      s.hom_vanishing (F.φ ⟨k, hkn⟩) ψ T.obj₃ B (hgt ⟨k, hkn⟩) (F.semistable ⟨k, hkn⟩) hB g
    have hef : e₂.hom ≫ f = 0 := by rw [hg, hg_eq, comp_zero]
    have : f = e₂.inv ≫ (e₂.hom ≫ f) := by
      rw [← Category.assoc, e₂.inv_hom_id, Category.id_comp]
    rw [this, hef, comp_zero]

/-- A morphism from an HN-filtered object whose phases are all strictly greater than
`ψ` to a semistable object of phase `ψ` is zero. -/
lemma Slicing.hom_eq_zero_of_lt_phases (s : Slicing C) {B E : C} {ψ : ℝ}
    (hB : (s.P ψ) B) (F : HNFiltration C s.P E) (hgt : ∀ i, ψ < F.φ i)
    (f : E ⟶ B) : f = 0 := by
  let eE := Classical.choice F.top_iso
  have h1 : eE.hom ≫ f = 0 :=
    chain_hom_eq_zero_of_lt C s hB F hgt F.n (by omega) _
  have : f = eE.inv ≫ (eE.hom ≫ f) := by
    rw [← Category.assoc, eE.inv_hom_id, Category.id_comp]
  rw [this, h1, comp_zero]

/-! ### Prefix HN filtrations

Extracting the first `k` factors from an HN filtration gives an HN filtration of the
`k`-th chain object. This is used for the t-structure decomposition.
-/

/-- Extract the first `k` factors from an HN filtration, giving a filtration
of the `k`-th chain object with phases `φ₀ > ⋯ > φ_{k-1}`. -/
def HNFiltration.prefix {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) :
    HNFiltration C P (F.chain.obj ⟨k, by omega⟩) :=
  { n := k
    chain := ComposableArrows.mkOfObjOfMapSucc
      (fun i : Fin (k + 1) ↦ F.chain.obj ⟨i.val, by omega⟩)
      (fun i : Fin k ↦ F.chain.map' i.val (i.val + 1) (by omega) (by omega))
    triangle := fun j ↦ F.triangle ⟨j.val, by omega⟩
    triangle_dist := fun j ↦ F.triangle_dist ⟨j.val, by omega⟩
    triangle_obj₁ := fun j ↦ F.triangle_obj₁ ⟨j.val, by omega⟩
    triangle_obj₂ := fun j ↦ F.triangle_obj₂ ⟨j.val, by omega⟩
    base_isZero := F.base_isZero
    top_iso := ⟨Iso.refl _⟩
    zero_isZero := fun h ↦ absurd h (by omega)
    φ := fun j ↦ F.φ ⟨j.val, by omega⟩
    hφ := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ (hab : a < b)
      exact F.hφ (show (⟨a, by omega⟩ : Fin F.n) < ⟨b, by omega⟩ from hab)
    semistable := fun j ↦ F.semistable ⟨j.val, by omega⟩ }

/-- The prefix filtration has all the original phases up to index `k`. -/
@[simp]
lemma HNFiltration.prefix_φ {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k)
    (j : Fin k) : (F.prefix C k hk hk0).φ j = F.φ ⟨j.val, by omega⟩ := rfl

/-- The prefix of an HN filtration with phases > t gives a filtration with all phases > t. -/
lemma HNFiltration.prefix_phiMinus_gt {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, t < F.φ ⟨j.val, by omega⟩) :
    t < (F.prefix C k hk hk0).phiMinus C hk0 := by
  simp only [HNFiltration.phiMinus, HNFiltration.prefix_φ]
  exact ht ⟨k - 1, by omega⟩

/-- The chain object at the split point satisfies `gtProp t` if all phases before
the split are > t. -/
lemma HNFiltration.chain_obj_gtProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, t < F.φ ⟨j.val, by omega⟩) :
    s.gtProp C t (F.chain.obj ⟨k, by omega⟩) :=
  Or.inr ⟨F.prefix C k hk hk0, hk0, F.prefix_phiMinus_gt C k hk hk0 t ht⟩

/-- The chain object at the split point satisfies `leProp t` if all phases before
the split are ≤ t. -/
lemma HNFiltration.chain_obj_leProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, F.φ ⟨j.val, by omega⟩ ≤ t) :
    s.leProp C t (F.chain.obj ⟨k, by omega⟩) := by
  refine Or.inr ⟨F.prefix C k hk hk0, hk0, ?_⟩
  simp only [HNFiltration.phiPlus, HNFiltration.prefix_φ]
  exact ht ⟨0, by omega⟩

/-- An HN-filtered object satisfies `gtProp t` if all its phases are > t. -/
lemma Slicing.gtProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ)
    (ht : ∀ j, t < F.φ j) (hn : 0 < F.n) :
    s.gtProp C t E := by
  refine Or.inr ⟨F, hn, ?_⟩
  simp only [HNFiltration.phiMinus]
  exact ht ⟨F.n - 1, by omega⟩

/-- An HN-filtered object satisfies `leProp t` if all its phases are ≤ t. -/
lemma Slicing.leProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ)
    (ht : ∀ j, F.φ j ≤ t) (hn : 0 < F.n) :
    s.leProp C t E := by
  refine Or.inr ⟨F, hn, ?_⟩
  simp only [HNFiltration.phiPlus]
  exact ht ⟨0, hn⟩

/-! ### Extending HN filtrations by one factor

Given an HN filtration of `Y'` and a distinguished triangle `Y' → Z → F → Y'[1]`
where `F` is semistable of a phase strictly less than all existing phases, we
construct an HN filtration of `Z` with one additional factor.
-/

/-- Extend an HN filtration by appending one semistable factor via a distinguished
triangle. Given an HN filtration `G` of `Y'` and a distinguished triangle
`Y' → Z → F → Y'[1]` (where `F` is semistable of phase `ψ` strictly less than
all phases of `G`), produce an HN filtration of `Z` with the additional factor `F`. -/
def HNFiltration.appendFactor {P : ℝ → ObjectProperty C} {Y' Z : C}
    (G : HNFiltration C P Y')
    (T : Triangle C) (hT : T ∈ distTriang C)
    (eT₁ : T.obj₁ ≅ Y') (eT₂ : T.obj₂ ≅ Z)
    (ψ : ℝ) (hψ : (P ψ) T.obj₃)
    (hψ_lt : ∀ j : Fin G.n, ψ < G.φ j) :
    HNFiltration C P Z := by
  let objFn : Fin (G.n + 2) → C :=
    fun i ↦ if h : i.val ≤ G.n then G.chain.obj ⟨i.val, by omega⟩ else Z
  let lastMor : G.chain.obj (Fin.last G.n) ⟶ Z :=
    (Classical.choice G.top_iso).hom ≫ eT₁.inv ≫ T.mor₁ ≫ eT₂.hom
  have mapSuccFn : ∀ (i : Fin (G.n + 1)), objFn (Fin.castSucc i) ⟶ objFn (Fin.succ i) := by
    intro ⟨i, hi⟩
    simp only [objFn, Fin.castSucc_mk, Fin.succ_mk]
    by_cases h1 : i + 1 ≤ G.n
    · simp only [show i ≤ G.n from by omega, h1, dite_true]
      exact G.chain.map' i (i + 1) (by omega) (by omega)
    · simp only [show i ≤ G.n from by omega, h1, dite_true, dite_false]
      exact eqToHom (by congr 1; ext; simp [Fin.last]; omega) ≫ lastMor
  exact
  { n := G.n + 1
    chain := ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn
    triangle := fun j ↦
      if h : j.val < G.n then G.triangle ⟨j.val, h⟩
      else T
    triangle_dist := fun j ↦ by
      split_ifs with h
      · exact G.triangle_dist ⟨j.val, h⟩
      · exact hT
    triangle_obj₁ := fun j ↦ by
      have newChainObj : ∀ k (hk : k ≤ G.n),
          (ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj ⟨k, by omega⟩ =
          G.chain.obj ⟨k, by omega⟩ := fun k hk ↦ by
        simp [ComposableArrows.mkOfObjOfMapSucc_obj, objFn, hk]
      split_ifs with h
      · refine ⟨(Classical.choice (G.triangle_obj₁ ⟨j.val, h⟩)).trans (eqToIso ?_)⟩
        simp only [ComposableArrows.obj']
        exact (newChainObj j.val (by omega)).symm
      · have hj : j.val = G.n := by omega
        refine ⟨eT₁.trans ((Classical.choice G.top_iso).symm.trans (eqToIso ?_))⟩
        change G.chain.obj (Fin.last G.n) =
          (ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj' j.val _
        simp only [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj, objFn,
          show j.val ≤ G.n from by omega, dite_true]
        congr 1; ext; simp [Fin.last]; omega
    triangle_obj₂ := fun j ↦ by
      have newChainObj : ∀ k (hk : k ≤ G.n),
          (ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj ⟨k, by omega⟩ =
          G.chain.obj ⟨k, by omega⟩ := fun k hk ↦ by
        simp [ComposableArrows.mkOfObjOfMapSucc_obj, objFn, hk]
      split_ifs with h
      · refine ⟨(Classical.choice (G.triangle_obj₂ ⟨j.val, h⟩)).trans (eqToIso ?_)⟩
        simp only [ComposableArrows.obj']
        exact (newChainObj (j.val + 1) (by omega)).symm
      · refine ⟨eT₂.trans (eqToIso ?_)⟩
        simp only [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj, objFn,
          show ¬(j.val + 1 ≤ G.n) from by omega, dite_false]
    base_isZero := by
      change IsZero ((ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj ⟨0, _⟩)
      simp only [ComposableArrows.mkOfObjOfMapSucc_obj, objFn,
        show (0 : ℕ) ≤ G.n from by omega, dite_true]
      exact G.base_isZero
    top_iso := ⟨by
      change (ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj ⟨G.n + 1, _⟩ ≅ Z
      simp only [ComposableArrows.mkOfObjOfMapSucc_obj, objFn,
        show ¬(G.n + 1 ≤ G.n) from by omega, dite_false]
      exact Iso.refl _⟩
    zero_isZero := fun h ↦ absurd h (by omega)
    φ := fun j ↦
      if h : j.val < G.n then G.φ ⟨j.val, h⟩
      else ψ
    hφ := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ (hab : a < b)
      change (if h : b < G.n then G.φ ⟨b, h⟩ else ψ) < (if h : a < G.n then G.φ ⟨a, h⟩ else ψ)
      by_cases hb' : b < G.n
      · by_cases ha' : a < G.n
        · simp only [hb', ha', dite_true]
          exact G.hφ (show (⟨a, ha'⟩ : Fin G.n) < ⟨b, hb'⟩ from hab)
        · exact absurd (lt_trans hab hb') (by omega)
      · by_cases ha' : a < G.n
        · simp only [hb', ha', dite_true, dite_false]
          exact hψ_lt ⟨a, ha'⟩
        · omega
    semistable := fun j ↦ by
      change (P (if h : j.val < G.n then G.φ ⟨j.val, h⟩ else ψ))
        ((if h : j.val < G.n then G.triangle ⟨j.val, h⟩ else T).obj₃)
      split_ifs with h
      · exact G.semistable ⟨j.val, h⟩
      · exact hψ }

/-! ### Transporting HN filtrations -/

/-- Transport an HN filtration across an isomorphism `E ≅ E'`. -/
def HNFiltration.ofIso {P : ℝ → ObjectProperty C} {E E' : C}
    (F : HNFiltration C P E) (e : E ≅ E') : HNFiltration C P E' where
  n := F.n
  chain := F.chain
  triangle := F.triangle
  triangle_dist := F.triangle_dist
  triangle_obj₁ := F.triangle_obj₁
  triangle_obj₂ := F.triangle_obj₂
  base_isZero := F.base_isZero
  top_iso := ⟨(Classical.choice F.top_iso).trans e⟩
  zero_isZero := fun h ↦ IsZero.of_iso (F.zero_isZero h) e.symm
  φ := F.φ
  hφ := F.hφ
  semistable := F.semistable

/-- Shift an HN filtration by `a : ℤ`. If `F` is an HN filtration of `E` with phases
`φ₀ > φ₁ > ⋯`, then `F.shiftHN s a` is an HN filtration of `E⟦a⟧` with phases
`φ₀ + a > φ₁ + a > ⋯`. -/
def HNFiltration.shiftHN (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (a : ℤ) : HNFiltration C s.P (E⟦a⟧) where
  n := F.n
  chain := F.chain ⋙ shiftFunctor C a
  triangle := fun i ↦ (Triangle.shiftFunctor C a).obj (F.triangle i)
  triangle_dist := fun i ↦ Triangle.shift_distinguished _ (F.triangle_dist i) a
  triangle_obj₁ := fun i ↦
    ⟨(shiftFunctor C a).mapIso (Classical.choice (F.triangle_obj₁ i))⟩
  triangle_obj₂ := fun i ↦
    ⟨(shiftFunctor C a).mapIso (Classical.choice (F.triangle_obj₂ i))⟩
  base_isZero := (shiftFunctor C a).map_isZero F.base_isZero
  top_iso := ⟨(shiftFunctor C a).mapIso (Classical.choice F.top_iso)⟩
  zero_isZero := fun h ↦ (shiftFunctor C a).map_isZero (F.zero_isZero h)
  φ := fun j ↦ F.φ j + ↑a
  hφ := by
    intro i j hij
    change F.φ j + ↑a < F.φ i + ↑a
    linarith [F.hφ hij]
  semistable := fun j ↦ (s.shift_int C (F.φ j) ((F.triangle j).obj₃) a).mp (F.semistable j)

/-- The phiMinus of a shifted HN filtration increases by `a`. -/
@[simp]
lemma HNFiltration.shiftHN_phiMinus (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (a : ℤ) (h : 0 < F.n) :
    (F.shiftHN C s a).phiMinus C h = F.phiMinus C h + ↑a := rfl

/-- The phiPlus of a shifted HN filtration increases by `a`. -/
@[simp]
lemma HNFiltration.shiftHN_phiPlus (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (a : ℤ) (h : 0 < F.n) :
    (F.shiftHN C s a).phiPlus C h = F.phiPlus C h + ↑a := rfl

/-! ### Closure under isomorphisms -/

/-- The property `P(> t)` is closed under isomorphisms. -/
instance Slicing.gtProp_closedUnderIso (s : Slicing C) (t : ℝ) :
    (s.gtProp C t).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    rcases hE with hZ | ⟨F, hF, hgt⟩
    · exact Or.inl (IsZero.of_iso hZ e.symm)
    · exact Or.inr ⟨F.ofIso C e, hF, hgt⟩

/-- The property `P(≤ t)` is closed under isomorphisms. -/
instance Slicing.leProp_closedUnderIso (s : Slicing C) (t : ℝ) :
    (s.leProp C t).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    rcases hE with hZ | ⟨F, hF, hle⟩
    · exact Or.inl (IsZero.of_iso hZ e.symm)
    · exact Or.inr ⟨F.ofIso C e, hF, hle⟩

/-! ### Shift lemmas for subcategory predicates -/

/-- If `E` has all HN phases `> t`, then `E⟦a⟧` has all HN phases `> t + ↑a`. -/
lemma Slicing.gtProp_shift (s : Slicing C) (t : ℝ) (E : C) (a : ℤ)
    (h : s.gtProp C t E) : s.gtProp C (t + ↑a) (E⟦a⟧) := by
  rcases h with hZ | ⟨F, hF, hgt⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hZ)
  · exact Or.inr ⟨F.shiftHN C s a, hF, by
      rw [F.shiftHN_phiMinus]; linarith⟩

/-- If `E` has all HN phases `≤ t`, then `E⟦a⟧` has all HN phases `≤ t + ↑a`. -/
lemma Slicing.leProp_shift (s : Slicing C) (t : ℝ) (E : C) (a : ℤ)
    (h : s.leProp C t E) : s.leProp C (t + ↑a) (E⟦a⟧) := by
  rcases h with hZ | ⟨F, hF, hle⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hZ)
  · exact Or.inr ⟨F.shiftHN C s a, hF, by
      rw [F.shiftHN_phiPlus]; linarith⟩

/-! ### Uniqueness of extreme phases

The highest phase `φ⁺` and lowest phase `φ⁻` of an HN filtration are independent of the
choice of filtration. This is proved via hom-vanishing: if a filtration has a nonzero factor
at a high phase, no other filtration can have all phases below that threshold.
-/

/-- Auxiliary: if `Hom(factor(0), E) = 0` for an HN filtration `F`, then all maps from
`factor(0)` to any chain object are zero. Proved by downward induction on the chain
using the coYoneda exact sequence on the inverted rotation. -/
private lemma chain_hom_eq_zero_of_factor_zero (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n)
    (hzero : ∀ f : (F.triangle ⟨0, hn⟩).obj₃ ⟶ E, f = 0) :
    ∀ (k : ℕ) (hk : k < F.n + 1)
      (f : (F.triangle ⟨0, hn⟩).obj₃ ⟶ F.chain.obj ⟨k, hk⟩), f = 0 := by
  -- Downward induction: start from k = n (where chain(n) ≅ E, so all maps are zero)
  -- and go down to k = 0.
  suffices ∀ (m : ℕ) (hm : m ≤ F.n) (k : ℕ) (hk : k < F.n + 1) (_ : F.n - m ≤ k)
      (f : (F.triangle ⟨0, hn⟩).obj₃ ⟶ F.chain.obj ⟨k, hk⟩), f = 0 by
    intro k hk f; exact this F.n le_rfl k hk (by omega) f
  intro m
  induction m with
  | zero =>
    intro _ k hk hkn f
    have hkn' : k = F.n := by omega
    subst hkn'
    let eN := Classical.choice F.top_iso
    have h1 : f ≫ eN.hom = 0 := hzero _
    calc f = f ≫ eN.hom ≫ eN.inv := by rw [eN.hom_inv_id, Category.comp_id]
      _ = (f ≫ eN.hom) ≫ eN.inv := (Category.assoc _ _ _).symm
      _ = 0 ≫ eN.inv := by rw [h1]
      _ = 0 := zero_comp
  | succ m ih =>
    intro hm k hk hkn f
    by_cases hkn' : k = F.n - (m + 1)
    · -- At the target level: use the invRotate exact sequence
      have hkF : k < F.n := by omega
      let Tk := F.triangle ⟨k, hkF⟩
      let e₁ := Classical.choice (F.triangle_obj₁ ⟨k, hkF⟩)
      let e₂ := Classical.choice (F.triangle_obj₂ ⟨k, hkF⟩)
      -- Step 1: f ≫ e₁.inv maps into T_k.obj₁, and composing with T_k.mor₁ maps into
      -- T_k.obj₂ ≅ chain(k+1). By IH, this is zero.
      have hstep : (f ≫ e₁.inv) ≫ Tk.mor₁ = 0 := by
        -- The composite f ≫ e₁.inv ≫ Tk.mor₁ ≫ e₂.hom : factor(0) → chain(k+1)
        -- is zero by the IH.
        have h2 : (f ≫ e₁.inv ≫ Tk.mor₁) ≫ e₂.hom = 0 := by
          rw [Category.assoc, Category.assoc]
          exact ih (by omega) (k + 1) (by omega) (by omega) _
        -- Since e₂.hom is an isomorphism, f ≫ e₁.inv ≫ Tk.mor₁ = 0
        rw [Category.assoc]
        simp only [Preadditive.IsIso.comp_right_eq_zero] at h2
        exact h2
      -- Step 2: By coyoneda_exact₂ on the invRotate of T_k, f ≫ e₁.inv factors through
      -- T_k.obj₃[-1] = factor(k)[-1].
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ Tk.invRotate
        (inv_rot_of_distTriang _ (F.triangle_dist ⟨k, hkF⟩)) (f ≫ e₁.inv) hstep
      -- Step 3: g maps from factor(0) to factor(k)[-1]. By hom-vanishing, g = 0.
      -- factor(0) ∈ P(φ(0)), factor(k)[-1] ∈ P(φ(k) - 1), and φ(0) > φ(k) - 1.
      have hg_zero : g = 0 := by
        have hφ0 : (s.P (F.φ ⟨0, hn⟩)) (F.triangle ⟨0, hn⟩).obj₃ := F.semistable ⟨0, hn⟩
        have hφk_shift : (s.P (F.φ ⟨k, hkF⟩ - 1)) Tk.invRotate.obj₁ := by
          have := F.semistable ⟨k, hkF⟩
          change (s.P (F.φ ⟨k, hkF⟩)) Tk.obj₃ at this
          rw [show F.φ ⟨k, hkF⟩ - 1 = F.φ ⟨k, hkF⟩ + ((-1 : ℤ) : ℝ) from by push_cast; ring]
          exact (s.shift_int C (F.φ ⟨k, hkF⟩) Tk.obj₃ (-1)).mp this
        exact s.hom_vanishing (F.φ ⟨0, hn⟩) (F.φ ⟨k, hkF⟩ - 1)
          (F.triangle ⟨0, hn⟩).obj₃ Tk.invRotate.obj₁
          (by
            have h := F.hφ.antitone (show (⟨0, hn⟩ : Fin F.n) ≤ ⟨k, hkF⟩ from
              Fin.mk_le_mk.mpr (Nat.zero_le k))
            linarith)
          hφ0 hφk_shift g
      -- Conclude: f ≫ e₁.inv = 0, hence f = 0.
      have hfe : f ≫ e₁.inv = 0 :=
        hg.trans (by subst hg_zero; exact zero_comp)
      calc f = (f ≫ e₁.inv) ≫ e₁.hom := by
              rw [Category.assoc, e₁.inv_hom_id, Category.comp_id]
        _ = 0 := by rw [hfe, zero_comp]
    · -- Not at the target level: k > F.n - (m + 1), use IH directly
      exact ih (by omega) k hk (by omega) f

/-- If `Hom(factor(0), E) = 0` for an HN filtration, then `factor(0)` is zero.
This follows from `chain_hom_eq_zero_of_factor_zero`: all maps from `factor(0)` to
`chain(1)` are zero, and `chain(1) ≅ factor(0)`, so `id = 0`. -/
lemma HNFiltration.isZero_factor_zero_of_hom_eq_zero (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n)
    (hzero : ∀ f : (F.triangle ⟨0, hn⟩).obj₃ ⟶ E, f = 0) :
    IsZero (F.triangle ⟨0, hn⟩).obj₃ := by
  rw [IsZero.iff_id_eq_zero]
  -- factor(0) ≅ chain(1) (since base is zero, first triangle gives iso)
  let e₂ := Classical.choice (F.triangle_obj₂ ⟨0, hn⟩)
  have hiso := (Triangle.isZero₁_iff_isIso₂
    (F.triangle ⟨0, hn⟩) (F.triangle_dist ⟨0, hn⟩)).mp
    (IsZero.of_iso F.base_isZero (Classical.choice (F.triangle_obj₁ ⟨0, hn⟩)))
  -- The map inv(mor₂) ≫ e₂.hom : factor(0) → chain(1) is an iso
  -- Any map from factor(0) to chain(1) is zero by chain_hom_eq_zero_of_factor_zero
  have h1 : inv (F.triangle ⟨0, hn⟩).mor₂ ≫ e₂.hom = 0 :=
    chain_hom_eq_zero_of_factor_zero C s F hn hzero 1 (by omega) _
  have h2 : inv (F.triangle ⟨0, hn⟩).mor₂ = 0 := by
    calc inv (F.triangle ⟨0, hn⟩).mor₂
        = (inv (F.triangle ⟨0, hn⟩).mor₂ ≫ e₂.hom) ≫ e₂.inv := by
          rw [Category.assoc, e₂.hom_inv_id, Category.comp_id]
      _ = 0 := by rw [h1, zero_comp]
  calc 𝟙 _ = inv (F.triangle ⟨0, hn⟩).mor₂ ≫ (F.triangle ⟨0, hn⟩).mor₂ := by
        rw [IsIso.inv_hom_id]
    _ = 0 ≫ (F.triangle ⟨0, hn⟩).mor₂ := by rw [h2]
    _ = 0 := zero_comp

/-- The highest phase `φ⁺` of a nonzero HN filtration cannot exceed the highest phase
of any other filtration of the same object, provided the first factor is nonzero.
Proved by contradiction using hom-vanishing and `isZero_factor_zero_of_hom_eq_zero`. -/
theorem HNFiltration.phiPlus_le_of_nonzero_factor (s : Slicing C) {E : C}
    (F₁ F₂ : HNFiltration C s.P E) (hn₁ : 0 < F₁.n) (hn₂ : 0 < F₂.n)
    (hne : ¬IsZero (F₁.triangle ⟨0, hn₁⟩).obj₃) :
    F₁.phiPlus C hn₁ ≤ F₂.phiPlus C hn₂ := by
  by_contra hlt
  push_neg at hlt
  -- F₁.φ(0) > F₂.φ(0), so all F₂ phases < F₁.φ(0)
  have hgap : ∀ j : Fin F₂.n, F₂.φ j < F₁.φ ⟨0, hn₁⟩ := fun j ↦
    lt_of_le_of_lt (F₂.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val)))
      (by change F₂.phiPlus C hn₂ < F₁.phiPlus C hn₁; exact hlt)
  -- By hom_eq_zero_of_gt_phases, Hom(factor₁(0), E) = 0
  have hzero : ∀ f : (F₁.triangle ⟨0, hn₁⟩).obj₃ ⟶ E, f = 0 :=
    fun f ↦ Slicing.hom_eq_zero_of_gt_phases C s
      (F₁.semistable ⟨0, hn₁⟩) F₂ hgap f
  -- By isZero_factor_zero_of_hom_eq_zero, factor₁(0) is zero
  exact hne (F₁.isZero_factor_zero_of_hom_eq_zero C s hn₁ hzero)

/-- For any two HN filtrations of a nonzero object where both have nonzero first factors,
the highest phases agree. -/
theorem HNFiltration.phiPlus_eq_of_nonzero_factors (s : Slicing C) {E : C}
    (F₁ F₂ : HNFiltration C s.P E) (hn₁ : 0 < F₁.n) (hn₂ : 0 < F₂.n)
    (hne₁ : ¬IsZero (F₁.triangle ⟨0, hn₁⟩).obj₃)
    (hne₂ : ¬IsZero (F₂.triangle ⟨0, hn₂⟩).obj₃) :
    F₁.phiPlus C hn₁ = F₂.phiPlus C hn₂ :=
  le_antisymm (F₁.phiPlus_le_of_nonzero_factor C s F₂ hn₁ hn₂ hne₁)
    (F₂.phiPlus_le_of_nonzero_factor C s F₁ hn₂ hn₁ hne₂)

/-- For any HN filtration of a nonzero object, at least one factor is nonzero.
If all factors were zero, the chain would start and end at zero, contradicting E nonzero. -/
lemma HNFiltration.exists_nonzero_factor {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hE : ¬IsZero E) :
    ∃ (i : Fin F.n), ¬IsZero (F.triangle i).obj₃ := by
  by_contra hall
  push_neg at hall
  -- All factors are zero. Show chain(k) ≅ 0 for all k by induction.
  suffices ∀ (k : ℕ) (hk : k < F.n + 1), IsZero (F.chain.obj ⟨k, hk⟩) by
    exact hE (IsZero.of_iso (this F.n (by omega)) (Classical.choice F.top_iso).symm)
  intro k hk
  induction k with
  | zero => exact F.base_isZero
  | succ k ih =>
    have hkn : k < F.n := by omega
    let Tk := F.triangle ⟨k, hkn⟩
    let e₁ := Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)
    let e₂ := Classical.choice (F.triangle_obj₂ ⟨k, hkn⟩)
    -- Tk.obj₃ = factor(k) is zero by hypothesis
    have hfact : IsZero Tk.obj₃ := hall ⟨k, hkn⟩
    -- IsZero Tk.obj₃ ↔ IsIso Tk.mor₁
    have hiso : IsIso Tk.mor₁ :=
      (Triangle.isZero₃_iff_isIso₁ _ (F.triangle_dist ⟨k, hkn⟩)).mp hfact
    -- Tk.obj₁ ≅ chain(k) which is zero by IH
    have h1 : IsZero Tk.obj₁ :=
      (ih (by omega)).of_iso e₁
    -- Since mor₁ is an iso and obj₁ is zero, obj₂ is zero
    have h2 : IsZero Tk.obj₂ := by
      -- obj₂ is zero: the iso mor₁ : obj₁ ≅ obj₂ transports the zero property
      exact h1.of_iso (asIso Tk.mor₁).symm
    exact h2.of_iso e₂.symm

/-- For a nonzero object, any HN filtration has at least one factor. -/
lemma HNFiltration.n_pos {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hE : ¬IsZero E) : 0 < F.n := by
  by_contra h
  push_neg at h
  exact hE (F.zero_isZero (by omega))

/-- Drop the first factor from an HN filtration when it is zero. The resulting
filtration has `n - 1` factors with phases `φ(1) > ⋯ > φ(n-1)`. -/
def HNFiltration.dropFirst {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hn : 1 < F.n)
    (hzero : IsZero (F.triangle ⟨0, by omega⟩).obj₃) :
    HNFiltration C P E :=
  -- chain(0) = 0 and factor(0) = 0 imply chain(1) ≅ 0 (new base)
  have h0 : 0 < F.n := by omega
  let T0 := F.triangle ⟨0, h0⟩
  have hiso0 : IsIso T0.mor₁ :=
    (Triangle.isZero₃_iff_isIso₁ T0 (F.triangle_dist ⟨0, h0⟩)).mp hzero
  have chain1_zero : IsZero (F.chain.obj ⟨1, by omega⟩) :=
    (F.base_isZero.of_iso (Classical.choice (F.triangle_obj₁ ⟨0, h0⟩))).of_iso
      (asIso T0.mor₁).symm |>.of_iso (Classical.choice (F.triangle_obj₂ ⟨0, h0⟩)).symm
  have heq : F.n - 1 + 1 = F.n := by omega
  { n := F.n - 1
    chain := ComposableArrows.mkOfObjOfMapSucc
      (fun i : Fin (F.n - 1 + 1) ↦ F.chain.obj ⟨i.val + 1, by omega⟩)
      (fun i : Fin (F.n - 1) ↦ F.chain.map' (i.val + 1) (i.val + 2) (by omega) (by omega))
    triangle := fun j ↦ F.triangle ⟨j.val + 1, by omega⟩
    triangle_dist := fun j ↦ F.triangle_dist ⟨j.val + 1, by omega⟩
    triangle_obj₁ := fun j ↦ by
      refine ⟨(Classical.choice (F.triangle_obj₁ ⟨j.val + 1, by omega⟩)).trans
        (eqToIso ?_)⟩
      simp [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj]
    triangle_obj₂ := fun j ↦ by
      refine ⟨(Classical.choice (F.triangle_obj₂ ⟨j.val + 1, by omega⟩)).trans
        (eqToIso ?_)⟩
      simp [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj]
    base_isZero := by
      change IsZero ((ComposableArrows.mkOfObjOfMapSucc _ _).obj ⟨0, _⟩)
      simp [ComposableArrows.mkOfObjOfMapSucc_obj]
      exact chain1_zero
    top_iso := ⟨by
      change (ComposableArrows.mkOfObjOfMapSucc _ _).obj ⟨F.n - 1, _⟩ ≅ E
      simp only [ComposableArrows.mkOfObjOfMapSucc_obj]
      exact (eqToIso (by congr 1; ext; simp; omega)).trans (Classical.choice F.top_iso)⟩
    zero_isZero := fun h ↦ by omega
    φ := fun j ↦ F.φ ⟨j.val + 1, by omega⟩
    hφ := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ (hab : a < b)
      exact F.hφ (show (⟨a + 1, by omega⟩ : Fin F.n) < ⟨b + 1, by omega⟩ from by
        exact Fin.mk_lt_mk.mpr (by omega))
    semistable := fun j ↦ F.semistable ⟨j.val + 1, by omega⟩ }

/-- For any nonzero object, there exists an HN filtration with nonzero first factor.
Proved by repeatedly dropping zero first factors; terminates since `n` decreases
and some factor must be nonzero (by `exists_nonzero_factor`). -/
lemma HNFiltration.exists_nonzero_first (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n), ¬IsZero (F.triangle ⟨0, hn⟩).obj₃ := by
  obtain ⟨F⟩ := s.hn_exists E
  suffices hmain : ∀ (m : ℕ) (G : HNFiltration C s.P E), G.n ≤ m →
      ∃ (H : HNFiltration C s.P E) (hn : 0 < H.n),
        ¬IsZero (H.triangle ⟨0, hn⟩).obj₃ from
    hmain F.n F le_rfl
  intro m
  induction m with
  | zero =>
    intro G hGn
    exact absurd (G.zero_isZero (by omega)) hE
  | succ m ih =>
    intro G hGn
    have hGn0 : 0 < G.n := G.n_pos C hE
    by_cases hfirst : IsZero (G.triangle ⟨0, hGn0⟩).obj₃
    · -- First factor is zero; drop it and recurse
      have hn1 : 1 < G.n := by
        by_contra h; push_neg at h
        have : ∀ (i : Fin G.n), IsZero (G.triangle i).obj₃ := fun i ↦ by
          have : i = ⟨0, hGn0⟩ := Fin.ext (by omega)
          subst this; exact hfirst
        exact absurd ((G.exists_nonzero_factor C hE).elim fun i hi ↦ absurd (this i) hi) id
      have hdrop : (G.dropFirst C hn1 hfirst).n ≤ m := by
        change G.n - 1 ≤ m; omega
      exact ih (G.dropFirst C hn1 hfirst) hdrop
    · exact ⟨G, hGn0, hfirst⟩

/-- Drop the last factor from an HN filtration when it is zero. The resulting
filtration has `n - 1` factors with phases `φ(0) > ⋯ > φ(n-2)`. -/
def HNFiltration.dropLast {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hn : 1 < F.n)
    (hzero : IsZero (F.triangle ⟨F.n - 1, by omega⟩).obj₃) :
    HNFiltration C P E :=
  have hn0 : 0 < F.n := by omega
  let Tn := F.triangle ⟨F.n - 1, by omega⟩
  have hiso : IsIso Tn.mor₁ :=
    (Triangle.isZero₃_iff_isIso₁ Tn (F.triangle_dist ⟨F.n - 1, by omega⟩)).mp hzero
  -- chain(n-1) ≅ chain(n) ≅ E via mor₁ and top_iso
  let e₁ := Classical.choice (F.triangle_obj₁ ⟨F.n - 1, by omega⟩)
  let e₂ := Classical.choice (F.triangle_obj₂ ⟨F.n - 1, by omega⟩)
  -- The new top_iso: prefix's chain(n-1) = F.chain.obj(n-1) ≅ chain(n) ≅ E
  let pfx := F.prefix C (F.n - 1) (by omega) (by omega)
  -- pfx.chain.right = pfx.chain.obj(n-1) which is F.chain.obj(n-1)
  -- F.chain.obj(n-1) ≅ Tn.obj₁ ≅ Tn.obj₂ ≅ F.chain.obj(n) ≅ E
  { n := F.n - 1
    chain := pfx.chain
    triangle := pfx.triangle
    triangle_dist := pfx.triangle_dist
    triangle_obj₁ := pfx.triangle_obj₁
    triangle_obj₂ := pfx.triangle_obj₂
    base_isZero := pfx.base_isZero
    top_iso := ⟨(Classical.choice pfx.top_iso).trans
      (e₁.symm.trans ((asIso Tn.mor₁).trans
        (e₂.trans ((eqToIso (by
          simp [ComposableArrows.obj', ComposableArrows.right]
          congr 1; ext; simp [Fin.last]; omega)).trans
          (Classical.choice F.top_iso)))))⟩
    zero_isZero := fun h ↦ by omega
    φ := pfx.φ
    hφ := pfx.hφ
    semistable := pfx.semistable }

/-- For any nonzero object, there exists an HN filtration with nonzero last factor.
Proved by repeatedly dropping zero last factors. -/
lemma HNFiltration.exists_nonzero_last (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.triangle ⟨F.n - 1, by omega⟩).obj₃ := by
  obtain ⟨F⟩ := s.hn_exists E
  suffices hmain : ∀ (m : ℕ) (G : HNFiltration C s.P E), G.n ≤ m →
      ∃ (H : HNFiltration C s.P E) (hn : 0 < H.n),
        ¬IsZero (H.triangle ⟨H.n - 1, by omega⟩).obj₃ from
    hmain F.n F le_rfl
  intro m
  induction m with
  | zero =>
    intro G hGn
    exact absurd (G.zero_isZero (by omega)) hE
  | succ m ih =>
    intro G hGn
    have hGn0 : 0 < G.n := G.n_pos C hE
    by_cases hlast : IsZero (G.triangle ⟨G.n - 1, by omega⟩).obj₃
    · have hn1 : 1 < G.n := by
        by_contra h; push_neg at h
        have : ∀ (i : Fin G.n), IsZero (G.triangle i).obj₃ := fun i ↦ by
          have : i = ⟨G.n - 1, by omega⟩ := Fin.ext (by omega)
          subst this; exact hlast
        exact absurd ((G.exists_nonzero_factor C hE).elim fun i hi ↦ absurd (this i) hi) id
      have hdrop : (G.dropLast C hn1 hlast).n ≤ m := by
        change G.n - 1 ≤ m; omega
      exact ih (G.dropLast C hn1 hlast) hdrop
    · exact ⟨G, hGn0, hlast⟩

/-! ### Intrinsic phase bounds

For a nonzero object `E` with an HN filtration, the highest and lowest phases are
independent of the choice of filtration (assuming the first/last factors are nonzero).
We define intrinsic `phiPlus` and `phiMinus` using `Classical.choice` and prove
they agree with any filtration having nonzero boundary factors.
-/

/-- The intrinsic highest phase of a nonzero object with respect to a slicing.
This is the phase of the first factor in any HN filtration with nonzero first factor.
Well-defined by `phiPlus_eq_of_nonzero_factors`. -/
noncomputable def Slicing.phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hn := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  F.φ ⟨0, hn⟩

/-- The intrinsic lowest phase of a nonzero object with respect to a slicing.
This is the phase of the last factor in any HN filtration with nonzero first factor. -/
noncomputable def Slicing.phiMinus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hn : 0 < F.n := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  F.φ ⟨F.n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩

/-- `Slicing.phiPlus` equals `G.φ ⟨0, hn⟩` for any HN filtration `G` with nonzero
first factor. -/
theorem Slicing.phiPlus_eq (s : Slicing C) (E : C) (hE : ¬IsZero E)
    (G : HNFiltration C s.P E) (hn : 0 < G.n)
    (hne : ¬IsZero (G.triangle ⟨0, hn⟩).obj₃) :
    s.phiPlus C E hE = G.φ ⟨0, hn⟩ := by
  unfold Slicing.phiPlus
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hnF := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  let hneF := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose_spec
  change F.φ ⟨0, hnF⟩ = G.φ ⟨0, hn⟩
  exact HNFiltration.phiPlus_eq_of_nonzero_factors C s F G hnF hn hneF hne

/-- `Slicing.phiMinus ≤ Slicing.phiPlus` for nonzero objects. -/
theorem Slicing.phiMinus_le_phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) :
    s.phiMinus C E hE ≤ s.phiPlus C E hE := by
  unfold Slicing.phiPlus Slicing.phiMinus
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hn := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  change F.φ ⟨F.n - 1, _⟩ ≤ F.φ ⟨0, hn⟩
  exact F.hφ.antitone (Fin.mk_le_mk.mpr (by have := hn; omega))

/-! ### Lemma 3.4: Triangle phase-bound inequalities

In a distinguished triangle `A → E → B → A⟦1⟧` where all three objects lie in an
interval subcategory of width ≤ 1, the intrinsic highest phases satisfy
`phiPlus(A) ≤ phiPlus(E)`. This is Lemma 3.4 of Bridgeland (2007).

The proof uses the coYoneda exact sequence on the inverse rotation of the triangle:
if `φ⁺(A) > φ⁺(E)`, then the top semistable factor `A⁺` of `A` has all maps to `E`
vanishing; by exactness, maps `A⁺ → A` factor through `B⟦-1⟧`, but B's shifted
phases are too low, so all maps to `B⟦-1⟧` vanish too, giving `A⁺ = 0`, a
contradiction.
-/

/-- The intrinsic phiPlus is bounded above by the top phase of any HN filtration. -/
lemma Slicing.phiPlus_le_phiPlus_of_hn (s : Slicing C) {E : C} (hE : ¬IsZero E)
    (G : HNFiltration C s.P E) (hn : 0 < G.n) :
    s.phiPlus C E hE ≤ G.phiPlus C hn := by
  obtain ⟨F, hnF, hneF⟩ := HNFiltration.exists_nonzero_first C s hE
  rw [s.phiPlus_eq C E hE F hnF hneF]
  exact F.phiPlus_le_of_nonzero_factor C s G hnF hn hneF

/-- The intrinsic phiPlus of a nonzero object is bounded above by the upper endpoint of any
interval containing the object. -/
lemma Slicing.phiPlus_lt_of_intervalProp (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {a b : ℝ} (hI : s.intervalProp C a b E) : s.phiPlus C E hE < b := by
  rcases hI with hZ | ⟨G, hG⟩
  · exact absurd hZ hE
  · have hGn : 0 < G.n := G.n_pos C hE
    calc s.phiPlus C E hE
        ≤ G.phiPlus C hGn := s.phiPlus_le_phiPlus_of_hn C hE G hGn
      _ < b := (hG ⟨0, hGn⟩).2

/-- The intrinsic phiPlus of a nonzero object is bounded below by the lower endpoint of any
interval containing the object. -/
lemma Slicing.phiPlus_gt_of_intervalProp (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {a b : ℝ} (hI : s.intervalProp C a b E) : a < s.phiPlus C E hE := by
  rcases hI with hZ | ⟨G, hG⟩
  · exact absurd hZ hE
  · have hGn : 0 < G.n := G.n_pos C hE
    by_contra hle
    push_neg at hle
    -- phiPlus(E) ≤ a. Get a filtration F with nonzero first factor.
    obtain ⟨F, hnF, hneF⟩ := HNFiltration.exists_nonzero_first C s hE
    rw [s.phiPlus_eq C E hE F hnF hneF] at hle
    -- F.φ(0) ≤ a, so all F phases ≤ a (since phases are strictly decreasing)
    have hF_le : ∀ j : Fin F.n, F.φ j ≤ a := fun j ↦
      le_trans (F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val))) hle
    -- G has all phases > a, F has all phases ≤ a, so there is a phase gap
    have hgap : ∀ (i : Fin G.n) (j : Fin F.n), F.φ j < G.φ i := fun i j ↦
      lt_of_le_of_lt (hF_le j) (hG i).1
    -- Hom(E, E) = 0 by phase gap, so id_E = 0, so E is zero — contradiction
    exact hE ((IsZero.iff_id_eq_zero E).mpr (s.hom_eq_zero_of_phase_gap C G F hgap (𝟙 E)))


/-- **Lemma 3.4** (left inequality). In a distinguished triangle `A → E → B → A⟦1⟧`
where the phases of A and B lie in an interval `(a, b)` with `b ≤ a + 1`,
we have `φ⁺(A) ≤ φ⁺(E)`.

The width condition `b ≤ a + 1` ensures `B⟦-1⟧` has all phases below any phase of `A`,
so the factoring argument through `B⟦-1⟧` gives a contradiction. -/
theorem Slicing.phiPlus_triangle_le (s : Slicing C) {A E B : C}
    (hA : ¬IsZero A) (hE : ¬IsZero E)
    {a b : ℝ} (hab : b ≤ a + 1)
    (hA_int : s.intervalProp C a b A)
    (hB_int : s.intervalProp C a b B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.phiPlus C A hA ≤ s.phiPlus C E hE := by
  -- Get filtrations with nonzero first factors
  obtain ⟨FA, hnA, hneA⟩ := HNFiltration.exists_nonzero_first C s hA
  obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_first C s hE
  rw [s.phiPlus_eq C A hA FA hnA hneA, s.phiPlus_eq C E hE FE hnE hneE]
  -- Suppose for contradiction that φ⁺(A) > φ⁺(E)
  by_contra hlt
  push_neg at hlt
  -- All E-phases < FA.φ(0)
  have hE_gap : ∀ j : Fin FE.n, FE.φ j < FA.φ ⟨0, hnA⟩ := fun j ↦
    lt_of_le_of_lt (FE.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val))) hlt
  -- All maps A⁺ → A are zero (the key step)
  -- For ANY map α : A⁺ → A, the composite α ≫ f : A⁺ → E is zero (since Hom(A⁺, E) = 0).
  -- By coyoneda exactness on invRotate, α factors through B⟦-1⟧.
  -- But Hom(A⁺, B⟦-1⟧) = 0 too, so α = 0.
  have hA_factor_zero : ∀ α : (FA.triangle ⟨0, hnA⟩).obj₃ ⟶ A, α = 0 := by
    intro α
    -- α ≫ f : A⁺ → E is zero
    have hαf : α ≫ f = 0 :=
      s.hom_eq_zero_of_gt_phases C (FA.semistable ⟨0, hnA⟩) FE hE_gap _
    -- By coyoneda on invRotate of the triangle, α factors through B⟦-1⟧
    let T := Triangle.mk f g h
    obtain ⟨β, hβ⟩ := Triangle.coyoneda_exact₂ T.invRotate
      (inv_rot_of_distTriang _ hT) α hαf
    -- β : A⁺ → B⟦-1⟧. Show β = 0.
    suffices hβ0 : β = 0 by rw [hβ, hβ0, zero_comp]; rfl
    by_cases hBZ : IsZero B
    · exact ((shiftFunctor C (-1 : ℤ)).map_isZero hBZ).eq_of_tgt β 0
    · -- Get an HN filtration of B⟦-1⟧ from hB_int
      rcases hB_int with hBZ' | ⟨GB, hGB⟩
      · exact absurd hBZ' hBZ
      · -- Shift GB by -1 to get filtration of B⟦-1⟧
        let GBs := GB.shiftHN C s (-1 : ℤ)
        have hnB : 0 < GB.n := GB.n_pos C hBZ
        -- GBs.φ(j) = GB.φ(j) - 1 < b - 1 ≤ a < FA.φ(0)
        have hBs_gap : ∀ j : Fin GBs.n, GBs.φ j < FA.φ ⟨0, hnA⟩ := by
          intro j
          change GB.φ j + ((-1 : ℤ) : ℝ) < FA.φ ⟨0, hnA⟩
          have h1 : GB.φ j < b := (hGB j).2
          have h2 : a < FA.φ ⟨0, hnA⟩ := by
            rw [← s.phiPlus_eq C A hA FA hnA hneA]
            exact s.phiPlus_gt_of_intervalProp C hA hA_int
          have h3 : ((-1 : ℤ) : ℝ) = -1 := by norm_num
          linarith
        exact s.hom_eq_zero_of_gt_phases C (FA.semistable ⟨0, hnA⟩) GBs hBs_gap β
  -- But A⁺ is nonzero, and all maps to A are zero — contradiction
  exact hneA (FA.isZero_factor_zero_of_hom_eq_zero C s hnA hA_factor_zero)

/-! ### Single-factor HN filtrations -/

/-- Construct a 1-factor HN filtration for a semistable object. -/
def HNFiltration.single {P : ℝ → ObjectProperty C} (S : C) (φ : ℝ)
    (hS : (P φ) S) : HNFiltration C P S where
  n := 1
  chain := ComposableArrows.mk₁ (0 : (0 : C) ⟶ S)
  triangle := fun _ ↦ Triangle.mk (0 : (0 : C) ⟶ S) (𝟙 S) 0
  triangle_dist := fun _ ↦ contractible_distinguished₁ S
  triangle_obj₁ := fun i ↦ by
    exact ⟨eqToIso (by simp [ComposableArrows.obj', ComposableArrows.mk₁_obj])⟩
  triangle_obj₂ := fun i ↦ by
    exact ⟨eqToIso (by simp [ComposableArrows.obj', ComposableArrows.mk₁_obj])⟩
  base_isZero := isZero_zero C
  top_iso := ⟨eqToIso (by simp [ComposableArrows.right, ComposableArrows.mk₁_obj])⟩
  zero_isZero := fun h ↦ absurd h (by omega)
  φ := fun _ ↦ φ
  hφ := fun i j h ↦ absurd h (by omega)
  semistable := fun j ↦ by
    have : j = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst this; exact hS

/-- A semistable object of phase `≤ t` satisfies `leProp t`. -/
lemma Slicing.leProp_of_semistable (s : Slicing C) (φ t : ℝ) (S : C)
    (hS : (s.P φ) S) (hle : φ ≤ t) :
    s.leProp C t S :=
  Or.inr ⟨HNFiltration.single C S φ hS,
    show 0 < 1 from by omega, hle⟩

/-- A semistable object of phase `> t` satisfies `gtProp t`. -/
lemma Slicing.gtProp_of_semistable (s : Slicing C) (φ t : ℝ) (S : C)
    (hS : (s.P φ) S) (hgt : t < φ) :
    s.gtProp C t S :=
  Or.inr ⟨HNFiltration.single C S φ hS,
    show 0 < 1 from by omega, hgt⟩

/-! ### Bounded t-structures -/

/-- A t-structure is bounded if every object lies between some `le a` and `ge b` levels.
This is the condition used in Lemma 3.2 and Proposition 5.3 of Bridgeland (2007). -/
def TStructure.IsBounded {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) : Prop :=
  ∀ E : C, ∃ a b : ℤ, t.le a E ∧ t.ge b E

/-! ### t-structure from a slicing

Given a slicing `s` on a triangulated category, we construct a t-structure where
`le n` consists of objects whose HN phases are all `> -n` (i.e., `gtProp(-n)`), and
`ge n` consists of objects whose HN phases are all `≤ 1-n` (i.e., `leProp(1-n)`).

The construction requires `[IsTriangulated C]` for the octahedral axiom, used in
the decomposition of objects into `le 0` and `ge 1` parts.
-/

/-- The hom-vanishing lemma for the t-structure: any morphism from an object with
all HN phases `> 0` to an object with all HN phases `≤ 0` is zero. -/
lemma Slicing.zero_of_gtProp_leProp (s : Slicing C) {X Y : C}
    (hX : s.gtProp C 0 X) (hY : s.leProp C 0 Y) (f : X ⟶ Y) : f = 0 := by
  rcases hX with hXZ | ⟨Fx, hFx, hFx_gt⟩
  · exact hXZ.eq_of_src f 0
  rcases hY with hYZ | ⟨Fy, hFy, hFy_le⟩
  · exact hYZ.eq_of_tgt f 0
  exact s.hom_eq_zero_of_phase_gap C Fx Fy
    (fun i j ↦ by linarith [(Fy.phase_mem_range C hFy j).2,
      (Fx.phase_mem_range C hFx i).1]) f

variable [IsTriangulated C]

/-- Auxiliary: given an HN filtration, produce a t-structure decomposition triangle.
This is the core of `exists_triangle_zero_one`. Uses induction on the number of
factors to handle the mixed-phase case by peeling off the last factor. -/
private lemma Slicing.tStructureAux (s : Slicing C)
    (A : C) (F : HNFiltration C s.P A) :
    ∃ (X Y : C) (_ : s.gtProp C 0 X) (_ : s.leProp C 0 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  -- Strengthened IH: also return phase bound data for the Y side, so that
  -- the recursive mixed-phase case can track the relationship between the
  -- prefix's phases and the Y-side filtration's phases.
  suffices hmain : ∀ (m : ℕ) (A : C) (F : HNFiltration C s.P A), F.n ≤ m →
      ∃ (X Y : C) (_ : s.gtProp C 0 X)
        (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧
        (IsZero Y ∨ ∃ (GY : HNFiltration C s.P Y) (hGY : 0 < GY.n),
          GY.phiPlus C hGY ≤ 0 ∧
          (∀ (_ : 0 < F.n) (j : Fin GY.n),
            F.φ ⟨F.n - 1, by omega⟩ ≤ GY.φ j)) by
    obtain ⟨X, Y, hX, f, g, h, hT, hY⟩ := hmain F.n A F le_rfl
    exact ⟨X, Y, hX,
      hY.elim Or.inl (fun ⟨GY, hGY, hle, _⟩ ↦ Or.inr ⟨GY, hGY, hle⟩),
      f, g, h, hT⟩
  intro m
  induction m with
  | zero =>
    intro A F hFn
    have hn : F.n = 0 := by omega
    exact ⟨A, 0, Or.inl (F.zero_isZero hn), 𝟙 A, 0, 0,
      contractible_distinguished A, Or.inl (isZero_zero C)⟩
  | succ m ih =>
    intro A F hFn
    by_cases hn : F.n = 0
    · exact ⟨A, 0, Or.inl (F.zero_isZero hn), 𝟙 A, 0, 0,
        contractible_distinguished A, Or.inl (isZero_zero C)⟩
    have hn0 : 0 < F.n := Nat.pos_of_ne_zero hn
    by_cases hall_pos : ∀ j : Fin F.n, 0 < F.φ j
    · -- All phases > 0: X = A, Y = 0
      exact ⟨A, 0, s.gtProp_of_hn C F 0 hall_pos hn0, 𝟙 A, 0, 0,
        contractible_distinguished A, Or.inl (isZero_zero C)⟩
    · push_neg at hall_pos
      by_cases hall_neg : ∀ j : Fin F.n, F.φ j ≤ 0
      · -- All phases ≤ 0: X = 0, Y = A, filtration is F itself
        refine ⟨0, A, Or.inl (isZero_zero C), 0, 𝟙 A, 0,
          contractible_distinguished₁ A,
          Or.inr ⟨F, hn0, hall_neg ⟨0, hn0⟩, fun _ j ↦
            F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))⟩⟩
      · -- Mixed case: some phases > 0 and some ≤ 0
        push_neg at hall_neg
        -- F.n ≥ 2: can't be mixed with only one factor
        have hn2 : 2 ≤ F.n := by
          by_contra hlt; push_neg at hlt
          obtain ⟨j, hj⟩ := hall_neg; obtain ⟨j', hj'⟩ := hall_pos
          have heq : F.φ j = F.φ j' := congrArg F.φ (Fin.ext (by omega))
          linarith
        -- Consider the prefix filtration with n-1 factors
        let G := F.prefix C (F.n - 1) (by omega) (by omega)
        -- Apply IH to chain(n-1) with the prefix filtration (n-1 ≤ m)
        obtain ⟨X, Y', hX, f', g', h', hT', hY'⟩ :=
          ih (F.chain.obj' (F.n - 1) (by omega)) G
            (by have : G.n = F.n - 1 := rfl; omega)
        -- Transport the last HN triangle to chain objects
        let T := F.triangle ⟨F.n - 1, by omega⟩
        let e₁ := Classical.choice (F.triangle_obj₁ ⟨F.n - 1, by omega⟩)
        let e₂ := Classical.choice (F.triangle_obj₂ ⟨F.n - 1, by omega⟩)
        let eA := Classical.choice F.top_iso
        have hchainN : F.chain.obj' (F.n - 1 + 1) (by omega) =
            F.chain.obj (Fin.last F.n) :=
          congrArg F.chain.obj (Fin.ext (by simp [Fin.last]; omega))
        let e₂A : T.obj₂ ≅ A :=
          e₂.trans ((eqToIso hchainN).trans eA)
        let u₂₃ : F.chain.obj' (F.n - 1) (by omega) ⟶ A :=
          e₁.inv ≫ T.mor₁ ≫ e₂A.hom
        let Tisoₘ := Triangle.isoMk (Triangle.mk u₂₃ (e₂A.inv ≫ T.mor₂)
          (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧')) T e₁.symm e₂A.symm (Iso.refl _)
          (by simp [u₂₃, e₂A])
          (by simp [e₂A])
          (by simp)
        have hTu₂₃ : Triangle.mk u₂₃ (e₂A.inv ≫ T.mor₂)
          (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') ∈ distTriang C :=
          isomorphic_distinguished _ (F.triangle_dist ⟨F.n - 1, by omega⟩) _ Tisoₘ
        -- The last phase is ≤ 0
        obtain ⟨j₀, hj₀⟩ := hall_pos
        have hφlast : F.φ ⟨F.n - 1, by omega⟩ ≤ 0 :=
          le_trans (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))) hj₀
        -- Case split on whether the prefix decomposition gave Y' = 0
        rcases hY' with hY'Z | ⟨GY', hGY', hGY'_le, hGY'_bound⟩
        · -- Y' is zero (prefix was all-positive): f' is iso
          have hf'Iso : IsIso f' :=
            (Triangle.isZero₃_iff_isIso₁ _ hT').mp hY'Z
          let eX : X ≅ F.chain.obj' (F.n - 1) (by omega) := asIso f'
          refine ⟨X, T.obj₃, hX, eX.hom ≫ u₂₃, e₂A.inv ≫ T.mor₂,
            T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.hom ≫
              (shiftFunctor C (1 : ℤ)).map eX.inv, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
          · -- Distinguished triangle via transport
            apply isomorphic_distinguished _ (F.triangle_dist ⟨F.n - 1, by omega⟩)
            exact Triangle.isoMk _ T (eX.trans e₁.symm) e₂A.symm (Iso.refl _)
              (by simp [u₂₃, eX, e₂A])
              (by simp [e₂A])
              (by simp [eX])
          · -- Single-factor HN filtration of T.obj₃
            exact HNFiltration.single C T.obj₃ (F.φ ⟨F.n - 1, by omega⟩)
              (F.semistable ⟨F.n - 1, by omega⟩)
          · -- 0 < 1
            change 0 < 1; omega
          · -- phiPlus ≤ 0: single.φ 0 = F.φ(n-1) ≤ 0
            exact hφlast
          · -- Phase bound: F.φ(n-1) ≤ single.φ j = F.φ(n-1)
            intro _ _; exact le_rfl
        · -- Y' has filtration with phase bound: use octahedral + appendFactor
          -- Extract the phase bound from the IH
          have hGn : 0 < G.n := by change 0 < F.n - 1; omega
          have hφlast_lt : ∀ j : Fin GY'.n,
              F.φ ⟨F.n - 1, by omega⟩ < GY'.φ j := by
            intro j
            calc F.φ ⟨F.n - 1, by omega⟩
                < F.φ ⟨F.n - 2, by omega⟩ :=
                  F.hφ (show (⟨F.n - 2, by omega⟩ : Fin F.n) <
                    ⟨F.n - 1, by omega⟩ from
                      Fin.mk_lt_mk.mpr (by omega))
              _ = G.φ ⟨G.n - 1, by omega⟩ := by
                  change F.φ ⟨F.n - 2, _⟩ = F.φ ⟨(F.n - 1) - 1, _⟩; congr 1
              _ ≤ GY'.φ j := hGY'_bound hGn j
          -- Complete f' ≫ u₂₃ to a distinguished triangle
          obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (f' ≫ u₂₃)
          -- Octahedral: Y' → Z → Factor(n-1) → Y'[1] is distinguished
          let oct := Triangulated.someOctahedron rfl hT' hTu₂₃ h₁₃
          let GZ := GY'.appendFactor C oct.triangle oct.mem (Iso.refl _)
            (Iso.refl _) (F.φ ⟨F.n - 1, by omega⟩)
            (F.semistable ⟨F.n - 1, by omega⟩) hφlast_lt
          have hGZn : GZ.n = GY'.n + 1 := rfl
          refine ⟨X, Z, hX, f' ≫ u₂₃, v₁₃, w₁₃, h₁₃,
            Or.inr ⟨GZ, by omega, ?_, fun _ j ↦ ?_⟩⟩
          · -- GZ.phiPlus ≤ 0: first phase comes from GY'
            change GZ.φ ⟨0, by omega⟩ ≤ 0
            simp only [GZ, HNFiltration.appendFactor, dif_pos hGY']
            exact hGY'_le
          · -- Phase bound: F.φ(n-1) ≤ GZ.φ j
            change F.φ ⟨F.n - 1, by omega⟩ ≤ GZ.φ j
            simp only [GZ, HNFiltration.appendFactor]
            split_ifs with hj
            · exact le_of_lt (hφlast_lt ⟨j.val, hj⟩)
            · exact le_rfl

/-- A slicing on a triangulated category determines a t-structure.

The convention is:
- `le n = gtProp(-n)`: objects whose HN phases are all `> -n`
- `ge n = leProp(1-n)`: objects whose HN phases are all `≤ 1-n`

This ensures `le 0 = gtProp(0)` (phases `> 0`) and `ge 1 = leProp(0)` (phases `≤ 0`),
with the heart being `P((0,1])`. -/
def Slicing.toTStructure (s : Slicing C) : TStructure C where
  le n := s.gtProp C (-↑n)
  ge n := s.leProp C (1 - ↑n)
  le_isClosedUnderIsomorphisms _ := inferInstance
  ge_isClosedUnderIsomorphisms _ := inferInstance
  le_shift n a n' h X hX := by
    show s.gtProp C (-↑n') (X⟦a⟧)
    have hcast : (↑a : ℝ) + ↑n' = ↑n := by exact_mod_cast h
    have : (-↑n' : ℝ) = -↑n + ↑a := by linarith
    rw [this]
    exact s.gtProp_shift C _ X a hX
  ge_shift n a n' h X hX := by
    show s.leProp C (1 - ↑n') (X⟦a⟧)
    have hcast : (↑a : ℝ) + ↑n' = ↑n := by exact_mod_cast h
    have : (1 - ↑n' : ℝ) = (1 - ↑n) + ↑a := by linarith
    rw [this]
    exact s.leProp_shift C _ X a hX
  zero' {X Y} f hX hY := by
    have hX' : s.gtProp C 0 X := by
      simpa [show (-↑(0 : ℤ) : ℝ) = 0 from by norm_num] using hX
    have hY' : s.leProp C 0 Y := by
      simpa [show (1 - ↑(1 : ℤ) : ℝ) = 0 from by norm_num] using hY
    exact s.zero_of_gtProp_leProp C hX' hY' f
  le_zero_le := by
    show s.gtProp C (-↑(0 : ℤ)) ≤ s.gtProp C (-↑(1 : ℤ))
    simp only [Int.cast_zero, neg_zero, Int.cast_one]
    exact s.gtProp_anti C (by norm_num : (-1 : ℝ) ≤ 0)
  ge_one_le := by
    show s.leProp C (1 - ↑(1 : ℤ)) ≤ s.leProp C (1 - ↑(0 : ℤ))
    simp only [Int.cast_one, sub_self, Int.cast_zero, sub_zero]
    exact s.leProp_mono C (by norm_num : (0 : ℝ) ≤ 1)
  exists_triangle_zero_one A := by
    obtain ⟨F⟩ := s.hn_exists A
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := Slicing.tStructureAux C s A F
    refine ⟨X, Y, ?_, ?_, f, g, h, hT⟩
    · simp only [Int.cast_zero, neg_zero]; exact hX
    · simp only [Int.cast_one, sub_self]; exact hY

end Slicing

end CategoryTheory.Triangulated
