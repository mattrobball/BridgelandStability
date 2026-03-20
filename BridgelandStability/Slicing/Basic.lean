/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.PostnikovTower
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

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
  (defined in `IntervalCategory.lean`, once the thin interval exact structure is available)

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
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

/-- The subcategory predicate `P(< t)`: an object `E` satisfies this if it is zero or
all phases in some HN filtration of `E` are `< t`. -/
def Slicing.ltProp (s : Slicing C) (t : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E) (h : 0 < F.n),
    F.phiPlus C h < t

/-- The subcategory predicate `P(≥ t)`: an object `E` satisfies this if it is zero or
all phases in some HN filtration of `E` are `≥ t`. -/
def Slicing.geProp (s : Slicing C) (t : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E) (h : 0 < F.n),
    t ≤ F.phiMinus C h

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

/-- Zero objects are in `P(< t)` for all `t`. -/
lemma Slicing.ltProp_zero (s : Slicing C) (t : ℝ) :
    s.ltProp C t (0 : C) :=
  Or.inl (isZero_zero C)

/-- Zero objects are in `P(≥ t)` for all `t`. -/
lemma Slicing.geProp_zero (s : Slicing C) (t : ℝ) :
    s.geProp C t (0 : C) :=
  Or.inl (isZero_zero C)

/-- `P(< t₁) ≤ P(< t₂)` when `t₁ ≤ t₂`. -/
lemma Slicing.ltProp_mono (s : Slicing C) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    s.ltProp C t₁ ≤ s.ltProp C t₂ := by
  intro E hE
  rcases hE with hZ | ⟨F, hF, hlt⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨F, hF, lt_of_lt_of_le hlt h⟩

/-- `P(≥ t₂) ≤ P(≥ t₁)` when `t₁ ≤ t₂`. -/
lemma Slicing.geProp_anti (s : Slicing C) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    s.geProp C t₂ ≤ s.geProp C t₁ := by
  intro E hE
  rcases hE with hZ | ⟨F, hF, hge⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨F, hF, le_trans h hge⟩

/-- `P(< t) ⊆ P(≤ t)` (strict upper bound implies non-strict). -/
lemma Slicing.leProp_of_ltProp (s : Slicing C) {t : ℝ} :
    s.ltProp C t ≤ s.leProp C t := by
  intro E hE
  rcases hE with hZ | ⟨F, hF, hlt⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨F, hF, le_of_lt hlt⟩

/-- `P(> t) ⊆ P(≥ t)` (strict lower bound implies non-strict). -/
lemma Slicing.geProp_of_gtProp (s : Slicing C) {t : ℝ} :
    s.gtProp C t ≤ s.geProp C t := by
  intro E hE
  rcases hE with hZ | ⟨F, hF, hgt⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨F, hF, le_of_lt hgt⟩

/-- `P((a, b)) ⊆ P(< b)` (interval containment gives strict upper bound). -/
lemma Slicing.ltProp_of_intervalProp (s : Slicing C) {a b : ℝ} {E : C}
    (hI : s.intervalProp C a b E) : s.ltProp C b E := by
  rcases hI with hZ | ⟨F, hF⟩
  · exact Or.inl hZ
  · by_cases hn : 0 < F.n
    · exact Or.inr ⟨F, hn, (hF ⟨0, hn⟩).2⟩
    · exact Or.inl (F.toPostnikovTower.zero_isZero (by omega))


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


end Slicing

end CategoryTheory.Triangulated
