/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.PostnikovTower.Defs
public meta import Informal
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
# Slicing Definitions

Core data-carrying declarations for Bridgeland slicings: the `HNFiltration` and `Slicing`
structures, the intrinsic phase functions `φ⁺`/`φ⁻`, and supporting HN filtration operations
(prefix, shift, transport, drop, existence of nonzero factors).

These definitions are separated from the full proof files so that downstream modules
(stability conditions, topology, Euler form) can import lightweight type-level dependencies
without pulling in hom-vanishing proofs and interval subcategory theory.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

/-! ### Grind annotations for arithmetic automation -/

-- Forward reasoning: monotonicity + order hypothesis → derived inequality
attribute [grind →] StrictAnti.imp
attribute [grind →] StrictMono.imp
attribute [grind →] Antitone.imp
attribute [grind →] Monotone.imp

namespace CategoryTheory.Triangulated

section Slicing

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Core structures -/

-- ANCHOR: CategoryTheory.Triangulated.HNFiltration
/-- A Harder-Narasimhan (HN) filtration of an object `E` with respect to a phase
predicate `P`. This extends a `PostnikovTower` with phase data: each factor is
semistable with a given phase, and the phases are strictly decreasing. -/
@[informal "Definition 3.3" "axiom (c): HN decomposition data for triangulated categories"]
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C) extends PostnikovTower C E where
  /-- The phases of the semistable factors, in strictly decreasing order. -/
  φ : Fin n → ℝ
  /-- The phases are strictly decreasing (higher phase factors appear first). -/
  hφ : StrictAnti φ
  /-- Each factor is semistable of the given phase. -/
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j)
-- ANCHOR_END: CategoryTheory.Triangulated.HNFiltration

-- ANCHOR: CategoryTheory.Triangulated.Slicing
/-- A slicing of a pretriangulated category `C`, as defined in
Bridgeland (2007), Definition 5.1. A slicing assigns to each real number `φ`
a full subcategory of semistable objects `P(φ)` (as an `ObjectProperty`),
subject to shift, Hom-vanishing, and Harder-Narasimhan existence axioms.

Each `P(φ)` is an `ObjectProperty C`, enabling use of the `ObjectProperty` API
(e.g. `FullSubcategory`, shift stability, closure properties). -/
@[informal "Definition 3.3"]
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
-- ANCHOR_END: CategoryTheory.Triangulated.Slicing

attribute [instance] Slicing.closedUnderIso

@[ext] theorem Slicing.ext {s t : Slicing C} (hP : s.P = t.P) : s = t := by
  rcases s with ⟨Ps, hsIso, hsZero, hsShift, hsHom, hsHN⟩
  rcases t with ⟨Pt, htIso, htZero, htShift, htHom, htHN⟩
  change Ps = Pt at hP
  cases hP
  simp

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

/-! ### Shift lemmas -/

/-- Forward shift by a natural number: if `(P φ) X` then `(P (φ + n)) (X⟦n⟧)`. -/
lemma Slicing.shift_nat (s : Slicing C) (φ : ℝ) (X : C) (n : ℕ) :
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
      ((shiftFunctorAdd' C (↑n : ℤ) 1 ((↑n : ℤ) + 1) (by lia)).app X).symm h1

/-- Backward shift by a natural number: if `(P (φ + n)) (X⟦n⟧)` then `(P φ) X`. -/
lemma Slicing.unshift_nat (s : Slicing C) (φ : ℝ) (X : C) (n : ℕ) :
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
      ((shiftFunctorAdd' C (↑n : ℤ) 1 ((↑n : ℤ) + 1) (by lia)).app X) h
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
      (shiftFunctorAdd' C (Int.negSucc m) ((m + 1 : ℕ) : ℤ) 0 (by lia)).app X
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
  F.φ ⟨F.n - 1, by lia⟩

-- ANCHOR: CategoryTheory.Triangulated.Slicing.intervalProp
/-- The interval subcategory predicate `P((a,b))`: an object `E` belongs to the
interval subcategory if it is zero or all phases in its HN filtration lie in `(a,b)`. -/
def Slicing.intervalProp (s : Slicing C) (a b : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (F : HNFiltration C s.P E), ∀ i, a < F.φ i ∧ F.φ i < b
-- ANCHOR_END: CategoryTheory.Triangulated.Slicing.intervalProp

/-! ### HN filtration operations -/

/-- Extract the first `k` factors from an HN filtration, giving a filtration
of the `k`-th chain object with phases `φ₀ > ⋯ > φ_{k-1}`. -/
def HNFiltration.prefix {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) :
    HNFiltration C P (F.chain.obj ⟨k, by lia⟩) :=
  { n := k
    chain := ComposableArrows.mkOfObjOfMapSucc
      (fun i : Fin (k + 1) ↦ F.chain.obj ⟨i.val, by lia⟩)
      (fun i : Fin k ↦ F.chain.map' i.val (i.val + 1) (by lia) (by lia))
    triangle := fun j ↦ F.triangle ⟨j.val, by lia⟩
    triangle_dist := fun j ↦ F.triangle_dist ⟨j.val, by lia⟩
    triangle_obj₁ := fun j ↦ F.triangle_obj₁ ⟨j.val, by lia⟩
    triangle_obj₂ := fun j ↦ F.triangle_obj₂ ⟨j.val, by lia⟩
    base_isZero := F.base_isZero
    top_iso := ⟨Iso.refl _⟩
    zero_isZero := fun h ↦ absurd h (by lia)
    φ := fun j ↦ F.φ ⟨j.val, by lia⟩
    hφ := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ (hab : a < b)
      exact F.hφ (show (⟨a, by lia⟩ : Fin F.n) < ⟨b, by lia⟩ from hab)
    semistable := fun j ↦ F.semistable ⟨j.val, by lia⟩ }

/-- The prefix filtration has all the original phases up to index `k`. -/
@[simp]
lemma HNFiltration.prefix_φ {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k)
    (j : Fin k) : (F.prefix C k hk hk0).φ j = F.φ ⟨j.val, by lia⟩ := rfl

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

/-! ### Existence of nonzero factors and intrinsic phases -/

/-- For a nonzero object, any HN filtration has at least one factor. -/
lemma HNFiltration.n_pos {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hE : ¬IsZero E) : 0 < F.n := by
  by_contra h
  push Not at h
  exact hE (F.zero_isZero (by lia))

/-- For any HN filtration of a nonzero object, at least one factor is nonzero.
If all factors were zero, the chain would start and end at zero, contradicting E nonzero. -/
lemma HNFiltration.exists_nonzero_factor {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hE : ¬IsZero E) :
    ∃ (i : Fin F.n), ¬IsZero (F.triangle i).obj₃ := by
  by_contra hall
  push Not at hall
  -- All factors are zero. Show chain(k) ≅ 0 for all k by induction.
  suffices ∀ (k : ℕ) (hk : k < F.n + 1), IsZero (F.chain.obj ⟨k, hk⟩) by
    exact hE (IsZero.of_iso (this F.n (by lia)) (Classical.choice F.top_iso).symm)
  intro k hk
  induction k with
  | zero => exact F.base_isZero
  | succ k ih =>
    have hkn : k < F.n := by lia
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
      (ih (by lia)).of_iso e₁
    -- Since mor₁ is an iso and obj₁ is zero, obj₂ is zero
    have h2 : IsZero Tk.obj₂ := by
      -- obj₂ is zero: the iso mor₁ : obj₁ ≅ obj₂ transports the zero property
      exact h1.of_iso (asIso Tk.mor₁).symm
    exact h2.of_iso e₂.symm

/-- Drop the first factor from an HN filtration when it is zero. The resulting
filtration has `n - 1` factors with phases `φ(1) > ⋯ > φ(n-1)`. -/
def HNFiltration.dropFirst {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hn : 1 < F.n)
    (hzero : IsZero (F.triangle ⟨0, by lia⟩).obj₃) :
    HNFiltration C P E :=
  -- chain(0) = 0 and factor(0) = 0 imply chain(1) ≅ 0 (new base)
  have h0 : 0 < F.n := by lia
  let T0 := F.triangle ⟨0, h0⟩
  have hiso0 : IsIso T0.mor₁ :=
    (Triangle.isZero₃_iff_isIso₁ T0 (F.triangle_dist ⟨0, h0⟩)).mp hzero
  have chain1_zero : IsZero (F.chain.obj ⟨1, by lia⟩) :=
    (F.base_isZero.of_iso (Classical.choice (F.triangle_obj₁ ⟨0, h0⟩))).of_iso
      (asIso T0.mor₁).symm |>.of_iso (Classical.choice (F.triangle_obj₂ ⟨0, h0⟩)).symm
  have heq : F.n - 1 + 1 = F.n := by lia
  { n := F.n - 1
    chain := ComposableArrows.mkOfObjOfMapSucc
      (fun i : Fin (F.n - 1 + 1) ↦ F.chain.obj ⟨i.val + 1, by lia⟩)
      (fun i : Fin (F.n - 1) ↦ F.chain.map' (i.val + 1) (i.val + 2) (by lia) (by lia))
    triangle := fun j ↦ F.triangle ⟨j.val + 1, by lia⟩
    triangle_dist := fun j ↦ F.triangle_dist ⟨j.val + 1, by lia⟩
    triangle_obj₁ := fun j ↦ by
      refine ⟨(Classical.choice (F.triangle_obj₁ ⟨j.val + 1, by lia⟩)).trans
        (eqToIso ?_)⟩
      simp [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj]
    triangle_obj₂ := fun j ↦ by
      refine ⟨(Classical.choice (F.triangle_obj₂ ⟨j.val + 1, by lia⟩)).trans
        (eqToIso ?_)⟩
      simp [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj]
    base_isZero := by
      change IsZero ((ComposableArrows.mkOfObjOfMapSucc _ _).obj ⟨0, _⟩)
      simp only [ComposableArrows.map', homOfLE_leOfHom, Fin.zero_eta,
        ComposableArrows.mkOfObjOfMapSucc_obj, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
      exact chain1_zero
    top_iso := ⟨by
      change (ComposableArrows.mkOfObjOfMapSucc _ _).obj ⟨F.n - 1, _⟩ ≅ E
      simp only [ComposableArrows.mkOfObjOfMapSucc_obj]
      exact (eqToIso (by congr 1; ext; lia)).trans (Classical.choice F.top_iso)⟩
    zero_isZero := fun h ↦ by lia
    φ := fun j ↦ F.φ ⟨j.val + 1, by lia⟩
    hφ := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ (hab : a < b)
      exact F.hφ (show (⟨a + 1, by lia⟩ : Fin F.n) < ⟨b + 1, by lia⟩ from by
        exact Fin.mk_lt_mk.mpr (by lia))
    semistable := fun j ↦ F.semistable ⟨j.val + 1, by lia⟩ }

-- ANCHOR: CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first
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
    exact absurd (G.zero_isZero (by lia)) hE
  | succ m ih =>
    intro G hGn
    have hGn0 : 0 < G.n := G.n_pos C hE
    by_cases hfirst : IsZero (G.triangle ⟨0, hGn0⟩).obj₃
    · -- First factor is zero; drop it and recurse
      have hn1 : 1 < G.n := by
        by_contra h; push Not at h
        have : ∀ (i : Fin G.n), IsZero (G.triangle i).obj₃ := fun i ↦ by
          have : i = ⟨0, hGn0⟩ := Fin.ext (by lia)
          subst this; exact hfirst
        exact absurd ((G.exists_nonzero_factor C hE).elim fun i hi ↦ absurd (this i) hi) id
      have hdrop : (G.dropFirst C hn1 hfirst).n ≤ m := by
        change G.n - 1 ≤ m; lia
      exact ih (G.dropFirst C hn1 hfirst) hdrop
    · exact ⟨G, hGn0, hfirst⟩
-- ANCHOR_END: CategoryTheory.Triangulated.HNFiltration.exists_nonzero_first

/-- Drop the last factor from an HN filtration when it is zero. The resulting
filtration has `n - 1` factors with phases `φ(0) > ⋯ > φ(n-2)`. -/
def HNFiltration.dropLast {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hn : 1 < F.n)
    (hzero : IsZero (F.triangle ⟨F.n - 1, by lia⟩).obj₃) :
    HNFiltration C P E :=
  have hn0 : 0 < F.n := by lia
  let Tn := F.triangle ⟨F.n - 1, by lia⟩
  have hiso : IsIso Tn.mor₁ :=
    (Triangle.isZero₃_iff_isIso₁ Tn (F.triangle_dist ⟨F.n - 1, by lia⟩)).mp hzero
  -- chain(n-1) ≅ chain(n) ≅ E via mor₁ and top_iso
  let e₁ := Classical.choice (F.triangle_obj₁ ⟨F.n - 1, by lia⟩)
  let e₂ := Classical.choice (F.triangle_obj₂ ⟨F.n - 1, by lia⟩)
  -- The new top_iso: prefix's chain(n-1) = F.chain.obj(n-1) ≅ chain(n) ≅ E
  let pfx := F.prefix C (F.n - 1) (by lia) (by lia)
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
          simp only [ComposableArrows.obj']
          congr 1; ext; lia)).trans
          (Classical.choice F.top_iso)))))⟩
    zero_isZero := fun h ↦ by lia
    φ := pfx.φ
    hφ := pfx.hφ
    semistable := pfx.semistable }

-- ANCHOR: CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last
/-- For any nonzero object, there exists an HN filtration with nonzero last factor.
Proved by repeatedly dropping zero last factors. -/
lemma HNFiltration.exists_nonzero_last (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.triangle ⟨F.n - 1, by lia⟩).obj₃ := by
  obtain ⟨F⟩ := s.hn_exists E
  suffices hmain : ∀ (m : ℕ) (G : HNFiltration C s.P E), G.n ≤ m →
      ∃ (H : HNFiltration C s.P E) (hn : 0 < H.n),
        ¬IsZero (H.triangle ⟨H.n - 1, by lia⟩).obj₃ from
    hmain F.n F le_rfl
  intro m
  induction m with
  | zero =>
    intro G hGn
    exact absurd (G.zero_isZero (by lia)) hE
  | succ m ih =>
    intro G hGn
    have hGn0 : 0 < G.n := G.n_pos C hE
    by_cases hlast : IsZero (G.triangle ⟨G.n - 1, by lia⟩).obj₃
    · have hn1 : 1 < G.n := by
        by_contra h; push Not at h
        have : ∀ (i : Fin G.n), IsZero (G.triangle i).obj₃ := fun i ↦ by
          have : i = ⟨G.n - 1, by lia⟩ := Fin.ext (by lia)
          subst this; exact hlast
        exact absurd ((G.exists_nonzero_factor C hE).elim fun i hi ↦ absurd (this i) hi) id
      have hdrop : (G.dropLast C hn1 hlast).n ≤ m := by
        change G.n - 1 ≤ m; lia
      exact ih (G.dropLast C hn1 hlast) hdrop
    · exact ⟨G, hGn0, hlast⟩
-- ANCHOR_END: CategoryTheory.Triangulated.HNFiltration.exists_nonzero_last

/-! ### Intrinsic phase definitions -/

-- ANCHOR: CategoryTheory.Triangulated.Slicing.phiPlus
/-- The intrinsic highest phase of a nonzero object with respect to a slicing.
This is the phase of the first factor in any HN filtration with nonzero first factor.
Well-defined by `phiPlus_eq_of_nonzero_factors`. -/
noncomputable def Slicing.phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_first C s hE).choose
  let hn := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  F.φ ⟨0, hn⟩
-- ANCHOR_END: CategoryTheory.Triangulated.Slicing.phiPlus

-- ANCHOR: CategoryTheory.Triangulated.Slicing.phiMinus
/-- The intrinsic lowest phase of a nonzero object with respect to a slicing.
This is the phase of the last factor in any HN filtration with nonzero last factor.
Well-defined by `phiMinus_eq_of_nonzero_last_factors`. -/
noncomputable def Slicing.phiMinus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_last C s hE).choose
  let hn : 0 < F.n := (HNFiltration.exists_nonzero_last C s hE).choose_spec.choose
  F.φ ⟨F.n - 1, Nat.sub_one_lt_of_le hn le_rfl⟩
-- ANCHOR_END: CategoryTheory.Triangulated.Slicing.phiMinus

end Slicing

end CategoryTheory.Triangulated
