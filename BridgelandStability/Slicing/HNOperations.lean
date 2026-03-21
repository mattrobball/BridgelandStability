/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Slicing.Basic

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


/-!
# HN Filtration Operations

Prefix HN filtrations, appending factors via triangles, transporting via isomorphisms,
shift, and closure of subcategory predicates under isomorphisms.
-/

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

/-- The chain object at the split point satisfies `ltProp t` if all phases before
the split are < t. -/
lemma HNFiltration.chain_obj_ltProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, F.φ ⟨j.val, by omega⟩ < t) :
    s.ltProp C t (F.chain.obj ⟨k, by omega⟩) := by
  refine Or.inr ⟨F.prefix C k hk hk0, hk0, ?_⟩
  simp only [HNFiltration.phiPlus, HNFiltration.prefix_φ]
  exact ht ⟨0, by omega⟩

/-- The chain object at the split point satisfies `geProp t` if all phases before
the split are ≥ t. -/
lemma HNFiltration.chain_obj_geProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, t ≤ F.φ ⟨j.val, by omega⟩) :
    s.geProp C t (F.chain.obj ⟨k, by omega⟩) := by
  refine Or.inr ⟨F.prefix C k hk hk0, hk0, ?_⟩
  simp only [HNFiltration.phiMinus, HNFiltration.prefix_φ]
  exact ht ⟨k - 1, by omega⟩

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

/-- An HN-filtered object satisfies `geProp t` if all its phases are ≥ t. -/
lemma Slicing.geProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ)
    (ht : ∀ j, t ≤ F.φ j) (hn : 0 < F.n) :
    s.geProp C t E := by
  refine Or.inr ⟨F, hn, ?_⟩
  simp only [HNFiltration.phiMinus]
  exact ht ⟨F.n - 1, by omega⟩

/-- An HN-filtered object satisfies `ltProp t` if all its phases are < t. -/
lemma Slicing.ltProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ)
    (ht : ∀ j, F.φ j < t) (hn : 0 < F.n) :
    s.ltProp C t E := by
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
      exact eqToHom (by congr 1; ext; grind) ≫ lastMor
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
        congr 1; ext; grind
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

/-- The property `P(< t)` is closed under isomorphisms. -/
instance Slicing.ltProp_closedUnderIso (s : Slicing C) (t : ℝ) :
    (s.ltProp C t).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    rcases hE with hZ | ⟨F, hF, hlt⟩
    · exact Or.inl (IsZero.of_iso hZ e.symm)
    · exact Or.inr ⟨F.ofIso C e, hF, hlt⟩

/-- The property `P(≥ t)` is closed under isomorphisms. -/
instance Slicing.geProp_closedUnderIso (s : Slicing C) (t : ℝ) :
    (s.geProp C t).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    rcases hE with hZ | ⟨F, hF, hge⟩
    · exact Or.inl (IsZero.of_iso hZ e.symm)
    · exact Or.inr ⟨F.ofIso C e, hF, hge⟩


end Slicing

end CategoryTheory.Triangulated
