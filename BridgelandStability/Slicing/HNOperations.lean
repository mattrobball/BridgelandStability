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

Appending factors via triangles, chain-object subcategory predicates,
and closure of subcategory predicates under isomorphisms.

Core operations (`prefix`, `ofIso`, `shiftHN`) are in `Slicing.Defs`.
-/

/-- The prefix of an HN filtration with phases > t gives a filtration with all phases > t. -/
lemma HNFiltration.prefix_phiMinus_gt {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, t < F.φ ⟨j.val, by lia⟩) :
    t < (F.prefix C k hk hk0).phiMinus C hk0 := by
  simp only [HNFiltration.phiMinus, HNFiltration.prefix_φ]
  exact ht ⟨k - 1, by lia⟩

/-- The chain object at the split point satisfies `gtProp t` if all phases before
the split are > t. -/
lemma HNFiltration.chain_obj_gtProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, t < F.φ ⟨j.val, by lia⟩) :
    s.gtProp C t (F.chain.obj ⟨k, by lia⟩) :=
  Or.inr ⟨F.prefix C k hk hk0, hk0, F.prefix_phiMinus_gt C k hk hk0 t ht⟩

/-- The chain object at the split point satisfies `leProp t` if all phases before
the split are ≤ t. -/
lemma HNFiltration.chain_obj_leProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, F.φ ⟨j.val, by lia⟩ ≤ t) :
    s.leProp C t (F.chain.obj ⟨k, by lia⟩) := by
  refine Or.inr ⟨F.prefix C k hk hk0, hk0, ?_⟩
  simp only [HNFiltration.phiPlus, HNFiltration.prefix_φ]
  exact ht ⟨0, by lia⟩

/-- The chain object at the split point satisfies `ltProp t` if all phases before
the split are < t. -/
lemma HNFiltration.chain_obj_ltProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, F.φ ⟨j.val, by lia⟩ < t) :
    s.ltProp C t (F.chain.obj ⟨k, by lia⟩) := by
  refine Or.inr ⟨F.prefix C k hk hk0, hk0, ?_⟩
  simp only [HNFiltration.phiPlus, HNFiltration.prefix_φ]
  exact ht ⟨0, by lia⟩

/-- The chain object at the split point satisfies `geProp t` if all phases before
the split are ≥ t. -/
lemma HNFiltration.chain_obj_geProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk0 : 0 < k) (t : ℝ)
    (ht : ∀ j : Fin k, t ≤ F.φ ⟨j.val, by lia⟩) :
    s.geProp C t (F.chain.obj ⟨k, by lia⟩) := by
  refine Or.inr ⟨F.prefix C k hk hk0, hk0, ?_⟩
  simp only [HNFiltration.phiMinus, HNFiltration.prefix_φ]
  exact ht ⟨k - 1, by lia⟩

/-- An HN-filtered object satisfies `gtProp t` if all its phases are > t. -/
lemma Slicing.gtProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ)
    (ht : ∀ j, t < F.φ j) (hn : 0 < F.n) :
    s.gtProp C t E := by
  refine Or.inr ⟨F, hn, ?_⟩
  simp only [HNFiltration.phiMinus]
  exact ht ⟨F.n - 1, by lia⟩

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
  exact ht ⟨F.n - 1, by lia⟩

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
    fun i ↦ if h : i.val ≤ G.n then G.chain.obj ⟨i.val, by lia⟩ else Z
  let lastMor : G.chain.obj (Fin.last G.n) ⟶ Z :=
    (Classical.choice G.top_iso).hom ≫ eT₁.inv ≫ T.mor₁ ≫ eT₂.hom
  have mapSuccFn : ∀ (i : Fin (G.n + 1)), objFn (Fin.castSucc i) ⟶ objFn (Fin.succ i) := by
    intro ⟨i, hi⟩
    simp only [objFn, Fin.castSucc_mk, Fin.succ_mk]
    by_cases h1 : i + 1 ≤ G.n
    · simp only [show i ≤ G.n from by lia, h1, dite_true]
      exact G.chain.map' i (i + 1) (by lia) (by lia)
    · simp only [show i ≤ G.n from by lia, h1, dite_true, dite_false]
      exact eqToHom (by congr 1; ext; simp [Fin.val_last]; lia) ≫ lastMor
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
          (ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj ⟨k, by lia⟩ =
          G.chain.obj ⟨k, by lia⟩ := fun k hk ↦ by
        simp [ComposableArrows.mkOfObjOfMapSucc_obj, objFn, hk]
      split_ifs with h
      · refine ⟨(Classical.choice (G.triangle_obj₁ ⟨j.val, h⟩)).trans (eqToIso ?_)⟩
        simp only [ComposableArrows.obj']
        exact (newChainObj j.val (by lia)).symm
      · have hj : j.val = G.n := by lia
        refine ⟨eT₁.trans ((Classical.choice G.top_iso).symm.trans (eqToIso ?_))⟩
        change G.chain.obj (Fin.last G.n) =
          (ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj' j.val _
        simp only [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj, objFn,
          show j.val ≤ G.n from by lia, dite_true]
        congr 1; ext; simp [Fin.val_last]; lia
    triangle_obj₂ := fun j ↦ by
      have newChainObj : ∀ k (hk : k ≤ G.n),
          (ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj ⟨k, by lia⟩ =
          G.chain.obj ⟨k, by lia⟩ := fun k hk ↦ by
        simp [ComposableArrows.mkOfObjOfMapSucc_obj, objFn, hk]
      split_ifs with h
      · refine ⟨(Classical.choice (G.triangle_obj₂ ⟨j.val, h⟩)).trans (eqToIso ?_)⟩
        simp only [ComposableArrows.obj']
        exact (newChainObj (j.val + 1) (by lia)).symm
      · refine ⟨eT₂.trans (eqToIso ?_)⟩
        simp only [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj, objFn,
          show ¬(j.val + 1 ≤ G.n) from by lia, dite_false]
    base_isZero := by
      change IsZero ((ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj ⟨0, _⟩)
      simp only [ComposableArrows.mkOfObjOfMapSucc_obj, objFn,
        show (0 : ℕ) ≤ G.n from by lia, dite_true]
      exact G.base_isZero
    top_iso := ⟨by
      change (ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn).obj ⟨G.n + 1, _⟩ ≅ Z
      simp only [ComposableArrows.mkOfObjOfMapSucc_obj, objFn,
        show ¬(G.n + 1 ≤ G.n) from by lia, dite_false]
      exact Iso.refl _⟩
    zero_isZero := fun h ↦ absurd h (by lia)
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
        · exact absurd (lt_trans hab hb') (by lia)
      · by_cases ha' : a < G.n
        · simp only [hb', ha', dite_true, dite_false]
          exact hψ_lt ⟨a, ha'⟩
        · lia
    semistable := fun j ↦ by
      change (P (if h : j.val < G.n then G.φ ⟨j.val, h⟩ else ψ))
        ((if h : j.val < G.n then G.triangle ⟨j.val, h⟩ else T).obj₃)
      split_ifs with h
      · exact G.semistable ⟨j.val, h⟩
      · exact hψ }

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
