/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Slicing.ExtensionClosure

/-!
# T-Structure from a Slicing

Single-factor HN filtrations, phase-shifted slicings, and construction of a
bounded t-structure from a slicing.
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

/-! ### Single-factor HN filtrations -/

/-- Construct a 0-factor HN filtration on a zero object. -/
def HNFiltration.zero {P : ℝ → ObjectProperty C} (E : C) (hE : IsZero E) :
    HNFiltration C P E where
  n := 0
  chain := ComposableArrows.mk₀ E
  triangle := fun i ↦ nomatch i
  triangle_dist := fun i ↦ nomatch i
  triangle_obj₁ := fun i ↦ nomatch i
  triangle_obj₂ := fun i ↦ nomatch i
  base_isZero := by simpa [ComposableArrows.left] using hE
  top_iso := ⟨by simpa [ComposableArrows.right] using Iso.refl E⟩
  zero_isZero := fun _ ↦ hE
  φ := fun i ↦ nomatch i
  hφ := by
    intro i
    nomatch i
  semistable := by
    intro i
    nomatch i

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
  zero_isZero := fun h ↦ absurd h (by grind)
  φ := fun _ ↦ φ
  hφ := fun i j h ↦ absurd h (by grind)
  semistable := fun j ↦ by
    have : j = ⟨0, by grind⟩ := Fin.ext (by grind)
    subst this; exact hS

/-- A semistable object of phase `≤ t` satisfies `leProp t`. -/
lemma Slicing.leProp_of_semistable (s : Slicing C) (φ t : ℝ) (S : C)
    (hS : (s.P φ) S) (hle : φ ≤ t) :
    s.leProp C t S :=
  Or.inr ⟨HNFiltration.single C S φ hS,
    show 0 < 1 from by grind, hle⟩

/-- A semistable object of phase `> t` satisfies `gtProp t`. -/
lemma Slicing.gtProp_of_semistable (s : Slicing C) (φ t : ℝ) (S : C)
    (hS : (s.P φ) S) (hgt : t < φ) :
    s.gtProp C t S :=
  Or.inr ⟨HNFiltration.single C S φ hS,
    show 0 < 1 from by grind, hgt⟩

/-- For a semistable nonzero object, `phiPlus = phiMinus = φ`. -/
theorem Slicing.phiPlus_eq_phiMinus_of_semistable (s : Slicing C) {E : C} {φ : ℝ}
    (hS : (s.P φ) E) (hE : ¬IsZero E) :
    s.phiPlus C E hE = φ ∧ s.phiMinus C E hE = φ := by
  let F := HNFiltration.single C E φ hS
  have hn : (0 : ℕ) < F.n := by change 0 < 1; grind
  have hne : ¬IsZero (F.triangle ⟨0, hn⟩).obj₃ := by
    change ¬IsZero (Triangle.mk (0 : (0 : C) ⟶ E) (𝟙 E) 0).obj₃
    exact hE
  constructor
  · exact s.phiPlus_eq C E hE F hn hne
  · have hneL : ¬IsZero (F.triangle ⟨F.n - 1, by grind⟩).obj₃ := by
      change ¬IsZero (F.triangle ⟨0, hn⟩).obj₃; exact hne
    exact s.phiMinus_eq C E hE F hn hneL

/-- **Converse of `phiPlus_eq_phiMinus_of_semistable`**: if `phiPlus(E) = phiMinus(E)` for
a nonzero object, then `E` is semistable of phase `phiPlus(E)`. The proof uses the
single-factor argument: equal extreme phases + strict antitonicity forces `n = 1`,
so the unique HN factor is isomorphic to `E`. -/
theorem Slicing.semistable_of_phiPlus_eq_phiMinus (s : Slicing C) {E : C}
    (hE : ¬IsZero E) (heq : s.phiPlus C E hE = s.phiMinus C E hE) :
    (s.P (s.phiPlus C E hE)) E := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C s hE
  have h0 := (s.phiPlus_eq C E hE F hn hfirst).symm
  have hn1 := (s.phiMinus_eq C E hE F hn hlast).symm
  -- StrictAnti + equal endpoints → n = 1
  have hn_eq : F.n = 1 := by
    by_contra h
    have hn' : F.n - 1 < F.n := by grind
    exact absurd (by rw [h0, hn1, ← heq] : F.φ ⟨0, hn⟩ = F.φ ⟨F.n - 1, hn'⟩)
      (ne_of_gt (F.hφ (Fin.mk_lt_mk.mpr (by grind))))
  -- T.obj₁ is zero, so T.mor₂ is an isomorphism
  let T := F.triangle ⟨0, hn⟩
  have hZ1 : IsZero T.obj₁ :=
    IsZero.of_iso F.base_isZero (Classical.choice (F.triangle_obj₁ ⟨0, hn⟩))
  have : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist ⟨0, hn⟩)).mp hZ1
  -- T.obj₂ ≅ chain(1) = chain.right ≅ E
  have hobj₂_eq : F.chain.obj' (0 + 1) (by grind) = F.chain.obj (Fin.last F.n) :=
    congrArg F.chain.obj (Fin.ext (by simp [Fin.last]; omega))
  let e₂E : T.obj₂ ≅ E :=
    (Classical.choice (F.triangle_obj₂ ⟨0, hn⟩)).trans
      ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
  -- E ≅ T.obj₃ (the factor), which is semistable of phase phiPlus(E)
  exact (s.P _).prop_of_iso (e₂E.symm.trans (asIso T.mor₂)).symm
    (by rw [← h0]; exact F.semistable ⟨0, hn⟩)

/-- **Extension-closure of the semistable subcategory**. If `A` and `B` are both
`P(φ)`-semistable, and `A → E → B → A⟦1⟧` is a distinguished triangle, then `E`
is also `P(φ)`-semistable. The proof uses `phiPlus_lt_of_triangle` and
`phiMinus_gt_of_triangle` to pin `phiPlus(E) = phiMinus(E) = φ`, then invokes
`semistable_of_phiPlus_eq_phiMinus`. -/
lemma Slicing.semistable_of_triangle (s : Slicing C) {A E B : C} (φ : ℝ)
    (hA : (s.P φ) A) (hB : (s.P φ) B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    (s.P φ) E := by
  by_cases hEZ : IsZero E
  · exact s.zero_mem' C φ E hEZ
  -- phiPlus(E) ≤ φ (by contradiction via phiPlus_lt_of_triangle)
  have hle : s.phiPlus C E hEZ ≤ φ := by
    by_contra hgt; push_neg at hgt
    exact absurd
      (s.phiPlus_lt_of_triangle C hEZ
        (fun hA' ↦ lt_of_eq_of_lt
          (s.phiPlus_eq_phiMinus_of_semistable C hA hA').1 hgt)
        (fun hB' ↦ lt_of_eq_of_lt
          (s.phiPlus_eq_phiMinus_of_semistable C hB hB').1 hgt) hT)
      (lt_irrefl _)
  -- φ ≤ phiMinus(E) (by contradiction via phiMinus_gt_of_triangle)
  have hge : φ ≤ s.phiMinus C E hEZ := by
    by_contra hlt; push_neg at hlt
    exact absurd
      (s.phiMinus_gt_of_triangle C hEZ
        (fun hA' ↦ by
          rw [(s.phiPlus_eq_phiMinus_of_semistable C hA hA').2]; exact hlt)
        (fun hB' ↦ by
          rw [(s.phiPlus_eq_phiMinus_of_semistable C hB hB').2]; exact hlt)
        hT)
      (lt_irrefl _)
  -- phiPlus = phiMinus = φ, hence semistable
  have h_eq : s.phiPlus C E hEZ = φ :=
    le_antisymm hle (le_trans hge (s.phiMinus_le_phiPlus C E hEZ))
  rw [← h_eq]
  exact s.semistable_of_phiPlus_eq_phiMinus C hEZ
    (le_antisymm (le_trans hle hge) (s.phiMinus_le_phiPlus C E hEZ))

/-- If all factors in an HN filtration have the same phase `φ`, then `E` is
`P(φ)`-semistable. The proof goes by induction along the chain, using
`semistable_of_triangle` at each step and `prop_of_iso` to transfer across
the structural isomorphisms. -/
lemma Slicing.semistable_of_HN_all_eq (s : Slicing C) {E : C} {φ : ℝ}
    (F : HNFiltration C s.P E) (hall : ∀ i : Fin F.n, F.φ i = φ) :
    (s.P φ) E := by
  by_cases hE : IsZero E
  · exact s.zero_mem' C φ E hE
  -- Each chain object is P(φ)-semistable, by induction on the chain index
  have hchain : ∀ k (hk : k ≤ F.n), (s.P φ) (F.chain.obj' k (by grind)) := by
    intro k hk
    induction k with
    | zero => exact s.zero_mem' C φ _ F.base_isZero
    | succ k ih =>
      have hkn : k < F.n := by grind
      let T := F.triangle ⟨k, hkn⟩
      -- T.obj₁ ≅ chain(k), T.obj₃ = factor(k) ∈ P(φ)
      have hT1 : (s.P φ) T.obj₁ :=
        (s.P φ).prop_of_iso (Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)).symm
          (ih (by grind))
      have hT3 : (s.P φ) T.obj₃ := by rw [← hall ⟨k, hkn⟩]; exact F.semistable ⟨k, hkn⟩
      -- By semistable_of_triangle: T.obj₂ ∈ P(φ)
      have hT2 : (s.P φ) T.obj₂ :=
        s.semistable_of_triangle C φ hT1 hT3 (F.triangle_dist ⟨k, hkn⟩)
      -- Transfer to chain(k+1) via triangle_obj₂
      exact (s.P φ).prop_of_iso (Classical.choice (F.triangle_obj₂ ⟨k, hkn⟩))
        hT2
  -- chain.right ∈ P(φ), then transfer to E
  exact (s.P φ).prop_of_iso (Classical.choice F.top_iso) (hchain F.n le_rfl)

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
    (fun i j ↦ by grind [(Fy.phase_mem_range C hFy j).2, (Fx.phase_mem_range C hFx i).1]) f

/-- Any morphism from an object with all HN phases `≥ 0` to one with all HN phases
`< 0` is zero. This is the vanishing convention needed for the right-heart
half-open interval `[0, 1)`. -/
lemma Slicing.zero_of_geProp_ltProp (s : Slicing C) {X Y : C}
    (hX : s.geProp C 0 X) (hY : s.ltProp C 0 Y) (f : X ⟶ Y) : f = 0 := by
  rcases hX with hXZ | ⟨Fx, hFx, hFx_ge⟩
  · exact hXZ.eq_of_src f 0
  rcases hY with hYZ | ⟨Fy, hFy, hFy_lt⟩
  · exact hYZ.eq_of_tgt f 0
  exact s.hom_eq_zero_of_phase_gap C Fx Fy
    (fun i j ↦ by grind [(Fy.phase_mem_range C hFy j).2, (Fx.phase_mem_range C hFx i).1]) f

/-! ### Phase-shifted slicing

Given a slicing `s` and a real parameter `t`, we define a new slicing `s.phaseShift t`
whose phase-`ψ` subcategory is `s.P(ψ + t)`. This shifts all phases by `-t`:
an object that was semistable of phase `φ` in `s` becomes semistable of phase `φ - t`
in `s.phaseShift t`.

The main application is real-valued truncation: `(s.phaseShift t).toTStructure` gives
a t-structure whose truncation at `0` corresponds to truncation at phase `t` in the
original slicing. This provides `P(> t)` / `P(≤ t)` decompositions for arbitrary
real cutoffs `t`, which is needed for **Lemma 6.4** (local injectivity). -/

/-- An HN filtration with respect to `s.P` can be converted to an HN filtration
with respect to the shifted phase predicate `fun ψ ↦ s.P (ψ + t)`, by subtracting
`t` from all phases. -/
def HNFiltration.phaseShift {s : Slicing C} {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) :
    HNFiltration C (fun ψ ↦ s.P (ψ + t)) E where
  n := F.n
  chain := F.chain
  triangle := F.triangle
  triangle_dist := F.triangle_dist
  triangle_obj₁ := F.triangle_obj₁
  triangle_obj₂ := F.triangle_obj₂
  base_isZero := F.base_isZero
  top_iso := F.top_iso
  zero_isZero := F.zero_isZero
  φ := fun i ↦ F.φ i - t
  hφ := by intro i j hij; change F.φ j - t < F.φ i - t; grind [F.hφ hij]
  semistable := by
    intro i; show s.P (F.φ i - t + t) _
    rw [show F.φ i - t + t = F.φ i from by grind]
    exact F.semistable i

/-- Phase-shifted slicing: `(s.phaseShift t).P ψ = s.P (ψ + t)`. This shifts
all phases down by `t`. -/
def Slicing.phaseShift (s : Slicing C) (t : ℝ) : Slicing C where
  P ψ := s.P (ψ + t)
  closedUnderIso φ := s.closedUnderIso (φ + t)
  zero_mem φ := s.zero_mem (φ + t)
  shift_iff φ X := by
    show s.P (φ + t) X ↔ s.P (φ + 1 + t) (X⟦(1 : ℤ)⟧)
    rw [show φ + 1 + t = (φ + t) + 1 from by grind]
    exact s.shift_iff (φ + t) X
  hom_vanishing φ₁ φ₂ A B h hA hB := by
    exact s.hom_vanishing (φ₁ + t) (φ₂ + t) A B (by grind) hA hB
  hn_exists E := ⟨(s.hn_exists E).some.phaseShift (C := C) t⟩

/-- `gtProp` of a phase-shifted slicing at cutoff `0` equals `gtProp` of the
original slicing at cutoff `t`. -/
theorem Slicing.phaseShift_gtProp_zero (s : Slicing C) (t : ℝ) (E : C) :
    (s.phaseShift C t).gtProp C 0 E ↔ s.gtProp C t E := by
  constructor
  · rintro (hZ | ⟨F, hF, hgt⟩)
    · exact Or.inl hZ
    · -- F has shifted phases; convert to original phases by adding t
      simp only [HNFiltration.phiMinus] at hgt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiMinus]; grind
  · rintro (hZ | ⟨F, hF, hgt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hgt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by grind]
        exact F.semistable j
      · dsimp only [HNFiltration.phiMinus]; grind

/-- `gtProp` of a phase-shifted slicing at cutoff `u` equals `gtProp` of the
original slicing at cutoff `u + t`. -/
theorem Slicing.phaseShift_gtProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).gtProp C u E ↔ s.gtProp C (u + t) E := by
  constructor
  · rintro (hZ | ⟨F, hF, hgt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hgt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiMinus]
      linarith
  · rintro (hZ | ⟨F, hF, hgt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hgt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by grind]
        exact F.semistable j
      · dsimp only [HNFiltration.phiMinus]
        linarith

/-- `leProp` of a phase-shifted slicing at cutoff `0` equals `leProp` of the
original slicing at cutoff `t`. -/
theorem Slicing.phaseShift_leProp_zero (s : Slicing C) (t : ℝ) (E : C) :
    (s.phaseShift C t).leProp C 0 E ↔ s.leProp C t E := by
  constructor
  · rintro (hZ | ⟨F, hF, hle⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiPlus]; grind
  · rintro (hZ | ⟨F, hF, hle⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by grind]
        exact F.semistable j
      · dsimp only [HNFiltration.phiPlus]; grind

/-- `leProp` of a phase-shifted slicing at cutoff `u` equals `leProp` of the
original slicing at cutoff `u + t`. -/
theorem Slicing.phaseShift_leProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).leProp C u E ↔ s.leProp C (u + t) E := by
  constructor
  · rintro (hZ | ⟨F, hF, hle⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiPlus]
      linarith
  · rintro (hZ | ⟨F, hF, hle⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by grind]
        exact F.semistable j
      · dsimp only [HNFiltration.phiPlus]
        linarith

/-- `ltProp` of a phase-shifted slicing at cutoff `0` equals `ltProp` of the
original slicing at cutoff `t`. -/
theorem Slicing.phaseShift_ltProp_zero (s : Slicing C) (t : ℝ) (E : C) :
    (s.phaseShift C t).ltProp C 0 E ↔ s.ltProp C t E := by
  constructor
  · rintro (hZ | ⟨F, hF, hlt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hlt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiPlus]; grind
  · rintro (hZ | ⟨F, hF, hlt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hlt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by grind]
        exact F.semistable j
      · dsimp only [HNFiltration.phiPlus]; grind

/-- `ltProp` of a phase-shifted slicing at cutoff `u` equals `ltProp` of the
original slicing at cutoff `u + t`. -/
theorem Slicing.phaseShift_ltProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).ltProp C u E ↔ s.ltProp C (u + t) E := by
  constructor
  · rintro (hZ | ⟨F, hF, hlt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hlt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiPlus]
      linarith
  · rintro (hZ | ⟨F, hF, hlt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hlt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by grind]
        exact F.semistable j
      · dsimp only [HNFiltration.phiPlus]
        linarith

/-- `geProp` of a phase-shifted slicing at cutoff `0` equals `geProp` of the
original slicing at cutoff `t`. -/
theorem Slicing.phaseShift_geProp_zero (s : Slicing C) (t : ℝ) (E : C) :
    (s.phaseShift C t).geProp C 0 E ↔ s.geProp C t E := by
  constructor
  · rintro (hZ | ⟨F, hF, hge⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hge
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiMinus]; grind
  · rintro (hZ | ⟨F, hF, hge⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hge
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by grind]
        exact F.semistable j
      · dsimp only [HNFiltration.phiMinus]; grind

/-- `geProp` of a phase-shifted slicing at cutoff `u` equals `geProp` of the
original slicing at cutoff `u + t`. -/
theorem Slicing.phaseShift_geProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).geProp C u E ↔ s.geProp C (u + t) E := by
  constructor
  · rintro (hZ | ⟨F, hF, hge⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hge
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiMinus]
      linarith
  · rintro (hZ | ⟨F, hF, hge⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hge
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by grind [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by grind]
        exact F.semistable j
      · dsimp only [HNFiltration.phiMinus]
        linarith

/-- The hom-vanishing lemma for phase-shifted slicings at general cutoff `t`:
any morphism from `P(> t)` to `P(≤ t)` is zero. -/
lemma Slicing.zero_of_gtProp_leProp_general (s : Slicing C) (t : ℝ) {X Y : C}
    (hX : s.gtProp C t X) (hY : s.leProp C t Y) (f : X ⟶ Y) : f = 0 := by
  have hX' := (s.phaseShift_gtProp_zero C t X).mpr hX
  have hY' := (s.phaseShift_leProp_zero C t Y).mpr hY
  exact (s.phaseShift C t).zero_of_gtProp_leProp C hX' hY' f

/-- The hom-vanishing lemma for the right-heart convention at general cutoff `t`:
any morphism from `P(≥ t)` to `P(< t)` is zero. -/
lemma Slicing.zero_of_geProp_ltProp_general (s : Slicing C) (t : ℝ) {X Y : C}
    (hX : s.geProp C t X) (hY : s.ltProp C t Y) (f : X ⟶ Y) : f = 0 := by
  have hX' := (s.phaseShift_geProp_zero C t X).mpr hX
  have hY' := (s.phaseShift_ltProp_zero C t Y).mpr hY
  exact (s.phaseShift C t).zero_of_geProp_ltProp C hX' hY' f


/-! ### Inverse phase shift for HN filtrations -/

/-- Inverse phase shift: given an HN filtration of `E` with respect to
the shifted slicing `(s.phaseShift t).P`, produce an HN filtration with
respect to `s.P` by adding `t` to all phases. -/
def HNFiltration.unphaseShift {s : Slicing C} {E : C} {t : ℝ}
    (G : HNFiltration C (s.phaseShift C t).P E) :
    HNFiltration C s.P E where
  n := G.n
  chain := G.chain
  triangle := G.triangle
  triangle_dist := G.triangle_dist
  triangle_obj₁ := G.triangle_obj₁
  triangle_obj₂ := G.triangle_obj₂
  base_isZero := G.base_isZero
  top_iso := G.top_iso
  zero_isZero := G.zero_isZero
  φ := fun j ↦ G.φ j + t
  hφ := by intro i j hij; grind [G.hφ hij]
  semistable := fun j ↦ G.semistable j

theorem HNFiltration.unphaseShift_n {s : Slicing C}
    {E : C} {t : ℝ}
    (G : HNFiltration C (s.phaseShift C t).P E) :
    G.unphaseShift.n = G.n := rfl

theorem HNFiltration.unphaseShift_phiPlus {s : Slicing C}
    {E : C} {t : ℝ}
    (G : HNFiltration C (s.phaseShift C t).P E)
    (hn : 0 < G.n) :
    G.unphaseShift.phiPlus C hn = G.phiPlus C hn + t := rfl

end Slicing

end CategoryTheory.Triangulated
