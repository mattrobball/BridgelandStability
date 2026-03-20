/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.Slicing.Basic

/-!
# T-Structure from a Slicing

Single-factor HN filtrations, phase-shifted slicings, and construction of a
bounded t-structure from a slicing.
-/

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

/-- For a semistable nonzero object, `phiPlus = phiMinus = φ`. -/
theorem Slicing.phiPlus_eq_phiMinus_of_semistable (s : Slicing C) {E : C} {φ : ℝ}
    (hS : (s.P φ) E) (hE : ¬IsZero E) :
    s.phiPlus C E hE = φ ∧ s.phiMinus C E hE = φ := by
  let F := HNFiltration.single C E φ hS
  have hn : (0 : ℕ) < F.n := by change 0 < 1; omega
  have hne : ¬IsZero (F.triangle ⟨0, hn⟩).obj₃ := by
    change ¬IsZero (Triangle.mk (0 : (0 : C) ⟶ E) (𝟙 E) 0).obj₃
    exact hE
  constructor
  · exact s.phiPlus_eq C E hE F hn hne
  · have hneL : ¬IsZero (F.triangle ⟨F.n - 1, by omega⟩).obj₃ := by
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
    have hn' : F.n - 1 < F.n := by omega
    exact absurd (by rw [h0, hn1, ← heq] : F.φ ⟨0, hn⟩ = F.φ ⟨F.n - 1, hn'⟩)
      (ne_of_gt (F.hφ (Fin.mk_lt_mk.mpr (by omega))))
  -- T.obj₁ is zero, so T.mor₂ is an isomorphism
  let T := F.triangle ⟨0, hn⟩
  have hZ1 : IsZero T.obj₁ :=
    IsZero.of_iso F.base_isZero (Classical.choice (F.triangle_obj₁ ⟨0, hn⟩))
  have : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist ⟨0, hn⟩)).mp hZ1
  -- T.obj₂ ≅ chain(1) = chain.right ≅ E
  have hobj₂_eq : F.chain.obj' (0 + 1) (by omega) = F.chain.obj (Fin.last F.n) :=
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
  have hchain : ∀ k (hk : k ≤ F.n), (s.P φ) (F.chain.obj' k (by omega)) := by
    intro k hk
    induction k with
    | zero => exact s.zero_mem' C φ _ F.base_isZero
    | succ k ih =>
      have hkn : k < F.n := by omega
      let T := F.triangle ⟨k, hkn⟩
      -- T.obj₁ ≅ chain(k), T.obj₃ = factor(k) ∈ P(φ)
      have hT1 : (s.P φ) T.obj₁ :=
        (s.P φ).prop_of_iso (Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)).symm
          (ih (by omega))
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
    (fun i j ↦ by linarith [(Fy.phase_mem_range C hFy j).2,
      (Fx.phase_mem_range C hFx i).1]) f

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
    (fun i j ↦ by linarith [(Fy.phase_mem_range C hFy j).2,
      (Fx.phase_mem_range C hFx i).1]) f

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
  hφ := by intro i j hij; change F.φ j - t < F.φ i - t; linarith [F.hφ hij]
  semistable := by
    intro i; show s.P (F.φ i - t + t) _
    rw [show F.φ i - t + t = F.φ i from by ring]
    exact F.semistable i

/-- Phase-shifted slicing: `(s.phaseShift t).P ψ = s.P (ψ + t)`. This shifts
all phases down by `t`. -/
def Slicing.phaseShift (s : Slicing C) (t : ℝ) : Slicing C where
  P ψ := s.P (ψ + t)
  closedUnderIso φ := s.closedUnderIso (φ + t)
  zero_mem φ := s.zero_mem (φ + t)
  shift_iff φ X := by
    show s.P (φ + t) X ↔ s.P (φ + 1 + t) (X⟦(1 : ℤ)⟧)
    rw [show φ + 1 + t = (φ + t) + 1 from by ring]
    exact s.shift_iff (φ + t) X
  hom_vanishing φ₁ φ₂ A B h hA hB := by
    exact s.hom_vanishing (φ₁ + t) (φ₂ + t) A B (by linarith) hA hB
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
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiMinus]; linarith
  · rintro (hZ | ⟨F, hF, hgt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hgt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by ring]
        exact F.semistable j
      · dsimp only [HNFiltration.phiMinus]; linarith

/-- `gtProp` of a phase-shifted slicing at cutoff `u` equals `gtProp` of the
original slicing at cutoff `u + t`. -/
theorem Slicing.phaseShift_gtProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).gtProp C u E ↔ s.gtProp C (u + t) E := by
  constructor
  · rintro (hZ | ⟨F, hF, hgt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hgt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiMinus]
      linarith
  · rintro (hZ | ⟨F, hF, hgt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hgt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by ring]
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
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiPlus]; linarith
  · rintro (hZ | ⟨F, hF, hle⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by ring]
        exact F.semistable j
      · dsimp only [HNFiltration.phiPlus]; linarith

/-- `leProp` of a phase-shifted slicing at cutoff `u` equals `leProp` of the
original slicing at cutoff `u + t`. -/
theorem Slicing.phaseShift_leProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).leProp C u E ↔ s.leProp C (u + t) E := by
  constructor
  · rintro (hZ | ⟨F, hF, hle⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiPlus]
      linarith
  · rintro (hZ | ⟨F, hF, hle⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by ring]
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
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiPlus]; linarith
  · rintro (hZ | ⟨F, hF, hlt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hlt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by ring]
        exact F.semistable j
      · dsimp only [HNFiltration.phiPlus]; linarith

/-- `ltProp` of a phase-shifted slicing at cutoff `u` equals `ltProp` of the
original slicing at cutoff `u + t`. -/
theorem Slicing.phaseShift_ltProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).ltProp C u E ↔ s.ltProp C (u + t) E := by
  constructor
  · rintro (hZ | ⟨F, hF, hlt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hlt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiPlus]
      linarith
  · rintro (hZ | ⟨F, hF, hlt⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hlt
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by ring]
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
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiMinus]; linarith
  · rintro (hZ | ⟨F, hF, hge⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hge
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by ring]
        exact F.semistable j
      · dsimp only [HNFiltration.phiMinus]; linarith

/-- `geProp` of a phase-shifted slicing at cutoff `u` equals `geProp` of the
original slicing at cutoff `u + t`. -/
theorem Slicing.phaseShift_geProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).geProp C u E ↔ s.geProp C (u + t) E := by
  constructor
  · rintro (hZ | ⟨F, hF, hge⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hge
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ F.semistable j⟩, hF, ?_⟩
      dsimp only [HNFiltration.phiMinus]
      linarith
  · rintro (hZ | ⟨F, hF, hge⟩)
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hge
      refine Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - t,
        fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hF, ?_⟩
      · change s.P (F.φ j - t + t) _
        rw [show F.φ j - t + t = F.φ j from by ring]
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

variable [IsTriangulated C]

/-- Auxiliary: given an HN filtration, produce a t-structure decomposition triangle.
This is the core of `exists_triangle_zero_one`. Uses induction on the number of
factors to handle the mixed-phase case by peeling off the last factor.

The strengthened IH tracks phase bound data for both X and Y. In particular, if
`F` has `n ≥ 1` factors, the X-part has `phiPlus ≤ F.φ(0)` (bounded by the
max original phase). This is used in **Lemma 6.4** to prove that the splitting
preserves interval properties. -/
theorem Slicing.tStructureAux (s : Slicing C)
    (A : C) (F : HNFiltration C s.P A) :
    ∃ (X Y : C) (_ : s.gtProp C 0 X) (_ : s.leProp C 0 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      (IsZero X ∨ ∃ (GX : HNFiltration C s.P X) (hGX : 0 < GX.n),
        0 < GX.phiMinus C hGX ∧
        (∀ hn0 : 0 < F.n, GX.phiPlus C hGX ≤ F.φ ⟨0, hn0⟩) ∧
        (∀ j : Fin GX.n, ∃ i : Fin F.n, GX.φ j = F.φ i)) ∧
      (IsZero Y ∨ ∃ (GY : HNFiltration C s.P Y) (hGY : 0 < GY.n),
        GY.phiPlus C hGY ≤ 0 ∧
        (∀ j : Fin GY.n, ∃ i : Fin F.n, GY.φ j = F.φ i)) := by
  -- Strengthened IH: also return phase bound data for both X and Y sides.
  suffices hmain : ∀ (m : ℕ) (A : C) (F : HNFiltration C s.P A), F.n ≤ m →
      ∃ (X Y : C) (_ : s.gtProp C 0 X)
        (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧
        (IsZero X ∨ ∃ (GX : HNFiltration C s.P X) (hGX : 0 < GX.n),
          0 < GX.phiMinus C hGX ∧
          (∀ hn0 : 0 < F.n, GX.phiPlus C hGX ≤ F.φ ⟨0, hn0⟩) ∧
          (∀ j : Fin GX.n, ∃ i : Fin F.n, GX.φ j = F.φ i)) ∧
        (IsZero Y ∨ ∃ (GY : HNFiltration C s.P Y) (hGY : 0 < GY.n),
          GY.phiPlus C hGY ≤ 0 ∧
          (∀ (_ : 0 < F.n) (j : Fin GY.n),
            F.φ ⟨F.n - 1, by omega⟩ ≤ GY.φ j) ∧
          (∀ j : Fin GY.n, ∃ i : Fin F.n, GY.φ j = F.φ i)) by
    obtain ⟨X, Y, hX, f, g, h, hT, hXdata, hY⟩ := hmain F.n A F le_rfl
    exact ⟨X, Y, hX,
      hY.elim Or.inl (fun ⟨GY, hGY, hle, _, _⟩ ↦ Or.inr ⟨GY, hGY, hle⟩),
      f, g, h, hT, hXdata,
      hY.elim Or.inl (fun ⟨GY, hGY, hle, _, hcontain⟩ ↦
        Or.inr ⟨GY, hGY, hle, hcontain⟩)⟩
  intro m
  induction m with
  | zero =>
    intro A F hFn
    have hn : F.n = 0 := by omega
    exact ⟨A, 0, Or.inl (F.zero_isZero hn), 𝟙 A, 0, 0,
      contractible_distinguished A, Or.inl (F.zero_isZero hn), Or.inl (isZero_zero C)⟩
  | succ m ih =>
    intro A F hFn
    by_cases hn : F.n = 0
    · exact ⟨A, 0, Or.inl (F.zero_isZero hn), 𝟙 A, 0, 0,
        contractible_distinguished A, Or.inl (F.zero_isZero hn), Or.inl (isZero_zero C)⟩
    have hn0 : 0 < F.n := Nat.pos_of_ne_zero hn
    by_cases hall_pos : ∀ j : Fin F.n, 0 < F.φ j
    · -- All phases > 0: X = A, Y = 0
      exact ⟨A, 0, s.gtProp_of_hn C F 0 hall_pos hn0, 𝟙 A, 0, 0,
        contractible_distinguished A,
        Or.inr ⟨F, hn0, by simp only [HNFiltration.phiMinus]; exact hall_pos ⟨F.n - 1, by omega⟩,
          fun hn0 ↦ le_refl _, fun j ↦ ⟨j, rfl⟩⟩,
        Or.inl (isZero_zero C)⟩
    · push_neg at hall_pos
      by_cases hall_neg : ∀ j : Fin F.n, F.φ j ≤ 0
      · -- All phases ≤ 0: X = 0, Y = A, filtration is F itself
        refine ⟨0, A, Or.inl (isZero_zero C), 0, 𝟙 A, 0,
          contractible_distinguished₁ A,
          Or.inl (isZero_zero C),
          Or.inr ⟨F, hn0, hall_neg ⟨0, hn0⟩, fun _ j ↦
            F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)), fun j ↦ ⟨j, rfl⟩⟩⟩
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
        obtain ⟨X, Y', hX, f', g', h', hT', hXdata, hY'⟩ :=
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
        rcases hY' with hY'Z | ⟨GY', hGY', hGY'_le, hGY'_bound, hGY'_contain⟩
        · -- Y' is zero (prefix was all-positive): f' is iso
          have hf'Iso : IsIso f' :=
            (Triangle.isZero₃_iff_isIso₁ _ hT').mp hY'Z
          let eX : X ≅ F.chain.obj' (F.n - 1) (by omega) := asIso f'
          have hGn0 : 0 < G.n := by change 0 < F.n - 1; omega
          refine ⟨X, T.obj₃, hX, eX.hom ≫ u₂₃, e₂A.inv ≫ T.mor₂,
            T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.hom ≫
              (shiftFunctor C (1 : ℤ)).map eX.inv, ?_,
            hXdata.imp id (fun ⟨GX, hGX, hpos, hbd, hcontain⟩ ↦
              ⟨GX, hGX, hpos, fun _ ↦ hbd hGn0, fun j ↦ by
                obtain ⟨i, hi⟩ := hcontain j
                have hi_lt := i.isLt; change i.val < F.n - 1 at hi_lt
                exact ⟨⟨i.val, by omega⟩, by simp [G, HNFiltration.prefix] at hi; exact hi⟩⟩),
            Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
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
          · -- Phase containment: single.φ j = F.φ(n-1)
            intro j; exact ⟨⟨F.n - 1, by omega⟩, by simp [HNFiltration.single]⟩
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
            hXdata.imp id (fun ⟨GX, hGX, hpos, hbd, hcontain⟩ ↦
              ⟨GX, hGX, hpos, fun _ ↦ hbd (by change 0 < F.n - 1; omega), fun j ↦ by
                obtain ⟨i, hi⟩ := hcontain j
                have hi_lt := i.isLt; change i.val < F.n - 1 at hi_lt
                exact ⟨⟨i.val, by omega⟩, by simp [G, HNFiltration.prefix] at hi; exact hi⟩⟩),
            Or.inr ⟨GZ, by omega, ?_, fun _ j ↦ ?_, fun j ↦ ?_⟩⟩
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
          · -- Phase containment: GZ.φ j comes from GY' or appended factor
            change ∃ i : Fin F.n, GZ.φ j = F.φ i
            simp only [GZ, HNFiltration.appendFactor]
            split_ifs with hj
            · -- j < GY'.n: GZ.φ j = GY'.φ ⟨j, hj⟩
              obtain ⟨i_G, hi_G⟩ := hGY'_contain ⟨j.val, hj⟩
              have hi_lt := i_G.isLt; change i_G.val < F.n - 1 at hi_lt
              exact ⟨⟨i_G.val, by omega⟩,
                by simp [G, HNFiltration.prefix] at hi_G; exact hi_G⟩
            · -- j = GY'.n: GZ.φ j = F.φ(n-1)
              exact ⟨⟨F.n - 1, by omega⟩, rfl⟩

/-- Auxiliary: given an HN filtration, produce the dual half-open t-structure
decomposition triangle for the convention `geProp 0` / `ltProp 0`. -/
theorem Slicing.tStructureAuxGE (s : Slicing C)
    (A : C) (F : HNFiltration C s.P A) :
    ∃ (X Y : C) (_ : s.geProp C 0 X) (_ : s.ltProp C 0 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  suffices hmain : ∀ (m : ℕ) (A : C) (F : HNFiltration C s.P A), F.n ≤ m →
      ∃ (X Y : C) (_ : s.geProp C 0 X) (_ : s.ltProp C 0 Y)
        (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C by
    exact hmain F.n A F le_rfl
  intro m
  induction m with
  | zero =>
    intro A F hFn
    have hn : F.n = 0 := by omega
    exact ⟨A, 0, Or.inl (F.zero_isZero hn), Or.inl (isZero_zero C), 𝟙 A, 0, 0,
      contractible_distinguished A⟩
  | succ m ih =>
    intro A F hFn
    by_cases hn : F.n = 0
    · exact ⟨A, 0, Or.inl (F.zero_isZero hn), Or.inl (isZero_zero C), 𝟙 A, 0, 0,
        contractible_distinguished A⟩
    have hn0 : 0 < F.n := Nat.pos_of_ne_zero hn
    by_cases hall_nonneg : ∀ j : Fin F.n, 0 ≤ F.φ j
    · exact ⟨A, 0, s.geProp_of_hn C F 0 hall_nonneg hn0, Or.inl (isZero_zero C),
        𝟙 A, 0, 0, contractible_distinguished A⟩
    · push_neg at hall_nonneg
      by_cases hall_neg : ∀ j : Fin F.n, F.φ j < 0
      · exact ⟨0, A, Or.inl (isZero_zero C), s.ltProp_of_hn C F 0 hall_neg hn0,
          0, 𝟙 A, 0, contractible_distinguished₁ A⟩
      · push_neg at hall_neg
        have hn2 : 2 ≤ F.n := by
          by_contra hlt
          push_neg at hlt
          obtain ⟨j, hj⟩ := hall_nonneg
          obtain ⟨j', hj'⟩ := hall_neg
          have heq : F.φ j = F.φ j' := congrArg F.φ (Fin.ext (by omega))
          linarith
        let G := F.prefix C (F.n - 1) (by omega) (by omega)
        obtain ⟨X, Y', hX, hY', f', g', h', hT'⟩ :=
          ih (F.chain.obj' (F.n - 1) (by omega)) G
            (by have : G.n = F.n - 1 := rfl; omega)
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
        have hφlast : F.φ ⟨F.n - 1, by omega⟩ < 0 := by
          obtain ⟨j, hj⟩ := hall_nonneg
          exact lt_of_le_of_lt
            (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))) hj
        obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (f' ≫ u₂₃)
        let oct := Triangulated.someOctahedron rfl hT' hTu₂₃ h₁₃
        have hLast : s.ltProp C 0 T.obj₃ := by
          exact s.ltProp_of_hn C
            (HNFiltration.single C T.obj₃ (F.φ ⟨F.n - 1, by omega⟩)
              (F.semistable ⟨F.n - 1, by omega⟩))
            0 (fun _ ↦ hφlast) (by
              change 0 < 1
              omega)
        have hZ : s.ltProp C 0 Z := s.ltProp_of_triangle C 0 hY' hLast oct.mem
        exact ⟨X, Z, hX, hZ, f' ≫ u₂₃, v₁₃, w₁₃, h₁₃⟩

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
    obtain ⟨X, Y, hX, hY, f, g, h, hT, _⟩ := Slicing.tStructureAux C s A F
    refine ⟨X, Y, ?_, ?_, f, g, h, hT⟩
    · simp only [Int.cast_zero, neg_zero]; exact hX
    · simp only [Int.cast_one, sub_self]; exact hY

/-- A slicing on a triangulated category also determines the dual half-open
t-structure whose heart is `P([0, 1))`.

The convention is:
- `le n = geProp(-n)`: objects whose HN phases are all `≥ -n`
- `ge n = ltProp(1-n)`: objects whose HN phases are all `< 1-n`

This ensures `le 0 = geProp(0)` (phases `≥ 0`) and `ge 1 = ltProp(0)` (phases `< 0`),
with the heart being `P([0,1))`. -/
def Slicing.toTStructureGE (s : Slicing C) : TStructure C where
  le n := s.geProp C (-↑n)
  ge n := s.ltProp C (1 - ↑n)
  le_isClosedUnderIsomorphisms _ := inferInstance
  ge_isClosedUnderIsomorphisms _ := inferInstance
  le_shift n a n' h X hX := by
    show s.geProp C (-↑n') (X⟦a⟧)
    have hcast : (↑a : ℝ) + ↑n' = ↑n := by exact_mod_cast h
    have : (-↑n' : ℝ) = -↑n + ↑a := by linarith
    rw [this]
    exact s.geProp_shift C _ X a hX
  ge_shift n a n' h X hX := by
    show s.ltProp C (1 - ↑n') (X⟦a⟧)
    have hcast : (↑a : ℝ) + ↑n' = ↑n := by exact_mod_cast h
    have : (1 - ↑n' : ℝ) = (1 - ↑n) + ↑a := by linarith
    rw [this]
    exact s.ltProp_shift C _ X a hX
  zero' {X Y} f hX hY := by
    have hX' : s.geProp C 0 X := by
      simpa [show (-↑(0 : ℤ) : ℝ) = 0 from by norm_num] using hX
    have hY' : s.ltProp C 0 Y := by
      simpa [show (1 - ↑(1 : ℤ) : ℝ) = 0 from by norm_num] using hY
    exact s.zero_of_geProp_ltProp C hX' hY' f
  le_zero_le := by
    show s.geProp C (-↑(0 : ℤ)) ≤ s.geProp C (-↑(1 : ℤ))
    simp only [Int.cast_zero, neg_zero, Int.cast_one]
    exact s.geProp_anti C (by norm_num : (-1 : ℝ) ≤ 0)
  ge_one_le := by
    show s.ltProp C (1 - ↑(1 : ℤ)) ≤ s.ltProp C (1 - ↑(0 : ℤ))
    simp only [Int.cast_one, sub_self, Int.cast_zero, sub_zero]
    exact s.ltProp_mono C (by norm_num : (0 : ℝ) ≤ 1)
  exists_triangle_zero_one A := by
    obtain ⟨F⟩ := s.hn_exists A
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := Slicing.tStructureAuxGE C s A F
    refine ⟨X, Y, ?_, ?_, f, g, h, hT⟩
    · simp only [Int.cast_zero, neg_zero]; exact hX
    · simp only [Int.cast_one, sub_self]; exact hY

/-- **Bounded t-structure from slicing.**
The t-structure induced by a slicing is bounded: every object lies between
`le a` and `ge b` for some integers `a, b`.

The proof uses the HN filtration axiom to place every object's phases in
a finite interval, then converts the phase bounds to `le`/`ge` bounds. -/
theorem Slicing.toTStructure_bounded (s : Slicing C) :
    s.toTStructure.IsBounded := by
  intro E
  obtain ⟨F⟩ := s.hn_exists E
  by_cases hE : IsZero E
  · exact ⟨0, 0, Or.inl hE, Or.inl hE⟩
  · have hn := F.n_pos C hE
    refine ⟨⌈-(F.phiMinus C hn)⌉ + 1, ⌊1 - F.phiPlus C hn⌋, Or.inr ⟨F, hn, ?_⟩,
      Or.inr ⟨F, hn, ?_⟩⟩
    · have := Int.le_ceil (-(F.phiMinus C hn))
      push_cast
      linarith
    · linarith [Int.floor_le (1 - F.phiPlus C hn)]

/-- **Bounded t-structure from the dual half-open convention.**
The t-structure induced by `toTStructureGE` is bounded. -/
theorem Slicing.toTStructureGE_bounded (s : Slicing C) :
    s.toTStructureGE.IsBounded := by
  intro E
  obtain ⟨F⟩ := s.hn_exists E
  by_cases hE : IsZero E
  · exact ⟨0, 0, Or.inl hE, Or.inl hE⟩
  · have hn := F.n_pos C hE
    refine ⟨⌈-(F.phiMinus C hn)⌉, ⌈1 - F.phiPlus C hn⌉ - 1, Or.inr ⟨F, hn, ?_⟩,
      Or.inr ⟨F, hn, ?_⟩⟩
    · have := Int.le_ceil (-(F.phiMinus C hn))
      push_cast
      linarith
    · have hceil : ((⌈1 - F.phiPlus C hn⌉ - 1 : ℤ) : ℝ) < 1 - F.phiPlus C hn := by
        exact (Int.lt_ceil).1 (by
          simpa using Int.sub_one_lt (⌈1 - F.phiPlus C hn⌉ : ℤ))
      linarith

/-- **Heart identification.**
An object `E` lies in the heart of the slicing-induced t-structure if and only
if it satisfies both `gtProp 0` (all HN phases > 0) and `leProp 1` (all HN
phases ≤ 1). This identifies the heart with the half-open interval `P((0, 1])`. -/
theorem Slicing.toTStructure_heart_iff (s : Slicing C) (E : C) :
    (s.toTStructure).heart E ↔ s.gtProp C 0 E ∧ s.leProp C 1 E := by
  change s.toTStructure.le 0 E ∧ s.toTStructure.ge 0 E ↔ _
  simp only [toTStructure, Int.cast_zero, neg_zero, sub_zero]

/-- **Heart identification for the dual half-open convention.**
An object `E` lies in the heart of `toTStructureGE` if and only if it satisfies
`geProp 0` and `ltProp 1`, i.e. its HN phases lie in `[0,1)`. -/
theorem Slicing.toTStructureGE_heart_iff (s : Slicing C) (E : C) :
    (s.toTStructureGE).heart E ↔ s.geProp C 0 E ∧ s.ltProp C 1 E := by
  change s.toTStructureGE.le 0 E ∧ s.toTStructureGE.ge 0 E ↔ _
  simp only [toTStructureGE, Int.cast_zero, neg_zero, sub_zero]

/-- **HN filtration splitting with interval data**. Given an HN filtration `F`
of `E` (wrt slicing `s`) with all phases in the open interval `(a, b)`, and a
cutoff `t ∈ (a, b)`, produce a distinguished triangle `X → E → Y` where:
- `X ∈ s.gtProp(t)` (all phases `> t`)
- `Y ∈ s.leProp(t)` (all phases `≤ t`)
- If `X` is nonzero, its maximum phase is `< b` (preserving the interval bound)

This is used in **Lemma 6.4** to split at the τ-semistable phase while preserving
the interval property from `d(σ, τ) < 1`. -/
theorem Slicing.exists_split_with_interval (s : Slicing C)
    {E : C} (F : HNFiltration C s.P E)
    {a b : ℝ} (hI : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b)
    (hn : 0 < F.n) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      s.gtProp C a X ∧ s.leProp C a Y ∧
      (∀ (hXne : ¬IsZero X), s.phiPlus C X hXne < b) := by
  -- Phase-shift by a, so the cutoff becomes 0
  let Fs := F.phaseShift (C := C) a
  have hFs_phases : ∀ i : Fin Fs.n, 0 < Fs.φ i ∧ Fs.φ i < b - a := by
    intro i; constructor
    · change 0 < F.φ i - a; linarith [(hI i).1]
    · change F.φ i - a < b - a; linarith [(hI i).2]
  -- Apply tStructureAux to the shifted filtration
  obtain ⟨X, Y, hX, hY, f, g, h, hT, hXdata⟩ :=
    Slicing.tStructureAux C (s.phaseShift C a) E Fs
  -- Convert gtProp/leProp from shifted to original
  have hXgt : s.gtProp C a X := (s.phaseShift_gtProp_zero C a X).mp hX
  have hYle : s.leProp C a Y := (s.phaseShift_leProp_zero C a Y).mp hY
  refine ⟨X, Y, f, g, h, hT, hXgt, hYle, fun hXne ↦ ?_⟩
  -- Extract X's phase bound from tStructureAux data
  rcases hXdata with hXZ | ⟨GX, hGX, _, hbd, _⟩
  · exact absurd hXZ hXne
  · -- GX is an HN filtration of X wrt the shifted slicing, with phiPlus ≤ Fs.φ(0)
    have hFsn : 0 < Fs.n := hn
    have hGX_phiPlus_le := hbd hFsn
    -- Fs.φ(0) = F.φ(0) - a < b - a, so GX.phiPlus (shifted) < b - a
    have hFsφ0 : Fs.φ ⟨0, hFsn⟩ < b - a := (hFs_phases ⟨0, hFsn⟩).2
    -- GX is a filtration wrt (s.phaseShift a).P = fun ψ ↦ s.P(ψ + a)
    -- Convert GX to original slicing: phases become GX.φ j + a
    -- phiPlus of the original-coords filtration = GX.phiPlus + a < (b - a) + a = b
    -- But phiPlus(X) is intrinsic, so phiPlus(X) ≤ original-coords phiPlus
    -- Build an HN filtration of X wrt s.P with known phases
    let GXorig : HNFiltration C s.P X :=
      { n := GX.n
        chain := GX.chain
        triangle := GX.triangle
        triangle_dist := GX.triangle_dist
        triangle_obj₁ := GX.triangle_obj₁
        triangle_obj₂ := GX.triangle_obj₂
        base_isZero := GX.base_isZero
        top_iso := GX.top_iso
        zero_isZero := GX.zero_isZero
        φ := fun j ↦ GX.φ j + a
        hφ := by intro i j hij; linarith [GX.hφ hij]
        semistable := fun j ↦ GX.semistable j }
    have hGXorig_phiPlus : GXorig.phiPlus C hGX = GX.phiPlus C hGX + a := by
      simp only [HNFiltration.phiPlus]; rfl
    calc s.phiPlus C X hXne
        ≤ GXorig.phiPlus C hGX :=
          s.phiPlus_le_phiPlus_of_hn C hXne GXorig hGX
      _ = GX.phiPlus C hGX + a := hGXorig_phiPlus
      _ ≤ Fs.φ ⟨0, hFsn⟩ + a := by linarith
      _ < (b - a) + a := by linarith
      _ = b := by ring

/-- **Generalized splitting at an arbitrary cutoff**. Given an HN filtration `F`
of `E` with all phases in `(a, b)` and a cutoff `t`, produce a
distinguished triangle `X → E → Y → X⟦1⟧` where:
- `X ∈ s.gtProp(t)` (all phases `> t`)
- `Y ∈ s.leProp(t)` (all phases `≤ t`)
- If `X` is nonzero, `φ⁺(X) < b` (preserving the upper interval bound)

This generalizes `exists_split_with_interval` which always splits at `a`.
The generalized version is needed for the deformation theorem (§7). -/
theorem Slicing.exists_split_at_cutoff (s : Slicing C)
    {E : C} (F : HNFiltration C s.P E)
    {a b t : ℝ} (hI : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b)
    (hn : 0 < F.n) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      s.gtProp C t X ∧ s.leProp C t Y ∧
      (∀ (hXne : ¬IsZero X), s.phiPlus C X hXne < b) := by
  -- Phase-shift by t, so the cutoff becomes 0
  let Fs := F.phaseShift (C := C) t
  -- Apply tStructureAux to the shifted filtration (no phase positivity needed)
  obtain ⟨X, Y, hX, hY, f, g, h, hT, hXdata⟩ :=
    Slicing.tStructureAux C (s.phaseShift C t) E Fs
  -- Convert gtProp/leProp from shifted to original
  have hXgt : s.gtProp C t X := (s.phaseShift_gtProp_zero C t X).mp hX
  have hYle : s.leProp C t Y := (s.phaseShift_leProp_zero C t Y).mp hY
  refine ⟨X, Y, f, g, h, hT, hXgt, hYle, fun hXne ↦ ?_⟩
  -- Extract X's phase bound from tStructureAux data
  rcases hXdata with hXZ | ⟨GX, hGX, _, hbd, _⟩
  · exact absurd hXZ hXne
  · have hFsn : 0 < Fs.n := hn
    have hGX_phiPlus_le := hbd hFsn
    -- Fs.φ ⟨0, _⟩ = F.φ ⟨0, _⟩ - t, and F.φ ⟨0, _⟩ < b
    have hFφ0_lt : F.φ ⟨0, hn⟩ < b := (hI ⟨0, hn⟩).2
    -- Build an HN filtration of X wrt s.P with known phases
    let GXorig : HNFiltration C s.P X :=
      { n := GX.n
        chain := GX.chain
        triangle := GX.triangle
        triangle_dist := GX.triangle_dist
        triangle_obj₁ := GX.triangle_obj₁
        triangle_obj₂ := GX.triangle_obj₂
        base_isZero := GX.base_isZero
        top_iso := GX.top_iso
        zero_isZero := GX.zero_isZero
        φ := fun j ↦ GX.φ j + t
        hφ := by intro i j hij; linarith [GX.hφ hij]
        semistable := fun j ↦ GX.semistable j }
    have hGXorig_phiPlus : GXorig.phiPlus C hGX = GX.phiPlus C hGX + t := by
      simp only [HNFiltration.phiPlus]; rfl
    calc s.phiPlus C X hXne
        ≤ GXorig.phiPlus C hGX :=
          s.phiPlus_le_phiPlus_of_hn C hXne GXorig hGX
      _ = GX.phiPlus C hGX + t := hGXorig_phiPlus
      _ ≤ Fs.φ ⟨0, hFsn⟩ + t := by linarith
      _ = (F.φ ⟨0, hn⟩ - t) + t := rfl
      _ = F.φ ⟨0, hn⟩ := by ring
      _ < b := hFφ0_lt

end Slicing
