/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Slicing.TStructure

/-!
# T-Structure Construction from Slicing

Core t-structure construction from a slicing (toTStructure, toTStructureGE),
boundedness, heart characterization, interval/cutoff splitting.
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
  [IsTriangulated C]

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
