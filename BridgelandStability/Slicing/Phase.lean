/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.Slicing.HNOperations

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

section Slicing

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]


/-!
# Intrinsic Phases and Phase Bounds

Shift lemmas for subcategory predicates, uniqueness of extreme phases (phiPlus/phiMinus),
intrinsic phase bounds, triangle phase-bound inequalities, and conversions between
gtProp/leProp and intervalProp.
-/

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

/-- If `E` has all HN phases `< t`, then `E⟦a⟧` has all HN phases `< t + ↑a`. -/
lemma Slicing.ltProp_shift (s : Slicing C) (t : ℝ) (E : C) (a : ℤ)
    (h : s.ltProp C t E) : s.ltProp C (t + ↑a) (E⟦a⟧) := by
  rcases h with hZ | ⟨F, hF, hlt⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hZ)
  · exact Or.inr ⟨F.shiftHN C s a, hF, by
      rw [F.shiftHN_phiPlus]; linarith⟩

/-- If `E` has all HN phases `≥ t`, then `E⟦a⟧` has all HN phases `≥ t + ↑a`. -/
lemma Slicing.geProp_shift (s : Slicing C) (t : ℝ) (E : C) (a : ℤ)
    (h : s.geProp C t E) : s.geProp C (t + ↑a) (E⟦a⟧) := by
  rcases h with hZ | ⟨F, hF, hge⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hZ)
  · exact Or.inr ⟨F.shiftHN C s a, hF, by
      rw [F.shiftHN_phiMinus]; linarith⟩

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

/-- If all maps from `E` to the last factor of an HN filtration are zero,
then the last factor is zero. This is the dual of `isZero_factor_zero_of_hom_eq_zero`,
using `yoneda_exact₃` and hom-vanishing on the shifted prefix filtration. -/
lemma HNFiltration.isZero_factor_last_of_hom_eq_zero (s : Slicing C) {E : C}
    (G : HNFiltration C s.P E) (hn : 0 < G.n)
    (hzero : ∀ f : E ⟶ (G.triangle ⟨G.n - 1, by omega⟩).obj₃, f = 0) :
    IsZero (G.triangle ⟨G.n - 1, by omega⟩).obj₃ := by
  rw [IsZero.iff_id_eq_zero]
  let T := G.triangle ⟨G.n - 1, by omega⟩
  -- T.obj₂ ≅ chain.obj'(G.n) ≅ E, so T.mor₂ : T.obj₂ → T.obj₃ is zero
  let e₂ := Classical.choice (G.triangle_obj₂ ⟨G.n - 1, by omega⟩)
  let eE := Classical.choice G.top_iso
  have hobj₂_eq : G.chain.obj' (G.n - 1 + 1) (by omega) = G.chain.right := by
    simp only [ComposableArrows.obj']
    congr 1; ext; simp; omega
  let eR : T.obj₂ ≅ E := e₂.trans (eqToIso hobj₂_eq |>.trans eE)
  have hmor₂ : T.mor₂ = 0 := by
    have h1 : eR.inv ≫ T.mor₂ = 0 := hzero _
    calc T.mor₂ = (eR.hom ≫ eR.inv) ≫ T.mor₂ := by
            rw [eR.hom_inv_id, Category.id_comp]
      _ = eR.hom ≫ (eR.inv ≫ T.mor₂) := by rw [Category.assoc]
      _ = 0 := by rw [h1, comp_zero]
  -- By yoneda_exact₃: since T.mor₂ ≫ id = 0, id = T.mor₃ ≫ γ for some γ
  have hmor₂_id : T.mor₂ ≫ 𝟙 T.obj₃ = 0 := by rw [Category.comp_id, hmor₂]
  obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₃ T (G.triangle_dist ⟨G.n - 1, by omega⟩)
    (𝟙 T.obj₃) hmor₂_id
  -- γ : T.obj₁⟦1⟧ → T.obj₃. Show γ = 0 by hom-vanishing on shifted prefix.
  suffices hγ0 : γ = 0 by rw [hγ, hγ0, comp_zero]
  let e₁ := Classical.choice (G.triangle_obj₁ ⟨G.n - 1, by omega⟩)
  by_cases hn1 : G.n = 1
  · -- If G.n = 1, T.obj₁ ≅ chain(0) = chain.left = 0, so T.obj₁⟦1⟧ is zero
    have he : G.chain.obj' (G.n - 1) (by omega) = G.chain.left := by
      simp only [ComposableArrows.obj']; congr 1; ext; simp; omega
    have hZ : IsZero T.obj₁ :=
      G.base_isZero.of_iso (e₁.trans (eqToIso he))
    exact ((shiftFunctor C (1 : ℤ)).map_isZero hZ).eq_of_src _ _
  · -- G.n ≥ 2: use the shifted prefix filtration on T.obj₁⟦1⟧
    let e₁_shift := (shiftFunctor C (1 : ℤ)).mapIso e₁
    let pfx := G.prefix C (G.n - 1) (by omega) (by omega)
    let pfx_shift := pfx.shiftHN C s (1 : ℤ)
    let pfx_on_T := pfx_shift.ofIso C e₁_shift.symm
    have hpn : pfx_on_T.n = G.n - 1 := rfl
    have hphases : ∀ j : Fin pfx_on_T.n,
        G.φ ⟨G.n - 1, by omega⟩ < pfx_on_T.φ j := by
      intro ⟨j, hj⟩
      change G.φ ⟨G.n - 1, by omega⟩ < G.φ ⟨j, by omega⟩ + (1 : ℤ)
      have h1 : G.φ ⟨j, by omega⟩ ≥ G.φ ⟨G.n - 1, by omega⟩ :=
        G.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
      have h2 : ((1 : ℤ) : ℝ) = 1 := by norm_num
      linarith
    exact s.hom_eq_zero_of_lt_phases C
      (G.semistable ⟨G.n - 1, by omega⟩) pfx_on_T hphases γ

/-- The lowest phase of an HN filtration with nonzero last factor is bounded below
by the lowest phase of any other HN filtration. Dual of `phiPlus_le_of_nonzero_factor`. -/
theorem HNFiltration.phiMinus_ge_of_nonzero_last_factor (s : Slicing C) {E : C}
    (F₁ F₂ : HNFiltration C s.P E) (hn₁ : 0 < F₁.n) (hn₂ : 0 < F₂.n)
    (hne₂ : ¬IsZero (F₂.triangle ⟨F₂.n - 1, by omega⟩).obj₃) :
    F₁.phiMinus C hn₁ ≤ F₂.phiMinus C hn₂ := by
  by_contra hlt
  push_neg at hlt
  -- F₁.φ(n₁-1) > F₂.φ(n₂-1), so all F₁ phases > F₂.φ(n₂-1)
  have hgap : ∀ j : Fin F₁.n, F₂.φ ⟨F₂.n - 1, by omega⟩ < F₁.φ j := fun j ↦
    lt_of_lt_of_le (by change F₂.phiMinus C hn₂ < F₁.phiMinus C hn₁; exact hlt)
      (F₁.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
  -- By hom_eq_zero_of_lt_phases, Hom(E, factor₂(n₂-1)) = 0
  have hzero : ∀ f : E ⟶ (F₂.triangle ⟨F₂.n - 1, by omega⟩).obj₃, f = 0 :=
    fun f ↦ s.hom_eq_zero_of_lt_phases C
      (F₂.semistable ⟨F₂.n - 1, by omega⟩) F₁ hgap f
  exact hne₂ (F₂.isZero_factor_last_of_hom_eq_zero C s hn₂ hzero)

/-- For any two HN filtrations of a nonzero object where both have nonzero last factors,
the lowest phases agree. Dual of `phiPlus_eq_of_nonzero_factors`. -/
theorem HNFiltration.phiMinus_eq_of_nonzero_last_factors (s : Slicing C) {E : C}
    (F₁ F₂ : HNFiltration C s.P E) (hn₁ : 0 < F₁.n) (hn₂ : 0 < F₂.n)
    (hne₁ : ¬IsZero (F₁.triangle ⟨F₁.n - 1, by omega⟩).obj₃)
    (hne₂ : ¬IsZero (F₂.triangle ⟨F₂.n - 1, by omega⟩).obj₃) :
    F₁.phiMinus C hn₁ = F₂.phiMinus C hn₂ :=
  le_antisymm (F₁.phiMinus_ge_of_nonzero_last_factor C s F₂ hn₁ hn₂ hne₂)
    (F₂.phiMinus_ge_of_nonzero_last_factor C s F₁ hn₂ hn₁ hne₁)

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
      simp only [ComposableArrows.map', homOfLE_leOfHom, Fin.zero_eta,
        ComposableArrows.mkOfObjOfMapSucc_obj, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
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
          simp only [ComposableArrows.obj']
          congr 1; ext; simp; omega)).trans
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

/-- For any nonzero object, there exists an HN filtration with both nonzero first and
last factors. This follows from `exists_nonzero_first` by repeatedly dropping zero
last factors (which preserves the nonzero first factor). -/
lemma HNFiltration.exists_both_nonzero (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.triangle ⟨0, hn⟩).obj₃ ∧
      ¬IsZero (F.triangle ⟨F.n - 1, by omega⟩).obj₃ := by
  obtain ⟨F, hnF, hfirst⟩ := HNFiltration.exists_nonzero_first C s hE
  suffices hmain : ∀ (m : ℕ) (G : HNFiltration C s.P E),
      G.n ≤ m → (hG : 0 < G.n) → ¬IsZero (G.triangle ⟨0, hG⟩).obj₃ →
      ∃ (H : HNFiltration C s.P E) (hH : 0 < H.n),
        ¬IsZero (H.triangle ⟨0, hH⟩).obj₃ ∧
        ¬IsZero (H.triangle ⟨H.n - 1, by omega⟩).obj₃ from
    hmain F.n F le_rfl hnF hfirst
  intro m; induction m with
  | zero => intro G hGn hG _; omega
  | succ m ih =>
    intro G hGn hG hGfirst
    by_cases hlast : IsZero (G.triangle ⟨G.n - 1, by omega⟩).obj₃
    · have hn1 : 1 < G.n := by
        by_contra h; push_neg at h
        have : (⟨0, hG⟩ : Fin G.n) = ⟨G.n - 1, by omega⟩ := Fin.ext (by omega)
        rw [this] at hGfirst; exact hGfirst hlast
      exact ih (G.dropLast C hn1 hlast) (by change G.n - 1 ≤ m; omega)
        (by change 0 < G.n - 1; omega) hGfirst
    · exact ⟨G, hG, hGfirst, hlast⟩

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
This is the phase of the last factor in any HN filtration with nonzero last factor.
Well-defined by `phiMinus_eq_of_nonzero_last_factors`. -/
noncomputable def Slicing.phiMinus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (HNFiltration.exists_nonzero_last C s hE).choose
  let hn : 0 < F.n := (HNFiltration.exists_nonzero_last C s hE).choose_spec.choose
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

/-- `Slicing.phiMinus` equals `G.φ ⟨G.n - 1, _⟩` for any HN filtration `G`
with nonzero last factor. -/
theorem Slicing.phiMinus_eq (s : Slicing C) (E : C) (hE : ¬IsZero E)
    (G : HNFiltration C s.P E) (hn : 0 < G.n)
    (hne : ¬IsZero (G.triangle ⟨G.n - 1, by omega⟩).obj₃) :
    s.phiMinus C E hE = G.φ ⟨G.n - 1, by omega⟩ := by
  unfold Slicing.phiMinus
  let F := (HNFiltration.exists_nonzero_last C s hE).choose
  let hnF := (HNFiltration.exists_nonzero_last C s hE).choose_spec.choose
  let hneF := (HNFiltration.exists_nonzero_last C s hE).choose_spec.choose_spec
  change F.φ ⟨F.n - 1, _⟩ = G.φ ⟨G.n - 1, _⟩
  exact HNFiltration.phiMinus_eq_of_nonzero_last_factors C s F G hnF hn hneF hne

/-- `Slicing.phiMinus ≤ Slicing.phiPlus` for nonzero objects. -/
theorem Slicing.phiMinus_le_phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) :
    s.phiMinus C E hE ≤ s.phiPlus C E hE := by
  by_contra hlt
  push_neg at hlt
  -- phiMinus > phiPlus. The filtration from exists_nonzero_last has all phases ≥ phiMinus,
  -- and from exists_nonzero_first all phases ≤ phiPlus. So there's a phase gap.
  let Fp := (HNFiltration.exists_nonzero_first C s hE).choose
  let hnp := (HNFiltration.exists_nonzero_first C s hE).choose_spec.choose
  let Fm := (HNFiltration.exists_nonzero_last C s hE).choose
  let hnm := (HNFiltration.exists_nonzero_last C s hE).choose_spec.choose
  -- All Fm phases ≥ phiMinus > phiPlus ≥ all Fp phases
  have hgap : ∀ i j, Fp.φ j < Fm.φ i := fun i j ↦
    calc Fp.φ j ≤ Fp.φ ⟨0, hnp⟩ := Fp.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val))
      _ = s.phiPlus C E hE := by unfold Slicing.phiPlus; rfl
      _ < s.phiMinus C E hE := hlt
      _ = Fm.φ ⟨Fm.n - 1, _⟩ := by unfold Slicing.phiMinus; rfl
      _ ≤ Fm.φ i := Fm.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
  -- By hom_eq_zero_of_phase_gap: 𝟙 E = 0, so E is zero
  have hid : (𝟙 E : E ⟶ E) = 0 :=
    s.hom_eq_zero_of_phase_gap C Fm Fp hgap (𝟙 E)
  exact hE ((IsZero.iff_id_eq_zero E).mpr hid)

/-- For any nonzero object, there exists an HN filtration whose extreme phases
match the intrinsic `phiPlus` and `phiMinus`. The filtration has nonzero first and
last factors, so `phiPlus_eq` and `phiMinus_eq` apply. -/
lemma Slicing.exists_HN_intrinsic_width (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      F.φ ⟨0, hn⟩ = s.phiPlus C E hE ∧
      F.φ ⟨F.n - 1, by omega⟩ = s.phiMinus C E hE := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C s hE
  exact ⟨F, hn, (s.phiPlus_eq C E hE F hn hfirst).symm,
    (s.phiMinus_eq C E hE F hn hlast).symm⟩

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

/-- The intrinsic phiMinus of a nonzero object is bounded above by the upper endpoint of any
interval containing the object. -/
lemma Slicing.phiMinus_lt_of_intervalProp (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {a b : ℝ} (hI : s.intervalProp C a b E) : s.phiMinus C E hE < b :=
  lt_of_le_of_lt (s.phiMinus_le_phiPlus C E hE) (s.phiPlus_lt_of_intervalProp C hE hI)

/-- The intrinsic phiMinus of a nonzero object is bounded below by the lower endpoint of any
interval containing the object. -/
lemma Slicing.phiMinus_gt_of_intervalProp (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {a b : ℝ} (hI : s.intervalProp C a b E) : a < s.phiMinus C E hE := by
  rcases hI with hZ | ⟨G, hG⟩
  · exact absurd hZ hE
  · obtain ⟨F, hnF, hneF⟩ := HNFiltration.exists_nonzero_last C s hE
    rw [s.phiMinus_eq C E hE F hnF hneF]
    have hGn : 0 < G.n := G.n_pos C hE
    exact lt_of_lt_of_le (hG ⟨G.n - 1, by omega⟩).1
      (G.phiMinus_ge_of_nonzero_last_factor C s F hGn hnF hneF)

/-! ### Conversion between gtProp/leProp and intervalProp -/

/-- The intrinsic phiMinus is an upper bound on any filtration's phiMinus.
Dual of `phiPlus_le_phiPlus_of_hn`. -/
lemma Slicing.phiMinus_ge_phiMinus_of_hn (s : Slicing C) {E : C} (hE : ¬IsZero E)
    (G : HNFiltration C s.P E) (hn : 0 < G.n) :
    G.phiMinus C hn ≤ s.phiMinus C E hE := by
  obtain ⟨F, hnF, hneF⟩ := HNFiltration.exists_nonzero_last C s hE
  rw [s.phiMinus_eq C E hE F hnF hneF]
  exact G.phiMinus_ge_of_nonzero_last_factor C s F hn hnF hneF

/-- If `E ∈ P(> t)` and `E` is nonzero, then `t < φ⁻(E)`. -/
lemma Slicing.phiMinus_gt_of_gtProp (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {t : ℝ} (hgt : s.gtProp C t E) : t < s.phiMinus C E hE := by
  rcases hgt with hZ | ⟨G, hGn, hGt⟩
  · exact absurd hZ hE
  · exact lt_of_lt_of_le hGt (s.phiMinus_ge_phiMinus_of_hn C hE G hGn)

/-- If `E ∈ P(≤ t)` and `E` is nonzero, then `φ⁺(E) ≤ t`. -/
lemma Slicing.phiPlus_le_of_leProp (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {t : ℝ} (hle : s.leProp C t E) : s.phiPlus C E hE ≤ t := by
  rcases hle with hZ | ⟨G, hGn, hGt⟩
  · exact absurd hZ hE
  · exact le_trans (s.phiPlus_le_phiPlus_of_hn C hE G hGn) hGt

/-- If `E ∈ P(< t)` and `E` is nonzero, then `φ⁺(E) < t`. -/
lemma Slicing.phiPlus_lt_of_ltProp (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {t : ℝ} (hlt : s.ltProp C t E) : s.phiPlus C E hE < t := by
  rcases hlt with hZ | ⟨G, hGn, hGt⟩
  · exact absurd hZ hE
  · exact lt_of_le_of_lt (s.phiPlus_le_phiPlus_of_hn C hE G hGn) hGt

/-- If `E ∈ P(≥ t)` and `E` is nonzero, then `t ≤ φ⁻(E)`. -/
lemma Slicing.phiMinus_ge_of_geProp (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {t : ℝ} (hge : s.geProp C t E) : t ≤ s.phiMinus C E hE := by
  rcases hge with hZ | ⟨G, hGn, hGt⟩
  · exact absurd hZ hE
  · exact le_trans hGt (s.phiMinus_ge_phiMinus_of_hn C hE G hGn)

/-- If `t < φ⁻(E)`, then `E ∈ P(> t)`. -/
lemma Slicing.gtProp_of_phiMinus_gt (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {t : ℝ} (hgt : t < s.phiMinus C E hE) : s.gtProp C t E := by
  obtain ⟨F, hn, _, hlast⟩ := HNFiltration.exists_both_nonzero C s hE
  refine Or.inr ⟨F, hn, ?_⟩
  simpa [s.phiMinus_eq C E hE F hn hlast] using hgt

/-- If `φ⁺(E) ≤ t`, then `E ∈ P(≤ t)`. -/
lemma Slicing.leProp_of_phiPlus_le (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {t : ℝ} (hle : s.phiPlus C E hE ≤ t) : s.leProp C t E := by
  obtain ⟨F, hn, hfirst, _⟩ := HNFiltration.exists_both_nonzero C s hE
  refine Or.inr ⟨F, hn, ?_⟩
  simpa [s.phiPlus_eq C E hE F hn hfirst] using hle

/-- If `φ⁺(E) < t`, then `E ∈ P(< t)`. -/
lemma Slicing.ltProp_of_phiPlus_lt (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {t : ℝ} (hlt : s.phiPlus C E hE < t) : s.ltProp C t E := by
  obtain ⟨F, hn, hfirst, _⟩ := HNFiltration.exists_both_nonzero C s hE
  refine Or.inr ⟨F, hn, ?_⟩
  simpa [s.phiPlus_eq C E hE F hn hfirst] using hlt

/-- If `t ≤ φ⁻(E)`, then `E ∈ P(≥ t)`. -/
lemma Slicing.geProp_of_phiMinus_ge (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {t : ℝ} (hge : t ≤ s.phiMinus C E hE) : s.geProp C t E := by
  obtain ⟨F, hn, _, hlast⟩ := HNFiltration.exists_both_nonzero C s hE
  refine Or.inr ⟨F, hn, ?_⟩
  simpa [s.phiMinus_eq C E hE F hn hlast] using hge

/-- **Interval containment from intrinsic phases.** If `a < φ⁻(E)` and `φ⁺(E) < b`, then
`E ∈ P((a, b))`. -/
lemma Slicing.intervalProp_of_intrinsic_phases (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {a b : ℝ} (hminus : a < s.phiMinus C E hE) (hplus : s.phiPlus C E hE < b) :
    s.intervalProp C a b E := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C s hE
  exact Or.inr ⟨F, fun i ↦ ⟨by
    calc a < s.phiMinus C E hE := hminus
      _ = F.φ ⟨F.n - 1, by omega⟩ := s.phiMinus_eq C E hE F hn hlast
      _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
    by calc F.φ i
        ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
      _ = s.phiPlus C E hE := (s.phiPlus_eq C E hE F hn hfirst).symm
      _ < b := hplus⟩⟩

/-! ### Contrapositive hom-vanishing lemmas -/

/-- If a semistable object of phase `φ` maps nonzero to `X`, then `φ ≤ φ⁺(X)`. This is the
contrapositive of `hom_eq_zero_of_gt_phases`. -/
lemma Slicing.phase_le_phiPlus_of_nonzero_hom (s : Slicing C) {A X : C} {φ : ℝ}
    (hA : (s.P φ) A) (hX : ¬IsZero X) (f : A ⟶ X) (hf : f ≠ 0) :
    φ ≤ s.phiPlus C X hX := by
  by_contra h
  push_neg at h
  obtain ⟨F, hnF, hneF⟩ := HNFiltration.exists_nonzero_first C s hX
  have hlt : ∀ j : Fin F.n, F.φ j < φ := fun j ↦
    calc F.φ j ≤ F.φ ⟨0, hnF⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val))
      _ = s.phiPlus C X hX := (s.phiPlus_eq C X hX F hnF hneF).symm
      _ < φ := h
  exact hf (s.hom_eq_zero_of_gt_phases C hA F hlt f)

/-- If `X` maps nonzero to a semistable object of phase `ψ`, then `φ⁻(X) ≤ ψ`. This is the
contrapositive of `hom_eq_zero_of_lt_phases`. -/
lemma Slicing.phiMinus_le_phase_of_nonzero_hom (s : Slicing C) {X B : C} {ψ : ℝ}
    (hB : (s.P ψ) B) (hX : ¬IsZero X) (f : X ⟶ B) (hf : f ≠ 0) :
    s.phiMinus C X hX ≤ ψ := by
  by_contra h
  push_neg at h
  obtain ⟨F, hnF, hneF⟩ := HNFiltration.exists_nonzero_last C s hX
  have hgt : ∀ j : Fin F.n, ψ < F.φ j := fun j ↦
    calc ψ < s.phiMinus C X hX := h
      _ = F.φ ⟨F.n - 1, by omega⟩ := s.phiMinus_eq C X hX F hnF hneF
      _ ≤ F.φ j := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
  exact hf (s.hom_eq_zero_of_lt_phases C hB F hgt f)


end Slicing

end CategoryTheory.Triangulated
