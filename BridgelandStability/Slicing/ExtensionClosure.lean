/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.Slicing.Phase

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

section Slicing

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]


/-!
# Extension-Closure of Subcategory Predicates

Closure of leProp/gtProp/ltProp/geProp under extensions in distinguished triangles,
and triangle phase-bound inequalities for slicings.
-/

/-! ### Extension-closure of subcategory predicates

The subcategory predicates `leProp` and `gtProp` are closed under extensions:
if a triangle `A → E → B → A⟦1⟧` is distinguished, and the outer objects satisfy
the predicate, then so does the middle object. The proofs use hom-vanishing and
the coYoneda/Yoneda exact sequences.
-/

/-- Extension-closure of `leProp`: if both `A` and `B` have all HN phases `≤ t`,
and `A → E → B → A⟦1⟧` is distinguished, then `E` also has all HN phases `≤ t`.

The proof uses the coYoneda exact sequence: if `φ⁺(E) > t`, then
`Hom(F⁺, A) = 0` and `Hom(F⁺, B) = 0` (by hom-vanishing), giving
`Hom(F⁺, E) = 0` by exactness, contradicting the nonzero first HN factor. -/
lemma Slicing.leProp_of_triangle (s : Slicing C) {A E B : C} (t : ℝ)
    (hA : s.leProp C t A) (hB : s.leProp C t B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.leProp C t E := by
  by_cases hEZ : IsZero E
  · exact Or.inl hEZ
  right
  obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_first C s hEZ
  refine ⟨FE, hnE, ?_⟩
  by_contra hgt
  push_neg at hgt
  -- F⁺ = FE.factor(0) is semistable of phase φ⁺(E) > t
  -- All maps F⁺ → A vanish
  have hA_vanish : ∀ α : (FE.triangle ⟨0, hnE⟩).obj₃ ⟶ A, α = 0 := by
    intro α
    rcases hA with hAZ | ⟨FA, hnA, hFA_le⟩
    · exact hAZ.eq_of_tgt α 0
    · exact s.hom_eq_zero_of_gt_phases C (FE.semistable ⟨0, hnE⟩) FA
        (fun i ↦ lt_of_le_of_lt
          (le_trans (FA.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val)))
            hFA_le) hgt) α
  -- All maps F⁺ → B vanish
  have hB_vanish : ∀ β : (FE.triangle ⟨0, hnE⟩).obj₃ ⟶ B, β = 0 := by
    intro β
    rcases hB with hBZ | ⟨FB, hnB, hFB_le⟩
    · exact hBZ.eq_of_tgt β 0
    · exact s.hom_eq_zero_of_gt_phases C (FE.semistable ⟨0, hnE⟩) FB
        (fun i ↦ lt_of_le_of_lt
          (le_trans (FB.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val)))
            hFB_le) hgt) β
  -- All maps F⁺ → E vanish (by coYoneda exactness)
  have hE_vanish :
      ∀ γ : (FE.triangle ⟨0, hnE⟩).obj₃ ⟶ E, γ = 0 := by
    intro γ
    obtain ⟨δ, hδ⟩ :=
      Triangle.coyoneda_exact₂ (Triangle.mk f g h) hT γ
        (hB_vanish (γ ≫ g))
    rw [hδ, hA_vanish δ]; exact zero_comp
  exact hneE (FE.isZero_factor_zero_of_hom_eq_zero C s hnE hE_vanish)

/-- Extension-closure of `ltProp`: if both `A` and `B` have all HN phases
`< t`, and `A → E → B → A⟦1⟧` is distinguished, then `E` also has all HN
phases `< t`. -/
lemma Slicing.ltProp_of_triangle (s : Slicing C) {A E B : C} (t : ℝ)
    (hA : s.ltProp C t A) (hB : s.ltProp C t B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.ltProp C t E := by
  by_cases hEZ : IsZero E
  · exact Or.inl hEZ
  right
  obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_first C s hEZ
  refine ⟨FE, hnE, ?_⟩
  by_contra hge
  push_neg at hge
  have hA_vanish : ∀ α : (FE.triangle ⟨0, hnE⟩).obj₃ ⟶ A, α = 0 := by
    intro α
    rcases hA with hAZ | ⟨FA, hnA, hFA_lt⟩
    · exact hAZ.eq_of_tgt α 0
    · exact s.hom_eq_zero_of_gt_phases C (FE.semistable ⟨0, hnE⟩) FA
        (fun i ↦ lt_of_le_of_lt
          (FA.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hFA_lt |>.trans_le hge) α
  have hB_vanish : ∀ β : (FE.triangle ⟨0, hnE⟩).obj₃ ⟶ B, β = 0 := by
    intro β
    rcases hB with hBZ | ⟨FB, hnB, hFB_lt⟩
    · exact hBZ.eq_of_tgt β 0
    · exact s.hom_eq_zero_of_gt_phases C (FE.semistable ⟨0, hnE⟩) FB
        (fun i ↦ lt_of_le_of_lt
          (FB.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hFB_lt |>.trans_le hge) β
  have hE_vanish :
      ∀ γ : (FE.triangle ⟨0, hnE⟩).obj₃ ⟶ E, γ = 0 := by
    intro γ
    obtain ⟨δ, hδ⟩ :=
      Triangle.coyoneda_exact₂ (Triangle.mk f g h) hT γ
        (hB_vanish (γ ≫ g))
    rw [hδ, hA_vanish δ]
    exact zero_comp
  exact hneE (FE.isZero_factor_zero_of_hom_eq_zero C s hnE hE_vanish)

/-- Extension-closure of `gtProp`: if both `A` and `B` have all HN phases
`> t`, and `A → E → B → A⟦1⟧` is distinguished, then `E` also has all HN
phases `> t`.

The proof uses the Yoneda exact sequence: if `φ⁻(E) ≤ t`, then
`Hom(A, F⁻) = 0` and `Hom(B, F⁻) = 0` (by hom-vanishing), giving
`Hom(E, F⁻) = 0` by exactness, contradicting the nonzero last HN factor. -/
lemma Slicing.gtProp_of_triangle (s : Slicing C) {A E B : C} (t : ℝ)
    (hA : s.gtProp C t A) (hB : s.gtProp C t B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.gtProp C t E := by
  by_cases hEZ : IsZero E
  · exact Or.inl hEZ
  right
  obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_last C s hEZ
  refine ⟨FE, hnE, ?_⟩
  by_contra hle
  push_neg at hle
  -- F⁻ = FE.factor(n-1) is semistable of phase φ⁻(E) ≤ t
  -- All maps A → F⁻ vanish
  have hA_vanish :
      ∀ α : A ⟶ (FE.triangle ⟨FE.n - 1, by omega⟩).obj₃, α = 0 := by
    intro α
    rcases hA with hAZ | ⟨FA, hnA, hFA_gt⟩
    · exact hAZ.eq_of_src α 0
    · exact s.hom_eq_zero_of_lt_phases C
        (FE.semistable ⟨FE.n - 1, by omega⟩) FA
        (fun i ↦ lt_of_le_of_lt hle
          (lt_of_lt_of_le hFA_gt
            (FA.hφ.antitone (Fin.mk_le_mk.mpr (by omega))))) α
  -- All maps B → F⁻ vanish
  have hB_vanish :
      ∀ β : B ⟶ (FE.triangle ⟨FE.n - 1, by omega⟩).obj₃, β = 0 := by
    intro β
    rcases hB with hBZ | ⟨FB, hnB, hFB_gt⟩
    · exact hBZ.eq_of_src β 0
    · exact s.hom_eq_zero_of_lt_phases C
        (FE.semistable ⟨FE.n - 1, by omega⟩) FB
        (fun i ↦ lt_of_le_of_lt hle
          (lt_of_lt_of_le hFB_gt
            (FB.hφ.antitone (Fin.mk_le_mk.mpr (by omega))))) β
  -- All maps E → F⁻ vanish (by Yoneda exactness)
  have hE_vanish :
      ∀ γ : E ⟶ (FE.triangle ⟨FE.n - 1, by omega⟩).obj₃, γ = 0 := by
    intro γ
    obtain ⟨δ, hδ⟩ :=
      Triangle.yoneda_exact₂ (Triangle.mk f g h) hT γ
        (hA_vanish (f ≫ γ))
    rw [hδ, hB_vanish δ]; exact comp_zero
  exact hneE (FE.isZero_factor_last_of_hom_eq_zero C s hnE hE_vanish)

/-- If `A → E → B → A⟦1⟧` is distinguished and `A`, `B` both have
`φ⁺ < t`, then so does `E`. Proved by contradiction using coYoneda exactness. -/
lemma Slicing.phiPlus_lt_of_triangle (s : Slicing C) {A E B : C}
    (hE : ¬IsZero E) {t : ℝ}
    (hA_lt : ∀ (hA : ¬IsZero A), s.phiPlus C A hA < t)
    (hB_lt : ∀ (hB : ¬IsZero B), s.phiPlus C B hB < t)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.phiPlus C E hE < t := by
  by_contra hge
  push_neg at hge
  obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_first C s hE
  -- F⁺ has phase φ⁺(E) ≥ t
  have hFE_ge : t ≤ FE.φ ⟨0, hnE⟩ := by
    rw [← s.phiPlus_eq C E hE FE hnE hneE]; exact hge
  -- All maps F⁺ → A vanish
  have hA_vanish : ∀ α : (FE.triangle ⟨0, hnE⟩).obj₃ ⟶ A, α = 0 := by
    intro α
    by_cases hAZ : IsZero A
    · exact hAZ.eq_of_tgt α 0
    · obtain ⟨FA, hnA, hneA⟩ :=
        HNFiltration.exists_nonzero_first C s hAZ
      have hFA_lt : FA.φ ⟨0, hnA⟩ < t := by
        rw [← s.phiPlus_eq C A hAZ FA hnA hneA]; exact hA_lt hAZ
      exact s.hom_eq_zero_of_gt_phases C (FE.semistable ⟨0, hnE⟩) FA
        (fun i ↦ lt_of_le_of_lt
          (FA.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val)))
          (lt_of_lt_of_le hFA_lt hFE_ge)) α
  -- All maps F⁺ → B vanish
  have hB_vanish : ∀ β : (FE.triangle ⟨0, hnE⟩).obj₃ ⟶ B, β = 0 := by
    intro β
    by_cases hBZ : IsZero B
    · exact hBZ.eq_of_tgt β 0
    · obtain ⟨FB, hnB, hneB⟩ :=
        HNFiltration.exists_nonzero_first C s hBZ
      have hFB_lt : FB.φ ⟨0, hnB⟩ < t := by
        rw [← s.phiPlus_eq C B hBZ FB hnB hneB]; exact hB_lt hBZ
      exact s.hom_eq_zero_of_gt_phases C (FE.semistable ⟨0, hnE⟩) FB
        (fun i ↦ lt_of_le_of_lt
          (FB.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val)))
          (lt_of_lt_of_le hFB_lt hFE_ge)) β
  -- All maps F⁺ → E vanish, contradiction
  have hE_vanish :
      ∀ γ : (FE.triangle ⟨0, hnE⟩).obj₃ ⟶ E, γ = 0 := by
    intro γ
    obtain ⟨δ, hδ⟩ :=
      Triangle.coyoneda_exact₂ (Triangle.mk f g h) hT γ
        (hB_vanish (γ ≫ g))
    rw [hδ, hA_vanish δ]; exact zero_comp
  exact hneE (FE.isZero_factor_zero_of_hom_eq_zero C s hnE hE_vanish)

/-- If `A → E → B → A⟦1⟧` is distinguished and `A`, `B` both have
`φ⁻ > t`, then so does `E`. Proved by contradiction using Yoneda exactness. -/
lemma Slicing.phiMinus_gt_of_triangle (s : Slicing C) {A E B : C}
    (hE : ¬IsZero E) {t : ℝ}
    (hA_gt : ∀ (hA : ¬IsZero A), t < s.phiMinus C A hA)
    (hB_gt : ∀ (hB : ¬IsZero B), t < s.phiMinus C B hB)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    t < s.phiMinus C E hE := by
  by_contra hle
  push_neg at hle
  obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_last C s hE
  -- F⁻ has phase φ⁻(E) ≤ t
  have hFE_le : FE.φ ⟨FE.n - 1, by omega⟩ ≤ t := by
    rw [← s.phiMinus_eq C E hE FE hnE hneE]; exact hle
  -- All maps A → F⁻ vanish
  have hA_vanish :
      ∀ α : A ⟶ (FE.triangle ⟨FE.n - 1, by omega⟩).obj₃, α = 0 := by
    intro α
    by_cases hAZ : IsZero A
    · exact hAZ.eq_of_src α 0
    · obtain ⟨FA, hnA, hneA⟩ :=
        HNFiltration.exists_nonzero_last C s hAZ
      have hFA_gt : t < FA.φ ⟨FA.n - 1, by omega⟩ := by
        rw [← s.phiMinus_eq C A hAZ FA hnA hneA]; exact hA_gt hAZ
      exact s.hom_eq_zero_of_lt_phases C
        (FE.semistable ⟨FE.n - 1, by omega⟩) FA
        (fun i ↦ lt_of_le_of_lt hFE_le
          (lt_of_lt_of_le hFA_gt
            (FA.hφ.antitone (Fin.mk_le_mk.mpr (by omega))))) α
  -- All maps B → F⁻ vanish
  have hB_vanish :
      ∀ β : B ⟶ (FE.triangle ⟨FE.n - 1, by omega⟩).obj₃, β = 0 := by
    intro β
    by_cases hBZ : IsZero B
    · exact hBZ.eq_of_src β 0
    · obtain ⟨FB, hnB, hneB⟩ :=
        HNFiltration.exists_nonzero_last C s hBZ
      have hFB_gt : t < FB.φ ⟨FB.n - 1, by omega⟩ := by
        rw [← s.phiMinus_eq C B hBZ FB hnB hneB]; exact hB_gt hBZ
      exact s.hom_eq_zero_of_lt_phases C
        (FE.semistable ⟨FE.n - 1, by omega⟩) FB
        (fun i ↦ lt_of_le_of_lt hFE_le
          (lt_of_lt_of_le hFB_gt
            (FB.hφ.antitone (Fin.mk_le_mk.mpr (by omega))))) β
  -- All maps E → F⁻ vanish, contradiction
  have hE_vanish :
      ∀ γ : E ⟶ (FE.triangle ⟨FE.n - 1, by omega⟩).obj₃, γ = 0 := by
    intro γ
    obtain ⟨δ, hδ⟩ :=
      Triangle.yoneda_exact₂ (Triangle.mk f g h) hT γ
        (hA_vanish (f ≫ γ))
    rw [hδ, hB_vanish δ]; exact comp_zero
  exact hneE (FE.isZero_factor_last_of_hom_eq_zero C s hnE hE_vanish)

/-- **Extension-closure of `intervalProp`**: if both `A` and `B` have HN phases in the
open interval `(a, b)`, and `A → E → B → A⟦1⟧` is distinguished, then `E` also has
HN phases in `(a, b)`. -/
lemma Slicing.intervalProp_of_triangle (s : Slicing C) {A E B : C} {a b : ℝ}
    (hA : s.intervalProp C a b A) (hB : s.intervalProp C a b B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a b E := by
  by_cases hEZ : IsZero E
  · exact Or.inl hEZ
  right
  have hPlus : s.phiPlus C E hEZ < b :=
    s.phiPlus_lt_of_triangle C hEZ
      (fun hA' ↦ s.phiPlus_lt_of_intervalProp C hA' hA)
      (fun hB' ↦ s.phiPlus_lt_of_intervalProp C hB' hB) hT
  have hMinus : a < s.phiMinus C E hEZ :=
    s.phiMinus_gt_of_triangle C hEZ
      (fun hA' ↦ s.phiMinus_gt_of_intervalProp C hA' hA)
      (fun hB' ↦ s.phiMinus_gt_of_intervalProp C hB' hB) hT
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C s hEZ
  exact ⟨F, fun i ↦ ⟨by
    calc a < s.phiMinus C E hEZ := hMinus
      _ = F.φ ⟨F.n - 1, by omega⟩ := s.phiMinus_eq C E hEZ F hn hlast
      _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
    by calc F.φ i
        ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
      _ = s.phiPlus C E hEZ := (s.phiPlus_eq C E hEZ F hn hfirst).symm
      _ < b := hPlus⟩⟩

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

/-- **Lemma 3.4** (right inequality). In a distinguished triangle `A → E → B → A⟦1⟧`
where the phases of A and B lie in an interval `(a, b)` with `b ≤ a + 1`,
we have `φ⁻(E) ≤ φ⁻(B)`.

The proof uses the Yoneda exact sequence: if `φ⁻(E) > φ⁻(B)`, then maps `E → B⁻`
vanish by hom-vanishing; by exactness, maps `B → B⁻` factor through `A⟦1⟧`, but
A's shifted phases are too high, so all maps `A⟦1⟧ → B⁻` vanish too, giving
`B⁻ = 0`, a contradiction. -/
theorem Slicing.phiMinus_triangle_le (s : Slicing C) {A E B : C}
    (hB : ¬IsZero B) (hE : ¬IsZero E)
    {a b : ℝ} (hab : b ≤ a + 1)
    (hA_int : s.intervalProp C a b A)
    (hB_int : s.intervalProp C a b B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.phiMinus C E hE ≤ s.phiMinus C B hB := by
  -- Get filtrations with nonzero last factors
  obtain ⟨FB, hnB, hneB⟩ := HNFiltration.exists_nonzero_last C s hB
  obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_last C s hE
  rw [s.phiMinus_eq C E hE FE hnE hneE, s.phiMinus_eq C B hB FB hnB hneB]
  -- Suppose for contradiction that φ⁻(E) > φ⁻(B)
  by_contra hlt
  push_neg at hlt
  -- All E-phases > FB.φ(n-1)
  have hE_gap : ∀ j : Fin FE.n, FB.φ ⟨FB.n - 1, by omega⟩ < FE.φ j := fun j ↦
    lt_of_lt_of_le hlt (FE.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
  -- All maps B → B⁻ are zero
  have hB_factor_zero :
      ∀ α : B ⟶ (FB.triangle ⟨FB.n - 1, by omega⟩).obj₃, α = 0 := by
    intro α
    -- g ≫ α : E → B⁻ is zero by hom-vanishing
    have hgα : g ≫ α = 0 :=
      s.hom_eq_zero_of_lt_phases C (FB.semistable ⟨FB.n - 1, by omega⟩) FE hE_gap _
    -- By yoneda_exact₃ on T, α = h ≫ γ for some γ : A⟦1⟧ → B⁻
    obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₃ (Triangle.mk f g h) hT α hgα
    -- Show γ = 0
    suffices hγ0 : γ = 0 by rw [hγ, hγ0]; exact comp_zero
    by_cases hAZ : IsZero A
    · exact ((shiftFunctor C (1 : ℤ)).map_isZero hAZ).eq_of_src γ 0
    · -- Get an HN filtration of A⟦1⟧ from hA_int
      rcases hA_int with hAZ' | ⟨GA, hGA⟩
      · exact absurd hAZ' hAZ
      · -- Shift GA by 1 to get filtration of A⟦1⟧
        let GAs := GA.shiftHN C s (1 : ℤ)
        -- GAs.φ(j) = GA.φ(j) + 1 > a + 1 ≥ b > FB.φ(n-1)
        have hAs_gap : ∀ j : Fin GAs.n,
            FB.φ ⟨FB.n - 1, by omega⟩ < GAs.φ j := by
          intro j
          change FB.φ ⟨FB.n - 1, by omega⟩ < GA.φ j + ((1 : ℤ) : ℝ)
          have h1 : GA.φ j > a := (hGA j).1
          have h2 : FB.φ ⟨FB.n - 1, by omega⟩ < b := by
            calc FB.φ ⟨FB.n - 1, by omega⟩
                = s.phiMinus C B hB :=
                  (s.phiMinus_eq C B hB FB hnB hneB).symm
              _ ≤ s.phiPlus C B hB := s.phiMinus_le_phiPlus C B hB
              _ < b := s.phiPlus_lt_of_intervalProp C hB hB_int
          have h3 : ((1 : ℤ) : ℝ) = 1 := by norm_num
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FB.semistable ⟨FB.n - 1, by omega⟩) GAs hAs_gap γ
  -- But B⁻ is nonzero and all maps B → B⁻ vanish — contradiction
  exact hneB (FB.isZero_factor_last_of_hom_eq_zero C s hnB hB_factor_zero)

/-- Variant of **Lemma 3.4** (`phiMinus_triangle_le`) where the hypothesis `B ∈ P((a,b))`
is weakened to `φ⁺(B) < b`. For a distinguished triangle `A → E → B → A⟦1⟧`
with `A ∈ P((a, b))` and `b ≤ a + 1`, if `φ⁺(B) < b` then `φ⁻(E) ≤ φ⁻(B)`. -/
theorem Slicing.phiMinus_triangle_le' (s : Slicing C) {A E B : C}
    (hB : ¬IsZero B) (hE : ¬IsZero E)
    {a b : ℝ} (hab : b ≤ a + 1)
    (hA_int : s.intervalProp C a b A)
    (hB_phiPlus_lt : s.phiPlus C B hB < b)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.phiMinus C E hE ≤ s.phiMinus C B hB := by
  obtain ⟨FB, hnB, hneB⟩ := HNFiltration.exists_nonzero_last C s hB
  obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_last C s hE
  rw [s.phiMinus_eq C E hE FE hnE hneE, s.phiMinus_eq C B hB FB hnB hneB]
  by_contra hlt
  push_neg at hlt
  have hE_gap : ∀ j : Fin FE.n, FB.φ ⟨FB.n - 1, by omega⟩ < FE.φ j := fun j ↦
    lt_of_lt_of_le hlt (FE.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
  have hB_factor_zero :
      ∀ α : B ⟶ (FB.triangle ⟨FB.n - 1, by omega⟩).obj₃, α = 0 := by
    intro α
    have hgα : g ≫ α = 0 :=
      s.hom_eq_zero_of_lt_phases C (FB.semistable ⟨FB.n - 1, by omega⟩) FE hE_gap _
    obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₃ (Triangle.mk f g h) hT α hgα
    suffices hγ0 : γ = 0 by rw [hγ, hγ0]; exact comp_zero
    by_cases hAZ : IsZero A
    · exact ((shiftFunctor C (1 : ℤ)).map_isZero hAZ).eq_of_src γ 0
    · rcases hA_int with hAZ' | ⟨GA, hGA⟩
      · exact absurd hAZ' hAZ
      · let GAs := GA.shiftHN C s (1 : ℤ)
        have hAs_gap : ∀ j : Fin GAs.n,
            FB.φ ⟨FB.n - 1, by omega⟩ < GAs.φ j := by
          intro j
          change FB.φ ⟨FB.n - 1, by omega⟩ < GA.φ j + ((1 : ℤ) : ℝ)
          have h1 : GA.φ j > a := (hGA j).1
          have h2 : FB.φ ⟨FB.n - 1, by omega⟩ < b := by
            calc FB.φ ⟨FB.n - 1, by omega⟩
                = s.phiMinus C B hB :=
                  (s.phiMinus_eq C B hB FB hnB hneB).symm
              _ ≤ s.phiPlus C B hB := s.phiMinus_le_phiPlus C B hB
              _ < b := hB_phiPlus_lt
          have h3 : ((1 : ℤ) : ℝ) = 1 := by norm_num
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FB.semistable ⟨FB.n - 1, by omega⟩) GAs hAs_gap γ
  exact hneB (FB.isZero_factor_last_of_hom_eq_zero C s hnB hB_factor_zero)


end Slicing

end CategoryTheory.Triangulated
