/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Slicing.TStructure

/-!
# HN Filtration Assembly

Generic operations on HN filtrations: appending across triangles (with lower and upper
phase bounds) and splitting at arbitrary cutoffs.
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

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

theorem semistable_of_hn_length_one
    {P : ℝ → ObjectProperty C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    {Y : C} (GY : HNFiltration C P Y) (h1 : GY.n = 1) :
    P (GY.φ ⟨0, by omega⟩) Y := by
  let j0 : Fin GY.n := ⟨0, by omega⟩
  let T := GY.triangle j0
  have hZ1 : IsZero T.obj₁ :=
    IsZero.of_iso GY.base_isZero (Classical.choice (GY.triangle_obj₁ j0))
  have hIso₂ : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (GY.triangle_dist j0)).mp hZ1
  have hobj₂_eq : GY.chain.obj' (0 + 1) (by omega) = GY.chain.obj (Fin.last GY.n) :=
    congrArg GY.chain.obj (Fin.ext (by simp [Fin.last, h1]))
  let e₂Y : T.obj₂ ≅ Y :=
    (Classical.choice (GY.triangle_obj₂ j0)).trans
      ((eqToIso hobj₂_eq).trans (Classical.choice GY.top_iso))
  letI : (P (GY.φ j0)).IsClosedUnderIsomorphisms := hPiso (GY.φ j0)
  exact (P (GY.φ j0)).prop_of_iso ((e₂Y.symm.trans (asIso T.mor₂)).symm) (GY.semistable j0)

/-- Concatenate HN filtrations across a distinguished triangle `X → E → Y → X[1]`,
provided every phase in the filtration on `Y` is strictly smaller than every phase in the
filtration on `X`. This is the generic Postnikov-splicing step needed to assemble the
faithful Section 7 HN filtration from filtrations on successive σ-semistable factors. -/
theorem append_hn_filtration_of_triangle
    [IsTriangulated C]
    {P : ℝ → ObjectProperty C} {X E Y : C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    (GX : HNFiltration C P X)
    (GY : HNFiltration C P Y)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C)
    (t : ℝ)
    (hX_gt : ∀ j : Fin GX.n, t < GX.φ j)
    (hY_gt : ∀ i : Fin GY.n, t < GY.φ i)
    (hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) :
    ∃ G : HNFiltration C P E, ∀ j : Fin G.n, t < G.φ j := by
  suffices hmain :
      ∀ (m : ℕ) {Y : C} (GY : HNFiltration C P Y), GY.n ≤ m →
        ∀ {E : C} (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C →
          ∀ (t : ℝ),
          (∀ j : Fin GX.n, t < GX.φ j) →
          (∀ i : Fin GY.n, t < GY.φ i) →
          (∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) →
          ∃ G : HNFiltration C P E, ∀ j : Fin G.n, t < G.φ j by
    exact hmain GY.n GY le_rfl f g h hT t hX_gt hY_gt hsep
  intro m
  induction m with
  | zero =>
      intro Y GY hn E f g h hT t hX_gt hY_gt hsep
      have hYn : GY.n = 0 := by omega
      have hYz : IsZero Y := GY.zero_isZero hYn
      haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
      refine ⟨GX.ofIso C (asIso f), ?_⟩
      intro j
      simpa using hX_gt j
  | succ m ih =>
      intro Y GY hn E f g h hT t hX_gt hY_gt hsep
      by_cases hYn : GY.n = 0
      · have hYz : IsZero Y := GY.zero_isZero hYn
        haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
        refine ⟨GX.ofIso C (asIso f), ?_⟩
        intro j
        simpa using hX_gt j
      · have hYpos : 0 < GY.n := Nat.pos_of_ne_zero hYn
        by_cases hYone : GY.n = 1
        · let j0 : Fin GY.n := ⟨0, by omega⟩
          have hsep0 : ∀ j : Fin GX.n, GY.φ j0 < GX.φ j := by
            intro j
            exact hsep j0 j
          have hYss : P (GY.φ j0) Y :=
            semistable_of_hn_length_one (C := C) hPiso GY hYone
          refine ⟨GX.appendFactor C (Triangle.mk f g h) hT (Iso.refl _) (Iso.refl _)
            (GY.φ j0) hYss hsep0, ?_⟩
          intro j
          by_cases hj : j.val < GX.n
          · have hsmall :
                GY.φ j0 <
                  (GX.appendFactor C (Triangle.mk f g h) hT (Iso.refl _) (Iso.refl _)
                    (GY.φ j0) hYss hsep0).φ j := by
              simpa [HNFiltration.appendFactor, hj] using hsep0 ⟨j.val, hj⟩
            exact lt_trans (hY_gt j0) hsmall
          · have hjLast :
                (GX.appendFactor C (Triangle.mk f g h) hT (Iso.refl _) (Iso.refl _)
                  (GY.φ j0) hYss hsep0).φ j = GY.φ j0 := by
              simp [HNFiltration.appendFactor, hj]
            exact hjLast.symm ▸ hY_gt j0
        · have hYtwo : 2 ≤ GY.n := by omega
          let jLast : Fin GY.n := ⟨GY.n - 1, by omega⟩
          let GY' := GY.prefix C (GY.n - 1) (by omega) (by omega)
          let Tlast := GY.triangle jLast
          let e₁ := Classical.choice (GY.triangle_obj₁ jLast)
          let e₂ := Classical.choice (GY.triangle_obj₂ jLast)
          let eY := by
            have hchainN : GY.chain.obj' (GY.n - 1 + 1) (by omega) =
                GY.chain.obj (Fin.last GY.n) :=
              congrArg GY.chain.obj (Fin.ext (by simp [Fin.last]; omega))
            exact e₂.trans ((eqToIso hchainN).trans (Classical.choice GY.top_iso))
          let f23 : GY.chain.obj ⟨GY.n - 1, by omega⟩ ⟶ Y :=
            e₁.inv ≫ Tlast.mor₁ ≫ eY.hom
          let g23 : Y ⟶ Tlast.obj₃ :=
            eY.inv ≫ Tlast.mor₂
          let h23 : Tlast.obj₃ ⟶ GY.chain.obj ⟨GY.n - 1, by omega⟩⟦(1 : ℤ)⟧ :=
            Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hT23 : Triangle.mk f23 g23 h23 ∈ distTriang C := by
            refine isomorphic_distinguished _ (GY.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm eY.symm (Iso.refl _)
              (by simp [Tlast, f23, eY])
              (by simp [Tlast, g23, eY])
              (by simp [Tlast, h23])
          obtain ⟨Z, f13, h13, hT13⟩ := distinguished_cocone_triangle₁ (g ≫ g23)
          let oct := Triangulated.someOctahedron'
            (show g ≫ g23 = g ≫ g23 by rfl) hT hT23 hT13
          have hsep' :
              ∀ i : Fin GY'.n, ∀ j : Fin GX.n, GY'.φ i < GX.φ j := by
            intro i j
            have hEqn : GY'.n = GY.n - 1 := rfl
            have hi : i.val < GY.n - 1 := by
              simpa [hEqn] using i.is_lt
            exact hsep ⟨i.val, by omega⟩ j
          have hX_gt_last : ∀ j : Fin GX.n, GY.φ jLast < GX.φ j := by
            intro j
            exact hsep jLast j
          have hY'_gt_last : ∀ i : Fin GY'.n, GY.φ jLast < GY'.φ i := by
            intro i
            have hEqn : GY'.n = GY.n - 1 := rfl
            have hi : i.val < GY.n - 1 := by
              simpa [hEqn] using i.is_lt
            change GY.φ jLast < GY.φ ⟨i.val, by omega⟩
            exact GY.hφ (show (⟨i.val, by omega⟩ : Fin GY.n) < jLast by
              exact Fin.mk_lt_mk.mpr (by omega))
          obtain ⟨GZ, hGZ⟩ := ih GY' (by
            change GY.n - 1 ≤ m
            omega) oct.triangle.mor₁ oct.triangle.mor₂ oct.triangle.mor₃ oct.mem
            (GY.φ jLast) hX_gt_last hY'_gt_last hsep'
          have hlast_gt_t : t < GY.φ jLast := hY_gt jLast
          refine ⟨GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
            (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast) hGZ, ?_⟩
          intro j
          by_cases hj : j.val < GZ.n
          · have hsmall :
                GY.φ jLast <
                  (GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
                    (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast)
                    hGZ).φ j := by
              simpa [HNFiltration.appendFactor, hj] using hGZ ⟨j.val, hj⟩
            exact lt_trans hlast_gt_t hsmall
          · have hjLast :
                (GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
                  (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast) hGZ).φ j =
                    GY.φ jLast := by
              simp [HNFiltration.appendFactor, hj]
            exact hjLast.symm ▸ hlast_gt_t

/-- Upper-bound companion for `append_hn_filtration_of_triangle`: if all input phases
are `≤ U`, so are all output phases. Follows from `appendFactor`'s phase structure
(`φ j = if j < G.n then G.φ j else ψ`). -/
theorem append_hn_filtration_of_triangle_le
    [IsTriangulated C]
    {P : ℝ → ObjectProperty C} {X E Y : C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C)
    (t U : ℝ)
    (hX_gt : ∀ j : Fin GX.n, t < GX.φ j)
    (hY_gt : ∀ i : Fin GY.n, t < GY.φ i)
    (hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j)
    (hX_le : ∀ j : Fin GX.n, GX.φ j ≤ U)
    (hY_le : ∀ i : Fin GY.n, GY.φ i ≤ U) :
    ∃ G : HNFiltration C P E, (∀ j : Fin G.n, t < G.φ j) ∧ (∀ j : Fin G.n, G.φ j ≤ U) := by
  suffices hmain :
      ∀ (m : ℕ) {Y : C} (GY : HNFiltration C P Y), GY.n ≤ m →
        ∀ {E : C} (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C →
          ∀ (t : ℝ),
          (∀ j : Fin GX.n, t < GX.φ j) →
          (∀ i : Fin GY.n, t < GY.φ i) →
          (∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) →
          (∀ j : Fin GX.n, GX.φ j ≤ U) →
          (∀ i : Fin GY.n, GY.φ i ≤ U) →
          ∃ G : HNFiltration C P E,
            (∀ j : Fin G.n, t < G.φ j) ∧ (∀ j : Fin G.n, G.φ j ≤ U) by
    exact hmain GY.n GY le_rfl f g h hT t hX_gt hY_gt hsep hX_le hY_le
  intro m
  induction m with
  | zero =>
      intro Y GY hn E f g h hT t hX_gt hY_gt hsep hX_le hY_le
      have hYn : GY.n = 0 := by omega
      have hYz : IsZero Y := GY.zero_isZero hYn
      haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
      refine ⟨GX.ofIso C (asIso f), fun j ↦ ?_, fun j ↦ ?_⟩
      · simpa using hX_gt j
      · simpa using hX_le j
  | succ m ih =>
      intro Y GY hn E f g h hT t hX_gt hY_gt hsep hX_le hY_le
      by_cases hYn : GY.n = 0
      · have hYz : IsZero Y := GY.zero_isZero hYn
        haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
        refine ⟨GX.ofIso C (asIso f), fun j ↦ ?_, fun j ↦ ?_⟩
        · simpa using hX_gt j
        · simpa using hX_le j
      · have hYpos : 0 < GY.n := Nat.pos_of_ne_zero hYn
        by_cases hYone : GY.n = 1
        · let j0 : Fin GY.n := ⟨0, by omega⟩
          have hsep0 : ∀ j : Fin GX.n, GY.φ j0 < GX.φ j := fun j ↦ hsep j0 j
          have hYss : P (GY.φ j0) Y :=
            semistable_of_hn_length_one (C := C) hPiso GY hYone
          refine ⟨GX.appendFactor C (Triangle.mk f g h) hT (Iso.refl _) (Iso.refl _)
            (GY.φ j0) hYss hsep0, fun j ↦ ?_, fun j ↦ ?_⟩
          · by_cases hj : j.val < GX.n
            · have : GY.φ j0 <
                  (GX.appendFactor C _ hT (Iso.refl _) (Iso.refl _) (GY.φ j0) hYss hsep0).φ j := by
                simpa [HNFiltration.appendFactor, hj] using hsep0 ⟨j.val, hj⟩
              exact lt_trans (hY_gt j0) this
            · have : (GX.appendFactor C _ hT (Iso.refl _) (Iso.refl _)
                  (GY.φ j0) hYss hsep0).φ j = GY.φ j0 := by
                simp [HNFiltration.appendFactor, hj]
              exact this.symm ▸ hY_gt j0
          · by_cases hj : j.val < GX.n
            · simp only [HNFiltration.appendFactor, hj, dite_true]
              exact hX_le ⟨j.val, hj⟩
            · simp only [HNFiltration.appendFactor, hj, dite_false]
              exact hY_le j0
        · have hYtwo : 2 ≤ GY.n := by omega
          let jLast : Fin GY.n := ⟨GY.n - 1, by omega⟩
          let GY' := GY.prefix C (GY.n - 1) (by omega) (by omega)
          let Tlast := GY.triangle jLast
          let e₁ := Classical.choice (GY.triangle_obj₁ jLast)
          let e₂ := Classical.choice (GY.triangle_obj₂ jLast)
          let eY := by
            have hchainN : GY.chain.obj' (GY.n - 1 + 1) (by omega) =
                GY.chain.obj (Fin.last GY.n) :=
              congrArg GY.chain.obj (Fin.ext (by simp [Fin.last]; omega))
            exact e₂.trans ((eqToIso hchainN).trans (Classical.choice GY.top_iso))
          let f23 : GY.chain.obj ⟨GY.n - 1, by omega⟩ ⟶ Y :=
            e₁.inv ≫ Tlast.mor₁ ≫ eY.hom
          let g23 : Y ⟶ Tlast.obj₃ := eY.inv ≫ Tlast.mor₂
          let h23 : Tlast.obj₃ ⟶ GY.chain.obj ⟨GY.n - 1, by omega⟩⟦(1 : ℤ)⟧ :=
            Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hT23 : Triangle.mk f23 g23 h23 ∈ distTriang C := by
            refine isomorphic_distinguished _ (GY.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm eY.symm (Iso.refl _)
              (by simp [Tlast, f23, eY]) (by simp [Tlast, g23, eY]) (by simp [Tlast, h23])
          obtain ⟨Z, f13, h13, hT13⟩ := distinguished_cocone_triangle₁ (g ≫ g23)
          let oct := Triangulated.someOctahedron'
            (show g ≫ g23 = g ≫ g23 by rfl) hT hT23 hT13
          have hsep' : ∀ i : Fin GY'.n, ∀ j : Fin GX.n, GY'.φ i < GX.φ j := by
            intro i j
            have hi : i.val < GY.n - 1 := i.is_lt
            exact hsep ⟨i.val, by omega⟩ j
          have hX_gt_last : ∀ j : Fin GX.n, GY.φ jLast < GX.φ j := fun j ↦ hsep jLast j
          have hY'_gt_last : ∀ i : Fin GY'.n, GY.φ jLast < GY'.φ i := by
            intro i
            have hi : i.val < GY.n - 1 := i.is_lt
            change GY.φ jLast < GY.φ ⟨i.val, by omega⟩
            exact GY.hφ (Fin.mk_lt_mk.mpr (by omega))
          obtain ⟨GZ, hGZ_lo, hGZ_le⟩ := ih GY' (by
            change GY.n - 1 ≤ m; omega)
            oct.triangle.mor₁ oct.triangle.mor₂ oct.triangle.mor₃ oct.mem
            (GY.φ jLast) hX_gt_last hY'_gt_last hsep'
            (fun j ↦ hX_le j)
            (fun i ↦ by
              have hi : i.val < GY.n - 1 := i.is_lt
              exact hY_le ⟨i.val, by omega⟩)
          have hlast_gt_t : t < GY.φ jLast := hY_gt jLast
          refine ⟨GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
            (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast) hGZ_lo,
            fun j ↦ ?_, fun j ↦ ?_⟩
          · by_cases hj : j.val < GZ.n
            · have : GY.φ jLast <
                  (GZ.appendFactor C _ hT13 (Iso.refl _) (Iso.refl _) (GY.φ jLast)
                    (GY.semistable jLast) hGZ_lo).φ j := by
                simpa [HNFiltration.appendFactor, hj] using hGZ_lo ⟨j.val, hj⟩
              exact lt_trans hlast_gt_t this
            · have : (GZ.appendFactor C _ hT13 (Iso.refl _) (Iso.refl _) (GY.φ jLast)
                  (GY.semistable jLast) hGZ_lo).φ j = GY.φ jLast := by
                simp [HNFiltration.appendFactor, hj]
              exact this.symm ▸ hlast_gt_t
          · by_cases hj : j.val < GZ.n
            · simp only [HNFiltration.appendFactor, hj, dite_true]
              exact hGZ_le ⟨j.val, hj⟩
            · simp only [HNFiltration.appendFactor, hj, dite_false]
              exact hY_le jLast

/-- Split an HN filtration at an arbitrary cutoff `t`. The `X`-part carries a filtration whose
phases are all `> t`, and the `Y`-part carries a filtration whose phases are all `≤ t`.

The strengthened conclusion tracks that every phase of the `Y`-part is bounded below by the
last phase of the original filtration. This is the generic cutoff invariant needed to append the
last factor in the mixed case, exactly as in Bridgeland's p.24 argument. -/
theorem split_hn_filtration_at_cutoff
    [IsTriangulated C]
    {P : ℝ → ObjectProperty C} {A : C}
    (F : HNFiltration C P A) (t : ℝ) :
    ∃ (X Y : C) (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      (∀ j : Fin GX.n, t < GX.φ j) ∧
      (∀ j : Fin GY.n, GY.φ j ≤ t) ∧
      (∀ (_ : 0 < F.n) (j : Fin GY.n),
        F.φ ⟨F.n - 1, by omega⟩ ≤ GY.φ j) ∧
      (∀ j : Fin GX.n, ∃ i : Fin F.n, GX.φ j = F.φ i) := by
  suffices hmain :
      ∀ (m : ℕ) (A : C) (F : HNFiltration C P A), F.n ≤ m →
        ∃ (X Y : C) (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
          (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C ∧
          (∀ j : Fin GX.n, t < GX.φ j) ∧
          (∀ j : Fin GY.n, GY.φ j ≤ t) ∧
          (∀ (_ : 0 < F.n) (j : Fin GY.n),
            F.φ ⟨F.n - 1, by omega⟩ ≤ GY.φ j) ∧
          (∀ j : Fin GX.n, ∃ i : Fin F.n, GX.φ j = F.φ i) by
    exact hmain F.n A F le_rfl
  intro m
  induction m with
  | zero =>
      intro A F hFn
      have hn : F.n = 0 := by omega
      refine ⟨A, 0, F, HNFiltration.zero C (P := P) 0 (isZero_zero C),
        𝟙 A, 0, 0, contractible_distinguished A, ?_, ?_, ?_, ?_⟩
      · intro j; exact False.elim (by simpa [hn] using j.is_lt)
      · intro j; exact Fin.elim0 j
      · intro hn0 j; exact False.elim (by omega)
      · intro j; exact False.elim (by simpa [hn] using j.isLt)
  | succ m ih =>
      intro A F hFn
      by_cases hn : F.n = 0
      · refine ⟨A, 0, F, HNFiltration.zero C (P := P) 0 (isZero_zero C),
          𝟙 A, 0, 0, contractible_distinguished A, ?_, ?_, ?_, ?_⟩
        · intro j; exact False.elim (by simpa [hn] using j.is_lt)
        · intro j; exact Fin.elim0 j
        · intro hn0 j; exact False.elim (by omega)
        · intro j; exact False.elim (by simpa [hn] using j.isLt)
      · have hn0 : 0 < F.n := Nat.pos_of_ne_zero hn
        by_cases hlast_gt : t < F.φ ⟨F.n - 1, by omega⟩
        · refine ⟨A, 0, F, HNFiltration.zero C (P := P) 0 (isZero_zero C),
            𝟙 A, 0, 0, contractible_distinguished A, ?_, ?_, ?_, ?_⟩
          · intro j; exact lt_of_lt_of_le hlast_gt
              (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
          · intro j; exact Fin.elim0 j
          · intro _ j; exact Fin.elim0 j
          · intro j; exact ⟨j, rfl⟩
        · have hlast_le : F.φ ⟨F.n - 1, by omega⟩ ≤ t := by
            linarith
          by_cases hFone : F.n = 1
          · refine ⟨0, A, HNFiltration.zero C (P := P) 0 (isZero_zero C), F,
              0, 𝟙 A, 0, contractible_distinguished₁ A, ?_, ?_, ?_, ?_⟩
            · intro j; exact Fin.elim0 j
            · intro j
              have hj : j = ⟨0, by omega⟩ := by apply Fin.ext; omega
              subst j; simpa [HNFiltration.phiPlus, hFone] using hlast_le
            · intro _ j
              have hj : j = ⟨0, by omega⟩ := by apply Fin.ext; omega
              subst j; simp [hFone]
            · intro j; exact Fin.elim0 j
          · have hn2 : 2 ≤ F.n := by omega
            let G := F.prefix C (F.n - 1) (by omega) (by omega)
            obtain ⟨X, Y', GX, GY', f', g', h', hT', hprops⟩ :=
              ih (F.chain.obj' (F.n - 1) (by omega)) G
                (by change F.n - 1 ≤ m; omega)
            have hGX_gt := And.left hprops
            have hGY'_le := And.left (And.right hprops)
            have hGY'_bound := And.left (And.right (And.right hprops))
            have hGX_contain := And.right (And.right (And.right hprops))
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
            let Tisoₘ := Triangle.isoMk
              (Triangle.mk u₂₃ (e₂A.inv ≫ T.mor₂) (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧')) T
              e₁.symm e₂A.symm (Iso.refl _)
              (by simp [u₂₃, e₂A])
              (by simp [e₂A])
              (by simp)
            have hTu₂₃ :
                Triangle.mk u₂₃ (e₂A.inv ≫ T.mor₂) (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') ∈
                  distTriang C :=
              isomorphic_distinguished _ (F.triangle_dist ⟨F.n - 1, by omega⟩) _ Tisoₘ
            have hGn : 0 < G.n := by
              change 0 < F.n - 1
              omega
            have hφlast_lt : ∀ j : Fin GY'.n, F.φ ⟨F.n - 1, by omega⟩ < GY'.φ j := by
              intro j
              calc
                F.φ ⟨F.n - 1, by omega⟩
                    < F.φ ⟨F.n - 2, by omega⟩ :=
                  F.hφ (show (⟨F.n - 2, by omega⟩ : Fin F.n) <
                    ⟨F.n - 1, by omega⟩ from
                      Fin.mk_lt_mk.mpr (by omega))
                _ = G.φ ⟨G.n - 1, by omega⟩ := by
                    change F.φ ⟨F.n - 2, _⟩ = F.φ ⟨(F.n - 1) - 1, _⟩
                    congr 1
                _ ≤ GY'.φ j := hGY'_bound hGn j
            obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (f' ≫ u₂₃)
            let oct := Triangulated.someOctahedron rfl hT' hTu₂₃ h₁₃
            let GZ := GY'.appendFactor C oct.triangle oct.mem (Iso.refl _)
              (Iso.refl _) (F.φ ⟨F.n - 1, by omega⟩)
              (F.semistable ⟨F.n - 1, by omega⟩) hφlast_lt
            refine ⟨X, Z, GX, GZ, f' ≫ u₂₃, v₁₃, w₁₃, h₁₃, hGX_gt, ?_, ?_, ?_⟩
            · intro j
              change GZ.φ j ≤ t
              simp only [GZ, HNFiltration.appendFactor]
              split_ifs with hj
              · exact hGY'_le ⟨j.val, hj⟩
              · exact hlast_le
            · intro _ j
              change F.φ ⟨F.n - 1, by omega⟩ ≤ GZ.φ j
              simp only [GZ, HNFiltration.appendFactor]
              split_ifs with hj
              · exact le_of_lt (hφlast_lt ⟨j.val, hj⟩)
              · exact le_rfl
            · -- Phase containment: GX.φ j is a phase of G, hence of F
              intro j
              obtain ⟨i_G, hi_G⟩ := hGX_contain j
              have hi_lt := i_G.isLt; change i_G.val < F.n - 1 at hi_lt
              exact ⟨⟨i_G.val, by omega⟩,
                by simp [G, HNFiltration.prefix] at hi_G; exact hi_G⟩

end CategoryTheory.Triangulated
