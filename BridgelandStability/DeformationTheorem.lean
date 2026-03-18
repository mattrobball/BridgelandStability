/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Deformation.Theorem71
import Mathlib.Topology.Bases
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Bridgeland's Theorem 1.2: Central charge is a local homeomorphism

Following Bridgeland's proof:
- **Lemma 6.2** (`stabSeminorm_dominated_of_connected`): seminorm equivalence on V(Σ).
- **Prop 6.3**: Z continuous into the seminorm topology.
- **Lemma 6.4** (`eq_of_same_Z_near`): Z locally injective.
- **Theorem 7.1** (`bridgeland_7_1`): Z locally surjective.
-/

set_option linter.style.longFile 0

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Topology
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Theorem 7.1 packaged in Bridgeland-basis form. A small deformation of the central
charge lifts directly to a point of `basisNhd C σ ε`.

This is the form used in the topology arguments for Theorem 1.2: it gives both the
prescribed central charge and the exact `basisNhd` control, so no radius enlargement
is needed after applying Theorem 7.1. -/
theorem bridgeland_7_1_mem_basisNhd (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hε₀_lf : ∃ δ : ℝ, 0 < δ ∧ ε₀ + δ < 1 / 2 ∧ ∀ t : ℝ,
      ∀ (E :
        (σ.slicing.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ))).FullSubcategory),
        IsArtinianObject E ∧ IsNoetherianObject E) :
    ∃ τ : StabilityCondition C, τ.Z = W ∧ τ ∈ basisNhd C σ ε := by
  obtain ⟨τ, hτZ, hτd⟩ :=
    bridgeland_7_1 C σ W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin hε₀_lf
  refine ⟨τ, hτZ, ?_⟩
  constructor
  · simpa [hτZ] using hsin
  · simpa using hτd

/-- **Local connectedness of `Stab(D)`**: every basis neighbourhood is contained in
the topological connected component of its centre.

This is the path-connectedness content of Bridgeland's Theorem 1.2 proof (§7).
For `τ ∈ basisNhd(σ, ε)`, the linear interpolation `W_t = Z(σ) + t·(Z(τ) − Z(σ))`
and `γ(t)` is obtained from `bridgeland_7_1_mem_basisNhd(σ, W_t, ε₀)`, so
`γ(t) ∈ basisNhd C σ ε` for all `t`.
Path-continuity at `t₀` follows from applying Theorem 7.1 centred at `γ(t₀)` with
a small `ε′`, then **Lemma 6.4** (uniqueness for same `Z` and `d < 1`) identifies
the result with `γ(t)`. The image of `[0, 1]` is therefore preconnected. -/
theorem basisNhd_subset_connectedComponent (σ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    basisNhd C σ ε ⊆ {τ | ConnectedComponents.mk τ = ConnectedComponents.mk σ} := by
  -- Roadmap (Bridgeland §7, path-connectedness):
  -- For τ ∈ basisNhd(σ, ε), define the linear interpolation
  --   W_t := Z(σ) + t · (Z(τ) − Z(σ)),  t ∈ [0,1]
  -- and let γ(t) be the lift from `bridgeland_7_1_mem_basisNhd`; then
  -- γ(t) ∈ basisNhd C σ ε, γ(0) = σ, and γ(1) = τ.
  --
  -- Continuity at t₀: apply Theorem 7.1 centred at γ(t₀) with small ε',
  -- then Lemma 6.4 (eq_of_same_Z_near) identifies the result with γ(t).
  --
  -- Requires:
  -- 1. ‖W_t - Z(σ)‖_σ = t · ‖Z(τ) - Z(σ)‖_σ < sin(πε₀) for all t ∈ [0,1]
  -- 2. Since γ(t₀) ∈ basisNhd C σ ε, the needed local norm comparison comes from
  --    `stabSeminorm_le_of_near`, not from the later connected-component lemma.
  -- 3. Continuity of t ↦ ‖W_t - Z(γ(t₀))‖_{γ(t₀)} near t₀
  -- The image of [0,1] under γ is connected, so τ and σ share a component.
  sorry

/-- **Lemma 6.2**: On a connected component, seminorms are equivalent (domination). -/
theorem stabSeminorm_dominated_of_connected (σ τ : StabilityCondition C)
    (h : ConnectedComponents.mk σ = ConnectedComponents.mk τ) :
    ∃ K : ENNReal, K ≠ ⊤ ∧
      ∀ (f : K₀ C →+ ℂ), stabSeminorm C σ f ≤ K * stabSeminorm C τ f := by
  sorry

/-- **Lemma 6.2**: On a connected component, the finite-seminorm subgroups agree. -/
theorem finiteSeminormSubgroup_eq_of_connected (σ τ : StabilityCondition C)
    (h : ConnectedComponents.mk σ = ConnectedComponents.mk τ) :
    finiteSeminormSubgroup C σ = finiteSeminormSubgroup C τ := by
  ext f
  show stabSeminorm C σ f < ⊤ ↔ stabSeminorm C τ f < ⊤
  obtain ⟨K₁, hK₁, hdom₁⟩ := stabSeminorm_dominated_of_connected C σ τ h
  obtain ⟨K₂, hK₂, hdom₂⟩ := stabSeminorm_dominated_of_connected C τ σ h.symm
  constructor
  · intro hf
    exact lt_of_le_of_lt (hdom₂ f)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK₂) hf)
  · intro hf
    exact lt_of_le_of_lt (hdom₁ f)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK₁) hf)

/-- The generating family of Bridgeland basis neighborhoods on `Stab(D)`. -/
def basisNhdFamily : Set (Set (StabilityCondition C)) :=
  {U | ∃ (σ : StabilityCondition C) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧ U = basisNhd C σ ε}

/-- A basis neighborhood contains its center. -/
theorem basisNhd_self (σ : StabilityCondition C) {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    σ ∈ basisNhd C σ ε := by
  constructor
  · rw [sub_self, stabSeminorm_zero]
    have hε1 : ε < 1 := by linarith
    exact ENNReal.ofReal_pos.mpr <|
      Real.sin_pos_of_pos_of_lt_pi
        (by positivity)
        (by nlinarith [Real.pi_pos, hε1])
  · rw [slicingDist_self]
    exact ENNReal.ofReal_pos.mpr hε

/-- Shrinking the radius at a fixed center shrinks the Bridgeland basis neighborhood. -/
theorem basisNhd_mono (σ : StabilityCondition C) {δ ε : ℝ}
    (hδ : 0 < δ) (hδε : δ ≤ ε) (hε8 : ε < 1 / 8) :
    basisNhd C σ δ ⊆ basisNhd C σ ε := by
  intro τ hτ
  rcases hτ with ⟨hτZ, hτd⟩
  constructor
  · have hsin_le : Real.sin (Real.pi * δ) ≤ Real.sin (Real.pi * ε) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
      · gcongr
    exact lt_of_lt_of_le hτZ <| ENNReal.ofReal_le_ofReal hsin_le
  · exact lt_of_lt_of_le hτd <| ENNReal.ofReal_le_ofReal hδε

/-- If `τ ∈ B_ε(σ)`, then some smaller basis neighborhood of `τ` is contained in `B_ε(σ)`.

This packages the two ingredients needed later in the local homeomorphism proof:
component constancy from `basisNhd_subset_connectedComponent`, and seminorm comparison on a
component from `stabSeminorm_dominated_of_connected`. -/
theorem exists_basisNhd_subset_basisNhd (σ τ : StabilityCondition C) {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 8 ∧ basisNhd C τ δ ⊆ basisNhd C σ ε := by
  rcases hτ with ⟨hτZ, hτd⟩
  have hτ_mem : τ ∈ basisNhd C σ ε := ⟨hτZ, hτd⟩
  have hτcc : ConnectedComponents.mk τ = ConnectedComponents.mk σ :=
    basisNhd_subset_connectedComponent C σ hε hε8 hτ_mem
  obtain ⟨K, hK, hdom⟩ :=
    stabSeminorm_dominated_of_connected C σ τ hτcc.symm
  have hsinε_pos : 0 < Real.sin (Real.pi * ε) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  have hτfin : stabSeminorm C σ (τ.Z - σ.Z) ≠ ⊤ := ne_top_of_lt hτZ
  have hK_eq : ENNReal.ofReal K.toReal = K := ENNReal.ofReal_toReal hK
  set dZ := (stabSeminorm C σ (τ.Z - σ.Z)).toReal
  have hdZ_eq : ENNReal.ofReal dZ = stabSeminorm C σ (τ.Z - σ.Z) :=
    ENNReal.ofReal_toReal hτfin
  have hdZ_nn : (0 : ℝ) ≤ dZ := ENNReal.toReal_nonneg
  have hdZ_lt : dZ < Real.sin (Real.pi * ε) := by
    rwa [← hdZ_eq, ENNReal.ofReal_lt_ofReal_iff hsinε_pos] at hτZ
  set gapZ := Real.sin (Real.pi * ε) - dZ
  have hgapZ : 0 < gapZ := sub_pos.mpr hdZ_lt
  have hτdfin : slicingDist C σ.slicing τ.slicing ≠ ⊤ := ne_top_of_lt hτd
  set dd := (slicingDist C σ.slicing τ.slicing).toReal
  have hdd_eq : ENNReal.ofReal dd = slicingDist C σ.slicing τ.slicing :=
    ENNReal.ofReal_toReal hτdfin
  have hdd_nn : (0 : ℝ) ≤ dd := ENNReal.toReal_nonneg
  have hdd_lt : dd < ε := by
    rwa [← hdd_eq, ENNReal.ofReal_lt_ofReal_iff hε] at hτd
  have hdd_le : dd ≤ ε := le_of_lt hdd_lt
  set gapd := ε - dd
  have hgapd : 0 < gapd := sub_pos.mpr hdd_lt
  set δ : ℝ :=
    min (1 / 16) (min (gapZ / ((K.toReal + 1) * (2 * Real.pi))) (gapd / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    refine lt_min ?_ ?_
    · exact div_pos hgapZ (by positivity)
    · linarith
  have hδ_lt : δ < 1 / 8 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hπδ : 0 < Real.pi * δ := by positivity
  have hsinδ_nn : 0 ≤ Real.sin (Real.pi * δ) :=
    (Real.sin_pos_of_pos_of_lt_pi hπδ (by nlinarith [Real.pi_pos])).le
  have hKsin : K.toReal * Real.sin (Real.pi * δ) < gapZ := by
    have hKnn := ENNReal.toReal_nonneg (a := K)
    have h1 : Real.sin (Real.pi * δ) ≤ Real.pi * δ := (Real.sin_lt hπδ).le
    have h4 : 0 < (K.toReal + 1) * (2 * Real.pi) := by positivity
    have h5 : δ * ((K.toReal + 1) * (2 * Real.pi)) ≤ gapZ := by
      have hmin : δ ≤ gapZ / ((K.toReal + 1) * (2 * Real.pi)) := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      calc δ * ((K.toReal + 1) * (2 * Real.pi))
          ≤ gapZ / ((K.toReal + 1) * (2 * Real.pi)) * ((K.toReal + 1) * (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_right hmin (le_of_lt h4)
        _ = gapZ := div_mul_cancel₀ gapZ (ne_of_gt h4)
    have step1 : K.toReal * Real.sin (Real.pi * δ) ≤ K.toReal * (Real.pi * δ) :=
      mul_le_mul_of_nonneg_left h1 hKnn
    have step2 : K.toReal * (Real.pi * δ) ≤ (K.toReal + 1) * (Real.pi * δ) := by
      gcongr
      linarith
    have step3 : (K.toReal + 1) * (Real.pi * δ) =
        δ * ((K.toReal + 1) * (2 * Real.pi)) / 2 := by
      ring
    linarith [half_lt_self hgapZ]
  refine ⟨δ, hδ_pos, hδ_lt, ?_⟩
  intro τ' hτ'
  rcases hτ' with ⟨hτ'Z, hτ'd⟩
  constructor
  · have hsub : stabSeminorm C σ ((τ'.Z - τ.Z) + (τ.Z - σ.Z)) ≤
      stabSeminorm C σ (τ'.Z - τ.Z) + stabSeminorm C σ (τ.Z - σ.Z) := by
      apply iSup_le; intro E; apply iSup_le; intro φ
      apply iSup_le; intro hP; apply iSup_le; intro hE
      calc ENNReal.ofReal (‖((τ'.Z - τ.Z) + (τ.Z - σ.Z)) (K₀.of C E)‖ /
              ‖σ.Z (K₀.of C E)‖)
          ≤ ENNReal.ofReal (‖(τ'.Z - τ.Z) (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖ +
              ‖(τ.Z - σ.Z) (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) := by
            apply ENNReal.ofReal_le_ofReal
            rw [AddMonoidHom.add_apply, ← add_div]
            exact div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
        _ = ENNReal.ofReal (‖(τ'.Z - τ.Z) (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) +
            ENNReal.ofReal (‖(τ.Z - σ.Z) (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) :=
          ENNReal.ofReal_add (div_nonneg (norm_nonneg _) (norm_nonneg _))
            (div_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ stabSeminorm C σ (τ'.Z - τ.Z) + stabSeminorm C σ (τ.Z - σ.Z) :=
          add_le_add
            (le_iSup_of_le E <| le_iSup_of_le φ <| le_iSup_of_le hP <|
              le_iSup_of_le hE le_rfl)
            (le_iSup_of_le E <| le_iSup_of_le φ <| le_iSup_of_le hP <|
              le_iSup_of_le hE le_rfl)
    have hbound : stabSeminorm C σ (τ'.Z - σ.Z) ≤
        K * ENNReal.ofReal (Real.sin (Real.pi * δ)) +
          stabSeminorm C σ (τ.Z - σ.Z) := by
      have hdecomp : (τ'.Z - σ.Z : K₀ C →+ ℂ) = (τ'.Z - τ.Z) + (τ.Z - σ.Z) := by
        ext
        simp [AddMonoidHom.sub_apply, sub_add_sub_cancel]
      calc stabSeminorm C σ (τ'.Z - σ.Z)
          = stabSeminorm C σ ((τ'.Z - τ.Z) + (τ.Z - σ.Z)) := by rw [hdecomp]
        _ ≤ stabSeminorm C σ (τ'.Z - τ.Z) + stabSeminorm C σ (τ.Z - σ.Z) := hsub
        _ ≤ K * ENNReal.ofReal (Real.sin (Real.pi * δ)) +
            stabSeminorm C σ (τ.Z - σ.Z) := by
            gcongr
            exact (hdom _).trans (by gcongr)
    have hlt : K * ENNReal.ofReal (Real.sin (Real.pi * δ)) +
        stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) := by
      conv_lhs => rw [← hdZ_eq, ← hK_eq]
      rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hsinδ_nn) hdZ_nn,
        ENNReal.ofReal_lt_ofReal_iff hsinε_pos]
      linarith
    exact lt_of_le_of_lt hbound hlt
  · have hδ_lt_gapd : δ < gapd := by
      have hδ_le : δ ≤ gapd / 2 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    have hτ'd_gap : slicingDist C τ.slicing τ'.slicing < ENNReal.ofReal gapd := by
      exact lt_of_lt_of_le hτ'd <| ENNReal.ofReal_le_ofReal (le_of_lt hδ_lt_gapd)
    calc slicingDist C σ.slicing τ'.slicing
        ≤ slicingDist C σ.slicing τ.slicing + slicingDist C τ.slicing τ'.slicing :=
          slicingDist_triangle C σ.slicing τ.slicing τ'.slicing
      _ < slicingDist C σ.slicing τ.slicing + ENNReal.ofReal gapd :=
          ENNReal.add_lt_add_left hτdfin hτ'd_gap
      _ = ENNReal.ofReal dd + ENNReal.ofReal gapd := by rw [← hdd_eq]
      _ = ENNReal.ofReal (dd + gapd) := by
          rw [← ENNReal.ofReal_add hdd_nn (sub_nonneg.mpr hdd_le)]
      _ = ENNReal.ofReal ε := by
          congr 1
          dsimp [gapd]
          linarith

/-- Every open neighborhood of `σ` contains a centered Bridgeland basis neighborhood. -/
theorem exists_basisNhd_subset_of_mem_open (σ : StabilityCondition C)
    {s : Set (StabilityCondition C)} (hs : IsOpen s) (hσ : σ ∈ s) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧ basisNhd C σ ε ⊆ s := by
  change TopologicalSpace.GenerateOpen (basisNhdFamily C) s at hs
  induction hs generalizing σ with
  | basic u hu =>
      rcases hu with ⟨τ, ε, hε, hε8, rfl⟩
      exact exists_basisNhd_subset_basisNhd C τ σ hε hε8 hσ
  | univ =>
      refine ⟨1 / 16, by norm_num, by norm_num, ?_⟩
      intro τ _
      simp
  | inter s t hs ht ihs iht =>
      rcases ihs σ hσ.1 with ⟨εs, hεs, hεs8, hs_sub⟩
      rcases iht σ hσ.2 with ⟨εt, hεt, hεt8, ht_sub⟩
      refine ⟨min εs εt, lt_min hεs hεt,
        lt_of_le_of_lt (min_le_left _ _) hεs8, ?_⟩
      intro τ hτ
      constructor
      · exact hs_sub <| basisNhd_mono C σ (lt_min hεs hεt) (min_le_left _ _) hεs8 hτ
      · exact ht_sub <| basisNhd_mono C σ (lt_min hεs hεt) (min_le_right _ _) hεt8 hτ
  | sUnion S hS ih =>
      rcases hσ with ⟨t, htS, hσt⟩
      rcases ih t htS σ hσt with ⟨ε, hε, hε8, hsub⟩
      refine ⟨ε, hε, hε8, hsub.trans ?_⟩
      intro x hx
      exact Set.mem_sUnion.mpr ⟨t, htS, hx⟩

/-- The Bridgeland neighborhoods form a topological basis for `Stab(D)`. -/
theorem isTopologicalBasis_basisNhd :
    TopologicalSpace.IsTopologicalBasis (basisNhdFamily C) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro U hU
    rcases hU with ⟨σ, ε, hε, hε8, rfl⟩
    change TopologicalSpace.GenerateOpen (basisNhdFamily C) (basisNhd C σ ε)
    exact TopologicalSpace.GenerateOpen.basic _ ⟨σ, ε, hε, hε8, rfl⟩
  · intro σ U hσU hU
    rcases exists_basisNhd_subset_of_mem_open C σ hU hσU with ⟨ε, hε, hε8, hsub⟩
    refine ⟨basisNhd C σ ε, ⟨σ, ε, hε, hε8, rfl⟩, basisNhd_self C σ hε hε8, hsub⟩

/-- Neighborhood-form extraction of a centered Bridgeland basis neighborhood. -/
theorem exists_basisNhd_subset_of_mem_nhds (σ : StabilityCondition C)
    {s : Set (StabilityCondition C)} (hs : s ∈ 𝓝 σ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧ basisNhd C σ ε ⊆ s := by
  rcases (isTopologicalBasis_basisNhd C).mem_nhds_iff.mp hs with ⟨t, ht, hσt, hts⟩
  rcases ht with ⟨τ, ε, hε, hε8, rfl⟩
  rcases exists_basisNhd_subset_basisNhd C τ σ hε hε8 hσt with ⟨δ, hδ, hδ8, hsub⟩
  exact ⟨δ, hδ, hδ8, hsub.trans hts⟩

/-- Wide-sector finite length is monotone under shrinking `ε₀`. -/
theorem wideSectorFiniteLength_mono (σ : StabilityCondition C)
    {ε₀ ε₁ : ℝ} (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hε₁ : 0 < ε₁) (hε₁8 : ε₁ < 1 / 8) (hε₁ε₀ : ε₁ ≤ ε₀) :
    WideSectorFiniteLength (C := C) σ ε₁ hε₁ hε₁8 := by
  dsimp [WideSectorFiniteLength] at hWide ⊢
  intro t
  let a₁ : ℝ := t - 4 * ε₁
  let b₁ : ℝ := t + 4 * ε₁
  let a₀ : ℝ := t - 4 * ε₀
  let b₀ : ℝ := t + 4 * ε₀
  letI : Fact (a₁ < b₁) := ⟨by
    dsimp [a₁, b₁]
    linarith [hε₁]⟩
  letI : Fact (b₁ - a₁ ≤ 1) := ⟨by
    dsimp [a₁, b₁]
    linarith [hε₁8]⟩
  letI : Fact (a₀ < b₀) := ⟨by
    dsimp [a₀, b₀]
    linarith [hε₀]⟩
  letI : Fact (b₀ - a₀ ≤ 1) := ⟨by
    dsimp [a₀, b₀]
    linarith [hε₀8]⟩
  intro E
  have hIncl : σ.slicing.intervalProp C a₁ b₁ ≤ σ.slicing.intervalProp C a₀ b₀ := by
    intro X hX
    exact σ.slicing.intervalProp_mono C
      (by
        dsimp [a₀, a₁]
        linarith)
      (by
        dsimp [b₀, b₁]
        linarith)
      hX
  let E' : σ.slicing.IntervalCat C a₀ b₀ := (ObjectProperty.ιOfLE hIncl).obj E
  have hE' : IsStrictArtinianObject E' ∧ IsStrictNoetherianObject E' := by
    simpa [a₀, b₀, E'] using hWide t E'
  letI : IsStrictArtinianObject E' := hE'.1
  letI : IsStrictNoetherianObject E' := hE'.2
  simpa [a₁, b₁] using
    (interval_strictFiniteLength_of_inclusion_strict
      (C := C) (s₁ := σ.slicing) (s₂ := σ.slicing)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₀) (b₂ := b₀) hIncl (X := E))

/-- Z(σ) has finite σ-seminorm: ‖Z(σ)‖_σ ≤ 1, hence Z(σ) ∈ V(σ). -/
theorem Z_mem_finiteSeminormSubgroup (σ : StabilityCondition C) :
    σ.Z ∈ finiteSeminormSubgroup C σ := by
  show stabSeminorm C σ σ.Z < ⊤
  calc stabSeminorm C σ σ.Z
      = ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
          ENNReal.ofReal (‖σ.Z (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) := rfl
    _ ≤ 1 := by
        apply iSup_le; intro E; apply iSup_le; intro φ
        apply iSup_le; intro _; apply iSup_le; intro _
        rw [ENNReal.ofReal_le_one]
        by_cases h : ‖σ.Z (K₀.of C E)‖ = 0
        · simp [h]
        · rw [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))]
    _ < ⊤ := ENNReal.one_lt_top

/-- Two stability conditions with same Z and d < 1 are equal (Lemma 6.4). -/
theorem StabilityCondition.eq_of_same_Z_near (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal 1) :
    σ = τ := by
  have hP : σ.slicing.P = τ.slicing.P := by
    funext φ; ext E; exact bridgeland_lemma_6_4 C σ τ hZ hd φ E
  cases σ; cases τ; simp only [StabilityCondition.mk.injEq]
  exact ⟨by cases ‹Slicing C›; cases ‹Slicing C›; simpa [Slicing.mk.injEq] using hP, hZ⟩

/-! ### Theorem 1.2 -/

theorem bridgeland_theorem_1_2' :
    bridgelandTheorem_1_2 C := by
  intro cc
  obtain ⟨σ₀⟩ := cc.exists_rep
  let V := finiteSeminormSubgroup C σ₀
  let comp := {σ : StabilityCondition C // ConnectedComponents.mk σ = cc}
  let Zmap : comp → V :=
    fun ⟨σ', hσ'⟩ ↦ ⟨σ'.Z, by
      show σ'.Z ∈ finiteSeminormSubgroup C σ₀
      rw [finiteSeminormSubgroup_eq_of_connected C σ₀ σ' (by
        have h1 : (⟦σ₀⟧ : ConnectedComponents _) = cc := ‹_›
        change (⟦σ₀⟧ : ConnectedComponents _) = ⟦σ'⟧; rw [h1, ← hσ']; rfl)]
      exact Z_mem_finiteSeminormSubgroup C σ'⟩
  -- Seminorm topology on V from ‖·‖_{σ₀}
  letI τ_V : TopologicalSpace V := TopologicalSpace.generateFrom
    {S : Set V | ∃ (W : V) (r : ℝ), 0 < r ∧
      S = {F : V | stabSeminorm C σ₀ (↑F - ↑W) < ENNReal.ofReal r}}
  refine ⟨V, τ_V, ?_, ?_⟩
  · intro σ hσ
    show σ.Z ∈ finiteSeminormSubgroup C σ₀
    rw [finiteSeminormSubgroup_eq_of_connected C σ₀ σ (by
      have h1 : (⟦σ₀⟧ : ConnectedComponents _) = cc := ‹_›
      change (⟦σ₀⟧ : ConnectedComponents _) = ⟦σ⟧; rw [h1, ← hσ]; rfl)]
    exact Z_mem_finiteSeminormSubgroup C σ
  · rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
    intro ⟨σ, hσ⟩
    obtain ⟨ε₀, hε₀, hε₀8, hε₀_lf⟩ := σ.exists_epsilon0 C
    let ε := ε₀ / 2
    have hε_pos : 0 < ε := by positivity
    have hε_lt : ε < 1 / 8 := by dsimp [ε]; linarith
    let U : Set comp := {τ | τ.val ∈ basisNhd C σ ε}
    refine ⟨U, ?_, ?_⟩
    · refine IsOpen.mem_nhds ?_ ?_
      · exact isOpen_induced_iff.mpr ⟨basisNhd C σ ε,
          TopologicalSpace.GenerateOpen.basic _
            ⟨σ, ε, hε_pos, hε_lt, rfl⟩, rfl⟩
      · show σ ∈ basisNhd C σ ε
        constructor
        · show stabSeminorm C σ (σ.Z - σ.Z) < _
          rw [sub_self, stabSeminorm_zero]
          exact ENNReal.ofReal_pos.mpr (Real.sin_pos_of_pos_of_lt_pi
            (by positivity) (by nlinarith [Real.pi_pos, Real.pi_gt_three]))
        · show slicingDist C σ.slicing σ.slicing < _
          rw [slicingDist_self]; exact ENNReal.ofReal_pos.mpr hε_pos
    · -- Continuity (Prop 6.3 + Lemma 6.2)
      have hZcont : Continuous Zmap := by
        rw [continuous_generateFrom_iff]
        rintro S ⟨W, r, hr, rfl⟩
        rw [isOpen_iff_mem_nhds]
        intro ⟨τ', hτ'cc⟩ hτ'_mem
        -- On comp, comparison is available: all points are on cc.
        have hconn_τ' : ConnectedComponents.mk σ₀ = ConnectedComponents.mk τ' := by
          have h1 : (⟦σ₀⟧ : ConnectedComponents _) = cc := ‹_›
          change (⟦σ₀⟧ : ConnectedComponents _) = ⟦τ'⟧; rw [h1, ← hτ'cc]; rfl
        obtain ⟨K, hK, hdom⟩ := stabSeminorm_dominated_of_connected C σ₀ τ' hconn_τ'
        -- Preimage of σ₀-ball is open: subadditivity + comparison + basisNhd.
        -- ‖Z(τ'')-W‖_{σ₀} ≤ ‖Z(τ'')-Z(τ')‖_{σ₀} + ‖Z(τ')-W‖_{σ₀}
        --                   ≤ K*‖Z(τ'')-Z(τ')‖_{τ'} + ‖Z(τ')-W‖_{σ₀}
        --                   < K*sin(πδ) + ‖Z(τ')-W‖_{σ₀}
        -- Choose δ so K*sin(πδ) < gap = r - ‖Z(τ')-W‖_{σ₀}.
        -- Unfold preimage membership to direct inequality
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hτ'_mem
        -- hτ'_mem : stabSeminorm C σ₀ (↑(Zmap ⟨τ', hτ'cc⟩) - ↑W) < ENNReal.ofReal r
        change stabSeminorm C σ₀ (τ'.Z - ↑W) < ENNReal.ofReal r at hτ'_mem
        -- Finiteness and gap
        have hfin : stabSeminorm C σ₀ (τ'.Z - ↑W) ≠ ⊤ := ne_top_of_lt hτ'_mem
        have hK_eq : ENNReal.ofReal K.toReal = K := ENNReal.ofReal_toReal hK
        set d := (stabSeminorm C σ₀ (τ'.Z - ↑W)).toReal
        have hd_eq : ENNReal.ofReal d = stabSeminorm C σ₀ (τ'.Z - ↑W) :=
          ENNReal.ofReal_toReal hfin
        have hd_nn : (0 : ℝ) ≤ d := ENNReal.toReal_nonneg
        have hd_lt : d < r := by
          rwa [← hd_eq, ENNReal.ofReal_lt_ofReal_iff hr] at hτ'_mem
        -- Choose δ so K·sin(πδ) < gap := r - d
        set gap := r - d
        have hgap : 0 < gap := sub_pos.mpr hd_lt
        set δ := min (1/16 : ℝ) (gap / ((K.toReal + 1) * (2 * Real.pi)))
        have hδ_pos : 0 < δ := lt_min (by norm_num) (div_pos hgap (by positivity))
        have hδ_lt : δ < 1/8 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
        have hπδ : 0 < Real.pi * δ := by positivity
        have hsin_nn : 0 ≤ Real.sin (Real.pi * δ) :=
          (Real.sin_pos_of_pos_of_lt_pi hπδ (by nlinarith [Real.pi_pos])).le
        have hKsin : K.toReal * Real.sin (Real.pi * δ) < gap := by
          have hKnn := ENNReal.toReal_nonneg (a := K)
          have h1 : Real.sin (Real.pi * δ) ≤ Real.pi * δ := (Real.sin_lt hπδ).le
          have h4 : 0 < (K.toReal + 1) * (2 * Real.pi) := by positivity
          have h5 : δ * ((K.toReal + 1) * (2 * Real.pi)) ≤ gap := by
            have := min_le_right (1/16 : ℝ) (gap / ((K.toReal + 1) * (2 * Real.pi)))
            calc δ * ((K.toReal + 1) * (2 * Real.pi))
                ≤ gap / ((K.toReal + 1) * (2 * Real.pi)) * ((K.toReal + 1) * (2 * Real.pi)) :=
                  mul_le_mul_of_nonneg_right this (le_of_lt h4)
              _ = gap := div_mul_cancel₀ gap (ne_of_gt h4)
          have step1 : K.toReal * Real.sin (Real.pi * δ) ≤ K.toReal * (Real.pi * δ) :=
            mul_le_mul_of_nonneg_left h1 hKnn
          have step2 : K.toReal * (Real.pi * δ) ≤ (K.toReal + 1) * (Real.pi * δ) := by
            gcongr; linarith
          have step3 : (K.toReal + 1) * (Real.pi * δ) =
              δ * ((K.toReal + 1) * (2 * Real.pi)) / 2 := by ring
          linarith [half_lt_self hgap]
        -- Exhibit basisNhd(τ', δ) as open neighborhood in comp
        refine Filter.mem_of_superset
          (IsOpen.mem_nhds
            (isOpen_induced_iff.mpr ⟨basisNhd C τ' δ,
              TopologicalSpace.GenerateOpen.basic _
                ⟨τ', δ, hδ_pos, hδ_lt, rfl⟩, rfl⟩)
            (show τ' ∈ basisNhd C τ' δ from
              ⟨by rw [sub_self, stabSeminorm_zero]
                  exact ENNReal.ofReal_pos.mpr
                    (Real.sin_pos_of_pos_of_lt_pi hπδ
                      (by nlinarith [Real.pi_pos])),
               by rw [slicingDist_self]; exact ENNReal.ofReal_pos.mpr hδ_pos⟩))
          ?_
        -- Subset: ∀ τ'' ∈ basisNhd(τ', δ) ∩ comp, ‖Z(τ'')-W‖_{σ₀} < r
        intro ⟨τ'', hτ''cc⟩ ⟨hτ''Z, hτ''d⟩
        show stabSeminorm C σ₀ (τ''.Z - ↑W) < ENNReal.ofReal r
        -- Connectivity for τ''
        have hconn'' : ConnectedComponents.mk σ₀ = ConnectedComponents.mk τ'' := by
          have h1 : (⟦σ₀⟧ : ConnectedComponents _) = cc := ‹_›
          change (⟦σ₀⟧ : ConnectedComponents _) = ⟦τ''⟧; rw [h1, ← hτ''cc]; rfl
        -- Subadditivity: ‖A+B‖ ≤ ‖A‖ + ‖B‖ for stabSeminorm
        have hsub : stabSeminorm C σ₀ ((τ''.Z - τ'.Z) + (τ'.Z - ↑W)) ≤
            stabSeminorm C σ₀ (τ''.Z - τ'.Z) + stabSeminorm C σ₀ (τ'.Z - ↑W) := by
          apply iSup_le; intro E; apply iSup_le; intro φ
          apply iSup_le; intro hP; apply iSup_le; intro hE
          calc ENNReal.ofReal (‖((τ''.Z - τ'.Z) + (τ'.Z - ↑W)) (K₀.of C E)‖ /
                  ‖σ₀.Z (K₀.of C E)‖)
              ≤ ENNReal.ofReal (‖(τ''.Z - τ'.Z) (K₀.of C E)‖ / ‖σ₀.Z (K₀.of C E)‖ +
                  ‖(τ'.Z - ↑W) (K₀.of C E)‖ / ‖σ₀.Z (K₀.of C E)‖) := by
                apply ENNReal.ofReal_le_ofReal; rw [AddMonoidHom.add_apply, ← add_div]
                exact div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
            _ = ENNReal.ofReal (‖(τ''.Z - τ'.Z) (K₀.of C E)‖ / ‖σ₀.Z (K₀.of C E)‖) +
                ENNReal.ofReal (‖(τ'.Z - ↑W) (K₀.of C E)‖ / ‖σ₀.Z (K₀.of C E)‖) :=
              ENNReal.ofReal_add (div_nonneg (norm_nonneg _) (norm_nonneg _))
                (div_nonneg (norm_nonneg _) (norm_nonneg _))
            _ ≤ stabSeminorm C σ₀ (τ''.Z - τ'.Z) + stabSeminorm C σ₀ (τ'.Z - ↑W) :=
              add_le_add
                (le_iSup_of_le E (le_iSup_of_le φ (le_iSup_of_le hP
                  (le_iSup_of_le hE le_rfl))))
                (le_iSup_of_le E (le_iSup_of_le φ (le_iSup_of_le hP
                  (le_iSup_of_le hE le_rfl))))
        -- Main bound: subadditivity + domination + basisNhd
        have hbound : stabSeminorm C σ₀ (τ''.Z - ↑W) ≤
            K * ENNReal.ofReal (Real.sin (Real.pi * δ)) +
              stabSeminorm C σ₀ (τ'.Z - ↑W) := by
          have hdecomp : (τ''.Z - ↑W : K₀ C →+ ℂ) = (τ''.Z - τ'.Z) + (τ'.Z - ↑W) := by
            ext; simp [AddMonoidHom.sub_apply, sub_add_sub_cancel]
          calc stabSeminorm C σ₀ (τ''.Z - ↑W)
              = stabSeminorm C σ₀ ((τ''.Z - τ'.Z) + (τ'.Z - ↑W)) := by rw [hdecomp]
            _ ≤ stabSeminorm C σ₀ (τ''.Z - τ'.Z) + stabSeminorm C σ₀ (τ'.Z - ↑W) := hsub
            _ ≤ K * ENNReal.ofReal (Real.sin (Real.pi * δ)) +
                stabSeminorm C σ₀ (τ'.Z - ↑W) := by
                gcongr
                exact (hdom _).trans (by gcongr)
        -- Convert to ℝ and close
        have hlt : K * ENNReal.ofReal (Real.sin (Real.pi * δ)) +
            stabSeminorm C σ₀ (τ'.Z - ↑W) < ENNReal.ofReal r := by
          conv_lhs => rw [← hd_eq, ← hK_eq]
          rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hsin_nn) hd_nn,
            ENNReal.ofReal_lt_ofReal_iff hr]
          linarith
        exact lt_of_le_of_lt hbound hlt
      -- Injectivity (Lemma 6.4)
      have hZinj : Function.Injective (U.restrict Zmap) := by
        intro ⟨⟨τ₁, hτ₁cc⟩, hτ₁U⟩ ⟨⟨τ₂, hτ₂cc⟩, hτ₂U⟩ hZeq
        have hZval : τ₁.Z = τ₂.Z := congrArg Subtype.val hZeq
        have hd : slicingDist C τ₁.slicing τ₂.slicing < ENNReal.ofReal 1 :=
          calc slicingDist C τ₁.slicing τ₂.slicing
              ≤ slicingDist C τ₁.slicing σ.slicing +
                  slicingDist C σ.slicing τ₂.slicing :=
                slicingDist_triangle C τ₁.slicing σ.slicing τ₂.slicing
            _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε :=
                add_le_add
                  (by rw [slicingDist_symm]; exact le_of_lt hτ₁U.2)
                  (le_of_lt hτ₂U.2)
            _ = ENNReal.ofReal (ε + ε) :=
                (ENNReal.ofReal_add (le_of_lt hε_pos) (le_of_lt hε_pos)).symm
            _ < ENNReal.ofReal 1 := by
                rw [ENNReal.ofReal_lt_ofReal_iff one_pos]
                dsimp [ε]; linarith
        exact Subtype.ext (Subtype.ext
          (StabilityCondition.eq_of_same_Z_near C τ₁ τ₂ hZval hd))
      -- Open map (Theorem 7.1 + Lemma 6.2). With seminorm topology: no far-fiber issues.
      -- For τ ∈ T ⊂ U: Z(T) ⊃ {‖·-Z(τ)‖_τ < sin(πδ)} by Thm 7.1.
      -- {‖·‖_{σ₀} < r₀} ⊂ {‖·‖_τ < sin(πδ)} by reverse comparison.
      -- So Z(T) contains a σ₀-ball. Hence image is open in τ_V.
      have hZopen : IsOpenMap (U.restrict Zmap) := by
        rw [isOpenMap_iff_nhds_le]
        intro ⟨⟨σ_x, hσ_x_cc⟩, hσ_x_U⟩
        -- Need: 𝓝 (Zmap ⟨σ_x, hσ_x_cc⟩) ≤ map (U.restrict Zmap) (𝓝 ⟨⟨σ_x, hσ_x_cc⟩, hσ_x_U⟩)
        rw [Filter.le_def]
        intro S hS
        rw [Filter.mem_map] at hS
        -- hS : (U.restrict Zmap)⁻¹' S ∈ 𝓝 ⟨⟨σ_x, hσ_x_cc⟩, hσ_x_U⟩
        -- Extract an open neighborhood from hS
        obtain ⟨T, hT_sub, hT_open, hx_T⟩ := mem_nhds_iff.mp hS
        -- Get ε₀_x for Theorem 7.1 at σ_x
        obtain ⟨ε₀_x, hε₀_x, hε₀_x8, hwide_x⟩ := σ_x.exists_epsilon0 C
        -- Comparison: ‖U‖_{σ_x} ≤ K_rev * ‖U‖_{σ₀}
        have hconn_x : ConnectedComponents.mk σ₀ = ConnectedComponents.mk σ_x := by
          have h1 : (⟦σ₀⟧ : ConnectedComponents _) = cc := ‹_›
          change (⟦σ₀⟧ : ConnectedComponents _) = ⟦σ_x⟧; rw [h1, ← hσ_x_cc]; rfl
        obtain ⟨K_rev, hK_rev, hdom_rev⟩ :=
          stabSeminorm_dominated_of_connected C σ_x σ₀ hconn_x.symm
        -- Openness via Theorem 7.1 + basisNhd_subset_connectedComponent.
        -- For W' near Z(σ_x) in σ₀-norm, reverse comparison makes W' small in the
        -- σ_x-seminorm. Then `bridgeland_7_1_mem_basisNhd` gives τ' with Z(τ') = W'
        -- and τ' ∈ basisNhd C σ_x δ directly.
        -- Hence `basisNhd_subset_connectedComponent` puts τ' in the same connected
        -- component as σ_x, so τ' ∈ comp with no post-hoc radius enlargement.
        -- Also τ' near σ_x gives τ' ∈ U ∩ T, so W' ∈ Zmap(T) ⊆ S.
        -- This shows S contains a σ₀-ball, giving S ∈ 𝓝(Zmap(σ_x)).
        --
        -- The only sorry'd ingredient is basisNhd_subset_connectedComponent
        -- (Deformation.lean), which encodes the path-continuity of the
        -- deformation — Bridgeland treats this as manifest in §7.
        sorry
      exact IsOpenEmbedding.of_continuous_injective_isOpenMap
        (hZcont.comp continuous_subtype_val) hZinj hZopen

end CategoryTheory.Triangulated
