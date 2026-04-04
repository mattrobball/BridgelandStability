/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.Deformation

/-!
# Connected Components of the Stability Space

Openness of connected components, seminorm equivalence on components,
topological basis, and membership of central charges in the finite seminorm subgroup.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject Topology

universe v u u'

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Every stability condition admits a small Bridgeland basis neighbourhood contained in its
topological connected component. This is the local connectedness input actually needed later. -/
theorem exists_basisNhd_subset_connectedComponent (σ : StabilityCondition.WithClassMap C v) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧
      basisNhd C σ ε ⊆ {τ | ConnectedComponents.mk τ = ConnectedComponents.mk σ} := by
  obtain ⟨ε₀, hε₀, hε₀10, hWide⟩ := σ.exists_epsilon0_tenth C
  let ε : ℝ := ε₀ / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_lt_ε₀ : ε < ε₀ := by
    dsimp [ε]
    linarith
  have hε8 : ε < 1 / 8 := by
    dsimp [ε]
    linarith
  refine ⟨ε, hε, hε8, ?_⟩
  exact basisNhd_subset_connectedComponent_small C σ hε₀ hε₀10 hWide hε hε_lt_ε₀

/-- Connected components in `StabilityCondition C` are open, because small Bridgeland basis
neighbourhoods stay inside the connected component of their centre. -/
theorem stabilityCondition_isOpen_connectedComponent (σ : StabilityCondition.WithClassMap C v) :
    IsOpen (connectedComponent σ) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨ε, hε, hε8, hsub⟩ := exists_basisNhd_subset_connectedComponent C x
  refine mem_nhds_iff.mpr ⟨basisNhd C x ε, ?_, ?_, basisNhd_self C x hε hε8⟩
  · intro y hy
    have hyx : ConnectedComponents.mk y = ConnectedComponents.mk x := hsub hy
    have hxσ : ConnectedComponents.mk x = ConnectedComponents.mk σ :=
      ConnectedComponents.coe_eq_coe'.2 hx
    exact ConnectedComponents.coe_eq_coe'.1 (hyx.trans hxσ)
  · change TopologicalSpace.GenerateOpen
        { U | ∃ (σ : StabilityCondition.WithClassMap C v) (ε : ℝ),
            0 < ε ∧ ε < 1 / 8 ∧ U = basisNhd C σ ε }
        (basisNhd C x ε)
    exact TopologicalSpace.GenerateOpen.basic _ ⟨x, ε, hε, hε8, rfl⟩

/-- **Lemma 6.2**: On a connected component, seminorms are equivalent (domination). -/
@[informal "Lemma 6.2" "one direction; apply both ways for full equivalence"]
theorem stabSeminorm_dominated_of_connected (σ τ : StabilityCondition.WithClassMap C v)
    (h : ConnectedComponents.mk σ = ConnectedComponents.mk τ) :
    ∃ K : ENNReal, K ≠ ⊤ ∧
      ∀ (f : Λ →+ ℂ), stabSeminorm C σ f ≤ K * stabSeminorm C τ f := by
  let P : StabilityCondition.WithClassMap C v → StabilityCondition.WithClassMap C v → Prop := fun ρ₁ ρ₂ =>
    ∃ K : ENNReal, K ≠ ⊤ ∧
      ∀ f : Λ →+ ℂ, stabSeminorm C ρ₁ f ≤ K * stabSeminorm C ρ₂ f
  have hs : _root_.IsPreconnected (connectedComponent σ) := isPreconnected_connectedComponent
  have hlocal :
      ∀ x ∈ connectedComponent σ, ∀ᶠ y in 𝓝[connectedComponent σ] x, P x y ∧ P y x := by
    intro x hx
    obtain ⟨ε₀, hε₀, hε₀10, hWide⟩ := x.exists_epsilon0_tenth C
    let δ : ℝ := ε₀ / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_lt_ε₀ : δ < ε₀ := by
      dsimp [δ]
      linarith
    have hδ8 : δ < 1 / 8 := by
      dsimp [δ]
      linarith
    have hU_mem : basisNhd C x δ ∈ 𝓝 x := by
      apply IsOpen.mem_nhds
      · change TopologicalSpace.GenerateOpen
            { U | ∃ (σ : StabilityCondition.WithClassMap C v) (ε : ℝ),
                0 < ε ∧ ε < 1 / 8 ∧ U = basisNhd C σ ε }
            (basisNhd C x δ)
        exact TopologicalSpace.GenerateOpen.basic _ ⟨x, δ, hδ, hδ8, rfl⟩
      · exact basisNhd_self C x hδ hδ8
    have hU_within : basisNhd C x δ ∈ 𝓝[connectedComponent σ] x :=
      mem_nhdsWithin_of_mem_nhds hU_mem
    refine Filter.mem_of_superset hU_within ?_
    intro y hy
    constructor
    · exact stabSeminorm_dominated_of_basisNhd C x y hδ hδ8 hy
    · exact stabSeminorm_center_dominates_of_basisNhd C x y hδ hδ8 hy
  have htrans :
      ∀ x y z, x ∈ connectedComponent σ → y ∈ connectedComponent σ → z ∈ connectedComponent σ →
        P x y → P y z → P x z := by
    intro x y z _hx _hy _hz hxy hyz
    rcases hxy with ⟨K₁, hK₁, hdom₁⟩
    rcases hyz with ⟨K₂, hK₂, hdom₂⟩
    refine ⟨K₁ * K₂, ENNReal.mul_ne_top hK₁ hK₂, ?_⟩
    intro f
    calc
      stabSeminorm C x f ≤ K₁ * stabSeminorm C y f := hdom₁ f
      _ ≤ K₁ * (K₂ * stabSeminorm C z f) := by
        gcongr
        exact hdom₂ f
      _ = (K₁ * K₂) * stabSeminorm C z f := by rw [mul_assoc]
  have hτ : τ ∈ connectedComponent σ := by
    change τ ∈ connectedComponent σ
    exact ConnectedComponents.coe_eq_coe'.1 h.symm
  exact _root_.IsPreconnected.induction₂' hs P hlocal htrans mem_connectedComponent hτ

/-- **Lemma 6.2**: On a connected component, the finite-seminorm subgroups agree. -/
theorem finiteSeminormSubgroup_eq_of_connected (σ τ : StabilityCondition.WithClassMap C v)
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
def basisNhdFamily : Set (Set (StabilityCondition.WithClassMap C v)) :=
  {U | ∃ (σ : StabilityCondition.WithClassMap C v) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧ U = basisNhd C σ ε}

/-- Every open neighborhood of `σ` contains a centered Bridgeland basis neighborhood. -/
theorem exists_basisNhd_subset_of_mem_open (σ : StabilityCondition.WithClassMap C v)
    {s : Set (StabilityCondition.WithClassMap C v)} (hs : IsOpen s) (hσ : σ ∈ s) :
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
theorem isTopologicalBasis_basisNhd (v : K₀ C →+ Λ) :
    TopologicalSpace.IsTopologicalBasis (basisNhdFamily (v := v) C) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro U hU
    rcases hU with ⟨σ, ε, hε, hε8, rfl⟩
    change TopologicalSpace.GenerateOpen (basisNhdFamily C) (basisNhd C σ ε)
    exact TopologicalSpace.GenerateOpen.basic _ ⟨σ, ε, hε, hε8, rfl⟩
  · intro σ U hσU hU
    rcases exists_basisNhd_subset_of_mem_open C σ hU hσU with ⟨ε, hε, hε8, hsub⟩
    refine ⟨basisNhd C σ ε, ⟨σ, ε, hε, hε8, rfl⟩, basisNhd_self C σ hε hε8, hsub⟩

/-- Neighborhood-form extraction of a centered Bridgeland basis neighborhood. -/
theorem exists_basisNhd_subset_of_mem_nhds (σ : StabilityCondition.WithClassMap C v)
    {s : Set (StabilityCondition.WithClassMap C v)} (hs : s ∈ 𝓝 σ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧ basisNhd C σ ε ⊆ s := by
  rcases (isTopologicalBasis_basisNhd C v).mem_nhds_iff.mp hs with ⟨t, ht, hσt, hts⟩
  rcases ht with ⟨τ, ε, hε, hε8, rfl⟩
  rcases exists_basisNhd_subset_basisNhd C τ σ hε hε8 hσt with ⟨δ, hδ, hδ8, hsub⟩
  exact ⟨δ, hδ, hδ8, hsub.trans hts⟩

section

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- An additive homomorphism on `Λ` is zero if it vanishes on all class images and `v` is
surjective. The surjectivity ensures `cl C v` generates all of `Λ`. -/
theorem eq_zero_of_vanishes_on_cl (U : Λ →+ ℂ)
    (hv : Function.Surjective v)
    (hU : ∀ E : C, U (cl C v E) = 0) :
    U = 0 := by
  have hcomp : U.comp v = 0 := K₀.hom_ext (C := C) (fun E => hU E)
  ext x; obtain ⟨y, rfl⟩ := hv x
  exact DFunLike.congr_fun hcomp y

end

/-- If the Bridgeland seminorm of `U` is finite and equal to zero, then `U = 0`.
Requires surjectivity of `v` so that vanishing on `cl C v` implies vanishing on all of `Λ`. -/
theorem eq_zero_of_stabSeminorm_toReal_eq_zero (σ : StabilityCondition.WithClassMap C v)
    (hv : Function.Surjective v)
    {U : Λ →+ ℂ} (hfin : stabSeminorm C σ U < ⊤)
    (hzero : (stabSeminorm C σ U).toReal = 0) :
    U = 0 := by
  have hU_ne_top : stabSeminorm C σ U ≠ ⊤ := ne_top_of_lt hfin
  have hseminorm_zero : stabSeminorm C σ U = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hzero with h | h
    · exact h
    · exact (hU_ne_top h).elim
  have hvanish : ∀ E : C, U (cl C v E) = 0 := by
    intro E
    by_cases hE : IsZero E
    · rw [cl_isZero (C := C) (v := v) hE, map_zero]
    · obtain ⟨F, hn, _, _⟩ := σ.slicing.exists_HN_intrinsic_width C hE
      have hfactor :
          ∀ i : Fin F.n, U (cl C v (F.toPostnikovTower.factor i)) = 0 := by
        intro i
        by_cases hi : IsZero (F.toPostnikovTower.factor i)
        · rw [cl_isZero (C := C) (v := v) hi, map_zero]
        · have hbound :=
            stabSeminorm_bound_real C σ U hU_ne_top (F.semistable i) hi
          rw [hseminorm_zero, ENNReal.toReal_zero, zero_mul] at hbound
          exact norm_eq_zero.mp <| le_antisymm hbound (norm_nonneg _)
      rw [cl_postnikovTower_eq_sum C v, map_sum]
      calc
        ∑ i : Fin F.n, U (cl C v (F.toPostnikovTower.factor i))
          = ∑ i : Fin F.n, 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hfactor i
        _ = 0 := by simp
  exact eq_zero_of_vanishes_on_cl C U hv hvanish

/-- Z(σ) has finite σ-seminorm: ‖Z(σ)‖_σ ≤ 1, hence Z(σ) ∈ V(σ). -/
theorem Z_mem_finiteSeminormSubgroup (σ : StabilityCondition.WithClassMap C v) :
    σ.Z ∈ finiteSeminormSubgroup C σ := by
  show stabSeminorm C σ σ.Z < ⊤
  calc stabSeminorm C σ σ.Z
      = ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
          ENNReal.ofReal (‖σ.charge E‖ / ‖σ.charge E‖) := rfl
    _ ≤ 1 := by
        apply iSup_le; intro E; apply iSup_le; intro φ
        apply iSup_le; intro _; apply iSup_le; intro _
        rw [ENNReal.ofReal_le_one]
        by_cases h : ‖σ.charge E‖ = 0
        · simp [h]
        · rw [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))]
    _ < ⊤ := ENNReal.one_lt_top

end CategoryTheory.Triangulated
