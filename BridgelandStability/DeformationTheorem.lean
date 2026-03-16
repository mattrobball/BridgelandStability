/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Deformation
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
        -- Finiteness: τ''.Z, τ'.Z ∈ V(σ₀), so difference is finite
        have hτ''_V : τ''.Z ∈ finiteSeminormSubgroup C σ₀ :=
          finiteSeminormSubgroup_eq_of_connected C σ₀ τ'' hconn'' ▸
            Z_mem_finiteSeminormSubgroup C τ''
        have hτ'_V : τ'.Z ∈ finiteSeminormSubgroup C σ₀ :=
          finiteSeminormSubgroup_eq_of_connected C σ₀ τ' hconn_τ' ▸
            Z_mem_finiteSeminormSubgroup C τ'
        have hdiff_fin : stabSeminorm C σ₀ (τ''.Z - τ'.Z) ≠ ⊤ :=
          ne_top_of_lt ((finiteSeminormSubgroup C σ₀).sub_mem hτ''_V hτ'_V)
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
                exact (hdom _ hdiff_fin).trans (by gcongr)
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
        -- Apply bridgeland_7_1_with_component to show Z is locally surjective
        -- onto comp with the connected-component guarantee.
        -- For each W' near Z(σ_x) in the σ₀-seminorm:
        --   (1) reverse comparison gives ‖W'-Z(σ_x)‖_{σ_x} small
        --   (2) Thm 7.1 + CC claim gives τ' with Z(τ')=W', same component
        --   (3) τ' near σ_x, hence in T ⊆ f⁻¹(S)
        --   (4) W' = Zmap(τ') ∈ S
        -- We exhibit a σ₀-ball of radius r > 0 inside S.
        -- Choose ε'_x for the inner Thm 7.1 call, and r accordingly.
        -- The argument uses bridgeland_7_1_with_component (sorry'd in Deformation.lean)
        -- for the connected component claim, which is the only unproved ingredient.
        -- Bridgeland treats this as manifest (§7, proof of Theorem 1.2).
        -- All remaining steps are standard ε-δ / filter arguments.
        -- The full ε-δ construction (choosing r, verifying basisNhd containment,
        -- extracting an open subset of T) follows Phase 3 of the plan.
        -- It uses: subadditivity of stabSeminorm, slicingDist triangle inequality,
        -- seminorm comparison (Lemma 6.2), and bridgeland_7_1_with_component.
        sorry
      exact IsOpenEmbedding.of_continuous_injective_isOpenMap
        (hZcont.comp continuous_subtype_val) hZinj hZopen

end CategoryTheory.Triangulated
