/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.ConnectedComponent

/-!
# Local Homeomorphism of the Central Charge

Component normed space construction, charge map structure, and the proof of
Bridgeland's Theorem 1.2: the central charge map is a local homeomorphism
on each connected component of Stab(D).
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Topology
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]


/-- A chosen representative of a connected component of `StabilityCondition C`. -/
def componentRep (cc : ConnectedComponents (StabilityCondition C)) : StabilityCondition C :=
  Classical.choose cc.exists_rep

@[simp] theorem mk_componentRep (cc : ConnectedComponents (StabilityCondition C)) :
    ConnectedComponents.mk (componentRep C cc) = cc :=
  Classical.choose_spec cc.exists_rep

/-- The component of stability conditions with connected-component label `cc`. -/
abbrev componentStabilityCondition (cc : ConnectedComponents (StabilityCondition C)) :=
  {σ : StabilityCondition C // ConnectedComponents.mk σ = cc}

/-- Bridgeland's `V(Σ)`, implemented using a chosen representative of the component. -/
def componentSeminormSubgroup (cc : ConnectedComponents (StabilityCondition C)) :
    Submodule ℂ (K₀ C →+ ℂ) where
  carrier := finiteSeminormSubgroup C (componentRep C cc)
  zero_mem' := by
    exact (finiteSeminormSubgroup C (componentRep C cc)).zero_mem
  add_mem' hU hV := by
    exact (finiteSeminormSubgroup C (componentRep C cc)).add_mem hU hV
  smul_mem' t U hU := by
    change stabSeminorm C (componentRep C cc) (t • U) < ⊤
    rw [stabSeminorm_smul_complex]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU

/-- The Bridgeland norm on `V(Σ)` attached to a chosen representative of the component. -/
noncomputable instance componentNorm
    (cc : ConnectedComponents (StabilityCondition C)) :
    Norm (componentSeminormSubgroup C cc) where
  norm U := (stabSeminorm C (componentRep C cc) (U : K₀ C →+ ℂ)).toReal

/-- The restricted Bridgeland seminorm is a genuine additive norm on `V(Σ)`. -/
noncomputable def componentAddGroupNorm
    (cc : ConnectedComponents (StabilityCondition C)) :
    AddGroupNorm (componentSeminormSubgroup C cc) where
  toFun U := ‖U‖
  map_zero' := by
    change (stabSeminorm C (componentRep C cc) (0 : K₀ C →+ ℂ)).toReal = 0
    rw [stabSeminorm_zero, ENNReal.toReal_zero]
  add_le' U V := by
    change (stabSeminorm C (componentRep C cc) (((U + V : componentSeminormSubgroup C cc) :
      K₀ C →+ ℂ))).toReal ≤
      (stabSeminorm C (componentRep C cc) (U : K₀ C →+ ℂ)).toReal +
        (stabSeminorm C (componentRep C cc) (V : K₀ C →+ ℂ)).toReal
    rw [show (((U + V : componentSeminormSubgroup C cc) : K₀ C →+ ℂ)) =
      (U : K₀ C →+ ℂ) + (V : K₀ C →+ ℂ) by rfl]
    have hle := stabSeminorm_add_le C (componentRep C cc) (U : K₀ C →+ ℂ) (V : K₀ C →+ ℂ)
    have hle' :
        stabSeminorm C (componentRep C cc) (((U + V : componentSeminormSubgroup C cc) :
          K₀ C →+ ℂ)) ≤
          stabSeminorm C (componentRep C cc) (U : K₀ C →+ ℂ) +
            stabSeminorm C (componentRep C cc) (V : K₀ C →+ ℂ) := by
      simpa using hle
    have htoReal :
        (stabSeminorm C (componentRep C cc) (((U + V : componentSeminormSubgroup C cc) :
          K₀ C →+ ℂ))).toReal ≤
          (stabSeminorm C (componentRep C cc) (U : K₀ C →+ ℂ) +
            stabSeminorm C (componentRep C cc) (V : K₀ C →+ ℂ)).toReal := by
      rw [ENNReal.toReal_le_toReal (ne_top_of_lt (U + V).2)
        (ENNReal.add_ne_top.mpr ⟨ne_top_of_lt U.2, ne_top_of_lt V.2⟩)]
      exact hle'
    refine htoReal.trans_eq ?_
    exact ENNReal.toReal_add (ne_top_of_lt U.2) (ne_top_of_lt V.2)
  neg' U := by
    change (stabSeminorm C (componentRep C cc) (-(U : K₀ C →+ ℂ))).toReal =
      (stabSeminorm C (componentRep C cc) (U : K₀ C →+ ℂ)).toReal
    rw [stabSeminorm_neg]
  eq_zero_of_map_eq_zero' U hU := by
    apply Subtype.ext
    change (stabSeminorm C (componentRep C cc) (U : K₀ C →+ ℂ)).toReal = 0 at hU
    exact eq_zero_of_stabSeminorm_toReal_eq_zero C (componentRep C cc) U.2 hU

noncomputable instance componentNormedAddCommGroup
    (cc : ConnectedComponents (StabilityCondition C)) :
    NormedAddCommGroup (componentSeminormSubgroup C cc) :=
  AddGroupNorm.toNormedAddCommGroup (componentAddGroupNorm C cc)

noncomputable instance componentNormedSpace
    (cc : ConnectedComponents (StabilityCondition C)) :
    NormedSpace ℂ (componentSeminormSubgroup C cc) :=
  NormedSpace.ofCore
    { norm_nonneg := fun U ↦ ENNReal.toReal_nonneg
      norm_smul := by
        intro a U
        change (stabSeminorm C (componentRep C cc) (((a • U : componentSeminormSubgroup C cc) :
          K₀ C →+ ℂ))).toReal =
            ‖a‖ * (stabSeminorm C (componentRep C cc) (U : K₀ C →+ ℂ)).toReal
        rw [show (((a • U : componentSeminormSubgroup C cc) : K₀ C →+ ℂ)) =
            a • (U : K₀ C →+ ℂ) by rfl]
        rw [stabSeminorm_smul_complex, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
      norm_triangle := by
        intro U V
        exact (componentAddGroupNorm C cc).add_le' U V
      norm_eq_zero_iff := by
        intro U
        constructor
        · intro hU
          apply Subtype.ext
          change (stabSeminorm C (componentRep C cc) (U : K₀ C →+ ℂ)).toReal = 0 at hU
          exact eq_zero_of_stabSeminorm_toReal_eq_zero C (componentRep C cc) U.2 hU
        · intro hU
          subst hU
          change (stabSeminorm C (componentRep C cc) (0 : K₀ C →+ ℂ)).toReal = 0
          rw [stabSeminorm_zero, ENNReal.toReal_zero] }

/-- The seminorm balls in `V(Σ)` coming from the representative `σ₀ ∈ Σ`. -/
def componentSeminormBall (cc : ConnectedComponents (StabilityCondition C))
    (W : componentSeminormSubgroup C cc) (r : ℝ) :
    Set (componentSeminormSubgroup C cc) :=
  {F | stabSeminorm C (componentRep C cc) (↑F - ↑W) < ENNReal.ofReal r}

/-- The old seminorm balls are exactly the metric balls for the induced norm on `V(Σ)`. -/
theorem componentSeminormBall_eq_ball (cc : ConnectedComponents (StabilityCondition C))
    (W : componentSeminormSubgroup C cc) {r : ℝ} (hr : 0 < r) :
    componentSeminormBall C cc W r = Metric.ball W r := by
  ext F
  rw [componentSeminormBall, Metric.mem_ball, dist_eq_norm]
  change stabSeminorm C (componentRep C cc) (↑F - ↑W) < ENNReal.ofReal r ↔
    (stabSeminorm C (componentRep C cc) (((F - W : componentSeminormSubgroup C cc) :
      K₀ C →+ ℂ))).toReal < r
  rw [show (((F - W : componentSeminormSubgroup C cc) : K₀ C →+ ℂ)) = ↑F - ↑W by rfl]
  have hfin : stabSeminorm C (componentRep C cc) (↑F - ↑W) ≠ ⊤ := ne_top_of_lt (F - W).2
  rw [← ENNReal.ofReal_lt_ofReal_iff hr, ENNReal.ofReal_toReal hfin]

/-- The basis of seminorm balls defining the topology on `V(Σ)`. -/
def componentSeminormBasis (cc : ConnectedComponents (StabilityCondition C)) :
    Set (Set (componentSeminormSubgroup C cc)) :=
  {S | ∃ (W : componentSeminormSubgroup C cc) (r : ℝ), 0 < r ∧
    S = componentSeminormBall C cc W r}

/-- The linear topology on `V(Σ)` generated by seminorm balls for one representative. -/
abbrev componentSeminormTopology (cc : ConnectedComponents (StabilityCondition C)) :
    TopologicalSpace (componentSeminormSubgroup C cc) :=
  TopologicalSpace.generateFrom (componentSeminormBasis C cc)

/-- The old seminorm-ball basis is a genuine topological basis for the norm topology on `V(Σ)`. -/
theorem isTopologicalBasis_componentSeminormBasis
    (cc : ConnectedComponents (StabilityCondition C)) :
    @TopologicalSpace.IsTopologicalBasis (componentSeminormSubgroup C cc)
      (inferInstance : TopologicalSpace (componentSeminormSubgroup C cc))
      (componentSeminormBasis C cc) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro S ⟨W, r, hr, rfl⟩
    rw [componentSeminormBall_eq_ball C cc W hr]
    exact Metric.isOpen_ball
  · intro W s hWs hs
    rcases Metric.nhds_basis_ball.mem_iff.mp (hs.mem_nhds hWs) with ⟨r, hr, hball⟩
    refine ⟨componentSeminormBall C cc W r, ⟨W, r, hr, rfl⟩, ?_, ?_⟩
    · rw [componentSeminormBall_eq_ball C cc W hr]
      exact Metric.mem_ball_self hr
    · rw [componentSeminormBall_eq_ball C cc W hr]
      exact hball

/-- The ad hoc generated topology on `V(Σ)` agrees with the topology induced by the Bridgeland
norm defined above. -/
theorem componentSeminormTopology_eq_normTopology
    (cc : ConnectedComponents (StabilityCondition C)) :
    componentSeminormTopology C cc =
      (inferInstance : TopologicalSpace (componentSeminormSubgroup C cc)) := by
  simpa [componentSeminormTopology] using
    (isTopologicalBasis_componentSeminormBasis C cc).eq_generateFrom.symm

/-- Any element of the chosen `V(Σ)` has finite Bridgeland seminorm with respect to any
stability condition in the same connected component. -/
theorem componentSeminorm_lt_top_of_mem_component
    (cc : ConnectedComponents (StabilityCondition C))
    (σ : StabilityCondition C) (hσ : ConnectedComponents.mk σ = cc)
    (U : componentSeminormSubgroup C cc) :
    stabSeminorm C σ (U : K₀ C →+ ℂ) < ⊤ := by
  change (U : K₀ C →+ ℂ) ∈ finiteSeminormSubgroup C σ
  rw [finiteSeminormSubgroup_eq_of_connected C σ (componentRep C cc) (by
    rw [hσ, mk_componentRep C cc])]
  exact U.2

/-- The chosen norm on `V(Σ)` is equivalent to the Bridgeland norm coming from any
representative `σ ∈ Σ`. This is the formal version of Bridgeland's statement that the norms
`‖·‖_σ` on a connected component are equivalent. -/
theorem componentNorm_equivalent_of_mem_component
    (cc : ConnectedComponents (StabilityCondition C))
    (σ : StabilityCondition C) (hσ : ConnectedComponents.mk σ = cc) :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ U : componentSeminormSubgroup C cc,
        ‖U‖ ≤ K * (stabSeminorm C σ (U : K₀ C →+ ℂ)).toReal ∧
        (stabSeminorm C σ (U : K₀ C →+ ℂ)).toReal ≤ L * ‖U‖ := by
  let σ₀ := componentRep C cc
  have hσ₀σ : ConnectedComponents.mk σ₀ = ConnectedComponents.mk σ := by
    rw [show σ₀ = componentRep C cc by rfl, mk_componentRep C cc, hσ]
  obtain ⟨A, hA, hdomA⟩ := stabSeminorm_dominated_of_connected C σ₀ σ hσ₀σ
  obtain ⟨B, hB, hdomB⟩ := stabSeminorm_dominated_of_connected C σ σ₀ hσ₀σ.symm
  refine ⟨A.toReal + 1, B.toReal + 1, by positivity, by positivity, ?_⟩
  intro U
  have hUσ : stabSeminorm C σ (U : K₀ C →+ ℂ) < ⊤ :=
    componentSeminorm_lt_top_of_mem_component C cc σ hσ U
  constructor
  · have hleA :
        ‖U‖ ≤ A.toReal * (stabSeminorm C σ (U : K₀ C →+ ℂ)).toReal := by
      change (stabSeminorm C σ₀ (U : K₀ C →+ ℂ)).toReal ≤
        A.toReal * (stabSeminorm C σ (U : K₀ C →+ ℂ)).toReal
      have hleA' :
          (stabSeminorm C σ₀ (U : K₀ C →+ ℂ)).toReal ≤
            (A * stabSeminorm C σ (U : K₀ C →+ ℂ)).toReal :=
        (ENNReal.toReal_le_toReal (ne_top_of_lt U.2)
          (ENNReal.mul_ne_top hA (ne_top_of_lt hUσ))).2 (hdomA _)
      simpa [ENNReal.toReal_mul] using hleA'
    have hσ_nonneg : 0 ≤ (stabSeminorm C σ (U : K₀ C →+ ℂ)).toReal := ENNReal.toReal_nonneg
    nlinarith [hleA]
  · have hleB :
        (stabSeminorm C σ (U : K₀ C →+ ℂ)).toReal ≤ B.toReal * ‖U‖ := by
      change (stabSeminorm C σ (U : K₀ C →+ ℂ)).toReal ≤
        B.toReal * (stabSeminorm C σ₀ (U : K₀ C →+ ℂ)).toReal
      have hleB' :
          (stabSeminorm C σ (U : K₀ C →+ ℂ)).toReal ≤
            (B * stabSeminorm C σ₀ (U : K₀ C →+ ℂ)).toReal :=
        (ENNReal.toReal_le_toReal (ne_top_of_lt hUσ)
          (ENNReal.mul_ne_top hB (ne_top_of_lt U.2))).2 (hdomB _)
      simpa [ENNReal.toReal_mul] using hleB'
    have hrep_nonneg : 0 ≤ ‖U‖ := norm_nonneg _
    nlinarith [hleB]

/-- For `σ ∈ Σ`, its central charge lies in `V(Σ)`. -/
theorem componentZ_mem (cc : ConnectedComponents (StabilityCondition C))
    (σ : StabilityCondition C) (hσ : ConnectedComponents.mk σ = cc) :
    σ.Z ∈ componentSeminormSubgroup C cc := by
  change σ.Z ∈ finiteSeminormSubgroup C (componentRep C cc)
  rw [finiteSeminormSubgroup_eq_of_connected C (componentRep C cc) σ (by
    rw [mk_componentRep C cc, hσ])]
  exact Z_mem_finiteSeminormSubgroup C σ

/-- The central charge map restricted to a connected component and landing in `V(Σ)`. -/
def componentZMap (cc : ConnectedComponents (StabilityCondition C)) :
    componentStabilityCondition C cc → componentSeminormSubgroup C cc :=
  fun ⟨σ, hσ⟩ ↦ ⟨σ.Z, componentZ_mem C cc σ hσ⟩

/-! ### Canonical component local model -/

/-- A reusable non-existential package for the current formalization of Bridgeland's
Theorem 1.2 on a fixed connected component. -/
structure ComponentTopologicalLinearLocalModel
    (cc : ConnectedComponents (StabilityCondition C)) where
  /-- The chosen complex-linear charge space `V(Σ)` for this connected component. -/
  V : Submodule ℂ (K₀ C →+ ℂ)
  instNormedAddCommGroup : NormedAddCommGroup V
  instNormedSpace : NormedSpace ℂ V
  mem_charge : ∀ σ : StabilityCondition C, ConnectedComponents.mk σ = cc → σ.Z ∈ V
  isLocalHomeomorph_chargeMap :
    @IsLocalHomeomorph
      {σ : StabilityCondition C // ConnectedComponents.mk σ = cc}
      V inferInstance inferInstance
      (fun ⟨σ, hσ⟩ ↦ ⟨σ.Z, mem_charge σ hσ⟩)

attribute [instance] ComponentTopologicalLinearLocalModel.instNormedAddCommGroup
attribute [instance] ComponentTopologicalLinearLocalModel.instNormedSpace

namespace ComponentTopologicalLinearLocalModel

variable {cc : ConnectedComponents (StabilityCondition C)}

/-- The restricted central charge map attached to a component local model. -/
def chargeMap (M : ComponentTopologicalLinearLocalModel C cc) :
    componentStabilityCondition C cc → M.V :=
  fun ⟨σ, hσ⟩ ↦ ⟨σ.Z, M.mem_charge σ hσ⟩

end ComponentTopologicalLinearLocalModel

/-! ### Theorem 1.2 -/

/-- The canonical componentwise local linear model used to state Bridgeland's
Theorem 1.2 in terms of an explicit normed complex vector space `V(Σ)`. -/
noncomputable def componentTopologicalLinearLocalModel
    (cc : ConnectedComponents (StabilityCondition C)) :
    ComponentTopologicalLinearLocalModel C cc := by
  let σ₀ := componentRep C cc
  let V := componentSeminormSubgroup C cc
  let comp := componentStabilityCondition C cc
  let Zmap : comp → V := componentZMap C cc
  letI : TopologicalSpace V := inferInstance
  refine ⟨V, inferInstance, inferInstance, ?_, ?_⟩
  · intro σ hσ
    exact componentZ_mem C cc σ hσ
  · have hLocal :
        @IsLocalHomeomorph comp V inferInstance (componentSeminormTopology C cc) Zmap := by
      letI : TopologicalSpace V := componentSeminormTopology C cc
      rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
      intro ⟨σ, hσ⟩
      obtain ⟨ε₀, hε₀, hε₀8, hWide⟩ := σ.exists_epsilon0 C
      let ε := ε₀ / 2
      have hε_pos : 0 < ε := by positivity
      have hε_lt : ε < 1 / 8 := by dsimp [ε]; grind
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
          change @Continuous comp ↥V instTopologicalSpaceSubtype
            (TopologicalSpace.generateFrom (componentSeminormBasis C cc)) Zmap
          rw [continuous_generateFrom_iff]
          rintro S ⟨W, r, hr, rfl⟩
          rw [isOpen_iff_mem_nhds]
          intro ⟨τ', hτ'cc⟩ hτ'_mem
          -- On comp, comparison is available: all points are on cc.
          have hconn_τ' : ConnectedComponents.mk σ₀ = ConnectedComponents.mk τ' := by
            rw [show σ₀ = componentRep C cc by rfl, mk_componentRep C cc, hτ'cc]
          obtain ⟨K, hK, hdom⟩ := stabSeminorm_dominated_of_connected C σ₀ τ' hconn_τ'
          -- Preimage of σ₀-ball is open: subadditivity + comparison + basisNhd.
          -- ‖Z(τ'')-W‖_{σ₀} ≤ ‖Z(τ'')-Z(τ')‖_{σ₀} + ‖Z(τ')-W‖_{σ₀}
          --                   ≤ K*‖Z(τ'')-Z(τ')‖_{τ'} + ‖Z(τ')-W‖_{σ₀}
          --                   < K*sin(πδ) + ‖Z(τ')-W‖_{σ₀}
          -- Choose δ so K*sin(πδ) < gap = r - ‖Z(τ')-W‖_{σ₀}.
          -- Unfold preimage membership to direct inequality
          simp only [Set.mem_preimage] at hτ'_mem
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
            rw [show σ₀ = componentRep C cc by rfl, mk_componentRep C cc, hτ''cc]
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
                  dsimp [ε]; grind
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
          -- Comparison: ‖U‖_{σ_x} ≤ K_rev * ‖U‖_{σ₀}
          have hconn_x : ConnectedComponents.mk σ₀ = ConnectedComponents.mk σ_x := by
            rw [show σ₀ = componentRep C cc by rfl, mk_componentRep C cc, hσ_x_cc]
          obtain ⟨K_rev, hK_rev, hdom_rev⟩ :=
            stabSeminorm_dominated_of_connected C σ_x σ₀ hconn_x.symm
          rcases isOpen_induced_iff.mp hT_open with ⟨Tcomp, hTcomp_open, hT_eq⟩
          rcases isOpen_induced_iff.mp hTcomp_open with ⟨Tamb, hTamb_open, hTcomp_eq⟩
          have hx_Tcomp : ⟨σ_x, hσ_x_cc⟩ ∈ Tcomp := by
            rwa [← hT_eq] at hx_T
          have hx_Tamb : σ_x ∈ Tamb := by
            rwa [← hTcomp_eq] at hx_Tcomp
          obtain ⟨δT, hδT, hδT8, hsubT⟩ :=
            exists_basisNhd_subset_of_mem_open C σ_x hTamb_open hx_Tamb
          obtain ⟨δU, hδU, hδU8, hsubU⟩ :=
            exists_basisNhd_subset_basisNhd C σ σ_x hε_pos hε_lt hσ_x_U
          obtain ⟨ε₀_x, hε₀_x, hε₀_x10, hWide_x⟩ := σ_x.exists_epsilon0_tenth C
          let δ : ℝ := min (ε₀_x / 2) (min δT δU)
          have hδ : 0 < δ := by
            dsimp [δ]
            refine lt_min ?_ ?_
            · linarith
            · exact lt_min hδT hδU
          have hδ_le_δT : δ ≤ δT := by
            dsimp [δ]
            exact le_trans (min_le_right _ _) (min_le_left _ _)
          have hδ_le_δU : δ ≤ δU := by
            dsimp [δ]
            exact le_trans (min_le_right _ _) (min_le_right _ _)
          have hδ_lt_ε₀x : δ < ε₀_x := by
            dsimp [δ]
            linarith [min_le_left (ε₀_x / 2) (min δT δU)]
          have hδ8 : δ < 1 / 8 := by
            exact lt_of_le_of_lt hδ_le_δT hδT8
          have hsinδ_pos : 0 < Real.sin (Real.pi * δ) := by
            exact Real.sin_pos_of_pos_of_lt_pi
              (by positivity)
              (by nlinarith [Real.pi_pos, hδ8])
          let r0 : ℝ := min 1 (Real.sin (Real.pi * δ) / (2 * (K_rev.toReal + 1)))
          have hr0 : 0 < r0 := by
            dsimp [r0]
            refine lt_min zero_lt_one ?_
            have hden : 0 < 2 * (K_rev.toReal + 1) := by positivity
            exact div_pos hsinδ_pos hden
          have hKball : K_rev.toReal * r0 < Real.sin (Real.pi * δ) := by
            have hKnn : 0 ≤ K_rev.toReal := ENNReal.toReal_nonneg
            have hr0_le : r0 ≤ Real.sin (Real.pi * δ) / (2 * (K_rev.toReal + 1)) := by
              dsimp [r0]
              exact min_le_right _ _
            calc
              K_rev.toReal * r0
                  ≤ K_rev.toReal * (Real.sin (Real.pi * δ) / (2 * (K_rev.toReal + 1))) := by
                      gcongr
              _ < Real.sin (Real.pi * δ) := by
                  have hden : 0 < 2 * (K_rev.toReal + 1) := by positivity
                  have hcalc : K_rev.toReal * (Real.sin (Real.pi * δ) / (2 * (K_rev.toReal + 1)))
                      < Real.sin (Real.pi * δ) / 2 := by
                    have hfrac : K_rev.toReal / (K_rev.toReal + 1) < 1 := by
                      rw [div_lt_one (by positivity)]
                      linarith
                    have hfrac_nonneg : 0 ≤ K_rev.toReal / (K_rev.toReal + 1) := by
                      positivity
                    have htmp :
                        K_rev.toReal * (Real.sin (Real.pi * δ) / (2 * (K_rev.toReal + 1))) =
                          (K_rev.toReal / (K_rev.toReal + 1)) * (Real.sin (Real.pi * δ) / 2) := by
                      field_simp [hden.ne']
                    rw [htmp]
                    have hhalf_pos : 0 < Real.sin (Real.pi * δ) / 2 := by positivity
                    nlinarith
                  have hhalf : Real.sin (Real.pi * δ) / 2 < Real.sin (Real.pi * δ) := by
                    nlinarith
                  exact lt_trans hcalc hhalf
          let B : Set V := {F : V | stabSeminorm C σ₀ (↑F - σ_x.Z) < ENNReal.ofReal r0}
          refine Filter.mem_of_superset
            (IsOpen.mem_nhds
              (by
                change TopologicalSpace.GenerateOpen (componentSeminormBasis C cc) B
                exact TopologicalSpace.GenerateOpen.basic _ ⟨Zmap ⟨σ_x, hσ_x_cc⟩, r0, hr0, by
                  ext F
                  change componentSeminormBall C cc (Zmap ⟨σ_x, hσ_x_cc⟩) r0 F ↔
                    stabSeminorm C σ₀ (↑F - σ_x.Z) < ENNReal.ofReal r0
                  change
                    stabSeminorm C (componentRep C cc)
                        (↑F - ↑(componentZMap C cc ⟨σ_x, hσ_x_cc⟩)) <
                      ENNReal.ofReal r0 ↔
                      stabSeminorm C (componentRep C cc) (↑F - σ_x.Z) <
                        ENNReal.ofReal r0
                  rfl⟩)
              (by
                change stabSeminorm C σ₀ (σ_x.Z - σ_x.Z) < ENNReal.ofReal r0
                rw [sub_self, stabSeminorm_zero]
                exact ENNReal.ofReal_pos.mpr hr0))
            ?_
          intro F hF
          have hFσ₀ : stabSeminorm C σ₀ ((F : V) - σ_x.Z) < ENNReal.ofReal r0 := by
            simpa [B] using hF
          have hFfin : stabSeminorm C σ₀ ((F : V) - σ_x.Z) ≠ ⊤ := ne_top_of_lt hFσ₀
          have hK_eq : ENNReal.ofReal K_rev.toReal = K_rev := ENNReal.ofReal_toReal hK_rev
          set d := (stabSeminorm C σ₀ ((F : V) - σ_x.Z)).toReal
          have hd_eq : ENNReal.ofReal d = stabSeminorm C σ₀ ((F : V) - σ_x.Z) :=
            ENNReal.ofReal_toReal hFfin
          have hd_lt : d < r0 := by
            rwa [← hd_eq, ENNReal.ofReal_lt_ofReal_iff hr0] at hFσ₀
          have hWclose :
              stabSeminorm C σ_x ((F : V) - σ_x.Z) < ENNReal.ofReal (Real.sin (Real.pi * δ)) := by
            have hmul : K_rev.toReal * d < Real.sin (Real.pi * δ) := by
              nlinarith [hd_lt, hKball, ENNReal.toReal_nonneg (a := K_rev)]
            calc
              stabSeminorm C σ_x ((F : V) - σ_x.Z)
                  ≤ K_rev * stabSeminorm C σ₀ ((F : V) - σ_x.Z) := hdom_rev _
              _ ≤ K_rev * ENNReal.ofReal d := by rw [hd_eq]
              _ = ENNReal.ofReal K_rev.toReal * ENNReal.ofReal d := by simp [hK_eq]
              _ = ENNReal.ofReal (K_rev.toReal * d) := by
                  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
              _ < ENNReal.ofReal (Real.sin (Real.pi * δ)) :=
                  (ENNReal.ofReal_lt_ofReal_iff hsinδ_pos).2 hmul
          have hsinδ_lt_one : Real.sin (Real.pi * δ) < 1 := by
            have hπδ_lt : Real.pi * δ < 1 := by
              nlinarith [Real.pi_lt_d4, hδ8]
            exact lt_trans (Real.sin_lt (by positivity)) hπδ_lt
          have hWclose1 : stabSeminorm C σ_x ((F : V) - σ_x.Z) < ENNReal.ofReal 1 := by
            exact lt_trans hWclose
              ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hsinδ_lt_one)
          obtain ⟨ρ, hρZ, hρmem⟩ :=
            bridgeland_7_1_mem_basisNhd C σ_x (F : V) hWclose1
              ε₀_x hε₀_x hε₀_x10 hWide_x δ hδ hδ_lt_ε₀x hWclose
          have hρccx :
              ConnectedComponents.mk ρ = ConnectedComponents.mk σ_x :=
            basisNhd_subset_connectedComponent_small C σ_x hε₀_x hε₀_x10 hWide_x hδ hδ_lt_ε₀x hρmem
          have hρcc : ConnectedComponents.mk ρ = cc := hρccx.trans hσ_x_cc
          let yComp : comp := ⟨ρ, hρcc⟩
          have hρmemT : ρ ∈ basisNhd C σ_x δT := by
            exact basisNhd_mono C σ_x hδ hδ_le_δT hδT8 hρmem
          have hρTamb : ρ ∈ Tamb := hsubT hρmemT
          have hyTcomp : yComp ∈ Tcomp := by
            rwa [← hTcomp_eq]
          have hρmemU : ρ ∈ basisNhd C σ ε := by
            exact hsubU <| basisNhd_mono C σ_x hδ hδ_le_δU hδU8 hρmem
          have hyU : yComp ∈ U := hρmemU
          let yU : U := ⟨yComp, hyU⟩
          have hyT : yU ∈ T := by
            rwa [← hT_eq]
          have hyS : (U.restrict Zmap) yU ∈ S := hT_sub hyT
          have hZeq : Zmap yComp = F := by
            apply Subtype.ext
            exact hρZ
          simpa [yU, yComp, hZeq] using hyS
        exact IsOpenEmbedding.of_continuous_injective_isOpenMap
          (hZcont.comp continuous_subtype_val) hZinj hZopen
    change @IsLocalHomeomorph comp V inferInstance inferInstance Zmap
    exact (componentSeminormTopology_eq_normTopology C cc) ▸ hLocal

theorem bridgeland_theorem_1_2' :
    bridgelandTheorem_1_2 C := by
  intro cc
  let M := componentTopologicalLinearLocalModel C cc
  exact ⟨M.V, M.instNormedAddCommGroup, M.instNormedSpace,
    M.mem_charge, M.isLocalHomeomorph_chargeMap⟩

end CategoryTheory.Triangulated
