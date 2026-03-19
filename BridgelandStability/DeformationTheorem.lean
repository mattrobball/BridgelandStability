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
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    ∃ τ : StabilityCondition C, τ.Z = W ∧ τ ∈ basisNhd C σ ε := by
  obtain ⟨τ, hτZ, hτd⟩ :=
    bridgeland_7_1 C σ W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin
  refine ⟨τ, hτZ, ?_⟩
  constructor
  · simpa [hτZ] using hsin
  · simpa using hτd

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

/-- A local `ε₀ < 1 / 10` witness for Theorem 7.1, obtained by shrinking the standard
`exists_epsilon0` witness. -/
theorem StabilityCondition.exists_epsilon0_tenth (σ : StabilityCondition C) :
    ∃ ε₀ : ℝ, ∃ hε₀ : 0 < ε₀, ∃ hε₀10 : ε₀ < 1 / 10,
      WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]) := by
  obtain ⟨ε₁, hε₁, hε₁8, hWide₁⟩ := σ.exists_epsilon0 C
  refine ⟨ε₁ / 2, by positivity, by linarith, ?_⟩
  exact wideSectorFiniteLength_mono C σ hε₁ hε₁8 hWide₁
    (by positivity) (by linarith) (by linarith)

/-- The affine interpolation between the central charges of `σ` and `τ`. -/
def linearInterpolationZ (σ τ : StabilityCondition C) (t : ℝ) : K₀ C →+ ℂ :=
  σ.Z + t • (τ.Z - σ.Z)

@[simp] theorem linearInterpolationZ_zero (σ τ : StabilityCondition C) :
    linearInterpolationZ C σ τ 0 = σ.Z := by
  simp [linearInterpolationZ]

@[simp] theorem linearInterpolationZ_one (σ τ : StabilityCondition C) :
    linearInterpolationZ C σ τ 1 = τ.Z := by
  ext x
  simp [linearInterpolationZ]

theorem linearInterpolationZ_sub (σ τ : StabilityCondition C) (t : ℝ) :
    linearInterpolationZ C σ τ t - σ.Z = t • (τ.Z - σ.Z) := by
  ext x
  simp [linearInterpolationZ]

theorem linearInterpolationZ_sub_sub (σ τ : StabilityCondition C) (s t : ℝ) :
    linearInterpolationZ C σ τ t - linearInterpolationZ C σ τ s =
      (t - s) • (τ.Z - σ.Z) := by
  ext x
  simp [linearInterpolationZ, smul_sub]
  module

theorem stabSeminorm_smul (σ : StabilityCondition C) (U : K₀ C →+ ℂ) (t : ℝ) :
    stabSeminorm C σ (t • U) = ENNReal.ofReal |t| * stabSeminorm C σ U := by
  unfold stabSeminorm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro E
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro φ
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro hP
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro hE
  rw [AddMonoidHom.smul_apply, norm_smul, Real.norm_eq_abs, div_eq_mul_inv,
    ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity)]
  simp [mul_assoc]

/-- A local form of Bridgeland's Lemma 6.2: on a single basis neighborhood, the
center seminorm is dominated by the nearby seminorm with a finite constant. -/
theorem stabSeminorm_dominated_of_basisNhd (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε) :
    ∃ K : ENNReal, K ≠ ⊤ ∧
      ∀ (U : K₀ C →+ ℂ), stabSeminorm C σ U ≤ K * stabSeminorm C τ U := by
  rcases hτ with ⟨hZnorm, hd⟩
  have hε2 : ε < 1 / 2 := by linarith
  have hsin_lt_cos : Real.sin (Real.pi * ε) < Real.cos (Real.pi * ε) := by
    rw [← Real.cos_pi_div_two_sub]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcos_pos' : 0 < Real.cos (Real.pi * ε) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hZdiff : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)) :=
    lt_trans hZnorm ((ENNReal.ofReal_lt_ofReal_iff hcos_pos').mpr hsin_lt_cos)
  have hZdiff_ne : stabSeminorm C σ (τ.Z - σ.Z) ≠ ⊤ :=
    ne_top_of_lt (lt_trans hZdiff ENNReal.ofReal_lt_top)
  set M_Z := (stabSeminorm C σ (τ.Z - σ.Z)).toReal with hMZ_def
  have hMZ0 : 0 ≤ M_Z := ENNReal.toReal_nonneg
  have hMZ_lt_sin : M_Z < Real.sin (Real.pi * ε) := by
    by_contra hle
    push_neg at hle
    have h1 : ENNReal.ofReal (Real.sin (Real.pi * ε)) ≤ ENNReal.ofReal M_Z :=
      ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_toReal hZdiff_ne] at h1
    exact absurd hZnorm (not_lt.mpr h1)
  have hcos_pos := hcos_pos'
  have hMZ_lt_cos : M_Z < Real.cos (Real.pi * ε) := lt_trans hMZ_lt_sin hsin_lt_cos
  set c := Real.cos (Real.pi * ε) with hc_def
  have hcMZ : 0 < c - M_Z := by linarith
  have hZbound : stabSeminorm C τ (τ.Z - σ.Z) ≤
      ENNReal.ofReal (M_Z / (c - M_Z)) :=
    stabSeminorm_le_of_near C σ τ hε hε2 hd hZdiff (τ.Z - σ.Z) hZdiff_ne
  have hsin_pos : 0 < Real.sin (Real.pi * ε) := by
    exact Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hsin_le : Real.sin (Real.pi * ε) ≤ Real.pi * ε :=
    Real.sin_le (by nlinarith [Real.pi_pos])
  have hx_ineq : (Real.pi * ε) ^ 2 + 2 * (Real.pi * ε) < 1 := by
    have hx_bound : Real.pi * ε < Real.pi / 8 := by
      nlinarith [hε8, Real.pi_pos]
    have h1 : (Real.pi * ε) ^ 2 + 2 * (Real.pi * ε) <
        (Real.pi / 8) ^ 2 + 2 * (Real.pi / 8) := by
      nlinarith [hx_bound, Real.pi_pos, sq_nonneg (Real.pi * ε)]
    have hpi := Real.pi_lt_d2
    have h2 : (Real.pi / 8) ^ 2 + 2 * (Real.pi / 8) < 1 := by
      nlinarith [hpi]
    exact lt_trans h1 h2
  have hMZ_bound : M_Z * (1 + c) < c ^ 2 := by
    calc M_Z * (1 + c)
        < Real.sin (Real.pi * ε) * (1 + c) :=
          mul_lt_mul_of_pos_right hMZ_lt_sin (by linarith)
      _ ≤ (Real.pi * ε) * 2 := by
          have hcos_le : c ≤ 1 := Real.cos_le_one _
          have : 1 + c ≤ 2 := by linarith
          exact mul_le_mul hsin_le this (by linarith) (by nlinarith [Real.pi_pos])
      _ = 2 * (Real.pi * ε) := by ring
      _ < 1 - (Real.pi * ε) ^ 2 := by linarith
      _ ≤ c ^ 2 := by
          have hsin_sq : Real.sin (Real.pi * ε) ^ 2 ≤ (Real.pi * ε) ^ 2 := by
            rw [sq, sq]
            exact mul_le_mul hsin_le hsin_le (le_of_lt hsin_pos)
              (by nlinarith [Real.pi_pos])
          have := Real.sin_sq_add_cos_sq (Real.pi * ε)
          nlinarith
  have hbound_lt_cos : M_Z / (c - M_Z) < c := by
    rw [div_lt_iff₀ hcMZ]
    linarith
  have hZτ_bound : stabSeminorm C τ (σ.Z - τ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)) := by
    have : stabSeminorm C τ (σ.Z - τ.Z) = stabSeminorm C τ (τ.Z - σ.Z) := by
      simp only [stabSeminorm, AddMonoidHom.sub_apply]
      congr 1
      ext E
      congr 1
      ext φ
      congr 1
      ext
      congr 1
      ext
      rw [norm_sub_rev]
    rw [this]
    exact lt_of_le_of_lt hZbound
      ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hbound_lt_cos)
  have hZτ_ne : stabSeminorm C τ (σ.Z - τ.Z) ≠ ⊤ :=
    ne_top_of_lt (lt_trans hZτ_bound ENNReal.ofReal_lt_top)
  set N_Z := (stabSeminorm C τ (σ.Z - τ.Z)).toReal with hNZ_def
  have hNZ_lt_cos : N_Z < c := by
    by_contra hle
    push_neg at hle
    have h1 : ENNReal.ofReal c ≤ ENNReal.ofReal N_Z := ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_toReal hZτ_ne] at h1
    exact absurd hZτ_bound (not_lt.mpr h1)
  have hcNZ : 0 < c - N_Z := by linarith
  refine ⟨ENNReal.ofReal (1 / (c - N_Z)), ENNReal.ofReal_ne_top, ?_⟩
  intro U
  by_cases hU : stabSeminorm C τ U = ⊤
  · have hK0 : ENNReal.ofReal ((c - N_Z)⁻¹) ≠ 0 := by
      exact ne_of_gt (by positivity)
    have hK0' : ENNReal.ofReal (1 / (c - N_Z)) ≠ 0 := by
      simpa [one_div] using hK0
    rw [hU, ENNReal.mul_top hK0']
    exact le_top
  · have hbound := stabSeminorm_le_of_near C τ σ hε hε2 (by rwa [slicingDist_symm])
        hZτ_bound U hU
    have hbound' :
        stabSeminorm C σ U ≤ ENNReal.ofReal ((stabSeminorm C τ U).toReal / (c - N_Z)) := by
      simpa [hNZ_def, hc_def] using hbound
    calc stabSeminorm C σ U
        ≤ ENNReal.ofReal ((stabSeminorm C τ U).toReal / (c - N_Z)) := hbound'
      _ = ENNReal.ofReal (1 / (c - N_Z)) * stabSeminorm C τ U := by
          rw [div_eq_mul_inv, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hU]
          simp [one_div, mul_comm, mul_left_comm, mul_assoc]

/-- Local forward domination inside a Bridgeland basis neighborhood. -/
theorem stabSeminorm_center_dominates_of_basisNhd (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε) :
    ∃ K : ENNReal, K ≠ ⊤ ∧
      ∀ (U : K₀ C →+ ℂ), stabSeminorm C τ U ≤ K * stabSeminorm C σ U := by
  rcases hτ with ⟨hZnorm, hd⟩
  have hε2 : ε < 1 / 2 := by linarith
  have hsin_lt_cos : Real.sin (Real.pi * ε) < Real.cos (Real.pi * ε) := by
    rw [← Real.cos_pi_div_two_sub]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcos_pos' : 0 < Real.cos (Real.pi * ε) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hZdiff : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)) :=
    lt_trans hZnorm ((ENNReal.ofReal_lt_ofReal_iff hcos_pos').mpr hsin_lt_cos)
  have hZdiff_ne : stabSeminorm C σ (τ.Z - σ.Z) ≠ ⊤ :=
    ne_top_of_lt (lt_trans hZdiff ENNReal.ofReal_lt_top)
  set M_Z := (stabSeminorm C σ (τ.Z - σ.Z)).toReal with hMZ_def
  have hMZ_lt_cos : M_Z < Real.cos (Real.pi * ε) := by
    by_contra hle
    push_neg at hle
    have h1 : ENNReal.ofReal (Real.cos (Real.pi * ε)) ≤ ENNReal.ofReal M_Z :=
      ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_toReal hZdiff_ne] at h1
    exact absurd hZdiff (not_lt.mpr h1)
  set c := Real.cos (Real.pi * ε) with hc_def
  have hcMZ : 0 < c - M_Z := by linarith
  refine ⟨ENNReal.ofReal (1 / (c - M_Z)), ENNReal.ofReal_ne_top, ?_⟩
  intro U
  by_cases hU : stabSeminorm C σ U = ⊤
  · have hK0 : ENNReal.ofReal ((c - M_Z)⁻¹) ≠ 0 := by
      exact ne_of_gt (by positivity)
    have hK0' : ENNReal.ofReal (1 / (c - M_Z)) ≠ 0 := by
      simpa [one_div] using hK0
    rw [hU, ENNReal.mul_top hK0']
    exact le_top
  · have hbound := stabSeminorm_le_of_near C σ τ hε hε2 hd hZdiff U hU
    have hbound' :
        stabSeminorm C τ U ≤ ENNReal.ofReal ((stabSeminorm C σ U).toReal / (c - M_Z)) := by
      simpa [hMZ_def, hc_def] using hbound
    calc stabSeminorm C τ U
        ≤ ENNReal.ofReal ((stabSeminorm C σ U).toReal / (c - M_Z)) := hbound'
      _ = ENNReal.ofReal (1 / (c - M_Z)) * stabSeminorm C σ U := by
          rw [div_eq_mul_inv, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hU]
          simp [one_div, mul_comm]

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

This is the local basis-refinement step used later in the local homeomorphism proof.
It only needs seminorm domination for nearby stability conditions. -/
theorem exists_basisNhd_subset_basisNhd (σ τ : StabilityCondition C) {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 8 ∧ basisNhd C τ δ ⊆ basisNhd C σ ε := by
  rcases hτ with ⟨hτZ, hτd⟩
  have hτ_mem : τ ∈ basisNhd C σ ε := ⟨hτZ, hτd⟩
  obtain ⟨K, hK, hdom⟩ :=
    stabSeminorm_dominated_of_basisNhd C σ τ hε hε8 hτ_mem
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

/-- Two stability conditions with same Z and d < 1 are equal (Lemma 6.4). -/
theorem StabilityCondition.eq_of_same_Z_near (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal 1) :
    σ = τ := by
  have hP : σ.slicing.P = τ.slicing.P := by
    funext φ; ext E; exact bridgeland_lemma_6_4 C σ τ hZ hd φ E
  cases σ; cases τ; simp only [StabilityCondition.mk.injEq]
  exact ⟨by cases ‹Slicing C›; cases ‹Slicing C›; simpa [Slicing.mk.injEq] using hP, hZ⟩

/-- Two stability conditions lying in the same Bridgeland basis neighborhood of `σ`
and with the same central charge are equal. -/
theorem StabilityCondition.eq_of_same_Z_of_mem_basisNhd (σ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8)
    {τ₁ τ₂ : StabilityCondition C}
    (hτ₁ : τ₁ ∈ basisNhd C σ ε) (hτ₂ : τ₂ ∈ basisNhd C σ ε)
    (hZ : τ₁.Z = τ₂.Z) :
    τ₁ = τ₂ := by
  apply StabilityCondition.eq_of_same_Z_near C τ₁ τ₂ hZ
  have hdist :
      slicingDist C τ₁.slicing τ₂.slicing < ENNReal.ofReal (ε + ε) := by
    calc
      slicingDist C τ₁.slicing τ₂.slicing
          ≤ slicingDist C τ₁.slicing σ.slicing + slicingDist C σ.slicing τ₂.slicing :=
            slicingDist_triangle C τ₁.slicing σ.slicing τ₂.slicing
      _ < ENNReal.ofReal ε + ENNReal.ofReal ε := by
          exact ENNReal.add_lt_add
            (by simpa [slicingDist_symm] using hτ₁.2)
            hτ₂.2
      _ = ENNReal.ofReal (ε + ε) := by
          rw [← ENNReal.ofReal_add (le_of_lt hε) (le_of_lt hε)]
  exact lt_trans hdist <|
    (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (by linarith [hε8])

/-- A small Bridgeland basis neighborhood, with radius below the local Theorem 7.1 witness,
lies in the connected component of its center. This is the direct straight-line interpolation
argument from Bridgeland §7. -/
theorem basisNhd_subset_connectedComponent_small (σ : StabilityCondition C)
    {ε₀ ε : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (hε : 0 < ε) (hεε₀ : ε < ε₀) :
    basisNhd C σ ε ⊆ {τ | ConnectedComponents.mk τ = ConnectedComponents.mk σ} := by
  have hε8 : ε < 1 / 8 := by linarith
  intro τ hτ
  rcases hτ with ⟨hτZ, hτd⟩
  let W : unitInterval → K₀ C →+ ℂ := fun t => linearInterpolationZ C σ τ t
  have hτfin : stabSeminorm C σ (τ.Z - σ.Z) ≠ ⊤ := ne_top_of_lt hτZ
  have hWt :
      ∀ t : unitInterval,
        stabSeminorm C σ (W t - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) := by
    intro t
    have ht_abs_le : |(t : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg t.2.1]
      exact t.2.2
    have hcoef : ENNReal.ofReal |(t : ℝ)| ≤ ENNReal.ofReal 1 :=
      ENNReal.ofReal_le_ofReal ht_abs_le
    calc stabSeminorm C σ (W t - σ.Z)
      = ENNReal.ofReal |(t : ℝ)| * stabSeminorm C σ (τ.Z - σ.Z) := by
          simp [W, linearInterpolationZ_sub, stabSeminorm_smul]
    _ ≤ ENNReal.ofReal 1 * stabSeminorm C σ (τ.Z - σ.Z) := by
          exact mul_le_mul' hcoef le_rfl
    _ = stabSeminorm C σ (τ.Z - σ.Z) := by simp
    _ < ENNReal.ofReal (Real.sin (Real.pi * ε)) := hτZ
  have hsinε_lt_one : Real.sin (Real.pi * ε) < 1 := by
    have hπε_lt : Real.pi * ε < 1 := by
      nlinarith [Real.pi_lt_d4, hε8]
    exact lt_trans (Real.sin_lt (by positivity)) hπε_lt
  have hW1 :
      ∀ t : unitInterval, stabSeminorm C σ (W t - σ.Z) < ENNReal.ofReal 1 := by
    intro t
    exact lt_trans (hWt t) ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hsinε_lt_one)
  have hγ_exists :
      ∀ t : unitInterval, ∃ ρ : StabilityCondition C, ρ.Z = W t ∧ ρ ∈ basisNhd C σ ε := by
    intro t
    exact bridgeland_7_1_mem_basisNhd C σ (W t) (hW1 t) ε₀ hε₀ hε₀10 hWide ε hε hεε₀ (hWt t)
  let γ : unitInterval → StabilityCondition C := fun t => Classical.choose (hγ_exists t)
  have hγZ : ∀ t : unitInterval, (γ t).Z = W t := by
    intro t
    exact (Classical.choose_spec (hγ_exists t)).1
  have hγmem : ∀ t : unitInterval, γ t ∈ basisNhd C σ ε := by
    intro t
    exact (Classical.choose_spec (hγ_exists t)).2
  have hγ0 : γ 0 = σ := by
    apply StabilityCondition.eq_of_same_Z_near C (γ 0) σ
    · simpa [γ, W] using hγZ 0
    · have h0 : slicingDist C σ.slicing (γ 0).slicing < ENNReal.ofReal ε := (hγmem 0).2
      have h0' : slicingDist C (γ 0).slicing σ.slicing < ENNReal.ofReal ε := by
        simpa [slicingDist_symm] using h0
      exact lt_trans h0' <|
        (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (by linarith)
  have hγ1 : γ 1 = τ := by
    apply StabilityCondition.eq_of_same_Z_near C (γ 1) τ
    · simpa [γ, W] using (hγZ 1).trans (linearInterpolationZ_one C σ τ)
    · have hsum :
          slicingDist C (γ 1).slicing τ.slicing < ENNReal.ofReal (ε + ε) := by
        calc slicingDist C (γ 1).slicing τ.slicing
            ≤ slicingDist C (γ 1).slicing σ.slicing + slicingDist C σ.slicing τ.slicing :=
              slicingDist_triangle C (γ 1).slicing σ.slicing τ.slicing
          _ < ENNReal.ofReal ε + ENNReal.ofReal ε := by
              have h1 : slicingDist C (γ 1).slicing σ.slicing < ENNReal.ofReal ε := by
                simpa [slicingDist_symm] using (hγmem 1).2
              exact ENNReal.add_lt_add h1 hτd
          _ = ENNReal.ofReal (ε + ε) := by
              rw [← ENNReal.ofReal_add (le_of_lt hε) (le_of_lt hε)]
      exact lt_trans hsum <|
        (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (by linarith [hεε₀, hε₀10])
  have hγcont : Continuous γ := by
    rw [continuous_generateFrom_iff]
    intro U hU
    rcases hU with ⟨ξ, δ₀, hδ₀, hδ₀8, rfl⟩
    rw [isOpen_iff_mem_nhds]
    intro t ht
    let ρ₀ := γ t
    obtain ⟨δ₁, hδ₁, hδ₁8, hsub₁⟩ :=
      exists_basisNhd_subset_basisNhd C ξ ρ₀ hδ₀ hδ₀8 ht
    obtain ⟨ε₁, hε₁, hε₁10, hWide₁⟩ := ρ₀.exists_epsilon0_tenth C
    let δ : ℝ := min (δ₁ / 2) (ε₁ / 2)
    have hδ : 0 < δ := by
      dsimp [δ]
      refine lt_min ?_ ?_
      · linarith
      · linarith
    have hδ_lt_δ₁ : δ < δ₁ := by
      dsimp [δ]
      linarith [min_le_left (δ₁ / 2) (ε₁ / 2)]
    have hδ_lt_ε₁ : δ < ε₁ := by
      dsimp [δ]
      linarith [min_le_right (δ₁ / 2) (ε₁ / 2)]
    have hδ8 : δ < 1 / 8 := by
      linarith [hδ_lt_δ₁, hδ₁8]
    have hsubU : basisNhd C ρ₀ δ ⊆ basisNhd C ξ δ₀ := by
      intro ρ hρ
      exact hsub₁ <| basisNhd_mono C ρ₀ hδ (le_of_lt hδ_lt_δ₁) hδ₁8 hρ
    have hρ₀mem : ρ₀ ∈ basisNhd C σ ε := hγmem t
    obtain ⟨K, hK, hdom⟩ :=
      stabSeminorm_center_dominates_of_basisNhd C σ ρ₀ hε hε8 hρ₀mem
    have hUfin : stabSeminorm C ρ₀ (τ.Z - σ.Z) ≠ ⊤ := by
      apply lt_top_iff_ne_top.mp
      exact lt_of_le_of_lt (hdom _) <|
        ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) (lt_trans hτZ ENNReal.ofReal_lt_top)
    set L := (stabSeminorm C ρ₀ (τ.Z - σ.Z)).toReal
    have hL_eq : ENNReal.ofReal L = stabSeminorm C ρ₀ (τ.Z - σ.Z) :=
      ENNReal.ofReal_toReal hUfin
    have hL_nonneg : 0 ≤ L := ENNReal.toReal_nonneg
    have hsinδ_pos : 0 < Real.sin (Real.pi * δ) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith [Real.pi_pos, hδ8]
    let η : ℝ := min 1 (Real.sin (Real.pi * δ) / (2 * (L + 1)))
    have hη : 0 < η := by
      dsimp [η]
      refine lt_min zero_lt_one ?_
      have hden : 0 < 2 * (L + 1) := by positivity
      exact div_pos hsinδ_pos hden
    let V : Set unitInterval := {s | |(s : ℝ) - t| < η}
    have hV_open : IsOpen V := by
      have hcont : Continuous fun s : unitInterval => |(s : ℝ) - t| := by
        exact continuous_abs.comp (continuous_subtype_val.sub continuous_const)
      simpa [V] using isOpen_lt hcont continuous_const
    refine mem_nhds_iff.mpr ⟨V, ?_, hV_open, ?_⟩
    · intro s hs
      have hsη : |(s : ℝ) - t| < η := hs
      have hsη' : |(s : ℝ) - t| < Real.sin (Real.pi * δ) / (2 * (L + 1)) := by
        exact lt_of_lt_of_le hsη <| by
          dsimp [η]
          exact min_le_right _ _
      have hWclose :
          stabSeminorm C ρ₀ (W s - ρ₀.Z) < ENNReal.ofReal (Real.sin (Real.pi * δ)) := by
        have hmul : |(s : ℝ) - t| * L < Real.sin (Real.pi * δ) := by
          have hLp1 : 0 < L + 1 := by positivity
          have hmul_le : |(s : ℝ) - t| * L ≤ |(s : ℝ) - t| * (L + 1) := by
            gcongr
            linarith
          have hmul_half : |(s : ℝ) - t| * (L + 1) < Real.sin (Real.pi * δ) / 2 := by
            calc
              |(s : ℝ) - t| * (L + 1)
                  < (Real.sin (Real.pi * δ) / (2 * (L + 1))) * (L + 1) := by
                      gcongr
              _ = Real.sin (Real.pi * δ) / 2 := by
                  field_simp [hLp1.ne']
          have hhalf_lt : Real.sin (Real.pi * δ) / 2 < Real.sin (Real.pi * δ) := by
            nlinarith
          exact lt_of_le_of_lt hmul_le (lt_trans hmul_half hhalf_lt)
        calc stabSeminorm C ρ₀ (W s - ρ₀.Z)
            = ENNReal.ofReal (|(s : ℝ) - t|) * stabSeminorm C ρ₀ (τ.Z - σ.Z) := by
                dsimp [ρ₀]
                rw [hγZ t]
                rw [show W s - W t = ((s : ℝ) - t) • (τ.Z - σ.Z) by
                  simpa [W] using linearInterpolationZ_sub_sub C σ τ t s]
                rw [stabSeminorm_smul]
            _ = ENNReal.ofReal (|(s : ℝ) - t|) * ENNReal.ofReal L := by rw [hL_eq]
            _ = ENNReal.ofReal (|(s : ℝ) - t| * L) := by
                rw [← ENNReal.ofReal_mul (abs_nonneg _)]
            _ < ENNReal.ofReal (Real.sin (Real.pi * δ)) :=
                (ENNReal.ofReal_lt_ofReal_iff hsinδ_pos).2 hmul
      have hsinδ_lt_one : Real.sin (Real.pi * δ) < 1 := by
        have hπδ_lt : Real.pi * δ < 1 := by
          nlinarith [Real.pi_lt_d4, hδ8]
        exact lt_trans (Real.sin_lt (by positivity)) hπδ_lt
      have hWclose1 : stabSeminorm C ρ₀ (W s - ρ₀.Z) < ENNReal.ofReal 1 := by
        exact lt_trans hWclose ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hsinδ_lt_one)
      obtain ⟨ρ, hρZ, hρmem⟩ :=
        bridgeland_7_1_mem_basisNhd C ρ₀ (W s) hWclose1 ε₁ hε₁ hε₁10 hWide₁ δ hδ
          hδ_lt_ε₁ hWclose
      have hγs_eq_ρ : γ s = ρ := by
        apply StabilityCondition.eq_of_same_Z_near C (γ s) ρ
        · rw [hγZ s, hρZ]
        · have hdist₁ :
              slicingDist C (γ s).slicing ρ₀.slicing < ENNReal.ofReal (ε + ε) := by
            calc slicingDist C (γ s).slicing ρ₀.slicing
                ≤ slicingDist C (γ s).slicing σ.slicing + slicingDist C σ.slicing ρ₀.slicing :=
                  slicingDist_triangle C (γ s).slicing σ.slicing ρ₀.slicing
              _ < ENNReal.ofReal ε + ENNReal.ofReal ε := by
                  have hρ₀d : slicingDist C σ.slicing ρ₀.slicing < ENNReal.ofReal ε := by
                    simpa [ρ₀, slicingDist_symm] using hρ₀mem.2
                  exact ENNReal.add_lt_add
                    (by simpa [slicingDist_symm] using (hγmem s).2) hρ₀d
              _ = ENNReal.ofReal (ε + ε) := by
                  rw [← ENNReal.ofReal_add (le_of_lt hε) (le_of_lt hε)]
          have hdist₂ :
              slicingDist C (γ s).slicing ρ.slicing < ENNReal.ofReal ((ε + ε) + δ) := by
            calc slicingDist C (γ s).slicing ρ.slicing
                ≤ slicingDist C (γ s).slicing ρ₀.slicing + slicingDist C ρ₀.slicing ρ.slicing :=
                  slicingDist_triangle C (γ s).slicing ρ₀.slicing ρ.slicing
              _ < ENNReal.ofReal (ε + ε) + ENNReal.ofReal δ := by
                  exact ENNReal.add_lt_add hdist₁ hρmem.2
              _ = ENNReal.ofReal ((ε + ε) + δ) := by
                  rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hδ)]
          exact lt_trans hdist₂ <|
            (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (by linarith [hεε₀, hε₀10, hδ8])
      exact hsubU <| by simpa [hγs_eq_ρ] using hρmem
    · simpa [V] using hη
  let p : Path σ τ :=
    { toFun := γ
      continuous_toFun := hγcont
      source' := by simpa [hγ0]
      target' := by simpa [hγ1] }
  have hpath : τ ∈ pathComponent σ := ⟨p⟩
  exact ConnectedComponents.coe_eq_coe'.2 <| pathComponent_subset_component σ hpath

/-- Local continuation along the straight-line charge interpolation inside a fixed basis
neighborhood. Starting from any lifted point `ρ₀` over time `t`, nearby times also admit lifts
inside the same ambient basis neighborhood and in the same connected component as `ρ₀`. -/
theorem exists_local_lift_sameComponent_in_basisNhd (σ τ ρ₀ : StabilityCondition C)
    {ε t : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε)
    (hρ₀mem : ρ₀ ∈ basisNhd C σ ε)
    (hρ₀Z : ρ₀.Z = linearInterpolationZ C σ τ t) :
    ∃ η : ℝ, 0 < η ∧
      ∀ ⦃s : ℝ⦄, |s - t| < η →
        ∃ ρ : StabilityCondition C,
          ρ.Z = linearInterpolationZ C σ τ s ∧
          ρ ∈ basisNhd C σ ε ∧
          ConnectedComponents.mk ρ = ConnectedComponents.mk ρ₀ := by
  rcases hτ with ⟨hτZ, _hτd⟩
  obtain ⟨δ₁, hδ₁, hδ₁8, hsub₁⟩ :=
    exists_basisNhd_subset_basisNhd C σ ρ₀ hε hε8 hρ₀mem
  obtain ⟨ε₁, hε₁, hε₁10, hWide₁⟩ := ρ₀.exists_epsilon0_tenth C
  let δ : ℝ := min (δ₁ / 2) (ε₁ / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · linarith
    · linarith
  have hδ_lt_δ₁ : δ < δ₁ := by
    dsimp [δ]
    linarith [min_le_left (δ₁ / 2) (ε₁ / 2)]
  have hδ_lt_ε₁ : δ < ε₁ := by
    dsimp [δ]
    linarith [min_le_right (δ₁ / 2) (ε₁ / 2)]
  have hδ8 : δ < 1 / 8 := by
    linarith [hδ_lt_δ₁, hδ₁8]
  have hsubU : basisNhd C ρ₀ δ ⊆ basisNhd C σ ε := by
    intro ρ hρ
    exact hsub₁ <| basisNhd_mono C ρ₀ hδ (le_of_lt hδ_lt_δ₁) hδ₁8 hρ
  obtain ⟨K, hK, hdom⟩ :=
    stabSeminorm_center_dominates_of_basisNhd C σ ρ₀ hε hε8 hρ₀mem
  have hUfin : stabSeminorm C ρ₀ (τ.Z - σ.Z) ≠ ⊤ := by
    apply lt_top_iff_ne_top.mp
    exact lt_of_le_of_lt (hdom _) <|
      ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) (lt_trans hτZ ENNReal.ofReal_lt_top)
  set L := (stabSeminorm C ρ₀ (τ.Z - σ.Z)).toReal
  have hL_eq : ENNReal.ofReal L = stabSeminorm C ρ₀ (τ.Z - σ.Z) :=
    ENNReal.ofReal_toReal hUfin
  have hL_nonneg : 0 ≤ L := ENNReal.toReal_nonneg
  have hsinδ_pos : 0 < Real.sin (Real.pi * δ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos, hδ8]
  let η : ℝ := min 1 (Real.sin (Real.pi * δ) / (2 * (L + 1)))
  have hη : 0 < η := by
    dsimp [η]
    refine lt_min zero_lt_one ?_
    have hden : 0 < 2 * (L + 1) := by positivity
    exact div_pos hsinδ_pos hden
  refine ⟨η, hη, ?_⟩
  intro s hsη
  have hsη' : |s - t| < Real.sin (Real.pi * δ) / (2 * (L + 1)) := by
    exact lt_of_lt_of_le hsη <| by
      dsimp [η]
      exact min_le_right _ _
  have hsinδ_lt_one : Real.sin (Real.pi * δ) < 1 := by
    have hπδ_lt : Real.pi * δ < 1 := by
      nlinarith [Real.pi_lt_d4, hδ8]
    exact lt_trans (Real.sin_lt (by positivity)) hπδ_lt
  have hWclose :
      stabSeminorm C ρ₀ (linearInterpolationZ C σ τ s - ρ₀.Z) <
        ENNReal.ofReal (Real.sin (Real.pi * δ)) := by
    have hLp1 : 0 < L + 1 := by positivity
    have hmul : |s - t| * L < Real.sin (Real.pi * δ) := by
      have hmul_le : |s - t| * L ≤ |s - t| * (L + 1) := by
        gcongr
        linarith
      have hmul_half : |s - t| * (L + 1) < Real.sin (Real.pi * δ) / 2 := by
        calc
          |s - t| * (L + 1)
              < (Real.sin (Real.pi * δ) / (2 * (L + 1))) * (L + 1) := by
                  gcongr
          _ = Real.sin (Real.pi * δ) / 2 := by
              field_simp [hLp1.ne']
      have hhalf_lt : Real.sin (Real.pi * δ) / 2 < Real.sin (Real.pi * δ) := by
        nlinarith
      exact lt_of_le_of_lt hmul_le (lt_trans hmul_half hhalf_lt)
    calc stabSeminorm C ρ₀ (linearInterpolationZ C σ τ s - ρ₀.Z)
        = ENNReal.ofReal |s - t| * stabSeminorm C ρ₀ (τ.Z - σ.Z) := by
            rw [hρ₀Z]
            rw [show linearInterpolationZ C σ τ s - linearInterpolationZ C σ τ t =
                (s - t) • (τ.Z - σ.Z) by
                  simpa using linearInterpolationZ_sub_sub C σ τ t s]
            rw [stabSeminorm_smul]
        _ = ENNReal.ofReal |s - t| * ENNReal.ofReal L := by rw [hL_eq]
        _ = ENNReal.ofReal (|s - t| * L) := by
            rw [← ENNReal.ofReal_mul (abs_nonneg _)]
        _ < ENNReal.ofReal (Real.sin (Real.pi * δ)) :=
            (ENNReal.ofReal_lt_ofReal_iff hsinδ_pos).2 hmul
  have hWclose1 :
      stabSeminorm C ρ₀ (linearInterpolationZ C σ τ s - ρ₀.Z) < ENNReal.ofReal 1 := by
    exact lt_trans hWclose ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hsinδ_lt_one)
  obtain ⟨ρ, hρZ, hρmem⟩ :=
    bridgeland_7_1_mem_basisNhd C ρ₀ (linearInterpolationZ C σ τ s) hWclose1 ε₁ hε₁ hε₁10
      hWide₁ δ hδ hδ_lt_ε₁ hWclose
  refine ⟨ρ, hρZ, hsubU hρmem, ?_⟩
  exact basisNhd_subset_connectedComponent_small C ρ₀ hε₁ hε₁10 hWide₁ hδ hδ_lt_ε₁ hρmem

/-- Existence of some lift in the ambient basis neighborhood at time `t`. -/
def LiftInBasisNhd (σ τ : StabilityCondition C) (ε : ℝ) (t : unitInterval) : Prop :=
  ∃ ρ : StabilityCondition C,
    ρ.Z = linearInterpolationZ C σ τ t ∧
    ρ ∈ basisNhd C σ ε

/-- Time `0` admits the obvious lift `σ`. -/
theorem liftInBasisNhd_zero (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    LiftInBasisNhd C σ τ ε 0 := by
  refine ⟨σ, ?_, basisNhd_self C σ hε hε8⟩
  simpa using linearInterpolationZ_zero C σ τ

/-- Time `1` admits the obvious lift `τ`. -/
theorem liftInBasisNhd_one (σ τ : StabilityCondition C)
    {ε : ℝ} (hτ : τ ∈ basisNhd C σ ε) :
    LiftInBasisNhd C σ τ ε 1 := by
  refine ⟨τ, ?_, hτ⟩
  simpa using linearInterpolationZ_one C σ τ

/-- Local continuation preserves ambient basis-neighborhood liftability. -/
theorem liftInBasisNhd_local (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε)
    {t : unitInterval} (ht : LiftInBasisNhd C σ τ ε t) :
    ∃ η : ℝ, 0 < η ∧
      ∀ ⦃s : unitInterval⦄, |(s : ℝ) - t| < η → LiftInBasisNhd C σ τ ε s := by
  rcases ht with ⟨ρ₀, hρ₀Z, hρ₀mem⟩
  obtain ⟨η, hη, hloc⟩ :=
    exists_local_lift_sameComponent_in_basisNhd C σ τ ρ₀ hε hε8 hτ hρ₀mem hρ₀Z
  refine ⟨η, hη, ?_⟩
  intro s hs
  rcases hloc hs with ⟨ρ, hρZ, hρmem, _⟩
  exact ⟨ρ, hρZ, hρmem⟩

/-- The times admitting some ambient basis-neighborhood lift form an open subset of `unitInterval`.
-/
theorem isOpen_liftInBasisNhd (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε) :
    IsOpen {t : unitInterval | LiftInBasisNhd C σ τ ε t} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨η, hη, hloc⟩ := liftInBasisNhd_local C σ τ hε hε8 hτ ht
  refine mem_nhds_iff.mpr ?_
  refine ⟨{s : unitInterval | |(s : ℝ) - t| < η}, ?_, ?_, ?_⟩
  · intro s hs
    exact hloc hs
  · have hcont : Continuous fun s : unitInterval => |(s : ℝ) - t| := by
      exact continuous_abs.comp (continuous_subtype_val.sub continuous_const)
    simpa using isOpen_lt hcont continuous_const
  · simpa using hη

/-- The set of times whose interpolated central charge admits a lift inside the fixed ambient
`basisNhd C σ ε`. -/
def liftInBasisNhdSet (σ τ : StabilityCondition C) (ε : ℝ) : Set unitInterval :=
  {t | LiftInBasisNhd C σ τ ε t}

@[simp] theorem mem_liftInBasisNhdSet_iff (σ τ : StabilityCondition C) (ε : ℝ)
    (t : unitInterval) :
    t ∈ liftInBasisNhdSet C σ τ ε ↔ LiftInBasisNhd C σ τ ε t := Iff.rfl

/-- The liftable-times set is open in `unitInterval`. -/
theorem isOpen_liftInBasisNhdSet (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε) :
    IsOpen (liftInBasisNhdSet C σ τ ε) := by
  simpa [liftInBasisNhdSet] using isOpen_liftInBasisNhd C σ τ hε hε8 hτ

/-- Time `0` belongs to the liftable-times set. -/
theorem zero_mem_liftInBasisNhdSet (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    (0 : unitInterval) ∈ liftInBasisNhdSet C σ τ ε := by
  simpa [liftInBasisNhdSet] using liftInBasisNhd_zero C σ τ hε hε8

/-- Time `1` belongs to the liftable-times set. -/
theorem one_mem_liftInBasisNhdSet (σ τ : StabilityCondition C)
    {ε : ℝ} (hτ : τ ∈ basisNhd C σ ε) :
    (1 : unitInterval) ∈ liftInBasisNhdSet C σ τ ε := by
  simpa [liftInBasisNhdSet] using liftInBasisNhd_one C σ τ hτ

/-- The globalization gap for Bridgeland's §7 argument: the liftable-times set is stable under
taking closure in `unitInterval`. Once this is shown, preconnectedness of `unitInterval`
forces it to be all of `unitInterval`. -/
theorem closure_liftInBasisNhdSet_subset (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε) :
    closure (liftInBasisNhdSet C σ τ ε) ⊆ liftInBasisNhdSet C σ τ ε := by
  sorry

/-- **Local connectedness of `Stab(D)`**: every basis neighbourhood is contained in
the topological connected component of its centre.

The only remaining input is the closure stability of the liftable-times set. Since that set is
open, nonempty, and contains its closure inside the preconnected space `unitInterval`, it must
be all of `unitInterval`. -/
theorem exists_lift_in_basisNhd_along_linearInterpolation (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε) :
    ∀ t : unitInterval, ∃ ρ : StabilityCondition C,
      ρ.Z = linearInterpolationZ C σ τ t ∧
      ρ ∈ basisNhd C σ ε := by
  have hOpen : IsOpen (liftInBasisNhdSet C σ τ ε) :=
    isOpen_liftInBasisNhdSet C σ τ hε hε8 hτ
  have hZero : ((Set.univ : Set unitInterval) ∩ liftInBasisNhdSet C σ τ ε).Nonempty := by
    refine ⟨0, ?_, zero_mem_liftInBasisNhdSet C σ τ hε hε8⟩
    simp
  have hSubset : (Set.univ : Set unitInterval) ⊆ liftInBasisNhdSet C σ τ ε := by
    exact isPreconnected_univ.subset_of_closure_inter_subset hOpen hZero <| by
      intro t ht
      exact closure_liftInBasisNhdSet_subset C σ τ hε hε8 hτ ht.1
  intro t
  simpa [liftInBasisNhdSet] using
    (hSubset (show t ∈ (Set.univ : Set unitInterval) by trivial))

/-- **Local connectedness of `Stab(D)`**: every basis neighbourhood is contained in
the topological connected component of its centre.

Once ambient lifts exist for every time along the straight-line charge interpolation, the local
continuation theorem shows that the connected-component label is locally constant in `t`; since
`unitInterval` is preconnected, it must be constant. -/
theorem exists_global_lift_sameComponent_in_basisNhd (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hτ : τ ∈ basisNhd C σ ε) :
    ∀ t : unitInterval, ∃ ρ : StabilityCondition C,
      ρ.Z = linearInterpolationZ C σ τ t ∧
      ρ ∈ basisNhd C σ ε ∧
      ConnectedComponents.mk ρ = ConnectedComponents.mk σ := by
  have hLift :=
    exists_lift_in_basisNhd_along_linearInterpolation C σ τ hε hε8 hτ
  let γ : unitInterval → StabilityCondition C := fun t => Classical.choose (hLift t)
  have hγZ : ∀ t : unitInterval, (γ t).Z = linearInterpolationZ C σ τ t := by
    intro t
    exact (Classical.choose_spec (hLift t)).1
  have hγmem : ∀ t : unitInterval, γ t ∈ basisNhd C σ ε := by
    intro t
    exact (Classical.choose_spec (hLift t)).2
  have hγ0 : γ 0 = σ := by
    apply StabilityCondition.eq_of_same_Z_of_mem_basisNhd C σ hε hε8 (hγmem 0)
      (basisNhd_self C σ hε hε8)
    simpa using (hγZ 0).trans (linearInterpolationZ_zero C σ τ)
  let compLabel : unitInterval → ConnectedComponents (StabilityCondition C) :=
    fun t => ConnectedComponents.mk (γ t)
  have hcompLoc : IsLocallyConstant compLabel := by
    rw [IsLocallyConstant.iff_exists_open]
    intro t
    obtain ⟨η, hη, hloc⟩ :=
      exists_local_lift_sameComponent_in_basisNhd C σ τ (γ t) hε hε8 hτ (hγmem t) (hγZ t)
    refine ⟨{s : unitInterval | |(s : ℝ) - t| < η}, ?_, ?_, ?_⟩
    · have hcont : Continuous fun s : unitInterval => |(s : ℝ) - t| := by
        exact continuous_abs.comp (continuous_subtype_val.sub continuous_const)
      simpa using isOpen_lt hcont continuous_const
    · simpa using hη
    · intro s hs
      rcases hloc hs with ⟨ρ, hρZ, hρmem, hρcc⟩
      have hγs_eq : γ s = ρ := by
        apply StabilityCondition.eq_of_same_Z_of_mem_basisNhd C σ hε hε8 (hγmem s) hρmem
        rw [hγZ s, hρZ]
      dsimp [compLabel]
      simpa [hγs_eq] using hρcc
  have hcompConst :
      ∀ t : unitInterval, compLabel t = compLabel 0 := by
    intro t
    exact hcompLoc.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
  intro t
  refine ⟨γ t, hγZ t, hγmem t, ?_⟩
  calc
    ConnectedComponents.mk (γ t) = ConnectedComponents.mk (γ 0) := hcompConst t
    _ = ConnectedComponents.mk σ := by simpa [hγ0]

/-- **Local connectedness of `Stab(D)`**: every basis neighbourhood is contained in
the topological connected component of its centre. -/
theorem basisNhd_subset_connectedComponent (σ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    basisNhd C σ ε ⊆ {τ | ConnectedComponents.mk τ = ConnectedComponents.mk σ} := by
  intro τ hτ
  obtain ⟨ρ, hρZ, hρmem, hρcc⟩ :=
    exists_global_lift_sameComponent_in_basisNhd C σ τ hε hε8 hτ 1
  have hρ_eq_τ : ρ = τ := by
    apply StabilityCondition.eq_of_same_Z_of_mem_basisNhd C σ hε hε8 hρmem hτ
    simpa using hρZ.trans (linearInterpolationZ_one C σ τ)
  simpa [hρ_eq_τ] using hρcc

/-- **Lemma 6.2**: On a connected component, seminorms are equivalent (domination). -/
theorem stabSeminorm_dominated_of_connected (σ τ : StabilityCondition C)
    (h : ConnectedComponents.mk σ = ConnectedComponents.mk τ) :
    ∃ K : ENNReal, K ≠ ⊤ ∧
      ∀ (f : K₀ C →+ ℂ), stabSeminorm C σ f ≤ K * stabSeminorm C τ f := by
  let P : StabilityCondition C → StabilityCondition C → Prop := fun ρ₁ ρ₂ =>
    ∃ K : ENNReal, K ≠ ⊤ ∧
      ∀ f : K₀ C →+ ℂ, stabSeminorm C ρ₁ f ≤ K * stabSeminorm C ρ₂ f
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
      linarith [hε₀10]
    have hU_mem : basisNhd C x δ ∈ 𝓝 x := by
      apply IsOpen.mem_nhds
      · change TopologicalSpace.GenerateOpen
            { U | ∃ (σ : StabilityCondition C) (ε : ℝ),
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
    AddSubgroup (K₀ C →+ ℂ) :=
  finiteSeminormSubgroup C (componentRep C cc)

/-- The seminorm balls in `V(Σ)` coming from the representative `σ₀ ∈ Σ`. -/
def componentSeminormBall (cc : ConnectedComponents (StabilityCondition C))
    (W : componentSeminormSubgroup C cc) (r : ℝ) :
    Set (componentSeminormSubgroup C cc) :=
  {F | stabSeminorm C (componentRep C cc) (↑F - ↑W) < ENNReal.ofReal r}

/-- The basis of seminorm balls defining the topology on `V(Σ)`. -/
def componentSeminormBasis (cc : ConnectedComponents (StabilityCondition C)) :
    Set (Set (componentSeminormSubgroup C cc)) :=
  {S | ∃ (W : componentSeminormSubgroup C cc) (r : ℝ), 0 < r ∧
    S = componentSeminormBall C cc W r}

/-- The linear topology on `V(Σ)` generated by seminorm balls for one representative. -/
abbrev componentSeminormTopology (cc : ConnectedComponents (StabilityCondition C)) :
    TopologicalSpace (componentSeminormSubgroup C cc) :=
  TopologicalSpace.generateFrom (componentSeminormBasis C cc)

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

/-! ### Theorem 1.2 -/

theorem bridgeland_theorem_1_2' :
    bridgelandTheorem_1_2 C := by
  intro cc
  let σ₀ := componentRep C cc
  let V := componentSeminormSubgroup C cc
  let comp := componentStabilityCondition C cc
  let Zmap : comp → V := componentZMap C cc
  letI : TopologicalSpace V := componentSeminormTopology C cc
  refine ⟨V, componentSeminormTopology C cc, ?_, ?_⟩
  · intro σ hσ
    exact componentZ_mem C cc σ hσ
  · rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
    intro ⟨σ, hσ⟩
    obtain ⟨ε₀, hε₀, hε₀8, hWide⟩ := σ.exists_epsilon0 C
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
        change @Continuous comp ↥V instTopologicalSpaceSubtype
          (componentSeminormTopology C cc) Zmap
        rw [componentSeminormTopology, continuous_generateFrom_iff]
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
            _ = ENNReal.ofReal K_rev.toReal * ENNReal.ofReal d := by simpa [hK_eq]
            _ = ENNReal.ofReal (K_rev.toReal * d) := by
                simpa using
                  (ENNReal.ofReal_mul ENNReal.toReal_nonneg (a := K_rev.toReal) (b := d)).symm
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

end CategoryTheory.Triangulated
