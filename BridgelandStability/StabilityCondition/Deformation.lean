/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.Theorem
public import BridgelandStability.StabilityCondition.Topology
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Connected.Clopen

/-!
# Bridgeland's Theorem 1.2: Central charge is a local homeomorphism

Following Bridgeland's proof:
- **Lemma 6.2** (`stabSeminorm_dominated_of_connected`): seminorm equivalence on V(Σ).
- **Prop 6.3**: Z continuous into the seminorm topology.
- **Lemma 6.4** (`eq_of_same_Z_near`): Z locally injective.
- **Theorem 7.1** (`exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin`): Z locally surjective.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

set_option linter.style.longFile 0

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Topology
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- A small deformation of the central charge lifts directly to a point of `basisNhd C σ ε`.

This is the form used in the topology arguments for Theorem 1.2: it gives both the
prescribed central charge and the exact `basisNhd` control, so no radius enlargement
is needed after applying the deformation theorem. -/
theorem StabilityCondition.exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    ∃ τ : StabilityCondition C, τ.Z = W ∧ τ ∈ basisNhd C σ ε := by
  obtain ⟨τ, hτZ, hτd⟩ :=
    σ.exists_eq_Z_and_slicingDist_lt_of_stabSeminorm_lt_sin C W hW ε₀ hε₀ hε₀10
      hWide ε hε hεε₀ hsin
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
    (by positivity) (by grind) (by grind)

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

theorem stabSeminorm_smul_complex (σ : StabilityCondition C) (U : K₀ C →+ ℂ) (t : ℂ) :
    stabSeminorm C σ (t • U) = ENNReal.ofReal ‖t‖ * stabSeminorm C σ U := by
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
  rw [AddMonoidHom.smul_apply, norm_smul, div_eq_mul_inv,
    ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity)]
  simp [mul_assoc]

theorem stabSeminorm_add_le (σ : StabilityCondition C) (U V : K₀ C →+ ℂ) :
    stabSeminorm C σ (U + V) ≤ stabSeminorm C σ U + stabSeminorm C σ V := by
  apply iSup_le
  intro E
  apply iSup_le
  intro φ
  apply iSup_le
  intro hP
  apply iSup_le
  intro hE
  calc ENNReal.ofReal (‖(U + V) (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)
      ≤ ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖ +
          ‖V (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) := by
        apply ENNReal.ofReal_le_ofReal
        rw [AddMonoidHom.add_apply, ← add_div]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    _ = ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) +
        ENNReal.ofReal (‖V (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) := by
        exact ENNReal.ofReal_add (div_nonneg (norm_nonneg _) (norm_nonneg _))
          (div_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ stabSeminorm C σ U + stabSeminorm C σ V := by
        exact add_le_add
          (le_iSup_of_le E (le_iSup_of_le φ (le_iSup_of_le hP (le_iSup_of_le hE le_rfl))))
          (le_iSup_of_le E (le_iSup_of_le φ (le_iSup_of_le hP (le_iSup_of_le hE le_rfl))))

theorem stabSeminorm_neg (σ : StabilityCondition C) (U : K₀ C →+ ℂ) :
    stabSeminorm C σ (-U) = stabSeminorm C σ U := by
  simp [stabSeminorm, AddMonoidHom.neg_apply, norm_neg]

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
          mul_lt_mul_of_pos_right hMZ_lt_sin (by grind)
      _ ≤ (Real.pi * ε) * 2 := by
          have hcos_le : c ≤ 1 := Real.cos_le_one _
          have : 1 + c ≤ 2 := by linarith
          exact mul_le_mul hsin_le this (by grind) (by nlinarith [Real.pi_pos])
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
      ((ENNReal.ofReal_lt_ofReal_iff (by grind)).mpr hbound_lt_cos)
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
          simp [one_div, mul_comm]

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
    refine lt_min (by grind) ?_
    refine lt_min ?_ ?_
    · exact div_pos hgapZ (by positivity)
    · linarith
  have hδ_lt : δ < 1 / 8 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_left _ _) (by grind)
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
    exact σ.exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin C (W t) (hW1 t)
      ε₀ hε₀ hε₀10 hWide ε hε hεε₀ (hWt t)
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
        (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (by grind)
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
        ρ₀.exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin C (W s) hWclose1
          ε₁ hε₁ hε₁10 hWide₁ δ hδ hδ_lt_ε₁ hWclose
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
      source' := by simp [hγ0]
      target' := by simp [hγ1] }
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
    ρ₀.exists_eq_Z_and_mem_basisNhd_of_stabSeminorm_lt_sin C
      (linearInterpolationZ C σ τ s) hWclose1 ε₁ hε₁ hε₁10 hWide₁ δ hδ hδ_lt_ε₁ hWclose
  refine ⟨ρ, hρZ, hsubU hρmem, ?_⟩
  exact basisNhd_subset_connectedComponent_small C ρ₀ hε₁ hε₁10 hWide₁ hδ hδ_lt_ε₁ hρmem

end CategoryTheory.Triangulated
