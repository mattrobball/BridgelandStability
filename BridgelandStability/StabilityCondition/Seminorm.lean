/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.Basic

/-!
# Stability Seminorm

The generalized metric `slicingDist`, the stability seminorm `stabSeminorm`,
the finite seminorm subgroup, and sector bound / comparison lemmas.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex Real
open scoped ZeroObject ENNReal

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### Generalized metric and seminorm -/

/-- The Bridgeland generalized metric on slicings (blueprint A8). For slicings `s₁` and `s₂`,
this is the supremum over all nonzero objects `E` of
`max(|φ₁⁺(E) - φ₂⁺(E)|, |φ₁⁻(E) - φ₂⁻(E)|)`,
where `φᵢ±` are the intrinsic phase bounds (well-defined by HN filtration uniqueness).
Values lie in `[0, ∞]`. -/
def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)

/-- The Bridgeland generalized metric is zero on the diagonal: `d(P, P) = 0`. -/
theorem slicingDist_self (s : Slicing C) : slicingDist C s s = 0 := by
  simp [slicingDist, sub_self, abs_zero, max_self, ENNReal.ofReal_zero]

/-- The Bridgeland generalized metric is symmetric: `d(P, Q) = d(Q, P)`. -/
theorem slicingDist_symm (s₁ s₂ : Slicing C) :
    slicingDist C s₁ s₂ = slicingDist C s₂ s₁ := by
  simp only [slicingDist, abs_sub_comm]

/-- The Bridgeland generalized metric satisfies the triangle inequality. -/
theorem slicingDist_triangle (s₁ s₂ s₃ : Slicing C) :
    slicingDist C s₁ s₃ ≤ slicingDist C s₁ s₂ + slicingDist C s₂ s₃ := by
  apply iSup_le
  intro E
  apply iSup_le
  intro hE
  calc ENNReal.ofReal (max |s₁.phiPlus C E hE - s₃.phiPlus C E hE|
          |s₁.phiMinus C E hE - s₃.phiMinus C E hE|)
      ≤ ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
            |s₁.phiMinus C E hE - s₂.phiMinus C E hE|) +
        ENNReal.ofReal (max |s₂.phiPlus C E hE - s₃.phiPlus C E hE|
            |s₂.phiMinus C E hE - s₃.phiMinus C E hE|) := by
        rw [← ENNReal.ofReal_add (le_max_of_le_left (abs_nonneg _))
          (le_max_of_le_left (abs_nonneg _))]
        apply ENNReal.ofReal_le_ofReal
        have abs_tri : ∀ (a b c : ℝ), |a - c| ≤ |a - b| + |b - c| := fun a b c ↦ by
          calc |a - c| = |(a - b) + (b - c)| := by ring_nf
            _ ≤ |a - b| + |b - c| := abs_add_le _ _
        apply max_le
        · calc |s₁.phiPlus C E hE - s₃.phiPlus C E hE|
              ≤ |s₁.phiPlus C E hE - s₂.phiPlus C E hE| +
                |s₂.phiPlus C E hE - s₃.phiPlus C E hE| := abs_tri _ _ _
            _ ≤ max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                  |s₁.phiMinus C E hE - s₂.phiMinus C E hE| +
                max |s₂.phiPlus C E hE - s₃.phiPlus C E hE|
                  |s₂.phiMinus C E hE - s₃.phiMinus C E hE| :=
              add_le_add (le_max_left _ _) (le_max_left _ _)
        · calc |s₁.phiMinus C E hE - s₃.phiMinus C E hE|
              ≤ |s₁.phiMinus C E hE - s₂.phiMinus C E hE| +
                |s₂.phiMinus C E hE - s₃.phiMinus C E hE| := abs_tri _ _ _
            _ ≤ max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                  |s₁.phiMinus C E hE - s₂.phiMinus C E hE| +
                max |s₂.phiPlus C E hE - s₃.phiPlus C E hE|
                  |s₂.phiMinus C E hE - s₃.phiMinus C E hE| :=
              add_le_add (le_max_right _ _) (le_max_right _ _)
    _ ≤ slicingDist C s₁ s₂ + slicingDist C s₂ s₃ := by
        exact add_le_add (le_iSup_of_le E (le_iSup_of_le hE le_rfl))
          (le_iSup_of_le E (le_iSup_of_le hE le_rfl))

/-- If the slicing distance is less than `ε`, the intrinsic `φ⁺` values are within `ε`.
This is one direction of **Lemma 6.1**. -/
theorem phiPlus_sub_lt_of_slicingDist (s₁ s₂ : Slicing C) {E : C} (hE : ¬IsZero E)
    {ε : ℝ}
    (hd : slicingDist C s₁ s₂ < ENNReal.ofReal ε) :
    |s₁.phiPlus C E hE - s₂.phiPlus C E hE| < ε := by
  by_contra h
  push_neg at h
  have h1 : ENNReal.ofReal ε ≤ ENNReal.ofReal
      (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
           |s₁.phiMinus C E hE - s₂.phiMinus C E hE|) :=
    ENNReal.ofReal_le_ofReal (le_max_of_le_left h)
  have h2 : ENNReal.ofReal
      (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
           |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)
      ≤ slicingDist C s₁ s₂ := le_iSup_of_le E (le_iSup_of_le hE le_rfl)
  exact absurd hd (not_lt.mpr (h1.trans h2))

/-- If the slicing distance is less than `ε`, the intrinsic `φ⁻` values are within `ε`.
This is one direction of **Lemma 6.1**. -/
theorem phiMinus_sub_lt_of_slicingDist (s₁ s₂ : Slicing C) {E : C} (hE : ¬IsZero E)
    {ε : ℝ}
    (hd : slicingDist C s₁ s₂ < ENNReal.ofReal ε) :
    |s₁.phiMinus C E hE - s₂.phiMinus C E hE| < ε := by
  by_contra h
  push_neg at h
  have h1 : ENNReal.ofReal ε ≤ ENNReal.ofReal
      (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
           |s₁.phiMinus C E hE - s₂.phiMinus C E hE|) :=
    ENNReal.ofReal_le_ofReal (le_max_of_le_right h)
  have h2 : ENNReal.ofReal
      (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
           |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)
      ≤ slicingDist C s₁ s₂ := le_iSup_of_le E (le_iSup_of_le hE le_rfl)
  exact absurd hd (not_lt.mpr (h1.trans h2))

/-- **Lemma 6.1** (one direction). If the slicing distance `d(P, Q) < ε`, then every
`Q`-semistable object of phase `φ` has all `P`-HN phases in the interval `(φ - ε, φ + ε)`.
In terms of intrinsic phases: `|φ⁺_P(E) - φ| < ε` and `|φ⁻_P(E) - φ| < ε`. -/
theorem intervalProp_of_semistable_slicingDist (s₁ s₂ : Slicing C) {E : C} {φ : ℝ}
    (hE : ¬IsZero E) (hS : (s₂.P φ) E)
    {ε : ℝ}
    (hd : slicingDist C s₁ s₂ < ENNReal.ofReal ε) :
    s₁.phiPlus C E hE ∈ Set.Ioo (φ - ε) (φ + ε) ∧
    s₁.phiMinus C E hE ∈ Set.Ioo (φ - ε) (φ + ε) := by
  have ⟨hpP, hpM⟩ := s₂.phiPlus_eq_phiMinus_of_semistable C hS hE
  have hP := phiPlus_sub_lt_of_slicingDist C s₁ s₂ hE hd
  have hM := phiMinus_sub_lt_of_slicingDist C s₁ s₂ hE hd
  rw [hpP] at hP; rw [hpM] at hM
  rw [abs_lt] at hP hM
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The generalized metric is at most `ε` if both `φ⁺` and `φ⁻` differences are bounded
by `ε` for all nonzero objects. This is the "converse" direction of the phase-bound lemmas
`phiPlus_sub_lt_of_slicingDist` and `phiMinus_sub_lt_of_slicingDist`. -/
theorem slicingDist_le_of_phase_bounds (s₁ s₂ : Slicing C) {ε : ℝ}
    (hP : ∀ (E : C) (hE : ¬IsZero E),
      |s₁.phiPlus C E hE - s₂.phiPlus C E hE| ≤ ε)
    (hM : ∀ (E : C) (hE : ¬IsZero E),
      |s₁.phiMinus C E hE - s₂.phiMinus C E hE| ≤ ε) :
    slicingDist C s₁ s₂ ≤ ENNReal.ofReal ε := by
  apply iSup_le; intro E
  apply iSup_le; intro hE
  exact ENNReal.ofReal_le_ofReal (max_le (hP E hE) (hM E hE))

/-- The seminorm `‖U‖_σ` on `Hom_ℤ(K₀(D), ℂ)` (blueprint A9). For a stability condition
`σ = (Z, P)` and a group homomorphism `U : K₀(D) → ℂ`, this is
`sup { |U(E)| / |Z(E)| : E is σ-semistable and nonzero }`.
Values lie in `[0, ∞]`. -/
def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)

/-- The seminorm is nonneg: `stabSeminorm σ U ≥ 0`. This is trivially true since
`ℝ≥0∞` values are nonneg, but useful for API. -/
theorem stabSeminorm_nonneg (σ : StabilityCondition C) (U : K₀ C →+ ℂ) :
    0 ≤ stabSeminorm C σ U :=
  zero_le _

/-- The seminorm at zero is zero. -/
theorem stabSeminorm_zero (σ : StabilityCondition C) :
    stabSeminorm C σ 0 = 0 := by
  simp [stabSeminorm, AddMonoidHom.zero_apply, norm_zero, zero_div,
    ENNReal.ofReal_zero]

/-- The subspace `V(σ)` of group homomorphisms with finite seminorm (blueprint Node 6.3a).
This is an `AddSubgroup` of `K₀ C →+ ℂ` consisting of those `U` for which
`‖U‖_σ < ∞`. On a connected component of `Stab(D)`, this subspace is independent
of the chosen `σ` (by Lemma 6.2). -/
def finiteSeminormSubgroup (σ : StabilityCondition C) : AddSubgroup (K₀ C →+ ℂ) where
  carrier := {U | stabSeminorm C σ U < ⊤}
  add_mem' {U V} hU hV := by
    change stabSeminorm C σ (U + V) < ⊤
    have hsub : stabSeminorm C σ (U + V) ≤ stabSeminorm C σ U + stabSeminorm C σ V := by
      apply iSup_le; intro E; apply iSup_le; intro φ
      apply iSup_le; intro hP; apply iSup_le; intro hE
      calc ENNReal.ofReal (‖(U + V) (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)
          ≤ ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖ +
              ‖V (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) := by
            apply ENNReal.ofReal_le_ofReal
            rw [AddMonoidHom.add_apply, ← add_div]
            exact div_le_div_of_nonneg_right
              (norm_add_le _ _) (norm_nonneg _)
        _ = ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) +
            ENNReal.ofReal (‖V (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖) :=
          ENNReal.ofReal_add (div_nonneg (norm_nonneg _) (norm_nonneg _))
            (div_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ stabSeminorm C σ U + stabSeminorm C σ V :=
          add_le_add (le_iSup_of_le E (le_iSup_of_le φ (le_iSup_of_le hP
            (le_iSup_of_le hE le_rfl))))
            (le_iSup_of_le E (le_iSup_of_le φ (le_iSup_of_le hP
              (le_iSup_of_le hE le_rfl))))
    exact lt_of_le_of_lt hsub (ENNReal.add_lt_top.mpr ⟨hU, hV⟩)
  zero_mem' := by change stabSeminorm C σ 0 < ⊤; rw [stabSeminorm_zero]; exact ENNReal.zero_lt_top
  neg_mem' {U} hU := by
    change stabSeminorm C σ (-U) < ⊤
    convert hU using 1
    simp [stabSeminorm, AddMonoidHom.neg_apply, norm_neg]

/-! ### Sector bound (Lemma 6.2 core) -/

/-- **Sector bound (Lemma 6.2 core)**. For a stability condition `σ = (Z, P)` and a group
homomorphism `U : K₀ C →+ ℂ`, if every semistable factor satisfies
`‖U([A])‖ ≤ M · ‖Z([A])‖`, then the bound extends to any object `E` with narrow HN width:
`‖U([E])‖ ≤ (M / cos(πη/2)) · ‖Z([E])‖`, where `η` bounds the HN phase width.

The proof decomposes `E` via its HN filtration (a PostnikovTower with phase data),
applies K₀ additivity, the pointwise seminorm bound on factors, and the
sector estimate `norm_sum_exp_ge_cos_mul_sum`. -/
theorem sector_bound (σ : StabilityCondition C) (U : K₀ C →+ ℂ)
    {E : C} (F : HNFiltration C σ.slicing.P E) (hn : 0 < F.n)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1)
    (hwidth : F.φ ⟨0, hn⟩ - F.φ ⟨F.n - 1, by omega⟩ ≤ η)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ (A : C) (φ : ℝ), σ.slicing.P φ A → ¬IsZero A →
      ‖U (K₀.of C A)‖ ≤ M * ‖σ.Z (K₀.of C A)‖) :
    ‖U (K₀.of C E)‖ ≤
      M / Real.cos (Real.pi * η / 2) * ‖σ.Z (K₀.of C E)‖ := by
  set P := F.toPostnikovTower
  -- K₀ decomposition
  have hK₀ : K₀.of C E = ∑ i : Fin F.n, K₀.of C (P.factor i) :=
    K₀.of_postnikovTower_eq_sum C P
  -- U and Z decompose over factors
  have hUE : U (K₀.of C E) = ∑ i : Fin F.n, U (K₀.of C (P.factor i)) := by
    rw [hK₀, map_sum]
  have hZE : σ.Z (K₀.of C E) = ∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i)) := by
    rw [hK₀, map_sum]
  -- Seminorm bound on each factor
  have hMi : ∀ i : Fin F.n,
      ‖U (K₀.of C (P.factor i))‖ ≤ M * ‖σ.Z (K₀.of C (P.factor i))‖ := by
    intro i
    by_cases hi : IsZero (P.factor i)
    · have h0 := K₀.of_isZero C hi; simp [h0]
    · exact hM _ _ (F.semistable i) hi
  -- Z decomposition: Z(factor i) = ‖Z(factor i)‖ * exp(iπφᵢ)
  have hZi : ∀ i : Fin F.n,
      σ.Z (K₀.of C (P.factor i)) =
      ↑(‖σ.Z (K₀.of C (P.factor i))‖) * exp (↑(Real.pi * F.φ i) * I) := by
    intro i
    by_cases hi : IsZero (P.factor i)
    · have h0 := K₀.of_isZero C hi; simp [h0]
    · obtain ⟨m, hm, hmZ⟩ := σ.compat (F.φ i) (P.factor i) (F.semistable i) hi
      rw [hmZ]; congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  -- Phase containment
  set α := Real.pi * F.φ ⟨F.n - 1, by omega⟩
  set w := Real.pi * η
  have hwπ : w < Real.pi := by
    change Real.pi * η < Real.pi; nlinarith [Real.pi_pos]
  have hw0 : 0 ≤ w := by change 0 ≤ Real.pi * η; positivity
  have hθ : ∀ i : Fin F.n, Real.pi * F.φ i ∈ Set.Icc α (α + w) := by
    intro i; simp only [Set.mem_Icc, α, w]; constructor
    · exact mul_le_mul_of_nonneg_left
        (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))) (le_of_lt Real.pi_pos)
    · calc Real.pi * F.φ i
          ≤ Real.pi * F.φ ⟨0, hn⟩ := mul_le_mul_of_nonneg_left
            (F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) (le_of_lt Real.pi_pos)
        _ ≤ Real.pi * F.φ ⟨F.n - 1, by omega⟩ + Real.pi * η := by nlinarith
  -- Sector estimate: cos(πη/2) * ∑ ‖Z(fi)‖ ≤ ‖Z(E)‖
  have hcos_pos : 0 < Real.cos (w / 2) := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> [linarith; linarith]
  have hsector : Real.cos (w / 2) * ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖ ≤
      ‖σ.Z (K₀.of C E)‖ := by
    calc Real.cos (w / 2) * ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖
        ≤ ‖∑ i : Fin F.n,
            ↑(‖σ.Z (K₀.of C (P.factor i))‖) * exp (↑(Real.pi * F.φ i) * I)‖ :=
          norm_sum_exp_ge_cos_mul_sum (fun i _ ↦ norm_nonneg _) hw0 hwπ (fun i _ ↦ hθ i)
      _ = ‖∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i))‖ := by
          congr 1; exact Finset.sum_congr rfl (fun i _ ↦ (hZi i).symm)
      _ = ‖σ.Z (K₀.of C E)‖ := by rw [← hZE]
  -- Combine
  have hsum_bound : ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖ ≤
      ‖σ.Z (K₀.of C E)‖ / Real.cos (w / 2) := by
    rw [le_div_iff₀ hcos_pos, mul_comm]; exact hsector
  calc ‖U (K₀.of C E)‖
      = ‖∑ i : Fin F.n, U (K₀.of C (P.factor i))‖ := by rw [hUE]
    _ ≤ ∑ i : Fin F.n, ‖U (K₀.of C (P.factor i))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin F.n, M * ‖σ.Z (K₀.of C (P.factor i))‖ :=
        Finset.sum_le_sum (fun i _ ↦ hMi i)
    _ = M * ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ M * (‖σ.Z (K₀.of C E)‖ / Real.cos (w / 2)) :=
        mul_le_mul_of_nonneg_left hsum_bound hM0
    _ = M / Real.cos (Real.pi * η / 2) * ‖σ.Z (K₀.of C E)‖ := by
        change M * (‖σ.Z (K₀.of C E)‖ / Real.cos (Real.pi * η / 2)) =
          M / Real.cos (Real.pi * η / 2) * ‖σ.Z (K₀.of C E)‖
        ring

/-- Sector bound using intrinsic phase width `phiPlus - phiMinus`. -/
theorem sector_bound' (σ : StabilityCondition C) (U : K₀ C →+ ℂ)
    {E : C} (hE : ¬IsZero E) {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1)
    (hwidth : σ.slicing.phiPlus C E hE - σ.slicing.phiMinus C E hE ≤ η)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ (A : C) (φ : ℝ), σ.slicing.P φ A → ¬IsZero A →
      ‖U (K₀.of C A)‖ ≤ M * ‖σ.Z (K₀.of C A)‖) :
    ‖U (K₀.of C E)‖ ≤
      M / Real.cos (Real.pi * η / 2) * ‖σ.Z (K₀.of C E)‖ := by
  obtain ⟨F, hn, hP, hM'⟩ := σ.slicing.exists_HN_intrinsic_width C hE
  exact sector_bound C σ U F hn hη hη1 (by rw [hP, hM']; exact hwidth) hM0 hM

/-- **Node 6.2d**: For a `τ`-semistable nonzero object `E` of phase `φ` with
`d(σ, τ) < ε < 1/2`, the `σ`-HN width of `E` is less than `2ε`, so the sector
bound applies. Combined with the seminorm bound on `W - Z`, this controls
`‖Z([E])‖` by `‖W([E])‖` (where `W = τ.Z` and `Z = σ.Z`). -/
theorem norm_Z_le_of_tau_semistable (σ τ : StabilityCondition C)
    {E : C} {φ : ℝ} (hE : ¬IsZero E) (hS : τ.slicing.P φ E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM_bound : ∀ (A : C) (ψ : ℝ), σ.slicing.P ψ A → ¬IsZero A →
      ‖(τ.Z - σ.Z) (K₀.of C A)‖ ≤ M * ‖σ.Z (K₀.of C A)‖) :
    (1 - M / Real.cos (Real.pi * ε)) * ‖σ.Z (K₀.of C E)‖ ≤
      ‖τ.Z (K₀.of C E)‖ := by
  -- The σ-HN width of E is < 2ε (since E is τ-semistable of phase φ and d < ε)
  have hbounds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hS hd
  have hwidth : σ.slicing.phiPlus C E hE - σ.slicing.phiMinus C E hE ≤ 2 * ε := by
    have := hbounds.1; have := hbounds.2
    rw [Set.mem_Ioo] at *; linarith
  -- Apply sector bound with η = 2ε to U = τ.Z - σ.Z
  have h2ε : 2 * ε < 1 := by linarith
  have hcos_eq : Real.pi * (2 * ε) / 2 = Real.pi * ε := by ring
  have hsector := sector_bound' C σ (τ.Z - σ.Z) hE (by linarith) h2ε hwidth hM0 hM_bound
  rw [hcos_eq] at hsector
  -- ‖(τ.Z - σ.Z)([E])‖ ≤ M / cos(πε) * ‖Z([E])‖
  -- By reverse triangle inequality:
  -- ‖τ.Z([E])‖ ≥ ‖Z([E])‖ - ‖(τ.Z - σ.Z)([E])‖
  --            ≥ ‖Z([E])‖ - M/cos(πε) * ‖Z([E])‖
  --            = (1 - M/cos(πε)) * ‖Z([E])‖
  have hkey : ‖(τ.Z - σ.Z) (K₀.of C E)‖ ≤
      M / Real.cos (Real.pi * ε) * ‖σ.Z (K₀.of C E)‖ := hsector
  calc (1 - M / Real.cos (Real.pi * ε)) * ‖σ.Z (K₀.of C E)‖
      = ‖σ.Z (K₀.of C E)‖ - M / Real.cos (Real.pi * ε) * ‖σ.Z (K₀.of C E)‖ := by ring
    _ ≤ ‖σ.Z (K₀.of C E)‖ - ‖(τ.Z - σ.Z) (K₀.of C E)‖ := by linarith
    _ ≤ ‖τ.Z (K₀.of C E)‖ := by
        have : ‖σ.Z (K₀.of C E)‖ ≤ ‖τ.Z (K₀.of C E)‖ +
          ‖(τ.Z - σ.Z) (K₀.of C E)‖ := by
          calc ‖σ.Z (K₀.of C E)‖
              = ‖τ.Z (K₀.of C E) - (τ.Z - σ.Z) (K₀.of C E)‖ := by
                congr 1; simp [AddMonoidHom.sub_apply]
            _ ≤ ‖τ.Z (K₀.of C E)‖ + ‖(τ.Z - σ.Z) (K₀.of C E)‖ :=
                norm_sub_le _ _
        linarith

/-! ### Seminorm comparison (Lemma 6.2 consequence) -/

/-- For σ-semistable nonzero `A`, the ratio `‖U(A)‖/‖Z(A)‖` is bounded by the seminorm. -/
lemma stabSeminorm_bound_real (σ : StabilityCondition C) (U : K₀ C →+ ℂ)
    (hfin : stabSeminorm C σ U ≠ ⊤)
    {A : C} {ψ : ℝ} (hP : σ.slicing.P ψ A) (hA : ¬IsZero A) :
    ‖U (K₀.of C A)‖ ≤ (stabSeminorm C σ U).toReal * ‖σ.Z (K₀.of C A)‖ := by
  obtain ⟨m, hm, hmZ⟩ := σ.compat ψ A hP hA
  have hZ_pos : (0 : ℝ) < ‖σ.Z (K₀.of C A)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  have h1 : ENNReal.ofReal (‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖) ≤
      stabSeminorm C σ U :=
    le_iSup_of_le A (le_iSup_of_le ψ (le_iSup_of_le hP (le_iSup_of_le hA le_rfl)))
  have hratio : ‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖ ≤
      (stabSeminorm C σ U).toReal := by
    calc ‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖
        = (ENNReal.ofReal (‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖)).toReal :=
          (ENNReal.toReal_ofReal (div_nonneg (norm_nonneg _) (norm_nonneg _))).symm
      _ ≤ (stabSeminorm C σ U).toReal := ENNReal.toReal_mono hfin h1
  calc ‖U (K₀.of C A)‖
      = ‖U (K₀.of C A)‖ / ‖σ.Z (K₀.of C A)‖ * ‖σ.Z (K₀.of C A)‖ := by
        rw [div_mul_cancel₀ _ (ne_of_gt hZ_pos)]
    _ ≤ (stabSeminorm C σ U).toReal * ‖σ.Z (K₀.of C A)‖ :=
        mul_le_mul_of_nonneg_right hratio (le_of_lt hZ_pos)

/-- **Seminorm comparison for same central charge** (**Lemma 6.2** consequence).
If `σ` and `τ` have the same central charge and `d(P, Q) < ε < 1/2`, then
`‖U‖_τ < ⊤` whenever `‖U‖_σ < ⊤`. This shows `V(σ) ⊆ V(τ)`, and by symmetry
`V(σ) = V(τ)` for nearby stability conditions with the same central charge. -/
theorem stabSeminorm_lt_top_of_same_Z (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    (U : K₀ C →+ ℂ) (hU : stabSeminorm C σ U < ⊤) :
    stabSeminorm C τ U < ⊤ := by
  have hU_ne : stabSeminorm C σ U ≠ ⊤ := ne_top_of_lt hU
  set M := (stabSeminorm C σ U).toReal with hM_def
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  -- M bounds ‖U(A)‖ for each σ-semistable nonzero A
  have hM_bound : ∀ (A : C) (ψ : ℝ), σ.slicing.P ψ A → ¬IsZero A →
      ‖U (K₀.of C A)‖ ≤ M * ‖σ.Z (K₀.of C A)‖ :=
    fun A ψ hP hA ↦ stabSeminorm_bound_real C σ U hU_ne hP hA
  -- cos(πε) > 0 since ε < 1/2
  have hcos_pos : 0 < Real.cos (Real.pi * ε) := by
    apply Real.cos_pos_of_mem_Ioo; constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  -- Bound each term in the τ-seminorm iSup by M / cos(πε)
  suffices h : stabSeminorm C τ U ≤
      ENNReal.ofReal (M / Real.cos (Real.pi * ε)) from
    lt_of_le_of_lt h ENNReal.ofReal_lt_top
  apply iSup_le; intro E; apply iSup_le; intro φ
  apply iSup_le; intro hP; apply iSup_le; intro hE
  apply ENNReal.ofReal_le_ofReal
  -- Goal: ‖U(E)‖ / ‖τ.Z(E)‖ ≤ M / cos(πε)
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hP hE
  have hZ_pos : (0 : ℝ) < ‖τ.Z (K₀.of C E)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  -- Sector bound: ‖U(E)‖ ≤ (M / cos(πε)) * ‖τ.Z(E)‖
  have hbounds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hP hd
  have hwidth : σ.slicing.phiPlus C E hE - σ.slicing.phiMinus C E hE ≤ 2 * ε := by
    have := hbounds.1; have := hbounds.2; rw [Set.mem_Ioo] at *; linarith
  have h2ε : 2 * ε < 1 := by linarith
  have hcos_eq : Real.pi * (2 * ε) / 2 = Real.pi * ε := by ring
  have hsector := sector_bound' C σ U hE (by linarith : (0 : ℝ) ≤ 2 * ε) h2ε hwidth hM0
    hM_bound
  rw [hcos_eq, hZ] at hsector
  calc ‖U (K₀.of C E)‖ / ‖τ.Z (K₀.of C E)‖
      ≤ M / Real.cos (Real.pi * ε) * ‖τ.Z (K₀.of C E)‖ / ‖τ.Z (K₀.of C E)‖ :=
        div_le_div_of_nonneg_right hsector (le_of_lt hZ_pos)
    _ = M / Real.cos (Real.pi * ε) :=
        mul_div_cancel_right₀ _ (ne_of_gt hZ_pos)

/-- **Proposition 6.3 (same Z case)**. If `σ` and `τ` have the same central charge
and `d(P, Q) < ε < 1/2`, then the finite seminorm subgroups agree: `V(σ) = V(τ)`.
This is the key ingredient for showing `V(Σ)` is well-defined on connected components. -/
theorem finiteSeminormSubgroup_eq_of_same_Z (σ τ : StabilityCondition C)
    (hZ : σ.Z = τ.Z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε) :
    finiteSeminormSubgroup C σ = finiteSeminormSubgroup C τ := by
  ext U; simp only [finiteSeminormSubgroup, AddSubgroup.mem_mk]
  constructor
  · exact stabSeminorm_lt_top_of_same_Z C σ τ hZ hε hε1 hd U
  · rw [slicingDist_symm] at hd
    exact stabSeminorm_lt_top_of_same_Z C τ σ hZ.symm hε hε1 hd U

/-- **General Lemma 6.2** (explicit seminorm bound). If `d(P, Q) < ε < 1/2`
and `‖τ.Z - σ.Z‖_σ < cos(πε)`, then for any `U` with finite `σ`-seminorm, the
`τ`-seminorm is bounded: `‖U‖_τ ≤ ‖U‖_σ / (cos(πε) - ‖τ.Z - σ.Z‖_σ)`.

This is the quantitative core of the seminorm comparison, used for both
`stabSeminorm_lt_top_of_near` and the reverse direction of **Proposition 6.3**. -/
theorem stabSeminorm_le_of_near (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    (hZdiff : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)))
    (U : K₀ C →+ ℂ) (hU : stabSeminorm C σ U ≠ ⊤) :
    stabSeminorm C τ U ≤
      ENNReal.ofReal ((stabSeminorm C σ U).toReal /
        (Real.cos (Real.pi * ε) - (stabSeminorm C σ (τ.Z - σ.Z)).toReal)) := by
  have hZdiff_ne : stabSeminorm C σ (τ.Z - σ.Z) ≠ ⊤ :=
    ne_top_of_lt (lt_trans hZdiff ENNReal.ofReal_lt_top)
  set M_U := (stabSeminorm C σ U).toReal
  set M_Z := (stabSeminorm C σ (τ.Z - σ.Z)).toReal
  have hMU0 : 0 ≤ M_U := ENNReal.toReal_nonneg
  have hMZ0 : 0 ≤ M_Z := ENNReal.toReal_nonneg
  have hcos_pos : 0 < Real.cos (Real.pi * ε) := by
    apply Real.cos_pos_of_mem_Ioo; constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hMZ_lt : M_Z < Real.cos (Real.pi * ε) := by
    by_contra hle; push_neg at hle
    have h1 : ENNReal.ofReal (Real.cos (Real.pi * ε)) ≤ ENNReal.ofReal M_Z :=
      ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_toReal hZdiff_ne] at h1
    exact absurd hZdiff (not_lt.mpr h1)
  set c := Real.cos (Real.pi * ε) with hc_def
  have hcMZ : 0 < c - M_Z := by linarith
  have hMU_bound : ∀ (A : C) (ψ : ℝ), σ.slicing.P ψ A → ¬IsZero A →
      ‖U (K₀.of C A)‖ ≤ M_U * ‖σ.Z (K₀.of C A)‖ :=
    fun A ψ hP hA ↦ stabSeminorm_bound_real C σ U hU hP hA
  have hMZ_bound : ∀ (A : C) (ψ : ℝ), σ.slicing.P ψ A → ¬IsZero A →
      ‖(τ.Z - σ.Z) (K₀.of C A)‖ ≤ M_Z * ‖σ.Z (K₀.of C A)‖ :=
    fun A ψ hP hA ↦ stabSeminorm_bound_real C σ (τ.Z - σ.Z) hZdiff_ne hP hA
  apply iSup_le; intro E; apply iSup_le; intro φ
  apply iSup_le; intro hP; apply iSup_le; intro hE
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨m, hm, hmZ⟩ := τ.compat φ E hP hE
  have hZτ_pos : (0 : ℝ) < ‖τ.Z (K₀.of C E)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  have hbounds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hP hd
  have hwidth : σ.slicing.phiPlus C E hE - σ.slicing.phiMinus C E hE ≤ 2 * ε := by
    have := hbounds.1; have := hbounds.2; rw [Set.mem_Ioo] at *; linarith
  have h2ε : 2 * ε < 1 := by linarith
  have hcos_eq : Real.pi * (2 * ε) / 2 = Real.pi * ε := by ring
  have hsector := sector_bound' C σ U hE (by linarith : (0 : ℝ) ≤ 2 * ε) h2ε hwidth hMU0
    hMU_bound
  rw [hcos_eq] at hsector
  have hreverse := norm_Z_le_of_tau_semistable C σ τ hE hP hε hε1 hd hMZ0 hMZ_bound
  have hσZ_le : ‖σ.Z (K₀.of C E)‖ ≤ c / (c - M_Z) * ‖τ.Z (K₀.of C E)‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcMZ]
    have hmul := mul_le_mul_of_nonneg_left hreverse (le_of_lt hcos_pos)
    have heq : c * ((1 - M_Z / c) * ‖σ.Z (K₀.of C E)‖) =
        (c - M_Z) * ‖σ.Z (K₀.of C E)‖ := by
      field_simp
    linarith
  calc ‖U (K₀.of C E)‖ / ‖τ.Z (K₀.of C E)‖
      ≤ (M_U / c * ‖σ.Z (K₀.of C E)‖) / ‖τ.Z (K₀.of C E)‖ :=
        div_le_div_of_nonneg_right hsector (le_of_lt hZτ_pos)
    _ ≤ (M_U / c * (c / (c - M_Z) * ‖τ.Z (K₀.of C E)‖)) /
          ‖τ.Z (K₀.of C E)‖ := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hZτ_pos)
        exact mul_le_mul_of_nonneg_left hσZ_le (div_nonneg hMU0 (le_of_lt hcos_pos))
    _ = M_U / (c - M_Z) := by
        field_simp [ne_of_gt hcos_pos, ne_of_gt hcMZ, ne_of_gt hZτ_pos]

/-- **General Lemma 6.2** (seminorm finiteness comparison). If `d(P, Q) < ε < 1/2`
and `‖τ.Z - σ.Z‖_σ < cos(πε)`, then `V(σ) ⊆ V(τ)`. -/
theorem stabSeminorm_lt_top_of_near (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    (hZdiff : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)))
    (U : K₀ C →+ ℂ) (hU : stabSeminorm C σ U < ⊤) :
    stabSeminorm C τ U < ⊤ :=
  lt_of_le_of_lt
    (stabSeminorm_le_of_near C σ τ hε hε1 hd hZdiff U (ne_top_of_lt hU))
    ENNReal.ofReal_lt_top

/-- **Proposition 6.3** (V(Σ) equality for nearby stability conditions). If
`τ ∈ B_ε(σ)` with `ε < 1/8`, then `V(σ) = V(τ)`. This shows the subgroup `V`
is locally constant on `Stab(D)`, hence constant on connected components.

The forward direction uses `stabSeminorm_le_of_near`. The reverse direction uses
the explicit bound to show `‖σ.Z - τ.Z‖_τ < cos(πε)`, then applies the
comparison with `σ` and `τ` swapped. The key inequality is
`sin(πε) · (1 + cos(πε)) < cos²(πε)` for `ε < 1/8`, proved via
`sin(x) < x` and `x² + 2x < 1` for `x = πε < π/8 < √2 - 1`. -/
theorem finiteSeminormSubgroup_eq_of_basisNhd (σ τ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 8)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε)
    (hZnorm : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    finiteSeminormSubgroup C σ = finiteSeminormSubgroup C τ := by
  have hε2 : ε < 1 / 2 := by linarith
  -- sin(πε) < cos(πε) for ε < 1/4, so the Z-norm hypothesis implies < cos(πε)
  have hsin_lt_cos : Real.sin (Real.pi * ε) < Real.cos (Real.pi * ε) := by
    rw [← Real.cos_pi_div_two_sub]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcos_pos' : 0 < Real.cos (Real.pi * ε) := by
    apply Real.cos_pos_of_mem_Ioo; constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hZdiff : stabSeminorm C σ (τ.Z - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)) :=
    lt_trans hZnorm ((ENNReal.ofReal_lt_ofReal_iff hcos_pos').mpr hsin_lt_cos)
  -- Forward: V(σ) ⊆ V(τ)
  have hfwd : ∀ U, stabSeminorm C σ U < ⊤ → stabSeminorm C τ U < ⊤ :=
    fun U hU ↦ stabSeminorm_lt_top_of_near C σ τ hε hε2 hd hZdiff U hU
  -- Reverse: V(τ) ⊆ V(σ)
  -- Step 1: Bound ‖τ.Z - σ.Z‖_τ using the explicit bound
  have hZdiff_ne : stabSeminorm C σ (τ.Z - σ.Z) ≠ ⊤ :=
    ne_top_of_lt (lt_trans hZdiff ENNReal.ofReal_lt_top)
  set M_Z := (stabSeminorm C σ (τ.Z - σ.Z)).toReal with hMZ_def
  have hMZ0 : 0 ≤ M_Z := ENNReal.toReal_nonneg
  have hMZ_lt_sin : M_Z < Real.sin (Real.pi * ε) := by
    by_contra hle; push_neg at hle
    have h1 : ENNReal.ofReal (Real.sin (Real.pi * ε)) ≤ ENNReal.ofReal M_Z :=
      ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_toReal hZdiff_ne] at h1
    exact absurd hZnorm (not_lt.mpr h1)
  have hcos_pos := hcos_pos'
  have hMZ_lt_cos : M_Z < Real.cos (Real.pi * ε) := lt_trans hMZ_lt_sin hsin_lt_cos
  set c := Real.cos (Real.pi * ε)
  have hcMZ : 0 < c - M_Z := by linarith
  -- Step 2: Apply explicit bound to U = τ.Z - σ.Z
  have hZbound : stabSeminorm C τ (τ.Z - σ.Z) ≤
      ENNReal.ofReal (M_Z / (c - M_Z)) :=
    stabSeminorm_le_of_near C σ τ hε hε2 hd hZdiff (τ.Z - σ.Z) hZdiff_ne
  -- Step 3: Show M_Z / (c - M_Z) < cos(πε) via the trigonometric inequality
  -- This is equivalent to M_Z · (1 + c) < c², which follows from
  -- M_Z < sin(πε) and sin(πε) · (1 + cos(πε)) < cos²(πε).
  -- Proof: sin(x)(1+cos(x)) ≤ 2x and cos²(x) ≥ 1-x², and 2x + x² < 1 for x < √2-1 > π/8.
  have hsin_pos : 0 < Real.sin (Real.pi * ε) := by
    exact Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  -- Key: sin(πε) · (1 + cos(πε)) < cos²(πε)
  -- Use sin(πε) ≤ πε, 1 + cos(πε) ≤ 2, cos²(πε) ≥ 1 - (πε)²
  have hsin_le : Real.sin (Real.pi * ε) ≤ Real.pi * ε :=
    Real.sin_le (by nlinarith [Real.pi_pos])
  have hx_bound : Real.pi * ε < Real.pi / 8 := by nlinarith [Real.pi_pos]
  -- (πε)² + 2(πε) < 1, which gives sin(πε)(1+cos(πε)) < cos²(πε)
  have hx_ineq : (Real.pi * ε) ^ 2 + 2 * (Real.pi * ε) < 1 := by
    -- Need π²ε² + 2πε < 1 for ε < 1/8.
    -- Equivalent to (π/8)² + π/4 < 1, i.e., π² + 16π < 64.
    -- Use π < 3.15 (from pi_lt_d2): 3.15² + 16·3.15 = 9.9225 + 50.4 = 60.3225 < 64. ✓
    have hpi := Real.pi_lt_d2 -- π < 3.15
    nlinarith [Real.pi_pos, sq_nonneg Real.pi, sq_nonneg ε]
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
          -- cos²(x) = 1 - sin²(x) ≥ 1 - x² since sin(x) ≤ x and 0 ≤ sin(x)
          have hsin_sq : Real.sin (Real.pi * ε) ^ 2 ≤ (Real.pi * ε) ^ 2 := by
            rw [sq, sq]
            exact mul_le_mul hsin_le hsin_le (le_of_lt hsin_pos)
              (by nlinarith [Real.pi_pos])
          have := Real.sin_sq_add_cos_sq (Real.pi * ε)
          nlinarith
  have hbound_lt_cos : M_Z / (c - M_Z) < c := by
    rw [div_lt_iff₀ hcMZ]; linarith
  -- Step 4: Conclude ‖σ.Z - τ.Z‖_τ < cos(πε)
  have hZτ_bound : stabSeminorm C τ (σ.Z - τ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * ε)) := by
    have : stabSeminorm C τ (σ.Z - τ.Z) = stabSeminorm C τ (τ.Z - σ.Z) := by
      simp only [stabSeminorm, AddMonoidHom.sub_apply]
      congr 1; ext E; congr 1; ext φ; congr 1; ext; congr 1; ext
      rw [norm_sub_rev]
    rw [this]
    exact lt_of_le_of_lt hZbound
      ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hbound_lt_cos)
  -- Step 5: Apply stabSeminorm_lt_top_of_near in reverse
  have hrev : ∀ U, stabSeminorm C τ U < ⊤ → stabSeminorm C σ U < ⊤ := by
    intro U hU
    have hd_sym : slicingDist C τ.slicing σ.slicing < ENNReal.ofReal ε := by
      rwa [slicingDist_symm]
    exact stabSeminorm_lt_top_of_near C τ σ hε hε2 hd_sym hZτ_bound U hU
  ext U; simp only [finiteSeminormSubgroup, AddSubgroup.mem_mk]
  exact ⟨hfwd U, hrev U⟩


end CategoryTheory.Triangulated
