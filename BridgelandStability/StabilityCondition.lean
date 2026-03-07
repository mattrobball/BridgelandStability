/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.GrothendieckGroup
import Mathlib.CategoryTheory.Triangulated.Slicing
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.ENNReal.Basic

/-!
# Bridgeland Stability Conditions

We define Bridgeland stability conditions on a pretriangulated category and state
the main theorem from "Stability conditions on triangulated categories" (2007):

* **Theorem 1.2**: For each connected component `Σ` of the space `Stab(D)` of
  locally-finite stability conditions, there exists a linear subspace
  `V(Σ) ⊆ Hom_ℤ(K₀(D), ℂ)` with a linear topology, and a local homeomorphism
  `𝒵 : Σ → V(Σ)` sending `(Z, P)` to `Z`.

## Main definitions

* `CategoryTheory.Triangulated.StabilityCondition`: a locally-finite stability condition
* `CategoryTheory.Triangulated.slicingDist`: the Bridgeland generalized metric on slicings
* `CategoryTheory.Triangulated.stabSeminorm`: the seminorm `‖U‖_σ` on `Hom_ℤ(K₀(D), ℂ)`
* `CategoryTheory.Triangulated.StabilityCondition.topologicalSpace`: the Bridgeland
  topology on `Stab(D)`, constructed from basis neighborhoods
* `CategoryTheory.Triangulated.bridgelandTheorem_1_2`: **Theorem 1.2** as a `Prop`,
  stated componentwise with a linear subspace `V(Σ)`

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ENNReal

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Stability conditions -/

/-- A Bridgeland stability condition on a pretriangulated category `C`.
This bundles a slicing with a central charge (an additive group homomorphism
from `K₀ C` to `ℂ`), subject to a compatibility condition relating the phase
of semistable objects to the argument of their central charge.
The slicing is required to be locally finite. -/
structure StabilityCondition where
  /-- The underlying slicing. -/
  slicing : Slicing C
  /-- The central charge, an additive group homomorphism `K₀ C →+ ℂ`. -/
  Z : K₀ C →+ ℂ
  /-- Compatibility: for every nonzero semistable object `E` of phase `φ`, the central charge
  `Z([E])` lies on the ray `ℝ₊ · exp(iπφ)` in `ℂ`. -/
  compat : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (K₀.of C E) = ↑m * exp (↑(Real.pi * φ) * I)
  /-- The slicing is locally finite. -/
  locallyFinite : slicing.IsLocallyFinite C

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

/-- The seminorm `‖U‖_σ` on `Hom_ℤ(K₀(D), ℂ)` (blueprint A9). For a stability condition
`σ = (Z, P)` and a group homomorphism `U : K₀(D) → ℂ`, this is
`sup { |U(E)| / |Z(E)| : E is σ-semistable and nonzero }`.
Values lie in `[0, ∞]`. -/
def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)

/-! ### Topology on Stab(D) -/

/-- The basis neighborhood `B_ε(σ)` for the Bridgeland topology (blueprint A10).
A stability condition `τ` lies in `B_ε(σ)` if the seminorm distance between
their central charges is less than `sin(πε)` and the slicing distance is less
than `ε`. -/
def basisNhd (σ : StabilityCondition C) (ε : ℝ) : Set (StabilityCondition C) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}

/-- The Bridgeland topology on `Stab(D)`, generated by the basis neighborhoods
`B_ε(σ)` for all stability conditions `σ` and all `ε ∈ (0, 1/8)`. -/
instance StabilityCondition.topologicalSpace :
    TopologicalSpace (StabilityCondition C) :=
  TopologicalSpace.generateFrom
    {U | ∃ (σ : StabilityCondition C) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧
      U = basisNhd C σ ε}

/-! ### Theorem 1.2 -/

/-- **Bridgeland's Theorem 1.2** (corrected statement). For each connected component
`Σ` of the topological space `Stab(D)` (with the Bridgeland topology), there exists
a linear subspace `V(Σ) ⊆ Hom_ℤ(K₀(D), ℂ)` with a topology such that the central
charge map `σ ↦ Z(σ)`, restricted to the component `Σ` and landing in `V(Σ)`, is a
local homeomorphism.

This uses `IsLocalHomeomorph` from `Mathlib.Topology.IsLocalHomeomorph`, avoiding
raw `PartialHomeomorph` with `@`-threaded topologies. The statement implies that each
connected component of `Stab(D)` is a manifold locally modelled on the topological
vector space `V(Σ)`. -/
def bridgelandTheorem_1_2 : Prop :=
  ∀ (cc : ConnectedComponents (StabilityCondition C)),
    ∃ (V : AddSubgroup (K₀ C →+ ℂ))
      (τ_V : TopologicalSpace V)
      (hZ : ∀ σ : StabilityCondition C,
        ConnectedComponents.mk σ = cc → σ.Z ∈ V),
      @IsLocalHomeomorph
        {σ : StabilityCondition C // ConnectedComponents.mk σ = cc}
        V inferInstance τ_V
        (fun ⟨σ, hσ⟩ ↦ ⟨σ.Z, hZ σ hσ⟩)

end CategoryTheory.Triangulated
