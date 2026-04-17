/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Slicing.Defs
public import BridgelandStability.GrothendieckGroup.Basic
public import BridgelandStability.IntervalCategory.FiniteLength
public import BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.SectorBound
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Stability Condition Definitions

Core data-carrying declarations for Bridgeland stability conditions: the
`PreStabilityCondition.WithClassMap` and `StabilityCondition.WithClassMap` structures,
the generalized metric `slicingDist`, the seminorm `stabSeminorm`, basis neighborhoods,
the Bridgeland topology, and connected-component types.

These definitions are separated from the proof files so that downstream modules
(Euler form, numerical stability, manifold structure) can import type-level dependencies
without pulling in phase rigidity proofs and sector-bound lemmas.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ENNReal

universe v u u'

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]

/-! ### Prestability and stability conditions -/

namespace PreStabilityCondition

/-- A Bridgeland prestability condition with respect to a class map
`v : K₀(C) → Λ`. The central charge lives on `Λ`, and the ordinary ambient
charge is recovered by precomposition with `v`. -/
@[informal "Definition 5.1" complete]
structure WithClassMap (v : K₀ C →+ Λ) where
  /-- The underlying slicing. -/
  slicing : Slicing C
  /-- The central charge on the class lattice `Λ`. -/
  Z : Λ →+ ℂ
  /-- Compatibility (raw). Use `σ.compat` instead. -/
  compat' : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)

omit [IsTriangulated C] in
variable {C} in
/-- The central charge evaluated at the class of `E`. This is `Z(v[E])`. -/
noncomputable abbrev WithClassMap.charge {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) (E : C) : ℂ :=
  σ.Z (cl C v E)

omit [IsTriangulated C] in
variable {C} in
theorem WithClassMap.charge_def {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) (E : C) :
    σ.charge E = σ.Z (cl C v E) := rfl

omit [IsTriangulated C] in
variable {C} in
/-- Compatibility: for nonzero semistable `E` of phase `φ`, `σ.charge E`
lies on the ray `ℝ₊ · exp(iπφ)`. -/
theorem WithClassMap.compat {v : K₀ C →+ Λ} (σ : WithClassMap C v)
    (φ : ℝ) (E : C) (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      σ.charge E = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) :=
  σ.compat' φ E hP hE

omit [IsTriangulated C] in
variable {C} in
theorem WithClassMap.charge_isZero {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) {E : C} (hE : IsZero E) :
    σ.charge E = 0 := by
  simp [charge_def, cl_isZero (C := C) (v := v) hE]

omit [IsTriangulated C] in
variable {C} in
theorem WithClassMap.charge_congr {v : K₀ C →+ Λ}
    {σ τ : WithClassMap C v} (h : σ.Z = τ.Z) (E : C) :
    σ.charge E = τ.charge E := by
  simp only [charge_def, h]

omit [IsTriangulated C] in
variable {C} in
theorem WithClassMap.charge_postnikovTower_eq_sum {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) {E : C} (P : PostnikovTower C E) :
    σ.charge E = ∑ i : Fin P.n, σ.charge (P.factor i) := by
  simp only [charge_def, cl_postnikovTower_eq_sum C v P, map_sum]

end PreStabilityCondition

/-- A Bridgeland prestability condition on `C`, viewed as the specialization of
the class-map theory to the identity map `K₀(C) → K₀(C)`. -/
abbrev PreStabilityCondition :=
  PreStabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))

namespace StabilityCondition

/-- A Bridgeland stability condition with respect to a class map `v : K₀(C) → Λ`.
This is the locally-finite refinement of `PreStabilityCondition.WithClassMap`. -/
@[informal "Definition 5.7" complete]
structure WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  /-- The slicing is locally finite. -/
  locallyFinite : slicing.IsLocallyFinite C

end StabilityCondition

/-- A Bridgeland stability condition on `C`, viewed as the specialization of the
class-map theory to the identity map `K₀(C) → K₀(C)`. -/
abbrev StabilityCondition :=
  StabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))

/-- The ordinary compatibility statement for a stability condition, with the
identity class map simplified away. -/
theorem stabilityCondition_compat_apply (σ : StabilityCondition C)
    (φ : ℝ) (E : C) (hE : σ.slicing.P φ E) (hNZ : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      σ.Z (K₀.of C E) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) := by
  simpa using σ.compat φ E hE hNZ

/-! ### Phase rotation identity -/

/-- The imaginary part of `m · exp(iπψ) · exp(-iπφ)` is `m · sin(π(ψ - φ))`.
This is the core identity underlying all phase-sign arguments in the Bridgeland
deformation theory (Lemmas 6.1–6.4 and the HN existence proof). -/
theorem im_ofReal_mul_exp_mul_exp_neg (m ψ φ : ℝ) :
    ((m : ℂ) * Complex.exp (↑(Real.pi * ψ) * Complex.I) *
      Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im =
      m * Real.sin (Real.pi * (ψ - φ)) := by
  rw [mul_assoc, ← Complex.exp_add,
    show ↑(Real.pi * ψ) * Complex.I + -(↑(Real.pi * φ) * Complex.I) =
      ↑(Real.pi * (ψ - φ)) * Complex.I from by push_cast; ring,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero]

/-! ### Generalized metric and seminorm -/

open Real in
/-- The Bridgeland generalized metric on slicings. For slicings `s₁` and `s₂`,
this is the supremum over all nonzero objects `E` of
`max(|φ₁⁺(E) - φ₂⁺(E)|, |φ₁⁻(E) - φ₂⁻(E)|)`. -/
def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)

/-- The Bridgeland seminorm `‖U‖_σ` on `Hom(Λ, ℂ)`. For a class-map stability
condition `σ = (Z, P)` with class map `v : K₀(D) → Λ` and a group homomorphism
`U : Λ → ℂ`, this is `sup { |U(v[E])| / |Z(v[E])| : E is σ-semistable and nonzero }`.

When `v = id` (i.e., `Λ = K₀(D)`), this recovers Bridgeland's original seminorm. -/
def stabSeminorm {v : K₀ C →+ Λ} (σ : StabilityCondition.WithClassMap C v)
    (U : Λ →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (cl C v E)‖ / ‖σ.charge E‖)

/-! ### Topology on Stab(D) -/

/-- The basis neighborhood `B_ε(σ)` for the Bridgeland topology on `Stab_v(D)`. -/
def basisNhd {v : K₀ C →+ Λ} (σ : StabilityCondition.WithClassMap C v) (ε : ℝ) :
    Set (StabilityCondition.WithClassMap C v) :=
  {τ | stabSeminorm C σ (τ.Z - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)) ∧
       slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε}

/-- The Bridgeland topology on `Stab_v(D)`, generated by the basis neighborhoods
`B_ε(σ)` for all stability conditions `σ` and all `ε ∈ (0, 1/8)`.

This is the BLMNPS topology: the coarsest making both the charge map `σ ↦ σ.Z`
and the slicing map continuous. When `v = id`, this recovers Bridgeland's original
topology on `Stab(D)`. -/
instance StabilityCondition.WithClassMap.topologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  TopologicalSpace.generateFrom
    {U | ∃ (σ : StabilityCondition.WithClassMap C v) (ε : ℝ), 0 < ε ∧ ε < 1 / 8 ∧
      U = basisNhd C σ ε}

namespace StabilityCondition.WithClassMap

/-- The connected-component index set for `Stab_v(D)`. -/
abbrev ComponentIndex (v : K₀ C →+ Λ) :=
  _root_.ConnectedComponents (StabilityCondition.WithClassMap C v)

/-- The type of `v`-relative stability conditions in a fixed connected component. -/
abbrev Component (v : K₀ C →+ Λ) (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :=
  {σ : StabilityCondition.WithClassMap C v // _root_.ConnectedComponents.mk σ = cc}

/-- The local-homeomorphism package for connected components of `Stab_v(D)`, stated directly in
terms of the class-map charge `Z : Λ →+ ℂ`. Specializing to `v = id` recovers Bridgeland's
Theorem 1.2 proposition-object; specializing to the numerical quotient recovers Corollary 1.3. -/
@[informal "Theorem 1.2" "statement only; proof is componentTopologicalLinearLocalModel"]
def CentralChargeIsLocalHomeomorphOnConnectedComponents {v : K₀ C →+ Λ} : Prop :=
  ∀ (cc : StabilityCondition.WithClassMap.ComponentIndex C v),
    ∃ (V : Submodule ℂ (Λ →+ ℂ))
      (_ : NormedAddCommGroup V)
      (_ : NormedSpace ℂ V)
      (hZ : ∀ σ : StabilityCondition.WithClassMap C v,
        ConnectedComponents.mk σ = cc → σ.Z ∈ V),
      @IsLocalHomeomorph
        (StabilityCondition.WithClassMap.Component C v cc)
        V inferInstance inferInstance
        (fun ⟨σ, hσ⟩ ↦ ⟨σ.Z, hZ σ hσ⟩)

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
