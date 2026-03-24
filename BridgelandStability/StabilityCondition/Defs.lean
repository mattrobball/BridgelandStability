/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Slicing.Defs
public import BridgelandStability.GrothendieckGroup.Defs
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
structure WithClassMap (v : K₀ C →+ Λ) where
  /-- The underlying slicing. -/
  slicing : Slicing C
  /-- The central charge on the class lattice `Λ`. -/
  Z : Λ →+ ℂ
  /-- Compatibility: for every nonzero semistable object `E` of phase `φ`, the
  class-map central charge `Z(v([E]))` lies on the ray `ℝ₊ · exp(iπφ)` in `ℂ`. -/
  compat : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)

/-- Forget a class-map prestability condition to the identity class map on `K₀(C)`. -/
def WithClassMap.toPreStabilityCondition {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) :
    WithClassMap C (AddMonoidHom.id (K₀ C)) where
  slicing := σ.slicing
  Z := σ.Z.comp v
  compat := by
    intro φ E hE hNZ
    simpa [AddMonoidHom.comp_apply] using σ.compat φ E hE hNZ

end PreStabilityCondition

/-- A Bridgeland prestability condition on `C`, viewed as the specialization of
the class-map theory to the identity map `K₀(C) → K₀(C)`. -/
abbrev PreStabilityCondition :=
  PreStabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))

namespace StabilityCondition

/-- A Bridgeland stability condition with respect to a class map `v : K₀(C) → Λ`.
This is the locally-finite refinement of `PreStabilityCondition.WithClassMap`. -/
structure WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  /-- The slicing is locally finite. -/
  locallyFinite : slicing.IsLocallyFinite C

/-- Forget a class-map stability condition to the identity class map on `K₀(C)`. -/
def WithClassMap.toStabilityCondition {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) :
    WithClassMap C (AddMonoidHom.id (K₀ C)) where
  toWithClassMap := σ.toWithClassMap.toPreStabilityCondition
  locallyFinite := σ.locallyFinite

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

/-! ### Generalized metric and seminorm -/

open Real in
/-- The Bridgeland generalized metric on slicings. For slicings `s₁` and `s₂`,
this is the supremum over all nonzero objects `E` of
`max(|φ₁⁺(E) - φ₂⁺(E)|, |φ₁⁻(E) - φ₂⁻(E)|)`. -/
def slicingDist (s₁ s₂ : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E),
    ENNReal.ofReal (max |s₁.phiPlus C E hE - s₂.phiPlus C E hE|
                        |s₁.phiMinus C E hE - s₂.phiMinus C E hE|)

/-- The seminorm `‖U‖_σ` on `Hom_ℤ(K₀(D), ℂ)`. For a stability condition
`σ = (Z, P)` and a group homomorphism `U : K₀(D) → ℂ`, this is
`sup { |U(E)| / |Z(E)| : E is σ-semistable and nonzero }`. -/
def stabSeminorm (σ : StabilityCondition C) (U : K₀ C →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (K₀.of C E)‖ / ‖σ.Z (K₀.of C E)‖)

/-! ### Topology on Stab(D) -/

/-- The basis neighborhood `B_ε(σ)` for the Bridgeland topology. -/
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

namespace StabilityCondition.WithClassMap

/-- The topology on `Stab_v(D)` is induced from the ordinary Bridgeland topology on `Stab(D)` by
forgetting the class-map charge to its ambient central charge on `K₀(C)`. -/
abbrev topologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  TopologicalSpace.induced
    (StabilityCondition.WithClassMap.toStabilityCondition (C := C) (v := v))
    inferInstance

instance (priority := 100) instTopologicalSpace {v : K₀ C →+ Λ} :
    TopologicalSpace (StabilityCondition.WithClassMap C v) :=
  StabilityCondition.WithClassMap.topologicalSpace (C := C) (v := v)

/-- The connected-component index set for `Stab_v(D)`. -/
abbrev ComponentIndex (v : K₀ C →+ Λ) :=
  _root_.ConnectedComponents (StabilityCondition.WithClassMap C v)

/-- The type of `v`-relative stability conditions in a fixed connected component. -/
abbrev Component (v : K₀ C →+ Λ) (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :=
  {σ : StabilityCondition.WithClassMap C v // _root_.ConnectedComponents.mk σ = cc}

/-- The local-homeomorphism package for connected components of `Stab_v(D)`, stated directly in
terms of the class-map charge `Z : Λ →+ ℂ`. Specializing to `v = id` recovers Bridgeland's
Theorem 1.2 proposition-object; specializing to the numerical quotient recovers Corollary 1.3. -/
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
