/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.GrothendieckGroup
import Mathlib.CategoryTheory.Triangulated.Slicing
import Mathlib.Topology.PartialHomeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Bridgeland Stability Conditions

We define Bridgeland stability conditions on a pretriangulated category and state
the main theorems from "Stability conditions on triangulated categories" (2007):

* **Theorem 1.2**: The space of locally-finite stability conditions is a complex manifold,
  and the central charge map is a local homeomorphism.
* **Corollary 1.3**: If the category is numerically finite, the space of numerical
  stability conditions is a finite-dimensional complex manifold.

The main theorem statements are `Prop`-valued definitions that ∃-quantify over the
topologies involved.

## Main definitions

* `CategoryTheory.Triangulated.StabilityCondition`: a locally-finite stability condition
* `CategoryTheory.Triangulated.bridgelandTheorem_1_2`: **Theorem 1.2** as a `Prop`
* `CategoryTheory.Triangulated.eulerFormRad`: radical of the Euler form
* `CategoryTheory.Triangulated.NumericalK₀`: numerical Grothendieck group
* `CategoryTheory.Triangulated.NumericallyFinite`: finite generation of numerical K₀
* `CategoryTheory.Triangulated.bridgelandCorollary_1_3`: **Corollary 1.3** as a `Prop`
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex

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

/-- The central charge of a stability condition, viewed as a function `K₀ C → ℂ`. -/
def StabilityCondition.centralChargeVal (σ : StabilityCondition C) : K₀ C → ℂ := σ.Z

/-- **Bridgeland's Theorem 1.2.** The space of locally-finite stability conditions on `C`
admits the structure of a complex manifold, such that the map sending each stability
condition to its central charge is a local homeomorphism onto an open subset of
`Hom(K₀(C), ℂ)`.

We formalize this as a `Prop`: there exist topologies on `StabilityCondition C` and on
`K₀ C →+ ℂ` such that for every stability condition `σ`, there is a partial homeomorphism
whose source contains `σ` and that agrees with the central charge map. -/
def bridgelandTheorem_1_2 : Prop :=
  ∃ (τ₁ : TopologicalSpace (StabilityCondition C))
    (τ₂ : TopologicalSpace (K₀ C →+ ℂ)),
    ∀ σ : StabilityCondition C,
      ∃ (e : @PartialHomeomorph (StabilityCondition C) (K₀ C →+ ℂ) τ₁ τ₂),
        σ ∈ e.source ∧ ∀ σ' ∈ e.source, e σ' = σ'.Z

/-! ### Numerical K-theory and Corollary 1.3 -/

/-- The radical of a bilinear form `χ` on `K₀ C`. This is the subgroup of elements
`x ∈ K₀ C` such that `χ(x, y) = 0` for all `y`. When `χ` is the Euler form
`χ(E,F) = Σᵢ (-1)ⁱ dim Hom(E, F[i])`, this gives the radical of the Euler pairing. -/
def eulerFormRad (χ : K₀ C →+ K₀ C →+ ℤ) : AddSubgroup (K₀ C) :=
  χ.ker

/-- The numerical Grothendieck group, defined as `K₀ C` modulo the radical of
the Euler form. -/
def NumericalK₀ (χ : K₀ C →+ K₀ C →+ ℤ) : Type _ :=
  K₀ C ⧸ eulerFormRad C χ

/-- The `AddCommGroup` instance on `NumericalK₀ C χ`, inherited from the quotient. -/
instance NumericalK₀.instAddCommGroup (χ : K₀ C →+ K₀ C →+ ℤ) :
    AddCommGroup (NumericalK₀ C χ) :=
  inferInstanceAs (AddCommGroup (K₀ C ⧸ eulerFormRad C χ))

/-- A numerical stability condition is a stability condition whose central charge
factors through the numerical Grothendieck group `NumericalK₀ C χ`. -/
structure NumericalStabilityCondition (χ : K₀ C →+ K₀ C →+ ℤ) where
  /-- The underlying stability condition. -/
  σ : StabilityCondition C
  /-- The central charge factors through the numerical K₀. -/
  factors : ∃ Z' : NumericalK₀ C χ →+ ℂ,
    σ.Z = Z'.comp (QuotientAddGroup.mk' (eulerFormRad C χ))

/-- The category `C` is numerically finite (with respect to Euler form `χ`) if the
numerical Grothendieck group `NumericalK₀ C χ` is finitely generated as an abelian group. -/
class NumericallyFinite (χ : K₀ C →+ K₀ C →+ ℤ) : Prop where
  /-- The numerical Grothendieck group is finitely generated. -/
  fg : AddGroup.FG (NumericalK₀ C χ)

/-- **Bridgeland's Corollary 1.3.** If `C` is numerically finite, then the space of
numerical stability conditions on `C` is a finite-dimensional complex manifold.

We formalize this as: assuming `NumericallyFinite C χ`, there exist a natural number `n`
and a topology on the space of numerical stability conditions such that every point
has a neighborhood homeomorphic to `ℂⁿ = Fin n → ℂ`. -/
def bridgelandCorollary_1_3 (χ : K₀ C →+ K₀ C →+ ℤ) : Prop :=
  NumericallyFinite C χ →
    ∃ (n : ℕ) (τ : TopologicalSpace (NumericalStabilityCondition C χ)),
      ∀ σ : NumericalStabilityCondition C χ,
        ∃ (e : @PartialHomeomorph (NumericalStabilityCondition C χ) (Fin n → ℂ) τ inferInstance),
          σ ∈ e.source

end CategoryTheory.Triangulated
