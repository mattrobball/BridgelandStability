/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.EulerForm.Basic
public import Mathlib.Geometry.Manifold.Complex

/-!
# Euler Form Definitions — Comparator Interface

Re-exports the data-carrying declarations from `EulerForm.Basic` (which provides
`eulerFormInner`, `eulerForm`, `eulerFormRad`, `NumericalK₀`, `numericalQuotientMap`,
`NumericallyFinite`, etc.) and adds `NumericalComponent`, the connected-component
type for numerical stability conditions.

This module, together with `Slicing.Defs` and `StabilityCondition.Defs`, provides all
type-level dependencies needed to state Bridgeland's Corollary 1.3.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CategoryTheory.Triangulated

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- A connected component of numerical stability conditions. -/
abbrev NumericalComponent [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :=
  StabilityCondition.WithClassMap.Component C (numericalQuotientMap k C) cc

end CategoryTheory.Triangulated
