/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.NumericalStability.Defs
public import BridgelandStability.StabilityCondition.Topology

/-!
# Numerical Stability — Basic

This file previously contained bridge infrastructure for `ClassMapStabilityCondition`
(the factorization-subtype presentation of `Stab_v(D)`). That infrastructure was
eliminated by the `WithClassMap C v` refactor: the manifold theorem now applies
`ComponentTopologicalLinearLocalModel` directly, without routing through a
factorization subtype.
-/
