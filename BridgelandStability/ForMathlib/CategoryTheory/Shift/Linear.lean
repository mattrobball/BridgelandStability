/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Shift.Basic

/-!
# Linearity of Shift Functors

If the shift-by-1 functor on a `k`-linear category is `k`-linear, then
every shift functor is `k`-linear. This is proved by induction on `ℤ`,
using the composition instance for `Functor.Linear`, the transfer lemma
`Functor.linear_of_iso`, and `Functor.linear_of_full_essSurj_comp` for the
negative direction.

## Main results

* `CategoryTheory.shiftFunctor_linear`: `(shiftFunctor C n).Linear R`
  for all `n : ℤ`, given `(shiftFunctor C 1).Linear R`.
-/

open CategoryTheory

universe v u

namespace CategoryTheory

variable {R : Type*} [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [HasShift C ℤ] [(shiftFunctor C (1 : ℤ)).Linear R]

private lemma shiftFunctor_linear_negOne :
    (shiftFunctor C (-1 : ℤ)).Linear R := by
  letI : (shiftFunctor C (0 : ℤ)).Linear R :=
    Functor.linear_of_iso R (shiftFunctorZero C ℤ).symm
  letI : (shiftFunctor C (1 : ℤ) ⋙ shiftFunctor C (-1 : ℤ)).Linear R :=
    Functor.linear_of_iso R (shiftFunctorAdd' C 1 (-1) 0 (by grind))
  exact Functor.linear_of_full_essSurj_comp
    (R := R) (shiftFunctor C (1 : ℤ)) (shiftFunctor C (-1 : ℤ))

private lemma shiftFunctor_linear_nat (n : ℕ) :
    (shiftFunctor C (n : ℤ)).Linear R := by
  induction n with
  | zero => exact Functor.linear_of_iso R (shiftFunctorZero C ℤ).symm
  | succ n ih =>
    letI := ih
    exact Functor.linear_of_iso R
      (shiftFunctorAdd' C (n : ℤ) 1 (↑(n + 1) : ℤ)
        (by grind)).symm

/-- If the shift-by-1 functor on a `R`-linear category is `R`-linear,
then every shift functor is `R`-linear. -/
instance shiftFunctor_linear (n : ℤ) :
    (shiftFunctor C n).Linear R := by
  obtain (n | n) := n
  · exact shiftFunctor_linear_nat n
  · induction n with
    | zero => exact shiftFunctor_linear_negOne
    | succ n ih =>
      letI := ih
      letI := shiftFunctor_linear_negOne (R := R) (C := C)
      exact Functor.linear_of_iso R
        (shiftFunctorAdd' C (Int.negSucc n) (-1)
          (Int.negSucc (n + 1)) (by grind)).symm

end CategoryTheory
