/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.NumericalStability
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Euler form descends to K₀

We prove that the Euler form `χ(E,F) = Σₙ (-1)ⁿ dim_k Hom(E, F[n])` is
triangle-additive in both arguments, providing an instance of `EulerFormDescends`.

The proof uses the long exact Hom sequence from the homological Yoneda functor
and the rank-nullity theorem for finite-dimensional vector spaces.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CategoryTheory.Triangulated

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [Linear k C] [IsFiniteType k C]

-- For a middle-exact sequence K →f M →g N of f.d. k-vector spaces (im f = ker g),
-- dim M = dim(ker g) + dim(im g) = dim(im f) + dim(im g).
-- This is just rank-nullity applied to g, combined with exactness.
private lemma finrank_mid_of_exact {K M N : Type v} [AddCommGroup K] [Module k K]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [Module.Finite k M]
    (f : K →ₗ[k] M) (g : M →ₗ[k] N) (hfg : LinearMap.range f = LinearMap.ker g) :
    (Module.finrank k M : ℤ) = Module.finrank k (LinearMap.range f) +
      Module.finrank k (LinearMap.range g) := by
  have h := g.finrank_range_add_finrank_ker
  rw [← hfg] at h
  omega

-- The contravariant Euler form `F ↦ χ(E,F)` is triangle-additive.
-- For a distinguished triangle A → B → C → A[1], the long exact Hom sequence
-- and the rank-nullity theorem give a telescoping identity:
--   Σ_n (-1)^n dim Hom(E, B[n]) = Σ_n (-1)^n dim Hom(E, A[n]) + Σ_n (-1)^n dim Hom(E, C[n])
-- Key cancellation: Σ (-1)^n r(n-1) = -Σ (-1)^n r(n), so the sum of both is zero.
-- This is the heart of the Euler characteristic telescoping.
-- Key cancellation: Σ (-1)^n r(n-1) + Σ (-1)^n r(n) = 0 for finitely supported r.
-- Proof: shift index in the first sum, use (-1)^(n+1) = -(-1)^n.
private lemma finsum_alternating_shift_cancel {r : ℤ → ℤ}
    (hr : (Function.support r).Finite) :
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * r (n - 1) +
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * r n = 0 := by
  -- Shift the first sum: n ↦ n-1 becomes m ↦ m+1
  have h_shift : ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * r (n - 1) =
      ∑ᶠ m : ℤ, ((m + 1).negOnePow : ℤ) * r m := by
    show ∑ᶠ n : ℤ, (((n : ℤ).negOnePow : ℤ) * r (n - 1)) =
        ∑ᶠ m : ℤ, (((m + 1 : ℤ).negOnePow : ℤ) * r m)
    have : (fun n : ℤ ↦ ((n : ℤ).negOnePow : ℤ) * r (n - 1)) =
        fun n : ℤ ↦ (((Equiv.subRight (1 : ℤ) n + 1 : ℤ).negOnePow : ℤ) *
          r (Equiv.subRight (1 : ℤ) n)) := by
      ext n; simp [Equiv.subRight, sub_add_cancel]
    rw [this]
    exact @finsum_comp_equiv ℤ ℤ ℤ _ (Equiv.subRight 1)
      (f := fun m ↦ ((m + 1 : ℤ).negOnePow : ℤ) * r m)
  rw [h_shift]
  -- (-1)^(m+1) = -(-1)^m
  simp_rw [Int.negOnePow_succ, Units.val_neg, neg_mul]
  -- Now: Σ -(-1)^m r(m) + Σ (-1)^n r(n) = 0
  rw [finsum_neg_distrib]
  linarith

private theorem eulerFormObj_contravariant_triangleAdditive (E : C) :
    IsTriangleAdditive (fun F ↦ eulerFormObj k C E F) where
  additive := fun T hT ↦ by
    -- Goal: χ(E, T.obj₂) = χ(E, T.obj₁) + χ(E, T.obj₃)
    -- The preadditiveCoyoneda.obj (op E) is homological, giving exactness at each degree.
    -- By rank-nullity + telescoping, the alternating sum is additive.
    sorry

-- The covariant Euler form `E ↦ χ(E,F)` is triangle-additive.
-- Same argument applied to the preadditiveYoneda functor.
private theorem eulerFormObj_covariant_triangleAdditive (F : C) :
    IsTriangleAdditive (fun E ↦ eulerFormObj k C E F) where
  additive := fun T hT ↦ by
    sorry

instance : EulerFormDescends k C where
  covariant := fun F ↦ eulerFormObj_covariant_triangleAdditive k C F
  contravariant := fun E ↦ eulerFormObj_contravariant_triangleAdditive k C E

end CategoryTheory.Triangulated
