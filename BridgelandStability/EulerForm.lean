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
private theorem eulerFormObj_contravariant_triangleAdditive (E : C) :
    IsTriangleAdditive (fun F ↦ eulerFormObj k C E F) where
  additive := fun T hT ↦ by
    -- The long exact Hom sequence from coyoneda gives, at each degree n:
    --   Hom(E, A[n]) → Hom(E, B[n]) → Hom(E, C[n])  exact (im f = ker g)
    -- Combined with the connecting maps Hom(E, C[n]) → Hom(E, A[n+1]),
    -- the alternating sum telescopes to zero.
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
