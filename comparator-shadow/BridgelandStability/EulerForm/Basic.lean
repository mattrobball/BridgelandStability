/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.NumericalStability.Defs
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Shift.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Euler form on `K₀`

We prove that the Euler form `χ(E,F) = Σₙ (-1)ⁿ dim_k Hom(E, F[n])` is
triangle-additive in both arguments, then lift it to a bilinear form on `K₀`.

The proof uses the long exact Hom sequence from the homological Yoneda functor
and the rank-nullity theorem for finite-dimensional vector spaces.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite

universe w v u

namespace CategoryTheory.Triangulated

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [Linear k C] [IsFiniteType k C]

-- For a middle-exact sequence K →f M →g N of f.d. k-vector spaces (im f = ker g),
-- dim M = dim(ker g) + dim(im g) = dim(im f) + dim(im g).
-- This is just rank-nullity applied to g, combined with exactness.
lemma finrank_mid_of_exact {K M N : Type v} [AddCommGroup K] [Module k K]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [Module.Finite k M]
    (f : K →ₗ[k] M) (g : M →ₗ[k] N) (hfg : LinearMap.range f = LinearMap.ker g) :
    (Module.finrank k M : ℤ) = Module.finrank k (LinearMap.range f) +
      Module.finrank k (LinearMap.range g) := by
  have h := g.finrank_range_add_finrank_ker
  rw [← hfg] at h
  lia

-- The contravariant Euler form `F ↦ χ(E,F)` is triangle-additive.
-- For a distinguished triangle A → B → C → A[1], the long exact Hom sequence
-- and the rank-nullity theorem give a telescoping identity:
--   Σ_n (-1)^n dim Hom(E, B[n]) = Σ_n (-1)^n dim Hom(E, A[n]) + Σ_n (-1)^n dim Hom(E, C[n])
-- Key cancellation: Σ (-1)^n r(n-1) = -Σ (-1)^n r(n), so the sum of both is zero.
-- This is the heart of the Euler characteristic telescoping.
-- Key cancellation: Σ (-1)^n r(n-1) + Σ (-1)^n r(n) = 0 for finitely supported r.
-- Proof: shift index in the first sum, use (-1)^(n+1) = -(-1)^n.
lemma finsum_alternating_shift_cancel {r : ℤ → ℤ} :
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

-- Abstract Euler sum lemma: if dim b(n) = dim a(n) + dim c(n) - r(n-1) - r(n)
-- pointwise, with all supports finite, then the alternating sums satisfy
-- Σ (-1)^n b(n) = Σ (-1)^n a(n) + Σ (-1)^n c(n).
omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsFiniteType k C] in
lemma eulerSum_of_rank_identity
    (E : C) {a b c : ℤ → C} {r : ℤ → ℤ}
    (hrank : ∀ n : ℤ, (Module.finrank k (E ⟶ b n) : ℤ) =
      Module.finrank k (E ⟶ a n) + Module.finrank k (E ⟶ c n) - r (n - 1) - r n)
    (hfin_a : Set.Finite {n : ℤ | Nontrivial (E ⟶ a n)})
    (hfin_b : Set.Finite {n : ℤ | Nontrivial (E ⟶ b n)})
    (hfin_c : Set.Finite {n : ℤ | Nontrivial (E ⟶ c n)})
    (hr : (Function.support r).Finite) :
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * Module.finrank k (E ⟶ b n)) =
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * Module.finrank k (E ⟶ a n)) +
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * Module.finrank k (E ⟶ c n)) := by
  let fa : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * Module.finrank k (E ⟶ a n)
  let fb : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * Module.finrank k (E ⟶ b n)
  let fc : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * Module.finrank k (E ⟶ c n)
  let fr : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * (-r (n - 1) - r n)
  have hfa : (Function.support fa).Finite := by
    refine Set.Finite.subset hfin_a ?_
    intro n hn
    have hfinrank_ne : (Module.finrank k (E ⟶ a n) : ℤ) ≠ 0 := by
      intro h0
      apply hn
      simp [fa, h0]
    letI : Nontrivial (E ⟶ a n) :=
      Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero (by exact_mod_cast hfinrank_ne))
    show Nontrivial (E ⟶ a n)
    infer_instance
  have hfb : (Function.support fb).Finite := by
    refine Set.Finite.subset hfin_b ?_
    intro n hn
    have hfinrank_ne : (Module.finrank k (E ⟶ b n) : ℤ) ≠ 0 := by
      intro h0
      apply hn
      simp [fb, h0]
    letI : Nontrivial (E ⟶ b n) :=
      Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero (by exact_mod_cast hfinrank_ne))
    show Nontrivial (E ⟶ b n)
    infer_instance
  have hfc : (Function.support fc).Finite := by
    refine Set.Finite.subset hfin_c ?_
    intro n hn
    have hfinrank_ne : (Module.finrank k (E ⟶ c n) : ℤ) ≠ 0 := by
      intro h0
      apply hn
      simp [fc, h0]
    letI : Nontrivial (E ⟶ c n) :=
      Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero (by exact_mod_cast hfinrank_ne))
    show Nontrivial (E ⟶ c n)
    infer_instance
  -- Rewrite b(n) using hrank: b(n) = a(n) + c(n) - r(n-1) - r(n)
  have key : ∀ n, (n.negOnePow : ℤ) * (Module.finrank k (E ⟶ b n) : ℤ) =
      (n.negOnePow : ℤ) * Module.finrank k (E ⟶ a n) +
      (n.negOnePow : ℤ) * Module.finrank k (E ⟶ c n) +
      (n.negOnePow : ℤ) * (-r (n - 1) - r n) := fun n ↦ by rw [hrank]; ring
  simp_rw [key]
  -- Goal: Σ (x + y + z) = Σ x + Σ y where z cancels
  -- Suffices: Σ z = 0
  suffices hz : ∑ᶠ n : ℤ, fr n = 0 by
    have hfac : (Function.support (fun n : ℤ ↦ fa n + fc n)).Finite :=
      Set.Finite.subset (hfa.union hfc) (Function.support_add _ _)
    have hr_shift : (Function.support fun n : ℤ ↦ r (n - 1)).Finite := by
      refine Set.Finite.subset (hr.image fun m : ℤ ↦ m + 1) ?_
      intro n hn
      refine ⟨n - 1, hn, by simp⟩
    have hfr : (Function.support fr).Finite := by
      refine Set.Finite.subset (hr_shift.union hr) ?_
      intro n hn
      by_cases h1 : r (n - 1) = 0
      · by_cases h2 : r n = 0
        · exfalso
          apply hn
          simp [fr, h1, h2]
        · exact Or.inr h2
      · exact Or.inl h1
    let lhs : ℤ := finsum (fun n : ℤ ↦ (fa n + fc n) + fr n)
    let rhs : ℤ := finsum fa + finsum fc
    have hsum := by
      show lhs = rhs
      dsimp [lhs, rhs]
      rw [finsum_add_distrib hfac]
      · rw [finsum_add_distrib hfa hfc, hz]
        simp
      · exact hfr
    simpa [fa, fc, fr, lhs, rhs]
  -- Expand: (-1)^n * (-r(n-1) - r(n)) = -((-1)^n * r(n-1)) - ((-1)^n * r(n))
  change ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (-r (n - 1) - r n) = 0
  simp_rw [show ∀ n : ℤ, (n.negOnePow : ℤ) * (-r (n - 1) - r n) =
      -(((n : ℤ).negOnePow : ℤ) * r (n - 1)) - ((n : ℤ).negOnePow : ℤ) * r n from
    fun n ↦ by ring]
  -- = -Σ (-1)^n r(n-1) - Σ (-1)^n r(n) by finsum_neg + finsum_sub
  rw [show (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r (n - 1)) -
      ((n : ℤ).negOnePow : ℤ) * r n) =
    fun n : ℤ ↦ (-(((n : ℤ).negOnePow : ℤ) * r (n - 1)) +
      (-(((n : ℤ).negOnePow : ℤ) * r n))) from by ext; ring]
  have hr_shift : (Function.support (fun n : ℤ ↦ r (n - 1))).Finite := by
    refine Set.Finite.subset (hr.image fun m : ℤ ↦ m + 1) ?_
    intro n hn
    refine ⟨n - 1, hn, by simp⟩
  have hfs1 : (Function.support (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r (n - 1)))).Finite := by
    apply hr_shift.subset; intro n hn
    simp only [Function.mem_support, neg_ne_zero, mul_ne_zero_iff] at hn
    exact hn.2
  have hfs2 : (Function.support (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r n))).Finite := by
    apply hr.subset; intro n hn
    simp only [Function.mem_support, neg_ne_zero, mul_ne_zero_iff] at hn
    exact hn.2
  rw [finsum_add_distrib hfs1 hfs2]
  simp only [finsum_neg_distrib]
  linarith [finsum_alternating_shift_cancel (r := r)]

-- A version of `eulerSum_of_rank_identity` for arbitrary finitely-supported integer-valued
-- sequences. This is used for the covariant Euler form, where the varying object appears in the
-- first argument of `Hom`.
lemma eulerSum_of_rank_identity_int {a b c r : ℤ → ℤ}
    (hrank : ∀ n : ℤ, b n = a n + c n - r (n - 1) - r n)
    (hfa : (Function.support a).Finite)
    (hfc : (Function.support c).Finite)
    (hr : (Function.support r).Finite) :
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * b n) =
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * a n) +
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * c n) := by
  let fa : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * a n
  let fc : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * c n
  let fr : ℤ → ℤ := fun n ↦ (n.negOnePow : ℤ) * (-r (n - 1) - r n)
  have hfa' : (Function.support fa).Finite := by
    refine Set.Finite.subset hfa ?_
    intro n hn
    simp [Function.mem_support, fa] at hn ⊢
    intro ha
    exact hn (by simp [ha])
  have hfc' : (Function.support fc).Finite := by
    refine Set.Finite.subset hfc ?_
    intro n hn
    simp [Function.mem_support, fc] at hn ⊢
    intro hc
    exact hn (by simp [hc])
  have key : ∀ n, (n.negOnePow : ℤ) * b n =
      (n.negOnePow : ℤ) * a n +
      (n.negOnePow : ℤ) * c n +
      (n.negOnePow : ℤ) * (-r (n - 1) - r n) := fun n ↦ by
    rw [hrank]
    ring
  simp_rw [key]
  suffices hz : ∑ᶠ n : ℤ, fr n = 0 by
    have hfac : (Function.support (fun n : ℤ ↦ fa n + fc n)).Finite :=
      Set.Finite.subset (hfa'.union hfc') (Function.support_add _ _)
    have hr_shift : (Function.support fun n : ℤ ↦ r (n - 1)).Finite := by
      refine Set.Finite.subset (hr.image fun m : ℤ ↦ m + 1) ?_
      intro n hn
      refine ⟨n - 1, hn, by simp⟩
    have hfr : (Function.support fr).Finite := by
      refine Set.Finite.subset (hr_shift.union hr) ?_
      intro n hn
      by_cases h1 : r (n - 1) = 0
      · by_cases h2 : r n = 0
        · exfalso
          apply hn
          simp [fr, h1, h2]
        · exact Or.inr h2
      · exact Or.inl h1
    let lhs : ℤ := finsum (fun n : ℤ ↦ (fa n + fc n) + fr n)
    let rhs : ℤ := finsum fa + finsum fc
    have hsum : lhs = rhs := by
      dsimp [lhs, rhs]
      rw [finsum_add_distrib hfac]
      · rw [finsum_add_distrib hfa' hfc', hz]
        simp
      · exact hfr
    simpa [fa, fc, fr, lhs, rhs]
  change ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (-r (n - 1) - r n) = 0
  simp_rw [show ∀ n : ℤ, (n.negOnePow : ℤ) * (-r (n - 1) - r n) =
      -(((n : ℤ).negOnePow : ℤ) * r (n - 1)) - ((n : ℤ).negOnePow : ℤ) * r n from
    fun n ↦ by ring]
  have hr_shift : (Function.support (fun n : ℤ ↦ r (n - 1))).Finite := by
    refine Set.Finite.subset (hr.image fun m : ℤ ↦ m + 1) ?_
    intro n hn
    refine ⟨n - 1, hn, by simp⟩
  have hfs1 : (Function.support (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r (n - 1)))).Finite := by
    apply hr_shift.subset
    intro n hn
    simp only [Function.mem_support, neg_ne_zero, mul_ne_zero_iff] at hn
    exact hn.2
  have hfs2 : (Function.support (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r n))).Finite := by
    apply hr.subset
    intro n hn
    simp only [Function.mem_support, neg_ne_zero, mul_ne_zero_iff] at hn
    exact hn.2
  rw [show (fun n : ℤ ↦ -(((n : ℤ).negOnePow : ℤ) * r (n - 1)) -
      ((n : ℤ).negOnePow : ℤ) * r n) =
    fun n : ℤ ↦ (-(((n : ℤ).negOnePow : ℤ) * r (n - 1)) +
      (-(((n : ℤ).negOnePow : ℤ) * r n))) from by
    ext
    ring]
  rw [finsum_add_distrib hfs1 hfs2]
  simp only [finsum_neg_distrib]
  linarith [finsum_alternating_shift_cancel (r := r)]

-- For a middle-exact sequence in AddCommGrpCat that is also k-linear,
-- the range/ker equality lifts from abelian groups to k-modules.
omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsFiniteType k C] in
lemma linearRange_eq_linearKer_of_ab_exact {A B C' : C} (E : C)
    (f : A ⟶ B) (g : B ⟶ C') (hfg : f ≫ g = 0)
    (hexact : ∀ (x : E ⟶ B), x ≫ g = 0 → ∃ y : E ⟶ A, y ≫ f = x) :
    LinearMap.range (Linear.rightComp k E f) = LinearMap.ker (Linear.rightComp k E g) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Linear.rightComp_apply]
  constructor
  · rintro ⟨y, rfl⟩; rw [Category.assoc, hfg, comp_zero]
  · intro hx; exact hexact x hx

lemma linearMap_range_eq_ker_of_addMonoidHom {V W X : Type v}
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    [AddCommGroup X] [Module k X]
    (f : V →ₗ[k] W) (g : W →ₗ[k] X)
    (h : f.toAddMonoidHom.range = g.toAddMonoidHom.ker) :
    LinearMap.range f = LinearMap.ker g := by
  ext x
  change x ∈ f.toAddMonoidHom.range ↔ x ∈ g.toAddMonoidHom.ker
  rw [h]

noncomputable instance linearCoyonedaObjIsHomological (E : C) :
    (((linearCoyoneda k C).obj (Opposite.op E)) : C ⥤ ModuleCat k).IsHomological where
  exact T hT := by
    rw [ShortComplex.exact_iff_exact_map_forget₂]
    simpa using ((preadditiveCoyoneda.obj (Opposite.op E)).map_distinguished_exact T hT)

section EulerTriangleAdditivity

omit [IsTriangulated C]

-- ANCHOR: CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive
theorem eulerFormObj_contravariant_triangleAdditive (E : C) :
    IsTriangleAdditive (fun F ↦ eulerFormObj k C E F) where
  additive := fun T hT ↦ by
    simp only [eulerFormObj]
    let F : C ⥤ ModuleCat k := (linearCoyoneda k C).obj (Opposite.op E)
    letI : F.ShiftSequence ℤ := Functor.ShiftSequence.tautological F ℤ
    letI : F.IsHomological := linearCoyonedaObjIsHomological (k := k) (C := C) E
    let δ_lin : (n : ℤ) → ((E ⟶ T.obj₃⟦n⟧) →ₗ[k] (E ⟶ T.obj₁⟦(n + 1)⟧)) := fun n ↦
      Linear.rightComp k E (T.mor₃⟦n⟧' ≫
        (shiftFunctorAdd' C 1 n (n + 1) (by lia)).inv.app T.obj₁)
    let r : ℤ → ℤ := fun n ↦ Module.finrank k (LinearMap.range (δ_lin n))
    have hδ_eq : ∀ n : ℤ, ((F.homologySequenceδ T n (n + 1) rfl).hom) = δ_lin n := by
      intro n
      ext x
      simpa [F, δ_lin] using
        (CategoryTheory.Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply
          (C := C) (T := T) (n₀ := n) (n₁ := n + 1) (h := rfl) (A := Opposite.op E) x)
    have h_ker_f_aux : ∀ m : ℤ,
        Module.finrank k (LinearMap.ker (((F.shift (m + 1)).map T.mor₁).hom)) = r m := by
      intro m
      let f_succ : (E ⟶ T.obj₁⟦m + 1⟧) →ₗ[k] (E ⟶ T.obj₂⟦m + 1⟧) :=
        ((F.shift (m + 1)).map T.mor₁).hom
      have h_exact₁ : LinearMap.range (δ_lin m) = LinearMap.ker f_succ := by
        simpa [f_succ, hδ_eq m] using
          (ShortComplex.Exact.moduleCat_range_eq_ker
            (F.homologySequence_exact₁ T hT m (m + 1) rfl))
      simpa [r] using
        congrArg (fun V : Submodule k (E ⟶ T.obj₁⟦m + 1⟧) => Module.finrank k V) h_exact₁.symm
    have hrank : ∀ n : ℤ,
        (Module.finrank k (E ⟶ T.obj₂⟦n⟧) : ℤ) =
        Module.finrank k (E ⟶ T.obj₁⟦n⟧) + Module.finrank k (E ⟶ T.obj₃⟦n⟧) -
          r (n - 1) - r n := by
      intro n
      let f_n : (E ⟶ T.obj₁⟦n⟧) →ₗ[k] (E ⟶ T.obj₂⟦n⟧) := ((F.shift n).map T.mor₁).hom
      let g_n : (E ⟶ T.obj₂⟦n⟧) →ₗ[k] (E ⟶ T.obj₃⟦n⟧) := ((F.shift n).map T.mor₂).hom
      have hexact_B : LinearMap.range f_n = LinearMap.ker g_n := by
        simpa [f_n, g_n, F] using
          (ShortComplex.Exact.moduleCat_range_eq_ker
            (F.homologySequence_exact₂ T hT n))
      haveI : Module.Finite k (E ⟶ T.obj₂⟦n⟧) := IsFiniteType.finite_dim (k := k) E (T.obj₂⟦n⟧)
      have h_mid := finrank_mid_of_exact k f_n g_n hexact_B
      haveI : Module.Finite k (E ⟶ T.obj₁⟦n⟧) := IsFiniteType.finite_dim (k := k) E (T.obj₁⟦n⟧)
      haveI : Module.Finite k (E ⟶ T.obj₃⟦n⟧) := IsFiniteType.finite_dim (k := k) E (T.obj₃⟦n⟧)
      have h_ker_f : Module.finrank k (LinearMap.ker f_n) = r (n - 1) := by
        change Module.finrank k (LinearMap.ker (((F.shift n).map T.mor₁).hom)) = r (n - 1)
        have hn : n = (n - 1) + 1 := by lia
        rw [hn]
        simpa using h_ker_f_aux (n - 1)
      have h_ker_δ : Module.finrank k (LinearMap.ker (δ_lin n)) =
          Module.finrank k (LinearMap.range g_n) := by
        have h_exact₃ : LinearMap.range g_n = LinearMap.ker (δ_lin n) := by
          simpa [g_n, hδ_eq n] using
            (ShortComplex.Exact.moduleCat_range_eq_ker
              (F.homologySequence_exact₃ T hT n (n + 1) rfl))
        simpa using
          congrArg (fun V : Submodule k (E ⟶ T.obj₃⟦n⟧) => Module.finrank k V) h_exact₃.symm
      have h_f : (Module.finrank k (LinearMap.range f_n) : ℤ) =
          Module.finrank k (E ⟶ T.obj₁⟦n⟧) - r (n - 1) := by
        have := f_n.finrank_range_add_finrank_ker
        lia
      have h_g : (Module.finrank k (LinearMap.range g_n) : ℤ) =
          Module.finrank k (E ⟶ T.obj₃⟦n⟧) - r n := by
        have h1 := (δ_lin n).finrank_range_add_finrank_ker
        have h2 := h_ker_δ
        simp only [r] at h2 ⊢
        lia
      linarith
    have hr : (Function.support r).Finite := by
      refine Set.Finite.subset
        ((IsFiniteType.finite_support (k := k) E T.obj₁).image fun m : ℤ ↦ m - 1) ?_
      intro n hn
      have hnonzero : (r n : ℤ) ≠ 0 := hn
      have hnontrivial : Nontrivial (E ⟶ T.obj₁⟦n + 1⟧) := by
        by_contra htriv
        haveI : Subsingleton (E ⟶ T.obj₁⟦n + 1⟧) := not_nontrivial_iff_subsingleton.mp htriv
        have hδ : δ_lin n = 0 := by
          ext x
          exact Subsingleton.elim _ _
        apply hnonzero
        simp [r]
      exact ⟨n + 1, hnontrivial, by simp⟩
    exact eulerSum_of_rank_identity (k := k) (C := C) E
      (a := fun n ↦ T.obj₁⟦n⟧)
      (b := fun n ↦ T.obj₂⟦n⟧)
      (c := fun n ↦ T.obj₃⟦n⟧)
      (r := r)
      hrank
      (by simpa using IsFiniteType.finite_support (k := k) E T.obj₁)
      (by simpa using IsFiniteType.finite_support (k := k) E T.obj₂)
      (by simpa using IsFiniteType.finite_support (k := k) E T.obj₃)
      hr
-- ANCHOR_END: CategoryTheory.Triangulated.eulerFormObj_contravariant_triangleAdditive

-- The covariant Euler form `E ↦ χ(E,F)` is triangle-additive.
-- Same argument applied to the preadditiveYoneda functor.
theorem eulerFormObj_covariant_triangleAdditive (F : C)
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    IsTriangleAdditive (fun E ↦ eulerFormObj k C E F) where
  additive := fun T hT ↦ by
    simp only [eulerFormObj]
    let Top : Triangle Cᵒᵖ := (triangleOpEquivalence C).functor.obj (Opposite.op T)
    have hTop : Top ∈ distTriang Cᵒᵖ := op_distinguished T hT
    let G : Cᵒᵖ ⥤ AddCommGrpCat := preadditiveYoneda.obj F
    let δ_lin : (n : ℤ) → ((T.obj₁ ⟶ F⟦n⟧) →ₗ[k] (T.obj₃ ⟶ F⟦(n + 1)⟧)) := fun n ↦
      { toFun := fun x =>
          T.mor₃ ≫ x⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C n 1 (n + 1) (by lia)).inv.app F
        map_add' := by
          intro x y
          simp [Functor.map_add]
        map_smul' := by
          intro r x
          simp [Functor.map_smul] }
    let r : ℤ → ℤ := fun n ↦ Module.finrank k (LinearMap.range (δ_lin n))
    have hδ_eq : ∀ n : ℤ,
        G.homologySequenceδ Top n (n + 1) rfl =
          AddCommGrpCat.ofHom (δ_lin n).toAddMonoidHom := by
      intro n
      ext x
      simpa [Top, δ_lin, G] using
        (CategoryTheory.Pretriangulated.preadditiveYoneda_homologySequenceδ_apply
          (C := C) (T := T) (n₀ := n) (n₁ := n + 1) (h := rfl) (B := F) x)
    have hmap₁ : ∀ n : ℤ,
        (G.shift n).map Top.mor₁ =
          AddCommGrpCat.ofHom (Linear.leftComp k (F⟦n⟧) T.mor₂).toAddMonoidHom := by
      intro n
      ext x
      rfl
    have hmap₂ : ∀ n : ℤ,
        (G.shift n).map Top.mor₂ =
          AddCommGrpCat.ofHom (Linear.leftComp k (F⟦n⟧) T.mor₁).toAddMonoidHom := by
      intro n
      ext x
      rfl
    have h_ker_f_aux : ∀ m : ℤ,
        Module.finrank k (LinearMap.ker (Linear.leftComp k (F⟦m + 1⟧) T.mor₂)) = r m := by
      intro m
      let f_succ : (T.obj₃ ⟶ F⟦m + 1⟧) →ₗ[k] (T.obj₂ ⟶ F⟦m + 1⟧) :=
        Linear.leftComp k (F⟦m + 1⟧) T.mor₂
      have h_exact₁_ab0 :=
        (ShortComplex.Exact.ab_range_eq_ker
          (G.homologySequence_exact₁ Top hTop m (m + 1) rfl))
      have h_exact₁_ab : ((δ_lin m).toAddMonoidHom).range = (f_succ.toAddMonoidHom).ker := by
        change (AddCommGrpCat.Hom.hom (G.homologySequenceδ Top m (m + 1) rfl)).range =
          (AddCommGrpCat.Hom.hom ((G.shift (m + 1)).map Top.mor₁)).ker at h_exact₁_ab0
        simpa [hδ_eq m, hmap₁ (m + 1), f_succ] using h_exact₁_ab0
      have h_exact₁ : LinearMap.range (δ_lin m) = LinearMap.ker f_succ :=
        linearMap_range_eq_ker_of_addMonoidHom (k := k) (δ_lin m) f_succ h_exact₁_ab
      simpa [r] using
        congrArg (fun V : Submodule k (T.obj₃ ⟶ F⟦m + 1⟧) => Module.finrank k V) h_exact₁.symm
    have hrank : ∀ n : ℤ,
        (Module.finrank k (T.obj₂ ⟶ F⟦n⟧) : ℤ) =
        Module.finrank k (T.obj₃ ⟶ F⟦n⟧) + Module.finrank k (T.obj₁ ⟶ F⟦n⟧) -
          r (n - 1) - r n := by
      intro n
      let f_n : (T.obj₃ ⟶ F⟦n⟧) →ₗ[k] (T.obj₂ ⟶ F⟦n⟧) := Linear.leftComp k (F⟦n⟧) T.mor₂
      let g_n : (T.obj₂ ⟶ F⟦n⟧) →ₗ[k] (T.obj₁ ⟶ F⟦n⟧) := Linear.leftComp k (F⟦n⟧) T.mor₁
      have hexact_B_ab0 :=
        (ShortComplex.Exact.ab_range_eq_ker
          (G.homologySequence_exact₂ Top hTop n))
      have hexact_B_ab : (f_n.toAddMonoidHom).range = (g_n.toAddMonoidHom).ker := by
        change (AddCommGrpCat.Hom.hom ((G.shift n).map Top.mor₁)).range =
          (AddCommGrpCat.Hom.hom ((G.shift n).map Top.mor₂)).ker at hexact_B_ab0
        simpa [hmap₁ n, hmap₂ n, f_n, g_n] using hexact_B_ab0
      have hexact_B : LinearMap.range f_n = LinearMap.ker g_n :=
        linearMap_range_eq_ker_of_addMonoidHom (k := k) f_n g_n hexact_B_ab
      haveI : Module.Finite k (T.obj₂ ⟶ F⟦n⟧) := IsFiniteType.finite_dim (k := k) T.obj₂ (F⟦n⟧)
      have h_mid := finrank_mid_of_exact k f_n g_n hexact_B
      haveI : Module.Finite k (T.obj₃ ⟶ F⟦n⟧) := IsFiniteType.finite_dim (k := k) T.obj₃ (F⟦n⟧)
      haveI : Module.Finite k (T.obj₁ ⟶ F⟦n⟧) := IsFiniteType.finite_dim (k := k) T.obj₁ (F⟦n⟧)
      have h_ker_f : Module.finrank k (LinearMap.ker f_n) = r (n - 1) := by
        have h_ker_f' :
            Module.finrank k
              (LinearMap.ker (Linear.leftComp k (F⟦n - 1 + 1⟧) T.mor₂)) = r (n - 1) := by
          simpa using h_ker_f_aux (n - 1)
        have hshift : F⟦n - 1 + 1⟧ = F⟦n⟧ :=
          congrArg (fun m : ℤ => (shiftFunctor C m).obj F) (by simp)
        rw [hshift] at h_ker_f'
        simpa [f_n] using h_ker_f'
      have h_ker_δ : Module.finrank k (LinearMap.ker (δ_lin n)) =
          Module.finrank k (LinearMap.range g_n) := by
        have h_exact₃_ab0 :=
          (ShortComplex.Exact.ab_range_eq_ker
            (G.homologySequence_exact₃ Top hTop n (n + 1) rfl))
        have h_exact₃_ab : (g_n.toAddMonoidHom).range = ((δ_lin n).toAddMonoidHom).ker := by
          change (AddCommGrpCat.Hom.hom ((G.shift n).map Top.mor₂)).range =
            (AddCommGrpCat.Hom.hom (G.homologySequenceδ Top n (n + 1) rfl)).ker at h_exact₃_ab0
          simpa [hδ_eq n, hmap₂ n, g_n] using h_exact₃_ab0
        have h_exact₃ : LinearMap.range g_n = LinearMap.ker (δ_lin n) :=
          linearMap_range_eq_ker_of_addMonoidHom (k := k) g_n (δ_lin n) h_exact₃_ab
        simpa using
          congrArg (fun V : Submodule k (T.obj₁ ⟶ F⟦n⟧) => Module.finrank k V) h_exact₃.symm
      have h_f : (Module.finrank k (LinearMap.range f_n) : ℤ) =
          Module.finrank k (T.obj₃ ⟶ F⟦n⟧) - r (n - 1) := by
        have := f_n.finrank_range_add_finrank_ker
        lia
      have h_g : (Module.finrank k (LinearMap.range g_n) : ℤ) =
          Module.finrank k (T.obj₁ ⟶ F⟦n⟧) - r n := by
        have h1 := (δ_lin n).finrank_range_add_finrank_ker
        have h2 := h_ker_δ
        simp only [r] at h2 ⊢
        lia
      linarith
    have hr : (Function.support r).Finite := by
      refine Set.Finite.subset
        ((IsFiniteType.finite_support (k := k) T.obj₃ F).image fun m : ℤ ↦ m - 1) ?_
      intro n hn
      have hnonzero : (r n : ℤ) ≠ 0 := hn
      have hnontrivial : Nontrivial (T.obj₃ ⟶ F⟦n + 1⟧) := by
        by_contra htriv
        haveI : Subsingleton (T.obj₃ ⟶ F⟦n + 1⟧) := not_nontrivial_iff_subsingleton.mp htriv
        have hδ : δ_lin n = 0 := by
          ext x
          exact Subsingleton.elim _ _
        apply hnonzero
        simp [r]
      exact ⟨n + 1, hnontrivial, by simp⟩
    let a : ℤ → ℤ := fun n ↦ Module.finrank k (T.obj₃ ⟶ F⟦n⟧)
    let b : ℤ → ℤ := fun n ↦ Module.finrank k (T.obj₂ ⟶ F⟦n⟧)
    let c : ℤ → ℤ := fun n ↦ Module.finrank k (T.obj₁ ⟶ F⟦n⟧)
    have hfa : (Function.support a).Finite := by
      refine Set.Finite.subset (IsFiniteType.finite_support (k := k) T.obj₃ F) ?_
      intro n hn
      have hfinrank_ne : (Module.finrank k (T.obj₃ ⟶ F⟦n⟧) : ℤ) ≠ 0 := hn
      letI : Nontrivial (T.obj₃ ⟶ F⟦n⟧) :=
        Module.nontrivial_of_finrank_pos (R := k)
          (Nat.pos_of_ne_zero (by exact_mod_cast hfinrank_ne))
      show Nontrivial (T.obj₃ ⟶ F⟦n⟧)
      infer_instance
    have hfc : (Function.support c).Finite := by
      refine Set.Finite.subset (IsFiniteType.finite_support (k := k) T.obj₁ F) ?_
      intro n hn
      have hfinrank_ne : (Module.finrank k (T.obj₁ ⟶ F⟦n⟧) : ℤ) ≠ 0 := hn
      letI : Nontrivial (T.obj₁ ⟶ F⟦n⟧) :=
        Module.nontrivial_of_finrank_pos (R := k)
          (Nat.pos_of_ne_zero (by exact_mod_cast hfinrank_ne))
      show Nontrivial (T.obj₁ ⟶ F⟦n⟧)
      infer_instance
    simpa [a, b, c, add_comm] using
      eulerSum_of_rank_identity_int (hrank := hrank) hfa hfc hr

end EulerTriangleAdditivity

/-! ## Euler form on `K₀` -/

-- ANCHOR: CategoryTheory.Triangulated.eulerFormInner
/-- For fixed `E`, lift `F ↦ χ(E, F)` to a group homomorphism `K₀ C →+ ℤ`
using the universal property of `K₀`. -/
def eulerFormInner (E : C) : K₀ C →+ ℤ := by
  letI := eulerFormObj_contravariant_triangleAdditive (k := k) (C := C) E
  exact K₀.lift C (fun F ↦ eulerFormObj k C E F)
-- ANCHOR_END: CategoryTheory.Triangulated.eulerFormInner

-- ANCHOR: CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive
/-- The outer function `E ↦ eulerFormInner E` is triangle-additive, so the Euler
form descends to a bilinear form on `K₀`. -/
instance eulerFormInner_isTriangleAdditive
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    IsTriangleAdditive (eulerFormInner k C) where
  additive T hT := by
    apply K₀.hom_ext; intro F
    simp only [AddMonoidHom.add_apply, eulerFormInner, K₀.lift_of]
    letI := eulerFormObj_covariant_triangleAdditive (k := k) (C := C) F
    exact IsTriangleAdditive.additive (f := fun E ↦ eulerFormObj k C E F) T hT
-- ANCHOR_END: CategoryTheory.Triangulated.eulerFormInner_isTriangleAdditive

-- ANCHOR: CategoryTheory.Triangulated.eulerForm
/-- The Euler form on `K₀`, obtained by applying the universal property of `K₀`
twice to `eulerFormObj`. -/
def eulerForm [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ K₀ C →+ ℤ :=
  K₀.lift C (eulerFormInner k C)
-- ANCHOR_END: CategoryTheory.Triangulated.eulerForm

-- ANCHOR: CategoryTheory.Triangulated.eulerFormRad
/-- The left radical of the Euler form on `K₀ C`. -/
def eulerFormRad [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddSubgroup (K₀ C) :=
  (eulerForm k C).ker
-- ANCHOR_END: CategoryTheory.Triangulated.eulerFormRad

-- ANCHOR: CategoryTheory.Triangulated.NumericalK₀
/-- The numerical Grothendieck group attached to the Euler form on `K₀`. -/
def NumericalK₀ [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k] :
    Type _ :=
  K₀ C ⧸ eulerFormRad k C
-- ANCHOR_END: CategoryTheory.Triangulated.NumericalK₀

-- ANCHOR: CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup
/-- The `AddCommGroup` instance on `NumericalK₀ k C`. -/
instance NumericalK₀.instAddCommGroup [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    AddCommGroup (NumericalK₀ k C) :=
  inferInstanceAs (AddCommGroup (K₀ C ⧸ eulerFormRad k C))
-- ANCHOR_END: CategoryTheory.Triangulated.NumericalK₀.instAddCommGroup

-- ANCHOR: CategoryTheory.Triangulated.numericalQuotientMap
/-- The quotient map `K₀(C) → N(C)`. -/
abbrev numericalQuotientMap [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] :
    K₀ C →+ NumericalK₀ k C :=
  QuotientAddGroup.mk' (eulerFormRad k C)
-- ANCHOR_END: CategoryTheory.Triangulated.numericalQuotientMap

-- ANCHOR: CategoryTheory.Triangulated.NumericallyFinite
/-- The category `C` is numerically finite if the numerical Grothendieck group attached to the
Euler form is finitely generated as an abelian group. -/
class NumericallyFinite [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] : Prop where
  /-- The Euler-form numerical Grothendieck group is finitely generated. -/
  fg : AddGroup.FG (NumericalK₀ k C)
-- ANCHOR_END: CategoryTheory.Triangulated.NumericallyFinite

/-- Instance synthesis for the finite generation of the numerical Grothendieck group. -/
instance [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k]
    [NumericallyFinite k C] : AddGroup.FG (NumericalK₀ k C) :=
  NumericallyFinite.fg

/-- Numerical stability conditions are stability conditions whose central charge factors through
the canonical numerical quotient map `K₀(C) → N(C)`. -/
abbrev NumericalStabilityCondition [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k] : Type _ :=
  StabilityCondition.WithClassMap C (numericalQuotientMap k C)

/-! ## Corollary 1.3 packaging -/

/-- The local-homeomorphism package for connected components of numerical stability conditions.
This is the proposition-object behind Bridgeland's Corollary 1.3. -/
abbrev NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents
    [Linear k C] [IsFiniteType k C] [(shiftFunctor C (1 : ℤ)).Linear k] : Prop :=
  StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents
    (C := C) (Λ := NumericalK₀ k C) (v := numericalQuotientMap k C)

-- ANCHOR: CategoryTheory.Triangulated.NumericalComponent
/-- A connected component of numerical stability conditions. -/
abbrev NumericalComponent [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :=
  StabilityCondition.WithClassMap.Component C (numericalQuotientMap k C) cc
-- ANCHOR_END: CategoryTheory.Triangulated.NumericalComponent

end CategoryTheory.Triangulated
