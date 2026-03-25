/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityFunction.MDQ

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex Real

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]


/-!
# HN Filtration Uniqueness and Intrinsic Phases

Uniqueness of HN filtrations, intrinsic phiPlus/phiMinus bounds.
-/

/-- If `E` is semistable and has an HN filtration, the filtration has exactly one factor. -/
private lemma hn_n_eq_one_of_semistable (Z : StabilityFunction A) {E : A}
    (hss : Z.IsSemistable E) (F : AbelianHNFiltration Z E) :
    F.n = 1 := by
  by_contra hn1
  have hhn := F.hn
  have hn_ge : 1 < F.n := by lia
  -- chain(1) is nonzero (since chain is strict mono and chain(0) = ⊥ < chain(1))
  have hchain1_ne_bot : F.chain ⟨1, by lia⟩ ≠ ⊥ := by
    intro heq
    have h01 : F.chain ⟨0, by lia⟩ < F.chain ⟨1, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    rw [F.chain_bot, heq] at h01
    exact lt_irrefl _ h01
  -- chain(0) as Fin F.n .castSucc = ⊥
  have h0_eq : F.chain (⟨0, F.hn⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  -- chain(1) = (⟨0, F.hn⟩ : Fin F.n).succ
  have h1_eq : (⟨0, F.hn⟩ : Fin F.n).succ = ⟨1, by lia⟩ := rfl
  -- phase(chain(1)) = φ(0)
  have hchain1_phase : Z.phase (F.chain ⟨1, by lia⟩ : A) = F.φ ⟨0, F.hn⟩ := by
    rw [← F.factor_phase ⟨0, F.hn⟩]
    have hsucc_eq : F.chain (⟨0, F.hn⟩ : Fin F.n).succ = F.chain ⟨1, by lia⟩ := by
      rw [h1_eq]
    exact ((phase_cokernel_ofLE_congr Z h0_eq hsucc_eq).trans
      (Z.phase_eq_of_iso
        (StabilityFunction.Subobject.cokernelBotIso (F.chain ⟨1, by lia⟩) bot_le))).symm
  -- By semistability: φ(0) ≤ phase(E)
  have hφ0_le : F.φ ⟨0, F.hn⟩ ≤ Z.phase E := by
    rw [← hchain1_phase]
    exact hss.2 _ (StabilityFunction.subobject_not_isZero_of_ne_bot hchain1_ne_bot)
  -- chain(n-1) ≠ ⊤ since chain(n-1) < chain(n) = ⊤
  have hchain_ne_top : F.chain ⟨F.n - 1, by lia⟩ ≠ ⊤ := by
    intro heq
    have hlt : F.chain ⟨F.n - 1, by lia⟩ < F.chain ⟨F.n, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    rw [heq, F.chain_top] at hlt
    exact lt_irrefl _ hlt
  -- The last Fin n index
  set last : Fin F.n := ⟨F.n - 1, by lia⟩
  -- chain(last.succ) = chain(n) = ⊤
  have hchain_top' : F.chain last.succ = ⊤ := by
    have : last.succ = ⟨F.n, by lia⟩ := Fin.ext (show last.val + 1 = F.n by
      simp only [last]; lia)
    rw [this, F.chain_top]
  -- phase of cokernel of chain(n-1).arrow = φ(last)
  -- phase(E) ≤ φ(last): use phase_le_of_epi on the quotient map, then relate to factor_phase
  have hE_le_last : Z.phase E ≤ F.φ last := by
    have hle := phase_le_of_epi Z (cokernel.π (F.chain ⟨F.n - 1, by lia⟩).arrow) hss
      (cokernel_nonzero_of_ne_top hchain_ne_top)
    suffices Z.phase (cokernel (F.chain ⟨F.n - 1, by lia⟩).arrow) = F.φ last by linarith
    -- factor_phase last : phase(cokernel(ofLE chain(last.castSucc) chain(last.succ) _)) = φ last
    -- We need: phase(cokernel(chain(n-1).arrow)) = phase(cokernel(ofLE ...))
    -- Strategy: use phase_cokernel_ofLE_congr to normalize both sides
    -- then use cokernelBotIso-style argument
    -- Step 1: chain(n-1).arrow = ofLE chain(n-1) ⊤ le_top ≫ ⊤.arrow (by ofLE_arrow)
    -- Step 2: cokernel(chain(n-1).arrow) ≅ cokernel(ofLE chain(n-1) ⊤ le_top)
    --   (by cokernelCompIsIso)
    -- Step 3: cokernel(ofLE chain(n-1) ⊤ _) has same phase as cokernel(ofLE ... chain(last.succ) _)
    --         by phase_cokernel_ofLE_congr Z rfl hchain_top'.symm
    set S := F.chain ⟨F.n - 1, by lia⟩
    haveI : IsIso (⊤ : Subobject E).arrow := inferInstance
    calc Z.phase (cokernel S.arrow)
        = Z.phase (cokernel (Subobject.ofLE S ⊤ le_top)) :=
          Z.phase_eq_of_iso
            (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _)
      _ = Z.phase (cokernel (Subobject.ofLE (F.chain last.castSucc) (F.chain last.succ)
            (le_of_lt (F.chain_strictMono last.castSucc_lt_succ)))) :=
          phase_cokernel_ofLE_congr Z rfl hchain_top'.symm
      _ = F.φ last := F.factor_phase last
  -- But φ(last) < φ(0) since last > 0 and φ is strictly anti
  have hφ_lt : F.φ last < F.φ ⟨0, F.hn⟩ :=
    F.φ_anti (Fin.mk_lt_mk.mpr (by lia))
  linarith

/-- If `B.arrow ≫ cokernel.π M.arrow = 0`, then `B ≤ M` as subobjects of `E`. -/
private lemma le_of_comp_cokernel_zero {E : A} {B M : Subobject E}
    (h : B.arrow ≫ cokernel.π M.arrow = 0) : B ≤ M := by
  have hker : kernelSubobject (cokernel.π M.arrow) = M := by
    simpa [imageSubobject_mono, Subobject.mk_arrow] using
      ((ShortComplex.mk M.arrow (cokernel.π M.arrow)
        (cokernel.condition M.arrow)).exact_iff_image_eq_kernel.mp
        (ShortComplex.exact_cokernel M.arrow)).symm
  rw [← hker]
  exact Subobject.le_of_comm
    (factorThruKernelSubobject _ B.arrow h)
    (factorThruKernelSubobject_comp_arrow _ _ _)

/-- If the composition `ofLE B S _ ≫ cokernel.π (ofLE M S _) = 0`, then `B ≤ M`. -/
private lemma le_of_ofLE_comp_cokernel_zero {E : A} {B M S : Subobject E}
    (hBS : B ≤ S) (hMS : M ≤ S)
    (h : Subobject.ofLE B S hBS ≫
      cokernel.π (Subobject.ofLE M S hMS) = 0) : B ≤ M := by
  -- The SES M →(ofLE)→ S →(cokernel.π)→ cokernel gives a kernel fork
  have hse : (ShortComplex.mk (Subobject.ofLE M S hMS)
      (cokernel.π (Subobject.ofLE M S hMS))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  -- Lift ofLE B S through the kernel fork
  set g := hse.fIsKernel.lift (KernelFork.ofι (Subobject.ofLE B S hBS) h)
  have hg : g ≫ Subobject.ofLE M S hMS = Subobject.ofLE B S hBS :=
    hse.fIsKernel.fac (KernelFork.ofι (Subobject.ofLE B S hBS) h) WalkingParallelPair.zero
  -- Compose with S.arrow: g ≫ M.arrow = B.arrow
  have key : g ≫ M.arrow = B.arrow :=
    calc g ≫ M.arrow
        = g ≫ (Subobject.ofLE M S hMS ≫ S.arrow) := by
          congr 1; exact (Subobject.ofLE_arrow hMS).symm
      _ = (g ≫ Subobject.ofLE M S hMS) ≫ S.arrow :=
          (Category.assoc _ _ _).symm
      _ = Subobject.ofLE B S hBS ≫ S.arrow := by congr 1
      _ = B.arrow := Subobject.ofLE_arrow hBS
  exact Subobject.le_of_comm g key

/-- Hom-vanishing from a semistable object to an HN factor: if `B` is semistable
with `phase(B) > φ(j)`, then every morphism from `(B : A)` to the `j`-th factor
of the HN filtration is zero. Direct corollary of `hom_zero_of_semistable_phase_gt`. -/
private lemma hom_zero_to_factor {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : A} (hB : Z.IsSemistable B)
    (j : Fin F.n) (hph : F.φ j < Z.phase B)
    (f : B ⟶ cokernel (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
      (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))) : f = 0 :=
  hom_zero_of_semistable_phase_gt Z hB (F.factor_semistable j)
    (F.factor_phase j ▸ hph) f

/-- **Semistable descent lemma**: A semistable subobject `B` of `E` whose phase
exceeds `φ(j)` for all `j ≥ k` must satisfy `B ≤ chain(k)`. The proof descends
from `chain(n) = ⊤` using hom-vanishing to each factor. -/
private lemma semistable_le_chain_of_phase_gt {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E} (hB : Z.IsSemistable (B : A))
    {k : ℕ} (hk : k ≤ F.n)
    (hph : ∀ j : Fin F.n, k ≤ j.val → F.φ j < Z.phase (B : A)) :
    B ≤ F.chain ⟨k, by lia⟩ := by
  -- Descend from chain(n) = ⊤ to chain(k), one step at a time.
  -- Induct on d = F.n - k.
  suffices h : ∀ d m (hm : m < F.n + 1), F.n - m = d → k ≤ m →
      B ≤ F.chain ⟨m, hm⟩ from
    h (F.n - k) k (by lia) rfl le_rfl
  intro d
  induction d with
  | zero =>
    intro m hm hd hkm
    have hmn : m = F.n := by lia
    subst hmn; rw [F.chain_top]; exact le_top
  | succ d ih =>
    intro m hm hd hkm
    -- B ≤ chain(m+1) by IH
    have hstep : B ≤ F.chain ⟨m + 1, by lia⟩ :=
      ih (m + 1) (by lia) (by lia) (by lia)
    -- Factor at index m: semistable with phase φ(m) < phase(B)
    have hm_lt : m < F.n := by lia
    set j : Fin F.n := ⟨m, hm_lt⟩
    have hj_succ_eq : (j.succ : Fin (F.n + 1)) = ⟨m + 1, by lia⟩ :=
      Fin.ext (by simp [j])
    have hle_jsucc : B ≤ F.chain j.succ := hj_succ_eq ▸ hstep
    have hcomp : Subobject.ofLE B (F.chain j.succ) hle_jsucc ≫
        cokernel.π (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
          (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))) = 0 :=
      hom_zero_of_semistable_phase_gt Z hB (F.factor_semistable j)
        (F.factor_phase j ▸ hph j (by lia)) _
    exact le_of_ofLE_comp_cokernel_zero hle_jsucc
      (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) hcomp

/-- **Semistable descent**: A semistable subobject whose phase exceeds all HN phases
must be zero. Specifically, if `phase(B) > φ(0)`, then `B = ⊥`. -/
private lemma semistable_eq_bot_of_phase_gt_max {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E} (hB : Z.IsSemistable (B : A))
    (hph : F.φ ⟨0, F.hn⟩ < Z.phase (B : A)) : B = ⊥ := by
  have hle : B ≤ F.chain ⟨0, by lia⟩ :=
    semistable_le_chain_of_phase_gt F hB (Nat.zero_le _)
      (fun j _ ↦ lt_of_le_of_lt (F.φ_anti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hph)
  rw [F.chain_bot] at hle
  exact le_bot_iff.mp hle



/-- If `f` is epi, then `imageSubobject f = ⊤`. -/
private lemma imageSubobject_epi_eq_top {X Y : A} (f : X ⟶ Y) [Epi f] :
    imageSubobject f = ⊤ := by
  haveI : Epi (imageSubobject f).arrow :=
    epi_of_epi_fac (imageSubobject_arrow_comp f)
  haveI : IsIso (imageSubobject f).arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

/-- The phase of `chain(1)` in an HN filtration equals `φ(0)`. -/
private lemma chain_one_phase {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn2 : 2 ≤ F.n) :
    Z.phase (F.chain ⟨1, by lia⟩ : A) = F.φ ⟨0, F.hn⟩ := by
  rw [← F.factor_phase ⟨0, F.hn⟩]
  exact ((phase_cokernel_ofLE_congr Z F.chain_bot rfl).trans
    (Z.phase_eq_of_iso
      (StabilityFunction.Subobject.cokernelBotIso (F.chain ⟨1, by lia⟩) bot_le))).symm

/-- In an HN filtration with `n ≥ 2`, `chain(1)` equals the maximally destabilizing
subobject (MDS). -/
private lemma chain_one_eq_MDS {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn2 : 2 ≤ F.n)
    {M : Subobject E} (hM_ne : M ≠ ⊥) (hM_ss : Z.IsSemistable (M : A))
    (hM_max : ∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A))
    (hM_strict : ∀ B : Subobject E, M < B → Z.phase (B : A) < Z.phase (M : A)) :
    F.chain ⟨1, by lia⟩ = M := by
  have hchain1_ne : F.chain ⟨1, by lia⟩ ≠ ⊥ := by
    intro h
    have := F.chain_strictMono (show (⟨0, by lia⟩ : Fin (F.n + 1)) <
      ⟨1, by lia⟩ from Fin.mk_lt_mk.mpr (by lia))
    rw [F.chain_bot, h] at this
    exact lt_irrefl _ this
  have hphM : ∀ j : Fin F.n, 1 ≤ j.val → F.φ j < Z.phase (M : A) := by
    intro j hj
    calc F.φ j
        ≤ F.φ (⟨1, by lia⟩ : Fin F.n) :=
          F.φ_anti.antitone (Fin.mk_le_mk.mpr hj)
      _ < F.φ (⟨0, F.hn⟩ : Fin F.n) :=
          F.φ_anti (Fin.mk_lt_mk.mpr (by lia))
      _ = Z.phase (F.chain ⟨1, by lia⟩ : A) :=
          (chain_one_phase F hn2).symm
      _ ≤ Z.phase (M : A) := hM_max _ hchain1_ne
  -- M ≤ chain(1) via semistable descent
  have hM_le : M ≤ F.chain ⟨1, by lia⟩ :=
    semistable_le_chain_of_phase_gt F hM_ss (by lia) hphM
  -- chain(1) ≤ M: if M < chain(1), then phase(chain(1)) < phase(M), so φ(0) < phase(M),
  -- then semistable_eq_bot_of_phase_gt_max gives M = ⊥, contradiction
  rcases hM_le.eq_or_lt with h | hlt
  · exact h.symm
  · exfalso
    have hlt_phase := hM_strict _ hlt
    rw [chain_one_phase F hn2] at hlt_phase
    exact hM_ne (semistable_eq_bot_of_phase_gt_max F hM_ss hlt_phase)

/-- For `M ≤ S` as subobjects of `E`, the pullback of `imageSubobject(S.arrow ≫ p)` along
`p = cokernel.π M.arrow` equals `S`. Uses the Z-value trick: `Z(pb(I)) = Z(S)` forces
the cokernel of the inclusion `S ↪ pb(I)` to be zero. -/
private lemma pullback_imageSubobject_eq (Z : StabilityFunction A) {E : A}
    {M S : Subobject E} (hMS : M ≤ S) :
    (Subobject.pullback (cokernel.π M.arrow)).obj
      (imageSubobject (S.arrow ≫ cokernel.π M.arrow)) = S := by
  set p := cokernel.π M.arrow
  set I := imageSubobject (S.arrow ≫ p)
  set pbI := (Subobject.pullback p).obj I
  -- S ≤ pb(I) via the pullback universal property
  have hle : S ≤ pbI := Subobject.le_of_comm
    ((Subobject.isPullback p I).isLimit.lift
      (PullbackCone.mk (factorThruImageSubobject (S.arrow ≫ p)) S.arrow
        (imageSubobject_arrow_comp (f := S.arrow ≫ p))))
    ((Subobject.isPullback p I).isLimit.fac _ WalkingCospan.right)
  -- Z(pb(I)) = Z(M) + Z(I) from pullback SES
  have hZ_pb := Zobj_pullback_eq_add Z M I
  -- Z(S) = Z(M) + Z(cokernel(ofLE M S)) from SES M → S → S/M
  have hZ_S := Z.additive _
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (Subobject.ofLE M S hMS))
      inferInstance inferInstance)
  -- Z(I) = Z(S/M): both sides equal Z(S) - Z(M)
  -- First, show Z(I) = Z(cokernel(ofLE M S)) via the canonical iso
  have hZ_I : Z.Zobj (I : A) = Z.Zobj (cokernel (Subobject.ofLE M S hMS)) := by
    -- Use the first isomorphism theorem: image(f) ≅ coimage(f) = cokernel(kernel.ι f)
    -- and kernel(f) ≅ (M : A), where f = S.arrow ≫ p
    -- Step 1: SES kernel(f) → (S : A) → cokernel(kernel.ι f) gives Z-additivity
    have hZ_ses := Z.additive _ (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (kernel.ι (S.arrow ≫ p))) inferInstance inferInstance)
    -- Step 2: Build iso kernel(S.arrow ≫ p) ≅ (M : A)
    have h_cond : Subobject.ofLE M S hMS ≫ (S.arrow ≫ p) = 0 := by
      rw [← Category.assoc, Subobject.ofLE_arrow]; exact cokernel.condition M.arrow
    have h_kerfact : (kernel.ι (S.arrow ≫ p) ≫ S.arrow) ≫ cokernel.π M.arrow = 0 := by
      rw [Category.assoc]; exact kernel.condition (S.arrow ≫ p)
    set k := kernel.lift (S.arrow ≫ p) (Subobject.ofLE M S hMS) h_cond
    set l := Abelian.monoLift M.arrow (kernel.ι (S.arrow ≫ p) ≫ S.arrow) h_kerfact
    have hk : k ≫ kernel.ι (S.arrow ≫ p) = Subobject.ofLE M S hMS := kernel.lift_ι _ _ _
    have hl : l ≫ M.arrow = kernel.ι (S.arrow ≫ p) ≫ S.arrow := Abelian.monoLift_comp _ _ _
    have hkl : k ≫ l = 𝟙 _ := by
      apply (cancel_mono M.arrow).mp
      rw [Category.assoc, hl, ← Category.assoc, hk, Subobject.ofLE_arrow, Category.id_comp]
    have hlk : l ≫ k = 𝟙 _ := by
      apply (cancel_mono (kernel.ι (S.arrow ≫ p))).mp
      rw [Category.assoc, hk, Category.id_comp]
      apply (cancel_mono S.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow, hl]
    have hZ_ker : Z.Zobj (M : A) = Z.Zobj (kernel (S.arrow ≫ p)) :=
      Z.Zobj_eq_of_iso ⟨k, l, hkl, hlk⟩
    -- Step 3: Z(coimage f) = Z(image f), Z(imageSubobject f) = Z(image f)
    have hZ_coim := Z.Zobj_eq_of_iso (Abelian.coimageIsoImage' (S.arrow ≫ p))
    have hZ_im := Z.Zobj_eq_of_iso (imageSubobjectIso (S.arrow ≫ p))
    -- Step 4: Combine: Z(I) = Z(image) = Z(coimage) = Z(S) - Z(kernel) = Z(S) - Z(M)
    rw [← hZ_ker] at hZ_ses
    exact (hZ_im.trans hZ_coim.symm).trans (add_left_cancel (hZ_ses.symm.trans hZ_S))
  -- Conclude Z(pb(I)) = Z(S)
  have hZ_eq : Z.Zobj (pbI : A) = Z.Zobj (S : A) := by
    have h : Z.Zobj (S : A) = Z.Zobj (M : A) +
        Z.Zobj (cokernel (Subobject.ofLE M S hMS)) := hZ_S
    rw [hZ_pb, hZ_I]; exact h.symm
  -- Z-value trick: cokernel of S ↪ pb(I) has Z = 0, hence is zero
  rcases hle.eq_or_lt with h | hlt
  · exact h.symm
  · exfalso
    have hse := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE S pbI hle)) inferInstance inferInstance
    have hZ_add := Z.additive _ hse
    have hZ_cok : Z.Zobj (cokernel (Subobject.ofLE S pbI hle)) = 0 := by
      have h : Z.Zobj (pbI : A) = Z.Zobj (S : A) +
          Z.Zobj (cokernel (Subobject.ofLE S pbI hle)) := hZ_add
      have h2 : Z.Zobj (S : A) + 0 = Z.Zobj (S : A) +
          Z.Zobj (cokernel (Subobject.ofLE S pbI hle)) := by
        rw [add_zero]; exact hZ_eq.symm.trans h
      exact (add_left_cancel h2).symm
    have hcok_nz : ¬IsZero (cokernel (Subobject.ofLE S pbI hle)) := by
      intro hZ
      haveI : Epi (Subobject.ofLE S pbI hle) :=
        Preadditive.epi_of_isZero_cokernel _ hZ
      haveI := isIso_of_mono_of_epi (Subobject.ofLE S pbI hle)
      exact absurd (Subobject.eq_of_comm (asIso (Subobject.ofLE S pbI hle))
        (Subobject.ofLE_arrow hle)) (ne_of_lt hlt)
    exact absurd hZ_cok (ne_of_mem_of_not_mem (Z.upper _ hcok_nz)
      (show (0 : ℂ) ∉ upperHalfPlaneUnion from fun hc ↦ by
        rcases hc with hc | ⟨_, hc⟩ <;> simp at hc))

/-- If `E` is not semistable, any HN filtration of `E` has at least 2 factors. -/
private lemma n_ge_two_of_not_semistable {Z : StabilityFunction A} {E : A}
    (hns : ¬Z.IsSemistable E) (F : AbelianHNFiltration Z E) : 2 ≤ F.n := by
  by_contra hlt
  simp only [not_le] at hlt
  have hn1 : F.n = 1 := by have := F.hn; lia
  suffices Z.IsSemistable E from hns this
  have hss := F.factor_semistable ⟨0, F.hn⟩
  have h_bot : F.chain (⟨0, F.hn⟩ : Fin F.n).castSucc = ⊥ :=
    (congrArg F.chain (Fin.ext rfl)).trans F.chain_bot
  have h_top : F.chain (⟨0, F.hn⟩ : Fin F.n).succ = ⊤ := by
    have : (⟨0, F.hn⟩ : Fin F.n).succ = ⟨F.n, lt_add_one F.n⟩ :=
      Fin.ext (by simp; lia)
    rw [this, F.chain_top]
  -- Transfer semistability: factor ≅ cokernel(ofLE ⊥ ⊤) ≅ (⊤ : A) ≅ E
  have h1 : Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ bot_le)) :=
    isSemistable_cokernel_ofLE_congr Z h_bot.symm h_top.symm hss
  exact Z.isSemistable_of_iso
    (StabilityFunction.Subobject.cokernelBotIso ⊤ bot_le ≪≫
      asIso (⊤ : Subobject E).arrow) h1

/-- The tail HN filtration of the quotient `E / chain(1)`, constructed by pushing
the chain forward via `imageSubobject(_.arrow ≫ cokernel.π chain(1).arrow)`. -/
private noncomputable def tailHNFiltration {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn2 : 2 ≤ F.n) :
    AbelianHNFiltration Z (cokernel (F.chain ⟨1, by lia⟩).arrow) where
  n := F.n - 1
  hn := by lia
  chain := fun ⟨j, _⟩ ↦ imageSubobject
    ((F.chain ⟨j + 1, by lia⟩).arrow ≫ cokernel.π (F.chain ⟨1, by lia⟩).arrow)
  chain_strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    change imageSubobject ((F.chain ⟨j + 1, by lia⟩).arrow ≫
        cokernel.π (F.chain ⟨1, by lia⟩).arrow) <
      imageSubobject ((F.chain ⟨j + 2, by lia⟩).arrow ≫
        cokernel.π (F.chain ⟨1, by lia⟩).arrow)
    have hM1 : F.chain ⟨1, by lia⟩ ≤ F.chain ⟨j + 1, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hM2 : F.chain ⟨1, by lia⟩ ≤ F.chain ⟨j + 2, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hS₁S₂ : F.chain ⟨j + 1, by lia⟩ < F.chain ⟨j + 2, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    have h_le : imageSubobject ((F.chain ⟨j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) ≤
        imageSubobject ((F.chain ⟨j + 2, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) := by
      rw [show (F.chain ⟨j + 1, by lia⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by lia⟩).arrow =
          Subobject.ofLE _ _ hS₁S₂.le ≫ ((F.chain ⟨j + 2, by lia⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by lia⟩).arrow) from
        by rw [← Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_comp_le _ _
    exact lt_of_le_of_ne h_le (fun heq ↦ absurd
      ((pullback_imageSubobject_eq Z hM1).symm.trans
        (heq ▸ pullback_imageSubobject_eq Z hM2))
      (ne_of_lt hS₁S₂))
  chain_bot := by
    change imageSubobject ((F.chain ⟨1, by lia⟩).arrow ≫
      cokernel.π (F.chain ⟨1, by lia⟩).arrow) = ⊥
    rw [cokernel.condition, imageSubobject_zero]
  chain_top := by
    change imageSubobject ((F.chain ⟨F.n - 1 + 1, by lia⟩).arrow ≫
      cokernel.π (F.chain ⟨1, by lia⟩).arrow) = ⊤
    have htop : F.chain ⟨F.n - 1 + 1, by lia⟩ = ⊤ :=
      (congrArg F.chain (Fin.ext (Nat.sub_add_cancel (by lia)))).trans
        F.chain_top
    rw [htop]
    haveI : IsIso (⊤ : Subobject E).arrow := inferInstance
    rw [imageSubobject_iso_comp]
    exact imageSubobject_epi_eq_top _
  φ := fun ⟨j, _⟩ ↦ F.φ ⟨j + 1, by lia⟩
  φ_anti := by
    intro ⟨j₁, _⟩ ⟨j₂, _⟩ h
    simp only [Fin.lt_def] at h
    exact F.φ_anti (Fin.mk_lt_mk.mpr (by lia))
  factor_phase := by
    intro ⟨j, _⟩
    exact ((phase_cokernel_pullback_eq Z (F.chain ⟨1, by lia⟩) _).symm.trans
      ((phase_cokernel_ofLE_congr Z
        (pullback_imageSubobject_eq Z
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))))
        (pullback_imageSubobject_eq Z
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))))).trans
      (F.factor_phase ⟨j + 1, by lia⟩)))
  factor_semistable := by
    intro ⟨j, hj⟩
    have hM1 : F.chain ⟨1, by lia⟩ ≤ F.chain ⟨j + 1, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hM2 : F.chain ⟨1, by lia⟩ ≤ F.chain ⟨j + 2, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hS₁S₂ : F.chain ⟨j + 1, by lia⟩ < F.chain ⟨j + 2, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    have h_le : imageSubobject ((F.chain ⟨j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) ≤
        imageSubobject ((F.chain ⟨j + 2, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) := by
      rw [show (F.chain ⟨j + 1, by lia⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by lia⟩).arrow =
          Subobject.ofLE _ _ hS₁S₂.le ≫ ((F.chain ⟨j + 2, by lia⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by lia⟩).arrow) from
        by rw [← Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_comp_le _ _
    exact Z.isSemistable_of_iso
      (cokernelPullbackIso Z (F.chain ⟨1, by lia⟩)
        (lt_of_le_of_ne h_le (fun heq ↦ absurd
          ((pullback_imageSubobject_eq Z hM1).symm.trans
            (heq ▸ pullback_imageSubobject_eq Z hM2))
          (ne_of_lt hS₁S₂))))
      (isSemistable_cokernel_ofLE_congr Z
        (pullback_imageSubobject_eq Z hM1)
        (pullback_imageSubobject_eq Z hM2)
        (F.factor_semistable ⟨j + 1, by lia⟩))

/-- Transporting an HN filtration along an equality preserves `.n`. -/
private lemma transport_n {Z : StabilityFunction A} {Q₁ Q₂ : A}
    (h : Q₁ = Q₂) (F : AbelianHNFiltration Z Q₁) :
    (h ▸ F).n = F.n := by subst h; rfl

/-- **Proposition 2.3** (Bridgeland): HN filtrations are essentially unique.
When all objects have finite subobject lattices, any two HN filtrations of the
same object have the same number of semistable factors.

The proof shows that `chain(1)` of any HN filtration equals the maximally
destabilizing subobject (MDS), which is intrinsic to the object. The key step
is the semistable descent lemma: any semistable subobject with phase `> φ(0)`
must be zero (by hom-vanishing to each factor). This forces the MDS phase to
equal `φ(0)`, and the MDS to equal `chain(1)`. We then quotient and induct. -/
theorem StabilityFunction.hn_unique (Z : StabilityFunction A) (E : A) (hE : ¬IsZero E)
    (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F₁ F₂ : AbelianHNFiltration Z E) :
    F₁.n = F₂.n := by
  suffices ∀ (k : ℕ) (E : A), ¬IsZero E →
      Nat.card (Subobject E) ≤ k →
      ∀ G₁ G₂ : AbelianHNFiltration Z E, G₁.n = G₂.n by
    exact this _ E hE le_rfl F₁ F₂
  intro k
  induction k with
  | zero =>
    intro E hE hcard
    haveI := hFinSub E
    haveI := Fintype.ofFinite (Subobject E)
    have : 0 < Nat.card (Subobject E) := by
      rw [Nat.card_eq_fintype_card]
      haveI : Nonempty (Subobject E) := ⟨⊥⟩
      exact Fintype.card_pos
    lia
  | succ k ih =>
    intro E hE hcard G₁ G₂
    haveI := hFinSub E
    by_cases hss : Z.IsSemistable E
    · exact (hn_n_eq_one_of_semistable Z hss G₁).trans
        (hn_n_eq_one_of_semistable Z hss G₂).symm
    · -- E not semistable: both filtrations have n ≥ 2
      have hn1 : 2 ≤ G₁.n := n_ge_two_of_not_semistable hss G₁
      have hn2 : 2 ≤ G₂.n := n_ge_two_of_not_semistable hss G₂
      -- Get maximally destabilizing subobject (MDS)
      obtain ⟨M, hM_ne, hM_max, hM_strict⟩ :=
        exists_maxPhase_maximal_subobject Z E hE
      have hM_ss := Z.maxPhase_isSemistable hM_ne hM_max
      have hM_ne_top :=
        Z.maxPhase_ne_top_of_not_semistable hss M hM_ne hM_max
      -- chain(1) = M for both filtrations
      have hc1 : G₁.chain ⟨1, by lia⟩ = M :=
        chain_one_eq_MDS G₁ hn1 hM_ne hM_ss hM_max hM_strict
      have hc2 : G₂.chain ⟨1, by lia⟩ = M :=
        chain_one_eq_MDS G₂ hn2 hM_ne hM_ss hM_max hM_strict
      -- Quotient Q = E/M has strictly fewer subobjects
      have hcard_Q : Nat.card (Subobject (cokernel M.arrow)) <
          Nat.card (Subobject E) :=
        card_subobject_cokernel_lt hM_ne
      -- Transport tail filtrations to cokernel M.arrow
      have hQ₁ : cokernel (G₁.chain ⟨1, by lia⟩).arrow =
          cokernel M.arrow :=
        congrArg (fun S ↦ cokernel (Subobject.arrow S)) hc1
      have hQ₂ : cokernel (G₂.chain ⟨1, by lia⟩).arrow =
          cokernel M.arrow :=
        congrArg (fun S ↦ cokernel (Subobject.arrow S)) hc2
      -- Apply IH: tail filtrations on Q have the same length
      have h_eq : (hQ₁ ▸ tailHNFiltration G₁ hn1).n =
          (hQ₂ ▸ tailHNFiltration G₂ hn2).n :=
        ih (cokernel M.arrow)
          (cokernel_nonzero_of_ne_top hM_ne_top)
          (by lia) _ _
      simp only [transport_n] at h_eq
      change G₁.n - 1 = G₂.n - 1 at h_eq
      lia

/-- The highest phase `φ(0)` of an HN filtration equals the phase of `chain(1)`,
which equals the MDS phase. This is independent of the filtration choice. -/
theorem StabilityFunction.hn_phiPlus_eq (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F₁ F₂ : AbelianHNFiltration Z E) :
    F₁.φ ⟨0, F₁.hn⟩ = F₂.φ ⟨0, F₂.hn⟩ := by
  haveI := hFinSub E
  by_cases hss : Z.IsSemistable E
  · -- Semistable: n = 1, each φ(0) = Z.phase E
    have h1 := hn_n_eq_one_of_semistable Z hss F₁
    have h2 := hn_n_eq_one_of_semistable Z hss F₂
    suffices ∀ (F : AbelianHNFiltration Z E), F.n = 1 →
        F.φ ⟨0, F.hn⟩ = Z.phase E from
      (this F₁ h1).trans (this F₂ h2).symm
    intro F hF
    rw [← F.factor_phase ⟨0, F.hn⟩]
    have h_bot : F.chain (⟨0, F.hn⟩ : Fin F.n).castSucc = ⊥ := by
      change F.chain ⟨0, by have := F.hn; lia⟩ = ⊥; exact F.chain_bot
    have h_top : F.chain (⟨0, F.hn⟩ : Fin F.n).succ = ⊤ := by
      have : (⟨0, F.hn⟩ : Fin F.n).succ = ⟨F.n, by lia⟩ :=
        Fin.ext (by simp; lia)
      rw [this]; exact F.chain_top
    exact (phase_cokernel_ofLE_congr Z h_bot h_top).trans
      (Z.phase_eq_of_iso (Subobject.cokernelBotIso ⊤ bot_le ≪≫
        asIso (⊤ : Subobject E).arrow))
  · -- Non-semistable: φ(0) = phase(chain(1)) = phase(MDS) for both
    have hn1 : 2 ≤ F₁.n := n_ge_two_of_not_semistable hss F₁
    have hn2 : 2 ≤ F₂.n := n_ge_two_of_not_semistable hss F₂
    obtain ⟨M, hM_ne, hM_max, hM_strict⟩ :=
      exists_maxPhase_maximal_subobject Z E hE
    have hM_ss := Z.maxPhase_isSemistable hM_ne hM_max
    have hc1 := chain_one_eq_MDS F₁ hn1 hM_ne hM_ss hM_max hM_strict
    have hc2 := chain_one_eq_MDS F₂ hn2 hM_ne hM_ss hM_max hM_strict
    rw [← chain_one_phase F₁ hn1, ← chain_one_phase F₂ hn2, hc1, hc2]

/-- Transporting an HN filtration along an equality preserves the lowest
phase `φ(n-1)`. -/
private lemma transport_phiMinus {Z : StabilityFunction A} {Q₁ Q₂ : A}
    (h : Q₁ = Q₂) (F : AbelianHNFiltration Z Q₁) :
    (h ▸ F).φ ⟨(h ▸ F).n - 1, by have := (h ▸ F).hn; lia⟩ =
      F.φ ⟨F.n - 1, by have := F.hn; lia⟩ := by
  subst h; rfl

/-- The tail filtration's lowest phase equals the original's lowest phase.
Since `tailHNFiltration.φ ⟨j, _⟩ = F.φ ⟨j+1, _⟩` and `tail.n = F.n - 1`,
the tail's last index `tail.n - 1 = F.n - 2` maps to `F.n - 1`. -/
private lemma tailHNFiltration_phiMinus {Z : StabilityFunction A} {E : A}
    (G : AbelianHNFiltration Z E) (hn2 : 2 ≤ G.n) :
    (tailHNFiltration G hn2).φ
      ⟨(tailHNFiltration G hn2).n - 1,
        by have := (tailHNFiltration G hn2).hn; lia⟩ =
    G.φ ⟨G.n - 1, by have := G.hn; lia⟩ :=
  -- After definitional reduction: LHS = G.φ ⟨(G.n-1)-1+1, _⟩
  congrArg G.φ (Fin.ext
    (show ((G.n - 1) - 1 + 1 : ℕ) = G.n - 1 from by lia))

/-- The lowest phase `φ(n-1)` of an HN filtration is independent of the
filtration choice. The proof parallels `hn_unique`: induction on
`Nat.card (Subobject E)`, using the tail filtration on the MDS quotient. -/
theorem StabilityFunction.hn_phiMinus_eq (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F₁ F₂ : AbelianHNFiltration Z E) :
    F₁.φ ⟨F₁.n - 1, by have := F₁.hn; lia⟩ =
      F₂.φ ⟨F₂.n - 1, by have := F₂.hn; lia⟩ := by
  suffices ∀ (k : ℕ) (E : A), ¬IsZero E →
      Nat.card (Subobject E) ≤ k →
      ∀ G₁ G₂ : AbelianHNFiltration Z E,
        G₁.φ ⟨G₁.n - 1, by have := G₁.hn; lia⟩ =
          G₂.φ ⟨G₂.n - 1, by have := G₂.hn; lia⟩ by
    exact this _ E hE le_rfl F₁ F₂
  intro k
  induction k with
  | zero =>
    intro E hE hcard
    haveI := hFinSub E
    haveI := Fintype.ofFinite (Subobject E)
    have : 0 < Nat.card (Subobject E) := by
      rw [Nat.card_eq_fintype_card]
      haveI : Nonempty (Subobject E) := ⟨⊥⟩
      exact Fintype.card_pos
    lia
  | succ k ih =>
    intro E hE hcard G₁ G₂
    haveI := hFinSub E
    by_cases hss : Z.IsSemistable E
    · -- Semistable: n = 1, phiMinus = phiPlus
      have h1 := hn_n_eq_one_of_semistable Z hss G₁
      have h2 := hn_n_eq_one_of_semistable Z hss G₂
      have hG₁_eq : (⟨G₁.n - 1, by have := G₁.hn; lia⟩ : Fin G₁.n) =
          ⟨0, G₁.hn⟩ := Fin.ext (by lia)
      have hG₂_eq : (⟨G₂.n - 1, by have := G₂.hn; lia⟩ : Fin G₂.n) =
          ⟨0, G₂.hn⟩ := Fin.ext (by lia)
      rw [hG₁_eq, hG₂_eq]
      exact Z.hn_phiPlus_eq E hE hFinSub G₁ G₂
    · -- Not semistable: use tail filtrations on MDS quotient
      have hn1 : 2 ≤ G₁.n := n_ge_two_of_not_semistable hss G₁
      have hn2 : 2 ≤ G₂.n := n_ge_two_of_not_semistable hss G₂
      obtain ⟨M, hM_ne, hM_max, hM_strict⟩ :=
        exists_maxPhase_maximal_subobject Z E hE
      have hM_ss := Z.maxPhase_isSemistable hM_ne hM_max
      have hM_ne_top :=
        Z.maxPhase_ne_top_of_not_semistable hss M hM_ne hM_max
      have hc1 := chain_one_eq_MDS G₁ hn1 hM_ne hM_ss hM_max hM_strict
      have hc2 := chain_one_eq_MDS G₂ hn2 hM_ne hM_ss hM_max hM_strict
      have hcard_Q : Nat.card (Subobject (cokernel M.arrow)) <
          Nat.card (Subobject E) := card_subobject_cokernel_lt hM_ne
      have hQ₁ : cokernel (G₁.chain ⟨1, by lia⟩).arrow =
          cokernel M.arrow :=
        congrArg (fun S ↦ cokernel (Subobject.arrow S)) hc1
      have hQ₂ : cokernel (G₂.chain ⟨1, by lia⟩).arrow =
          cokernel M.arrow :=
        congrArg (fun S ↦ cokernel (Subobject.arrow S)) hc2
      -- Tail filtrations on the quotient
      let T₁ := hQ₁ ▸ tailHNFiltration G₁ hn1
      let T₂ := hQ₂ ▸ tailHNFiltration G₂ hn2
      -- IH: tail filtrations have the same lowest phase
      have h_tail : T₁.φ ⟨T₁.n - 1, by have := T₁.hn; lia⟩ =
          T₂.φ ⟨T₂.n - 1, by have := T₂.hn; lia⟩ :=
        ih (cokernel M.arrow) (cokernel_nonzero_of_ne_top hM_ne_top)
          (by lia) T₁ T₂
      -- Connect tail's phiMinus to original's phiMinus
      have hrel₁ : T₁.φ ⟨T₁.n - 1, by have := T₁.hn; lia⟩ =
          G₁.φ ⟨G₁.n - 1, by have := G₁.hn; lia⟩ :=
        (transport_phiMinus hQ₁ (tailHNFiltration G₁ hn1)).trans
          (tailHNFiltration_phiMinus G₁ hn1)
      have hrel₂ : T₂.φ ⟨T₂.n - 1, by have := T₂.hn; lia⟩ =
          G₂.φ ⟨G₂.n - 1, by have := G₂.hn; lia⟩ :=
        (transport_phiMinus hQ₂ (tailHNFiltration G₂ hn2)).trans
          (tailHNFiltration_phiMinus G₂ hn2)
      linarith

/-! ### Intrinsic phase bounds -/

/-- The intrinsic highest phase of a nonzero object `E` with respect to a
stability function `Z`, assuming finite subobject lattices. This is the phase of
the maximally destabilizing subobject. It is well-defined by `hn_phiPlus_eq`. -/
noncomputable def StabilityFunction.phiPlus (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E)) : ℝ :=
  let F := Classical.choice (Z.hasHN_of_finiteLength hFinSub E hE)
  F.φ ⟨0, F.hn⟩

/-- `phiPlus` equals `F.φ ⟨0, F.hn⟩` for any HN filtration `F`. -/
theorem StabilityFunction.phiPlus_eq (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F : AbelianHNFiltration Z E) :
    Z.phiPlus E hE hFinSub = F.φ ⟨0, F.hn⟩ :=
  Z.hn_phiPlus_eq E hE hFinSub _ F

/-- The intrinsic lowest phase of a nonzero object `E` with respect to a
stability function `Z`, assuming finite subobject lattices. This is the phase of
the last HN factor. It is well-defined by `hn_phiMinus_eq`. -/
noncomputable def StabilityFunction.phiMinus (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E)) : ℝ :=
  let F := Classical.choice (Z.hasHN_of_finiteLength hFinSub E hE)
  F.φ ⟨F.n - 1, by have := F.hn; lia⟩

/-- `phiMinus` equals `F.φ ⟨F.n - 1, _⟩` for any HN filtration `F`. -/
theorem StabilityFunction.phiMinus_eq (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (F : AbelianHNFiltration Z E) :
    Z.phiMinus E hE hFinSub =
      F.φ ⟨F.n - 1, by have := F.hn; lia⟩ :=
  Z.hn_phiMinus_eq E hE hFinSub _ F

/-- `phiMinus ≤ phiPlus` for nonzero objects. -/
theorem StabilityFunction.phiMinus_le_phiPlus
    (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E)) :
    Z.phiMinus E hE hFinSub ≤ Z.phiPlus E hE hFinSub := by
  let F := Classical.choice (Z.hasHN_of_finiteLength hFinSub E hE)
  rw [Z.phiPlus_eq E hE hFinSub F, Z.phiMinus_eq E hE hFinSub F]
  exact F.φ_anti.antitone (Fin.mk_le_mk.mpr (by have := F.hn; lia))

/-- For semistable objects, `phiPlus = phiMinus = Z.phase E`. -/
theorem StabilityFunction.phiPlus_eq_phiMinus_of_semistable
    (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) (hFinSub : ∀ (E : A), Finite (Subobject E))
    (hss : Z.IsSemistable E) :
    Z.phiPlus E hE hFinSub = Z.phiMinus E hE hFinSub := by
  let F := Classical.choice (Z.hasHN_of_finiteLength hFinSub E hE)
  have h1 := hn_n_eq_one_of_semistable Z hss F
  have hp := Z.phiPlus_eq E hE hFinSub F
  have hm := Z.phiMinus_eq E hE hFinSub F
  have heq : F.φ ⟨0, F.hn⟩ =
      F.φ ⟨F.n - 1, by have := F.hn; lia⟩ :=
    congrArg F.φ (Fin.ext (by lia))
  linarith

end CategoryTheory
