/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityFunction.Basic
public meta import Informal

/-!
# Harder-Narasimhan Filtrations for Stability Functions

HN filtrations in abelian categories, existence from finite length and from
artinian+noetherian, uniqueness, maximally destabilizing quotients, and
intrinsic phase bounds (phiPlus/phiMinus).
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex Real

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-! ### Harder-Narasimhan filtrations (abelian setting) -/

/-- A Harder-Narasimhan filtration of a nonzero object `E` in an abelian category,
with respect to a stability function `Z`.

This is a finite chain of subobjects `0 = E₀ < E₁ < ⋯ < Eₙ = E` with:
- `n ≥ 1` factors
- the phases are strictly decreasing
- each factor `Eᵢ₊₁/Eᵢ` is semistable with phase `φ i`

The semistability condition connects the chain to the stability function `Z`:
the `i`-th factor (successive quotient) is semistable and has phase `φ i`.
We encode this via `factor_semistable` and `factor_phase`, where the factor
objects are obtained as cokernels of the successive inclusion maps. -/
@[informal "Definition 2.3" "HN filtration for abelian categories" complete]
structure AbelianHNFiltration (Z : StabilityFunction A) (E : A) where
  /-- The number of semistable factors. -/
  n : ℕ
  hn : 0 < n
  /-- The chain of subobjects, strictly monotone. -/
  chain : Fin (n + 1) → Subobject E
  chain_strictMono : StrictMono chain
  chain_bot : chain ⟨0, Nat.zero_lt_succ _⟩ = ⊥
  chain_top : chain ⟨n, n.lt_succ_iff.mpr le_rfl⟩ = ⊤
  /-- The phases of the semistable quotients, in strictly decreasing order. -/
  φ : Fin n → ℝ
  φ_anti : StrictAnti φ
  /-- The phase of each factor equals the given phase. -/
  factor_phase : ∀ (j : Fin n),
    Z.phase (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
      (le_of_lt (chain_strictMono j.castSucc_lt_succ)))) = φ j
  /-- Each successive quotient is semistable. -/
  factor_semistable : ∀ (j : Fin n),
    Z.IsSemistable (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
      (le_of_lt (chain_strictMono j.castSucc_lt_succ))))

/-- A stability function has the Harder-Narasimhan property if every nonzero object
admits a Harder-Narasimhan filtration (Bridgeland, Proposition 2.4). -/
@[informal "Definition 2.3" "HN property predicate" complete]
def StabilityFunction.HasHNProperty (Z : StabilityFunction A) : Prop :=
  ∀ (E : A), ¬IsZero E → Nonempty (AbelianHNFiltration Z E)

/-! ### Pullback infrastructure for HN proof -/

/-- In an abelian category, precomposing by an epi doesn't change the image subobject. -/
private lemma imageSubobject_epi_comp {X Y Z : A} (g : X ⟶ Y) [Epi g] (f : Y ⟶ Z) :
    imageSubobject (g ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le g f)
  have h_le := imageSubobject_comp_le g f
  haveI : Mono (Subobject.ofLE _ _ h_le) := by
    apply (mono_comp_iff_of_mono _ (imageSubobject f).arrow).mp
    rw [Subobject.ofLE_arrow]; infer_instance
  haveI : Epi (Subobject.ofLE _ _ h_le) := imageSubobject_comp_le_epi_of_epi g f
  haveI := isIso_of_mono_of_epi (Subobject.ofLE _ _ h_le)
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ h_le))
    (by rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow])

/-- For epi `p` in an abelian category, `pullbackπ p B` is epi. -/
private lemma epi_pullbackπ_of_epi {X Y : A} (p : X ⟶ Y) [Epi p] (B : Subobject Y) :
    Epi (Subobject.pullbackπ p B) := by
  rw [← (Subobject.isPullback p B).isoPullback_hom_fst]; infer_instance

/-- For epi `p` in an abelian category, `(Subobject.pullback p).obj` is injective. -/
lemma pullback_obj_injective_of_epi {X Y : A} (p : X ⟶ Y) [Epi p] :
    Function.Injective (Subobject.pullback p).obj := by
  intro B₁ B₂ h
  haveI := epi_pullbackπ_of_epi p B₁
  haveI := epi_pullbackπ_of_epi p B₂
  calc B₁ = imageSubobject (Subobject.pullbackπ p B₁ ≫ B₁.arrow) := by
          rw [imageSubobject_epi_comp, imageSubobject_mono, Subobject.mk_arrow]
    _ = imageSubobject (((Subobject.pullback p).obj B₁).arrow ≫ p) := by
          rw [(Subobject.isPullback p B₁).w]
    _ = imageSubobject (((Subobject.pullback p).obj B₂).arrow ≫ p) := by rw [h]
    _ = imageSubobject (Subobject.pullbackπ p B₂ ≫ B₂.arrow) := by
          rw [← (Subobject.isPullback p B₂).w]
    _ = B₂ := by rw [imageSubobject_epi_comp, imageSubobject_mono, Subobject.mk_arrow]

/-- Quotients of Noetherian objects are Noetherian. -/
theorem isNoetherianObject_of_epi {X Y : A} (p : X ⟶ Y) [Epi p]
    [IsNoetherianObject X] : IsNoetherianObject Y := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let g : ℕ →o Subobject X :=
    ⟨fun n ↦ (Subobject.pullback p).obj (f n),
      fun i j hij ↦ (Subobject.pullback p).monotone (f.2 hij)⟩
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject g
  exact ⟨n, fun m hm ↦ pullback_obj_injective_of_epi p (hn m hm)⟩

/-- Quotients of Artinian objects are Artinian. -/
theorem isArtinianObject_of_epi {X Y : A} (p : X ⟶ Y) [Epi p]
    [IsArtinianObject X] : IsArtinianObject Y := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  let g : ℕ →o (Subobject X)ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual <| (Subobject.pullback p).obj (f n),
      fun i j hij ↦ by
        change (Subobject.pullback p).obj (f j) ≤ (Subobject.pullback p).obj (f i)
        exact (Subobject.pullback p).monotone (f.2 hij)⟩
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject g
  exact ⟨n, fun m hm ↦ by
    apply pullback_obj_injective_of_epi p
    simpa using hn m hm⟩

/-- The subobject `M ≤ (pullback p).obj ⊥` when `M.arrow ≫ p = 0`. This is used to show
that pullback along the cokernel projection maps every subobject above the kernel. -/
private lemma le_pullback_bot_of_comp_eq_zero {X Y : A} {M : Subobject X}
    (p : X ⟶ Y) (hMp : M.arrow ≫ p = 0) :
    M ≤ (Subobject.pullback p).obj ⊥ := by
  have hpb := Subobject.isPullback p (⊥ : Subobject Y)
  have hpb_zero : ((Subobject.pullback p).obj ⊥).arrow ≫ p = 0 := by
    have := hpb.w; simp only [Subobject.bot_arrow, comp_zero] at this; rw [this]
  exact Subobject.le_of_comm
    (hpb.isLimit.lift (PullbackCone.mk (0 : (M : A) ⟶ _) M.arrow (by simp [hMp])))
    (hpb.isLimit.fac _ WalkingCospan.right)

/-- For epi `cokernel.π M.arrow`, every subobject of the target pulls back to a
subobject of the source that is `≥ M`, hence `≠ ⊥` when `M ≠ ⊥`. -/
private lemma pullback_cokernel_ne_bot {E : A} {M : Subobject E}
    (hM : M ≠ ⊥) (B : Subobject (cokernel M.arrow)) :
    (Subobject.pullback (cokernel.π M.arrow)).obj B ≠ ⊥ := by
  intro h
  have hle : M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ :=
    le_pullback_bot_of_comp_eq_zero _ (cokernel.condition M.arrow)
  have hle' : M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B :=
    le_trans hle ((Subobject.pullback (cokernel.π M.arrow)).monotone bot_le)
  rw [h] at hle'
  exact hM (eq_bot_iff.mpr hle')

/-- **Cardinality decrease**: `Nat.card (Subobject Q) < Nat.card (Subobject E)` where
`Q = cokernel M.arrow` for a proper nonzero subobject `M`. -/
lemma card_subobject_cokernel_lt {E : A} {M : Subobject E}
    (hM_ne_bot : M ≠ ⊥) [hFin : Finite (Subobject E)] :
    Nat.card (Subobject (cokernel M.arrow)) < Nat.card (Subobject E) := by
  haveI := Fintype.ofFinite (Subobject E)
  haveI : Finite (Subobject (cokernel M.arrow)) :=
    Finite.of_injective _ (pullback_obj_injective_of_epi (cokernel.π M.arrow))
  haveI := Fintype.ofFinite (Subobject (cokernel M.arrow))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem
    (Subobject.pullback (cokernel.π M.arrow)).obj
    (pullback_obj_injective_of_epi _)
    (by simp only [Set.mem_range, not_exists]
        exact fun B ↦ pullback_cokernel_ne_bot hM_ne_bot B)

/-- The pullback of `⊥` along `cokernel.π M.arrow` equals `M` as a subobject of `E`. -/
lemma pullback_cokernel_bot_eq {E : A} (M : Subobject E) :
    (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ = M := by
  apply le_antisymm
  · set P := (Subobject.pullback (cokernel.π M.arrow)).obj ⊥
    have hP : P.arrow ≫ cokernel.π M.arrow = 0 := by
      have := (Subobject.isPullback (cokernel.π M.arrow)
        (⊥ : Subobject (cokernel M.arrow))).w
      simp only [Subobject.bot_arrow, comp_zero] at this; rw [this]
    have hker : kernelSubobject (cokernel.π M.arrow) = M := by
      simpa [imageSubobject_mono, Subobject.mk_arrow] using
        ((ShortComplex.mk M.arrow (cokernel.π M.arrow)
          (cokernel.condition M.arrow)).exact_iff_image_eq_kernel.mp
          (ShortComplex.exact_cokernel M.arrow)).symm
    rw [← hker]
    exact Subobject.le_of_comm
      (factorThruKernelSubobject _ P.arrow hP)
      (factorThruKernelSubobject_comp_arrow _ _ _)
  · exact le_pullback_bot_of_comp_eq_zero _ (cokernel.condition M.arrow)

-- Subobject.pullback_top already exists in Mathlib

/-- For epi `p`, `(Subobject.pullback p).obj` is strictly monotone. -/
private lemma pullback_obj_strictMono_of_epi {X Y : A} (p : X ⟶ Y) [Epi p] :
    StrictMono (Subobject.pullback p).obj :=
  (Subobject.pullback p).monotone.strictMono_of_injective
    (pullback_obj_injective_of_epi p)

/-- Among all nonzero subobjects with maximal phase, there exists one that is maximal
in the subobject ordering. The third condition says every subobject strictly above `M`
has strictly lower phase, preventing equal-phase subobjects from being larger. -/
lemma exists_maxPhase_maximal_subobject (Z : StabilityFunction A) (E : A)
    (hE : ¬IsZero E) [hFin : Finite (Subobject E)] :
    ∃ M : Subobject E, M ≠ ⊥ ∧
      (∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A)) ∧
      (∀ B : Subobject E, M < B → Z.phase (B : A) < Z.phase (M : A)) := by
  obtain ⟨M₀, hM₀_ne, hM₀_max⟩ := Z.exists_maxPhase_subobject E hE
  set S := {B : Subobject E | B ≠ ⊥ ∧ Z.phase (B : A) = Z.phase (M₀ : A)}
  have hS_ne : S.Nonempty := ⟨M₀, hM₀_ne, rfl⟩
  have hS_fin : S.Finite := Set.toFinite _
  obtain ⟨M, ⟨hM_ne, hM_phase⟩, hM_max_in_S⟩ := hS_fin.exists_maximal hS_ne
  refine ⟨M, hM_ne, fun B hB ↦ hM_phase ▸ hM₀_max B hB, fun B hB ↦ ?_⟩
  have hB_ne : B ≠ ⊥ := ne_bot_of_gt hB
  have hle := hM₀_max B hB_ne
  rw [hM_phase]
  exact lt_of_le_of_ne hle (fun heq ↦
    absurd (hM_max_in_S ⟨hB_ne, heq⟩ hB.le) (not_le_of_gt hB))

/-- In an abelian category, if `M.arrow` is not an epimorphism, then `cokernel M.arrow`
is nonzero. This applies when `M ≠ ⊤` as a subobject. -/
lemma cokernel_nonzero_of_ne_top {E : A} {M : Subobject E} (hM : M ≠ ⊤) :
    ¬IsZero (cokernel M.arrow) := by
  intro hZ
  haveI : Epi M.arrow := Preadditive.epi_of_isZero_cokernel M.arrow hZ
  haveI : IsIso M.arrow := isIso_of_mono_of_epi M.arrow
  exact hM (Subobject.eq_top_of_isIso_arrow M)

/-- In an abelian category, `M ≠ ⊤` implies `M.arrow` is not epi. -/
private lemma not_epi_of_ne_top {E : A} {M : Subobject E} (hM : M ≠ ⊤) : ¬Epi M.arrow := by
  intro h; haveI := h
  haveI : IsIso M.arrow := isIso_of_mono_of_epi M.arrow
  exact hM (Subobject.eq_top_of_isIso_arrow M)

/-! ### Short exact sequence from pullback along cokernel projection

For a subobject `M'` of `E` and a subobject `B` of `cokernel M'.arrow`, the pullback
`pb'(B)` of `B` along `cokernel.π M'.arrow` gives a short exact sequence
`M' → pb'(B) → B`. This is used in the HN existence proof to compare phases. -/

/-- The inclusion `M' ≤ pb'(B)` for any subobject `B` of the cokernel. -/
lemma le_pullback_cokernel {E : A} (M' : Subobject E)
    (B : Subobject (cokernel M'.arrow)) :
    M' ≤ (Subobject.pullback (cokernel.π M'.arrow)).obj B :=
  (pullback_cokernel_bot_eq M').symm.le.trans
    ((Subobject.pullback (cokernel.π M'.arrow)).monotone bot_le)

/-- The composition `ofLE ≫ pullbackπ = 0` for the pullback SES. -/
private lemma ofLE_pullbackπ_eq_zero {E : A} (M' : Subobject E)
    (B : Subobject (cokernel M'.arrow)) :
    Subobject.ofLE M' _ (le_pullback_cokernel M' B) ≫
      Subobject.pullbackπ (cokernel.π M'.arrow) B = 0 := by
  apply (cancel_mono B.arrow).mp
  simp only [zero_comp, Category.assoc]
  have hw := (Subobject.isPullback (cokernel.π M'.arrow) B).w
  calc Subobject.ofLE M' _ (le_pullback_cokernel M' B) ≫
        (Subobject.pullbackπ (cokernel.π M'.arrow) B ≫ B.arrow)
      = Subobject.ofLE M' _ (le_pullback_cokernel M' B) ≫
          (((Subobject.pullback (cokernel.π M'.arrow)).obj B).arrow ≫
            cokernel.π M'.arrow) := by rw [hw]
    _ = (Subobject.ofLE M' _ (le_pullback_cokernel M' B) ≫
          ((Subobject.pullback (cokernel.π M'.arrow)).obj B).arrow) ≫
            cokernel.π M'.arrow := by rw [Category.assoc]
    _ = M'.arrow ≫ cokernel.π M'.arrow := by rw [Subobject.ofLE_arrow]
    _ = 0 := cokernel.condition M'.arrow

/-- The short exact sequence `M' → pb'(B) → B` is short exact. -/
private lemma shortExact_ofLE_pullbackπ_cokernel {E : A} (M' : Subobject E)
    (B : Subobject (cokernel M'.arrow)) :
    (ShortComplex.mk
      (Subobject.ofLE M' _ (le_pullback_cokernel M' B))
      (Subobject.pullbackπ (cokernel.π M'.arrow) B)
      (ofLE_pullbackπ_eq_zero M' B)).ShortExact := by
  set p' := cokernel.π M'.arrow
  set pbB := (Subobject.pullback p').obj B
  set hle := le_pullback_cokernel M' B
  set hcomp := ofLE_pullbackπ_eq_zero M' B
  have hse_orig : (ShortComplex.mk M'.arrow p' (cokernel.condition M'.arrow)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel M'.arrow) inferInstance
      inferInstance
  have hkernel := hse_orig.fIsKernel
  haveI : Epi (Subobject.pullbackπ p' B) := epi_pullbackπ_of_epi p' B
  apply ShortComplex.ShortExact.mk' _ inferInstance inferInstance
  apply ShortComplex.exact_of_f_is_kernel
  have hw := (Subobject.isPullback p' B).w
  -- Helper: given g' ≫ pullbackπ = 0, deduce (g' ≫ pbB.arrow) ≫ p' = 0
  have key : ∀ {W' : A} (g' : W' ⟶ (pbB : A)),
      g' ≫ Subobject.pullbackπ p' B = 0 → (g' ≫ pbB.arrow) ≫ p' = 0 := by
    intro W' g' eq'
    calc (g' ≫ pbB.arrow) ≫ p'
        = g' ≫ (pbB.arrow ≫ p') := by rw [Category.assoc]
      _ = g' ≫ (Subobject.pullbackπ p' B ≫ B.arrow) := by congr 1; exact hw.symm
      _ = (g' ≫ Subobject.pullbackπ p' B) ≫ B.arrow := by rw [← Category.assoc]
      _ = 0 ≫ B.arrow := by rw [eq']
      _ = 0 := zero_comp
  exact KernelFork.IsLimit.ofι' (Subobject.ofLE M' pbB hle) hcomp
    (fun g' eq' ↦ ⟨hkernel.lift (KernelFork.ofι (g' ≫ pbB.arrow) (key g' eq')), by
      apply (cancel_mono pbB.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow]
      exact hkernel.fac (KernelFork.ofι (g' ≫ pbB.arrow) (key g' eq'))
        WalkingParallelPair.zero⟩)

/-- For the maximally destabilizing subobject `M'`, any nonzero subobject `B` of the
quotient `E/M'` has phase strictly less than `phase(M')`. -/
private lemma phase_subobject_cokernel_lt
    (Z : StabilityFunction A) {E : A} {M' : Subobject E}
    (hM'_ne : M' ≠ ⊥)
    (hM'_strict : ∀ B : Subobject E, M' < B → Z.phase (B : A) < Z.phase (M' : A))
    {B : Subobject (cokernel M'.arrow)} (hB : B ≠ ⊥) :
    Z.phase (B : A) < Z.phase (M' : A) := by
  set p' := cokernel.π M'.arrow
  set pbB := (Subobject.pullback p').obj B
  have hle := le_pullback_cokernel M' B
  have hlt : M' < pbB := by
    rcases hle.eq_or_lt with h | h
    · exfalso; apply hB
      exact ((pullback_obj_injective_of_epi p')
        (h ▸ pullback_cokernel_bot_eq M')).symm
    · exact h
  have hpbB_lt := hM'_strict pbB hlt
  have hse := shortExact_ofLE_pullbackπ_cokernel M' B
  have hM'_nz : ¬IsZero (M' : A) := by
    intro hZ; apply hM'_ne
    have : M'.arrow = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rwa [← Subobject.mk_arrow M', Subobject.mk_eq_bot_iff_zero]
  have hB_nz : ¬IsZero (B : A) := by
    intro hZ; apply hB
    have : B.arrow = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rwa [← Subobject.mk_arrow B, Subobject.mk_eq_bot_iff_zero]
  have hmin := Z.min_phase_le_of_shortExact _ hse hM'_nz hB_nz
  by_contra hge
  push Not at hge
  rw [min_eq_left hge] at hmin
  linarith

/-- Z-additivity for the pullback SES: `Z(pb'(B)) = Z(M') + Z(B)`. -/
lemma Zobj_pullback_eq_add
    (Z : StabilityFunction A) {E : A} (M' : Subobject E)
    (B : Subobject (cokernel M'.arrow)) :
    Z.Zobj (((Subobject.pullback (cokernel.π M'.arrow)).obj B) : A) =
      Z.Zobj (M' : A) + Z.Zobj (B : A) :=
  Z.additive _ (shortExact_ofLE_pullbackπ_cokernel M' B)

/-- The cokernel of pulled-back subobjects has the same Z-value as the original cokernel.
`Z(cokernel(ofLE pb'(A) pb'(B))) = Z(cokernel(ofLE A B))`. -/
private lemma Zobj_cokernel_pullback_eq
    (Z : StabilityFunction A) {E : A} (M' : Subobject E)
    {A' B' : Subobject (cokernel M'.arrow)} (h : A' ≤ B') :
    Z.Zobj (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M'.arrow)).obj A')
      ((Subobject.pullback (cokernel.π M'.arrow)).obj B')
      ((Subobject.pullback (cokernel.π M'.arrow)).monotone h))) =
      Z.Zobj (cokernel (Subobject.ofLE A' B' h)) := by
  have hse1 : (ShortComplex.mk
      (Subobject.ofLE _ _
        ((Subobject.pullback (cokernel.π M'.arrow)).monotone h))
      (cokernel.π (Subobject.ofLE _ _
        ((Subobject.pullback (cokernel.π M'.arrow)).monotone h)))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have hse2 : (ShortComplex.mk (Subobject.ofLE A' B' h)
      (cokernel.π (Subobject.ofLE A' B' h))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have h1 := Z.additive _ hse1
  have h2 := Z.additive _ hse2
  have hA := Zobj_pullback_eq_add Z M' A'
  have hB := Zobj_pullback_eq_add Z M' B'
  linear_combination -h1 + h2 - hA + hB

/-- The cokernel of consecutive pulled-back subobjects has the same phase as the
original cokernel factor. -/
lemma phase_cokernel_pullback_eq
    (Z : StabilityFunction A) {E : A} (M' : Subobject E)
    {A' B' : Subobject (cokernel M'.arrow)} (h : A' ≤ B') :
    Z.phase (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M'.arrow)).obj A')
      ((Subobject.pullback (cokernel.π M'.arrow)).obj B')
      ((Subobject.pullback (cokernel.π M'.arrow)).monotone h))) =
      Z.phase (cokernel (Subobject.ofLE A' B' h)) := by
  simp only [StabilityFunction.phase, Zobj_cokernel_pullback_eq Z M' h]

/-- The cokernel of consecutive pulled-back subobjects is isomorphic to the original
cokernel factor. -/
def cokernelPullbackIso (Z : StabilityFunction A) {E : A} (M' : Subobject E)
    {A' B' : Subobject (cokernel M'.arrow)} (h : A' < B') :
    cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M'.arrow)).obj A')
      ((Subobject.pullback (cokernel.π M'.arrow)).obj B')
      ((Subobject.pullback (cokernel.π M'.arrow)).monotone h.le)) ≅
      cokernel (Subobject.ofLE A' B' h.le) := by
  set p' := cokernel.π M'.arrow
  set pbA := (Subobject.pullback p').obj A'
  set pbB := (Subobject.pullback p').obj B'
  set hpb : pbA ≤ pbB := (Subobject.pullback p').monotone h.le
  -- Construct the induced map via cokernel.desc
  have hw_A := (Subobject.isPullback p' A').w
  have hw_B := (Subobject.isPullback p' B').w
  have hcomm : Subobject.ofLE pbA pbB hpb ≫ Subobject.pullbackπ p' B' =
      Subobject.pullbackπ p' A' ≫ Subobject.ofLE A' B' h.le := by
    apply (cancel_mono B'.arrow).mp
    simp only [Category.assoc, Subobject.ofLE_arrow]
    calc Subobject.ofLE pbA pbB hpb ≫ (Subobject.pullbackπ p' B' ≫ B'.arrow)
        = Subobject.ofLE pbA pbB hpb ≫ (pbB.arrow ≫ p') := by rw [hw_B]
      _ = (Subobject.ofLE pbA pbB hpb ≫ pbB.arrow) ≫ p' := by rw [Category.assoc]
      _ = pbA.arrow ≫ p' := by rw [Subobject.ofLE_arrow]
      _ = Subobject.pullbackπ p' A' ≫ A'.arrow := hw_A.symm
    -- Goal after simp: ... = pullbackπ p' A' ≫ A'.arrow
  have hfact : Subobject.ofLE pbA pbB hpb ≫
      (Subobject.pullbackπ p' B' ≫ cokernel.π (Subobject.ofLE A' B' h.le)) = 0 := by
    rw [← Category.assoc, hcomm, Category.assoc, cokernel.condition, comp_zero]
  set φ := cokernel.desc (Subobject.ofLE pbA pbB hpb)
    (Subobject.pullbackπ p' B' ≫ cokernel.π (Subobject.ofLE A' B' h.le)) hfact
  -- φ is epi
  haveI : Epi (Subobject.pullbackπ p' B') := epi_pullbackπ_of_epi p' B'
  haveI : Epi φ :=
    epi_of_epi_fac (cokernel.π_desc _ _ _)
  -- φ is mono: kernel must be zero since Z-values match
  haveI : Mono φ := by
    suffices hk : kernel.ι φ = 0 from Preadditive.mono_of_kernel_zero hk
    have hse_φ : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel φ) inferInstance inferInstance
    have hZ_add := Z.additive _ hse_φ
    -- hZ_add : Z(cokernel₁) = Z(kernel φ) + Z(cokernel₂)
    have hZ_eq : Z.Zobj (cokernel (Subobject.ofLE pbA pbB hpb)) =
        Z.Zobj (cokernel (Subobject.ofLE A' B' h.le)) :=
      Zobj_cokernel_pullback_eq Z M' h.le
    -- Substitute to get: Z(cokernel₂) = Z(kernel φ) + Z(cokernel₂)
    rw [hZ_eq] at hZ_add
    -- So Z(kernel φ) = 0
    have hZ_ker : Z.Zobj (kernel φ) = 0 := add_eq_right.mp hZ_add.symm
    by_contra hne
    have hker_nz : ¬IsZero (kernel φ) := fun hZ =>
      hne (zero_of_source_iso_zero _ hZ.isoZero)
    exact absurd hZ_ker (ne_of_mem_of_not_mem (Z.upper _ hker_nz)
      (show (0 : ℂ) ∉ upperHalfPlaneUnion from fun hc ↦ by
        rcases hc with hc | ⟨_, hc⟩ <;> simp at hc))
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  exact asIso φ

/-- Phase equality when `ofLE` subobject arguments are propositionally equal.
This avoids dependent rewriting issues inside `cokernel (Subobject.ofLE ...)`. -/
lemma phase_cokernel_ofLE_congr (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂} :
    Z.phase (cokernel (Subobject.ofLE A₁ B₁ h₁)) =
    Z.phase (cokernel (Subobject.ofLE A₂ B₂ h₂)) := by
  subst hA; subst hB; rfl

/-- Semistability transfer when `ofLE` subobject arguments are propositionally equal.
This avoids dependent rewriting issues inside `cokernel (Subobject.ofLE ...)`. -/
lemma isSemistable_cokernel_ofLE_congr (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂}
    (hs : Z.IsSemistable (cokernel (Subobject.ofLE A₂ B₂ h₂))) :
    Z.IsSemistable (cokernel (Subobject.ofLE A₁ B₁ h₁)) := by
  subst hA; subst hB; exact hs

/-- **Proposition 2.4** (Bridgeland): If every object of `A` has a finite subobject
lattice, then any stability function on `A` has the Harder-Narasimhan property.

The hypothesis `Finite (Subobject E)` follows from Artinian + Noetherian for abelian
categories (via modularity of the subobject lattice). We use it directly to find
the maximally destabilizing subobject (MDS).

The proof proceeds by induction on the cardinality of the subobject lattice.
For a nonzero object `E`: if `E` is semistable, it is its own HN filtration;
otherwise we find the MDS `M` (maximal phase, semistable), and recurse on the
quotient `E/M`, which has strictly fewer subobjects. -/
theorem StabilityFunction.hasHN_of_finiteLength (Z : StabilityFunction A)
    (hFinSub : ∀ (E : A), Finite (Subobject E)) :
    Z.HasHNProperty := by
  -- Prove by induction on Nat.card (Subobject E)
  suffices ∀ (k : ℕ) (E : A), ¬IsZero E →
      Nat.card (Subobject E) ≤ k → Nonempty (AbelianHNFiltration Z E) by
    intro E hE; exact this _ E hE le_rfl
  intro k
  induction k with
  | zero =>
    intro E hE hcard
    haveI := hFinSub E
    haveI : Fintype (Subobject E) := Fintype.ofFinite _
    haveI : Nonempty (Subobject E) := ⟨⊥⟩
    have : 0 < Nat.card (Subobject E) := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos
    lia
  | succ k ih =>
    intro E hE hcard
    haveI := hFinSub E
    by_cases hss : Z.IsSemistable E
    · -- E is semistable: single-factor HN filtration
      exact ⟨{
        n := 1
        hn := Nat.one_pos
        chain := fun i ↦ if i = 0 then ⊥ else ⊤
        chain_strictMono := by
          intro ⟨i, hi⟩ ⟨j, hj⟩ h
          simp only [Fin.lt_def] at h
          have hi0 : i = 0 := by lia
          have hj1 : j = 1 := by lia
          subst hi0; subst hj1
          simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ↓reduceIte,
            Fin.mk_one, one_ne_zero, gt_iff_lt]
          exact lt_of_le_of_ne bot_le
            (Ne.symm (subobject_top_ne_bot_of_not_isZero hE))
        chain_bot := by simp
        chain_top := by simp
        φ := fun _ ↦ Z.phase E
        φ_anti := fun a b h ↦ by exfalso; exact absurd h (by lia)
        factor_phase := by
          intro ⟨j, hj⟩
          have hj0 : j = 0 := by lia
          subst hj0
          change Z.phase (cokernel (Subobject.ofLE ⊥ ⊤ _)) = Z.phase E
          rw [Z.phase_eq_of_iso (Subobject.cokernelBotIso ⊤ bot_le)]
          exact Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow)
        factor_semistable := by
          intro ⟨j, hj⟩
          have hj0 : j = 0 := by lia
          subst hj0
          change Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ _))
          exact Z.isSemistable_of_iso
            ((asIso (⊤ : Subobject E).arrow).symm ≪≫
              (Subobject.cokernelBotIso ⊤ bot_le).symm) hss
      }⟩
    · -- E is not semistable: find MDS and recurse on the quotient
      obtain ⟨M', hM'_ne, hM'_max, hM'_strict⟩ :=
        exists_maxPhase_maximal_subobject Z E hE
      have hM'_ss := Z.maxPhase_isSemistable hM'_ne hM'_max
      have hM'_ne_top : M' ≠ ⊤ :=
        Z.maxPhase_ne_top_of_not_semistable hss M' hM'_ne hM'_max
      set Q' := cokernel M'.arrow
      have hQ'_nz : ¬IsZero Q' := cokernel_nonzero_of_ne_top hM'_ne_top
      have hcard_Q' : Nat.card (Subobject Q') < Nat.card (Subobject E) :=
        card_subobject_cokernel_lt hM'_ne
      haveI := hFinSub Q'
      obtain ⟨hn_Q'⟩ := ih Q' hQ'_nz (by lia)
      have hQ'n_pos := hn_Q'.hn
      -- Build the concatenated HN filtration
      set p' := cokernel.π M'.arrow
      set pb' := (Subobject.pullback p').obj
      have hpb_mono : StrictMono pb' :=
        (Subobject.pullback p').monotone.strictMono_of_injective
          (pullback_obj_injective_of_epi p')
      have hpb_bot : pb' (hn_Q'.chain ⟨0, Nat.zero_lt_succ _⟩) = M' := by
        rw [hn_Q'.chain_bot]; exact pullback_cokernel_bot_eq M'
      have hpb_top :
          pb' (hn_Q'.chain ⟨hn_Q'.n, hn_Q'.n.lt_succ_iff.mpr le_rfl⟩) = ⊤ := by
        rw [hn_Q'.chain_top]; exact Subobject.pullback_top p'
      -- Define the new chain: ⊥ at index 0, then pb'(Q'_j) for j = 0..m
      let newChain : Fin (hn_Q'.n + 2) → Subobject E :=
        fun i ↦ if (i : ℕ) = 0 then ⊥
          else pb' (hn_Q'.chain ⟨(i : ℕ) - 1, by lia⟩)
      have hNewBot : newChain ⟨0, by lia⟩ = ⊥ := by simp [newChain]
      have hNewTop : newChain ⟨hn_Q'.n + 1, by lia⟩ = ⊤ := by
        simp only [newChain, show hn_Q'.n + 1 ≠ 0 from by lia, ite_false]
        convert hpb_top using 2
      have hNewMono : StrictMono newChain := by
        apply Fin.strictMono_iff_lt_succ.mpr
        intro ⟨i, hi⟩
        change newChain ⟨i, by lia⟩ < newChain ⟨i + 1, by lia⟩
        by_cases hi0 : i = 0
        · subst hi0
          simp only [newChain, ite_true, show (0 + 1 : ℕ) ≠ 0 from by lia,
            ite_false]
          rw [hpb_bot]
          exact lt_of_le_of_ne bot_le (Ne.symm (subobject_ne_bot_of_not_isZero
            (subobject_not_isZero_of_ne_bot hM'_ne)))
        · simp only [newChain, hi0, ite_false, show i + 1 ≠ 0 from by lia]
          apply hpb_mono
          exact hn_Q'.chain_strictMono (by simp [Fin.lt_def]; lia)
      -- Key fact: all hn_Q' phases are < phase(M')
      have hQ'_phase_lt : ∀ j : Fin hn_Q'.n,
          hn_Q'.φ j < Z.phase (M' : A) := by
        intro j
        have h_ne : hn_Q'.chain ⟨1, by lia⟩ ≠ ⊥ := by
          intro h
          have := hn_Q'.chain_strictMono (Fin.mk_lt_mk.mpr (by lia) :
            (⟨0, by lia⟩ : Fin _) < ⟨1, by lia⟩)
          rw [hn_Q'.chain_bot, h] at this; exact lt_irrefl _ this
        have hsucc_ne :
            hn_Q'.chain (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).succ ≠ ⊥ := by
          intro h; exact lt_irrefl _
            (hn_Q'.chain_bot ▸ h ▸ hn_Q'.chain_strictMono
              (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).castSucc_lt_succ)
        have hcsc : hn_Q'.chain (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).castSucc =
            ⊥ :=
          (congrArg hn_Q'.chain (Fin.ext rfl)).trans hn_Q'.chain_bot
        have h0_lt : hn_Q'.φ ⟨0, hn_Q'.hn⟩ < Z.phase (M' : A) := by
          rw [← hn_Q'.factor_phase ⟨0, hn_Q'.hn⟩]
          have h_eq : Z.phase (cokernel (Subobject.ofLE
              (hn_Q'.chain (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).castSucc)
              (hn_Q'.chain (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).succ)
              (le_of_lt (hn_Q'.chain_strictMono
                (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).castSucc_lt_succ)))) =
            Z.phase ((hn_Q'.chain
              (⟨0, hn_Q'.hn⟩ : Fin hn_Q'.n).succ : A)) :=
            (phase_cokernel_ofLE_congr Z hcsc rfl).trans
              (Z.phase_eq_of_iso (Subobject.cokernelBotIso _ bot_le))
          linarith [phase_subobject_cokernel_lt Z hM'_ne hM'_strict
            hsucc_ne]
        calc hn_Q'.φ j
            ≤ hn_Q'.φ ⟨0, hn_Q'.hn⟩ :=
              hn_Q'.φ_anti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ < Z.phase (M' : A) := h0_lt
      -- Helper: for j ≥ 1, newChain(castSucc ⟨j,_⟩) = pb'(chain ⟨j-1,_⟩)
      have hNC_cs : ∀ (j : ℕ) (hj : j < hn_Q'.n + 1), j ≠ 0 →
          newChain (Fin.castSucc ⟨j, hj⟩) =
            pb' (hn_Q'.chain ⟨j - 1, by lia⟩) :=
        fun j _ hj0 ↦ if_neg hj0
      -- Helper: newChain(succ ⟨j,_⟩) = pb'(chain ⟨j,_⟩)
      have hNC_s : ∀ (j : ℕ) (hj : j < hn_Q'.n + 1),
          newChain (Fin.succ ⟨j, hj⟩) =
            pb' (hn_Q'.chain ⟨j, by lia⟩) :=
        fun j _ ↦ if_neg (Nat.succ_ne_zero j)
      -- Helper: chain ⟨j,_⟩ = chain(⟨j-1,_⟩.succ) for j ≥ 1
      have hChain_succ : ∀ (j : ℕ) (hj : j < hn_Q'.n + 1),
          j ≠ 0 → hn_Q'.chain ⟨j, by lia⟩ =
            hn_Q'.chain (⟨j - 1, by lia⟩ : Fin hn_Q'.n).succ :=
        fun j _ hj0 ↦ congrArg hn_Q'.chain
          (Fin.ext (show j = (j - 1) + 1 by lia))
      -- Build the AbelianHNFiltration
      refine ⟨{
        n := hn_Q'.n + 1
        hn := Nat.succ_pos _
        chain := newChain
        chain_strictMono := hNewMono
        chain_bot := hNewBot
        chain_top := hNewTop
        φ := fun ⟨j, hj⟩ ↦ if j = 0 then Z.phase (M' : A)
          else hn_Q'.φ ⟨j - 1, by lia⟩
        φ_anti := by
          intro ⟨i, hi⟩ ⟨j, hj⟩ hij
          simp only [Fin.lt_def] at hij
          simp only
          by_cases hi0 : i = 0
          · subst hi0; simp only [ite_true]
            have hj0 : j ≠ 0 := by lia
            simp only [hj0, ite_false]
            calc hn_Q'.φ ⟨j - 1, by lia⟩
                ≤ hn_Q'.φ ⟨0, hn_Q'.hn⟩ :=
                  hn_Q'.φ_anti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
              _ < Z.phase (M' : A) :=
                  hQ'_phase_lt ⟨0, hn_Q'.hn⟩
          · have hj0 : j ≠ 0 := by lia
            simp only [hi0, ite_false, hj0]
            exact hn_Q'.φ_anti (Fin.mk_lt_mk.mpr (by lia))
        factor_phase := ?_
        factor_semistable := ?_ }⟩
      · -- factor_phase
        intro ⟨j, hj⟩
        simp only
        by_cases hj0 : j = 0
        · -- j = 0: factor ≅ M' via cokernelBotIso + hpb_bot
          subst hj0; simp only [ite_true]
          apply Z.phase_eq_of_iso
          exact Subobject.cokernelBotIso _ bot_le ≪≫
            eqToIso (congrArg (Subobject.underlying.obj ·) hpb_bot)
        · -- j ≥ 1: bridge newChain → pb' → chain → factor_phase
          simp only [hj0, ite_false]
          have h_le : hn_Q'.chain ⟨j - 1, by lia⟩ ≤
              hn_Q'.chain ⟨j, by lia⟩ :=
            le_of_lt (hn_Q'.chain_strictMono (Fin.mk_lt_mk.mpr (by lia)))
          exact (phase_cokernel_ofLE_congr Z
              (hNC_cs j hj hj0) (hNC_s j hj)).trans
            ((phase_cokernel_pullback_eq Z M' h_le).trans
            ((phase_cokernel_ofLE_congr Z rfl
              (hChain_succ j hj hj0)).trans
            (hn_Q'.factor_phase ⟨j - 1, by lia⟩)))
      · -- factor_semistable
        intro ⟨j, hj⟩
        by_cases hj0 : j = 0
        · -- j = 0: factor ≅ M' (semistable by hM'_ss)
          subst hj0
          exact Z.isSemistable_of_iso
            ((Subobject.cokernelBotIso _ bot_le ≪≫
              eqToIso (congrArg (Subobject.underlying.obj ·)
                hpb_bot)).symm) hM'_ss
        · -- j ≥ 1: bridge via congr lemmas
          have h_lt : hn_Q'.chain ⟨j - 1, by lia⟩ <
              hn_Q'.chain ⟨j, by lia⟩ :=
            hn_Q'.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
          exact isSemistable_cokernel_ofLE_congr Z
            (hNC_cs j hj hj0) (hNC_s j hj)
            (Z.isSemistable_of_iso (cokernelPullbackIso Z M' h_lt).symm
              (isSemistable_cokernel_ofLE_congr Z rfl
                (hChain_succ j hj hj0)
                (hn_Q'.factor_semistable ⟨j - 1, by lia⟩)))

/-- The quotient of a quotient, expressed via a pulled-back kernel in the source, is
canonically isomorphic to the quotient in the intermediate object. -/
noncomputable def cokernelPullbackTopIso (Z : StabilityFunction A) {E : A}
    (M : Subobject E) {B : Subobject (cokernel M.arrow)} (hB : B ≠ ⊤) :
    cokernel ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow ≅ cokernel B.arrow := by
  let p := cokernel.π M.arrow
  have hlt : B < ⊤ := lt_of_le_of_ne le_top hB
  haveI : IsIso (((Subobject.pullback p).obj ⊤).arrow) := by
    rw [Subobject.pullback_top]
    infer_instance
  calc
    cokernel (((Subobject.pullback p).obj B).arrow)
      ≅ cokernel
          (Subobject.ofLE ((Subobject.pullback p).obj B) ((Subobject.pullback p).obj ⊤)
            ((Subobject.pullback p).monotone le_top)) :=
        cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _
    _ ≅ cokernel (Subobject.ofLE B ⊤ le_top) :=
        cokernelPullbackIso Z M hlt
    _ ≅ cokernel B.arrow :=
        (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _).symm

/-- If `A` is a semistable subobject of `E` with strictly larger phase than `E`, then the
quotient `E/A` has phase at most the phase of `E`. -/
lemma phase_cokernel_le_of_destabilizing_semistable_subobject
    (Z : StabilityFunction A) {E : A} {A' : Subobject E}
    (hA'_ss : Z.IsSemistable (A' : A)) (hA'_phase : Z.phase E < Z.phase (A' : A))
    (hA'_top : A' ≠ ⊤) :
    Z.phase (cokernel A'.arrow) ≤ Z.phase E := by
  have hA'_nz : ¬IsZero (A' : A) := hA'_ss.1
  have hQ_nz : ¬IsZero (cokernel A'.arrow) := cokernel_nonzero_of_ne_top hA'_top
  have hse : (ShortComplex.mk A'.arrow (cokernel.π A'.arrow)
      (cokernel.condition A'.arrow)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel A'.arrow) inferInstance inferInstance
  have hmin := Z.min_phase_le_of_shortExact _ hse hA'_nz hQ_nz
  by_contra hgt
  have hmin_gt : Z.phase E < min (Z.phase (A' : A)) (Z.phase (cokernel A'.arrow)) :=
    lt_min hA'_phase (lt_of_not_ge hgt)
  exact (not_lt_of_ge hmin) hmin_gt

/-- In the same situation, the quotient actually has strictly smaller phase. This is the
strict quotient inequality used in Bridgeland's Proposition 2.4 when ruling out
non-semistable minimal-phase quotients. -/
lemma phase_cokernel_lt_of_destabilizing_semistable_subobject
    (Z : StabilityFunction A) {E : A} {A' : Subobject E}
    (hA'_ss : Z.IsSemistable (A' : A)) (hA'_phase : Z.phase E < Z.phase (A' : A))
    (hA'_top : A' ≠ ⊤) :
    Z.phase (cokernel A'.arrow) < Z.phase E := by
  have hA'_nz : ¬IsZero (A' : A) := hA'_ss.1
  have hQ_nz : ¬IsZero (cokernel A'.arrow) := cokernel_nonzero_of_ne_top hA'_top
  have hse : (ShortComplex.mk A'.arrow (cokernel.π A'.arrow)
      (cokernel.condition A'.arrow)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel A'.arrow) inferInstance inferInstance
  have hA_arg : arg (Z.Zobj E) < arg (Z.Zobj (A' : A)) := by
    unfold StabilityFunction.phase at hA'_phase
    exact lt_of_mul_lt_mul_left hA'_phase (div_pos one_pos Real.pi_pos).le
  have hadd : Z.Zobj E = Z.Zobj (A' : A) + Z.Zobj (cokernel A'.arrow) := Z.additive _ hse
  have hA_mem := Z.upper (A' : A) hA'_nz
  have hQ_mem := Z.upper (cokernel A'.arrow) hQ_nz
  have hne : arg (Z.Zobj (A' : A)) ≠ arg (Z.Zobj (cokernel A'.arrow)) := by
    intro hEq
    have hsum_ge : arg (Z.Zobj (A' : A)) ≤ arg (Z.Zobj E) := by
      rw [hadd]
      calc
        arg (Z.Zobj (A' : A))
            = min (arg (Z.Zobj (A' : A))) (arg (Z.Zobj (cokernel A'.arrow))) := by
              rw [hEq, min_eq_left le_rfl]
        _ ≤ arg (Z.Zobj (A' : A) + Z.Zobj (cokernel A'.arrow)) :=
          min_arg_le_arg_add hA_mem hQ_mem
    exact not_le_of_gt hA_arg hsum_ge
  by_contra hge
  push Not at hge
  have hQ_arg : arg (Z.Zobj E) ≤ arg (Z.Zobj (cokernel A'.arrow)) := by
    unfold StabilityFunction.phase at hge
    exact le_of_mul_le_mul_left hge (div_pos one_pos Real.pi_pos)
  have hmin_ge :
      arg (Z.Zobj E) ≤ min (arg (Z.Zobj (A' : A))) (arg (Z.Zobj (cokernel A'.arrow))) :=
    le_min hA_arg.le hQ_arg
  have hmin_lt :
      min (arg (Z.Zobj (A' : A))) (arg (Z.Zobj (cokernel A'.arrow))) < arg (Z.Zobj E) := by
    rw [hadd]
    exact min_arg_lt_arg_add hA_mem hQ_mem hne
  exact not_lt_of_ge hmin_ge hmin_lt

/-- A faithful Artinian/Noetherian substitute for Bridgeland's quotient-selection step:
every nonzero object admits a nonzero semistable quotient whose phase is at most that of the
object. The proof follows the paper's recursive quotient construction, with termination
supplied by Noetherianity. -/
theorem exists_semistable_quotient_le_phase_of_artinian_noetherian
    (Z : StabilityFunction A) {E : A} [IsArtinianObject E] [IsNoetherianObject E]
    (hE : ¬IsZero E) :
    ∃ (Q : A) (p : E ⟶ Q), Epi p ∧ ¬IsZero Q ∧ Z.IsSemistable Q ∧ Z.phase Q ≤ Z.phase E := by
  suffices
      ∀ (S : Subobject E), ¬IsZero (cokernel S.arrow) →
        ∃ (Q : A) (p : cokernel S.arrow ⟶ Q), Epi p ∧ ¬IsZero Q ∧
          Z.IsSemistable Q ∧ Z.phase Q ≤ Z.phase (cokernel S.arrow) by
    let e0 : cokernel (⊥ : Subobject E).arrow ≅ E := by
      simpa [Subobject.bot_arrow] using
        (cokernelZeroIsoTarget (X := ((⊥ : Subobject E) : A)) (Y := E))
    have hbot : ¬IsZero (cokernel (⊥ : Subobject E).arrow) := fun hZ =>
      hE (hZ.of_iso e0.symm)
    obtain ⟨Q, p, hp, hQ_nz, hQ_ss, hQ_phase⟩ := this ⊥ hbot
    refine ⟨Q, e0.inv ≫ p, ?_, hQ_nz, hQ_ss, ?_⟩
    · haveI : Epi p := hp
      infer_instance
    · simpa [Subobject.bot_arrow] using
        hQ_phase.trans_eq (Z.phase_eq_of_iso e0)
  intro S
  induction S using WellFoundedGT.induction with
  | ind S ih =>
      intro hQS_nz
      let QS := cokernel S.arrow
      haveI : IsArtinianObject QS := isArtinianObject_of_epi (cokernel.π S.arrow)
      haveI : IsNoetherianObject QS := isNoetherianObject_of_epi (cokernel.π S.arrow)
      by_cases hQS_ss : Z.IsSemistable QS
      · exact ⟨QS, 𝟙 _, inferInstance, hQS_nz, hQS_ss, le_rfl⟩
      · obtain ⟨A', hA'_ne, hA'_ss, hA'_phase⟩ :=
          Z.exists_semistable_subobject_gt_phase_of_not_semistable (E := QS) hQS_nz hQS_ss
        have hA'_top : A' ≠ ⊤ := by
          intro hA'_eq
          have hphase_eq : Z.phase (A' : A) = Z.phase QS := by
            rw [hA'_eq]
            exact Z.phase_eq_of_iso (asIso (⊤ : Subobject QS).arrow)
          linarith
        let T : Subobject E := (Subobject.pullback (cokernel.π S.arrow)).obj A'
        have hST_le : S ≤ T := le_pullback_cokernel S A'
        have hST_lt : S < T := by
          rcases hST_le.eq_or_lt with h | h
          · exfalso
            have hpb :
                (Subobject.pullback (cokernel.π S.arrow)).obj ⊥ =
                  (Subobject.pullback (cokernel.π S.arrow)).obj A' := by
              calc
                (Subobject.pullback (cokernel.π S.arrow)).obj ⊥ = S :=
                  pullback_cokernel_bot_eq S
                _ = T := h
                _ = (Subobject.pullback (cokernel.π S.arrow)).obj A' := rfl
            apply hA'_ne
            exact ((pullback_obj_injective_of_epi (cokernel.π S.arrow)) hpb).symm
          · exact h
        let eT : cokernel T.arrow ≅ cokernel A'.arrow :=
          cokernelPullbackTopIso Z S hA'_top
        have hQT_nz : ¬IsZero (cokernel T.arrow) := fun hZ =>
          (cokernel_nonzero_of_ne_top hA'_top) (hZ.of_iso eT.symm)
        obtain ⟨R, r, hr_epi, hR_nz, hR_ss, hR_phase⟩ := ih T hST_lt hQT_nz
        haveI : Epi r := hr_epi
        have hA'_cok_phase :
            Z.phase (cokernel A'.arrow) ≤ Z.phase QS :=
          phase_cokernel_le_of_destabilizing_semistable_subobject Z hA'_ss hA'_phase hA'_top
        refine ⟨R, cokernel.π A'.arrow ≫ eT.inv ≫ r, ?_, hR_nz, hR_ss, ?_⟩
        · infer_instance
        · calc
            Z.phase R ≤ Z.phase (cokernel T.arrow) := hR_phase
            _ = Z.phase (cokernel A'.arrow) := Z.phase_eq_of_iso eT
            _ ≤ Z.phase QS := hA'_cok_phase

/-- For a semistable object `E`, every nonzero epi quotient has phase `≥ phase(E)`.
This uses the phase see-saw and the semistability condition. -/
lemma phase_le_of_epi (Z : StabilityFunction A)
    {E Q : A} (p : E ⟶ Q) [Epi p] (hss : Z.IsSemistable E) (hQ : ¬IsZero Q) :
    Z.phase E ≤ Z.phase Q := by
  by_cases hker : IsZero (kernel p)
  · haveI : Mono p := Preadditive.mono_of_kernel_zero
      (zero_of_source_iso_zero _ hker.isoZero)
    haveI := isIso_of_mono_of_epi p
    exact le_of_eq (Z.phase_eq_of_iso (asIso p))
  · -- K → E → Q short exact, K = kernel p
    have hK_sub : Z.phase (kernel p) ≤ Z.phase E := by
      calc Z.phase (kernel p)
          = Z.phase (kernelSubobject p : A) :=
            Z.phase_eq_of_iso (kernelSubobjectIso p).symm
        _ ≤ Z.phase E := by
            apply hss.2
            intro hZ
            exact hker (hZ.of_iso (kernelSubobjectIso p).symm)
    by_contra hlt
    push Not at hlt
    have hadd : Z.Zobj E = Z.Zobj (kernel p) + Z.Zobj Q :=
      Z.additive _
        (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance)
    have hK_mem := Z.upper (kernel p) hker
    have hQ_mem := Z.upper Q hQ
    -- Convert phase inequalities to arg inequalities
    have pi_pos := Real.pi_pos
    have hargK : arg (Z.Zobj (kernel p)) ≤ arg (Z.Zobj E) := by
      unfold StabilityFunction.phase at hK_sub
      exact le_of_mul_le_mul_left (by linarith) (div_pos one_pos pi_pos)
    have hargQ : arg (Z.Zobj Q) < arg (Z.Zobj E) := by
      unfold StabilityFunction.phase at hlt
      exact lt_of_mul_lt_mul_left (by linarith) (div_pos one_pos pi_pos).le
    rw [hadd] at hargK hargQ
    -- hargK : arg(Z(K)) ≤ arg(Z(K)+Z(Q))
    -- hargQ : arg(Z(Q)) < arg(Z(K)+Z(Q))
    have hub := arg_add_le_max hK_mem hQ_mem
    -- hub : arg(Z(K)+Z(Q)) ≤ max(arg(Z(K)), arg(Z(Q)))
    -- From hargQ and hub: arg(Z(Q)) < max(arg(Z(K)), arg(Z(Q)))
    have hQ_lt_max : arg (Z.Zobj Q) < max (arg (Z.Zobj (kernel p))) (arg (Z.Zobj Q)) :=
      lt_of_lt_of_le hargQ hub
    have hK_gt_Q : arg (Z.Zobj Q) < arg (Z.Zobj (kernel p)) := by
      rcases lt_max_iff.mp hQ_lt_max with h | h
      · exact h
      · exact absurd h (lt_irrefl _)
    have hne : arg (Z.Zobj (kernel p)) ≠ arg (Z.Zobj Q) := ne_of_gt hK_gt_Q
    have hstrict := arg_add_lt_max hK_mem hQ_mem hne
    rw [max_eq_left hK_gt_Q.le] at hstrict
    linarith

/-- Hom-vanishing between semistable objects of different phases: if `E` is semistable
with `phase(E) > phase(F)` and `F` is semistable, then every morphism `E → F` is zero. -/
lemma hom_zero_of_semistable_phase_gt (Z : StabilityFunction A)
    {E F : A} (hE : Z.IsSemistable E) (hF : Z.IsSemistable F)
    (hph : Z.phase F < Z.phase E) (f : E ⟶ F) : f = 0 := by
  by_contra hf
  have hI : ¬IsZero (Limits.image f) := by
    intro hZ
    apply hf
    have : Limits.image.ι f = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rw [← Limits.image.fac f, this, comp_zero]
  have hge := phase_le_of_epi Z (factorThruImage f) hE hI
  have hle : Z.phase (Limits.image f) ≤ Z.phase F := by
    calc Z.phase (Limits.image f)
        = Z.phase (imageSubobject f : A) :=
          Z.phase_eq_of_iso (imageSubobjectIso f).symm
      _ ≤ Z.phase F := by
          apply hF.2
          intro hZ
          exact hI (hZ.of_iso (imageSubobjectIso f).symm)
  linarith

end CategoryTheory
