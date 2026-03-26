/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.TStructure
public import BridgelandStability.Deformation.IntervalAbelian
public import BridgelandStability.Deformation.PhiPlusHN

/-!
# Deformation of Stability Conditions — Theorem71

Deformed slicing construction, main theorem, Theorem 1.2
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Intermediate lemmas (Bridgeland §7, p.23–24) -/

/-- **Lemma 7.7 interior HN** (ssf version, Bridgeland p.23). Every nonzero object in
the interior `P((a+2ε, b−4ε))` of a thin finite-length interval `P((a,b))` has an HN
filtration whose factors are `ssf.Semistable` in `P((a,b))` with phases in `(a+ε, b−ε)`.

**Sorry**: Core of Lemma 7.7 — requires class G/H induction on the Noetherian strict
subobject lattice, propagating phase bounds via Lemma 7.3 (phase confinement). -/
theorem interior_has_enveloped_HN_ssf
    [IsTriangulated C]
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ε : ℝ} (hε : 0 < ε) (hε10 : ε < 1 / 10)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hFL : ThinFiniteLengthInInterval (C := C) σ a b)
    {E : C} (hE : ¬IsZero E)
    (hInt : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) E) :
    let ssf := σ.skewedStabilityFunction_of_near C W hW hab
    ∃ G : HNFiltration C (fun ψ F => ssf.Semistable C F ψ) E,
      ∀ j, a + ε < G.φ j ∧ G.φ j < b - ε := by
  let ssf := σ.skewedStabilityFunction_of_near C W hW hab
  have hε2 : ε < 1 / 4 := by linarith
  -- E ∈ P((a, b)) via interval monotonicity
  have hE_ab : σ.slicing.intervalProp C a b E :=
    σ.slicing.intervalProp_mono C (by linarith) (by linarith) hInt
  -- Lift E to IntervalCat(a,b)
  let XI : σ.slicing.IntervalCat C a b := ⟨E, hE_ab⟩
  have hXI_ne : ¬IsZero XI := by
    intro hZ; exact hE (((σ.slicing.intervalProp C a b).ι).map_isZero hZ)
  -- Global perturbation bounds
  have hthin' : b - a < 1 := by linarith
  have hpert := hperturb_of_stabSeminorm C σ W hW hthin' hε hε2 hsin
  have hsmall : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * (b - a) / 2)) :=
    stabSeminorm_lt_cos_of_hsin_hthin (C := C) (σ := σ) (W := W) hab hε hthin hsin
  -- W ≠ 0 for nonzero interval objects
  have hW_ne : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0 := fun hF hFne =>
    σ.W_ne_zero_of_intervalProp C W hthin' hsmall hFne hF
  -- Perturbation bounds for global window (stated in terms of W and (a+b)/2 directly)
  have hW_ne_sem : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b → W (K₀.of C F) ≠ 0 := fun F φ hP hFne _ _ =>
    σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  have hpert_lo : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      a - ε < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
      wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < a - ε + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hpert_hi : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      b + ε - 1 < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
      wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b + ε := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  -- Global window: L = a - ε, U = b + ε
  have hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      a - ε < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b + ε := fun hF hFne =>
    ⟨wPhaseOf_gt_of_intervalProp C σ hFne W
        (by linarith [hab]) hF hW_ne_sem hpert_lo,
      wPhaseOf_lt_of_intervalProp C σ hFne W
        (by linarith [hab]) hF hW_ne_sem hpert_hi⟩
  have hWidth : (b + ε) - (a - ε) < 1 := by linarith
  -- Part A: Apply φ⁺ reduction recursion (replaces hHom + hDestabBound sorry path)
  have hε8 : ε < 1 / 8 := by linarith
  have h_wide : 6 * ε ≤ b - a := by
    have h1 := σ.slicing.phiMinus_gt_of_intervalProp C hE hInt
    have h2 := σ.slicing.phiPlus_lt_of_intervalProp C hE hInt
    have h3 := σ.slicing.phiMinus_le_phiPlus C E hE
    linarith
  obtain ⟨G, hGφ⟩ :=
    hn_exists_with_phiPlus_reduction
      (C := C) σ W hW hab hε hε2 hε8 hthin hsin hFL hW_ne
      (L := a - ε) (U := b + ε) hWindow hWidth
      (a + ε) (le_refl _) XI hXI_ne
      (fun {B} q hq hBne ↦ by
        simpa [ssf, StabilityCondition.skewedStabilityFunction_of_near] using
          wPhaseOf_gt_of_strictQuotient_of_inner_strip
            (C := C) (σ := σ) (W := W) (hW := hW) hε hε2 hthin hsin
            (X := XI) hInt q hq hBne)
      (by linarith) h_wide
      (fun hXne => σ.slicing.phiPlus_lt_of_intervalProp C hXne hInt)
  -- Phase lower bound is immediate: a + ε < G.φ j
  -- Part B: Tight upper bound on phases (Bridgeland p.23 argument)
  -- The first HN factor F₁ has phase ψ₁ < b - 3ε
  have hGn : 0 < G.n := by
    by_contra h; push_neg at h
    exact hE (G.toPostnikovTower.zero_isZero (show G.n = 0 by lia))
  set P := G.toPostnikovTower with hP_def
  -- F₁ = factor 0 is ssf-semistable with phase G.φ ⟨0, hGn⟩
  have hF₁_ss : ssf.Semistable C (P.factor ⟨0, hGn⟩) (G.φ ⟨0, hGn⟩) :=
    G.semistable ⟨0, hGn⟩
  have hF₁_ne : ¬IsZero (P.factor ⟨0, hGn⟩) := hF₁_ss.nonzero
  -- Phase confinement: phiMinus(F₁) > G.φ ⟨0, hGn⟩ - ε
  have hψ₁_conf := phase_confinement_from_stabSeminorm C σ W hW hab hε hε2 hthin hsin hF₁_ss
  -- phiPlus(E) < b - 4ε (from E ∈ P((a+2ε, b-4ε)))
  have hE_phiPlus : σ.slicing.phiPlus C E hE < b - 4 * ε :=
    σ.slicing.phiPlus_lt_of_intervalProp C hE hInt
  -- Tight upper bound: ψ(F₁) < b - 3ε (Bridgeland p.23, ¶2)
  -- "there is a nonzero map F₁ → E" (from chain(1) ≅ F₁ ↪ chain(n) ≅ E in the
  -- abelian category A = IntervalCat(a,b), the PostnikovTower inclusion is mono)
  -- "together with Lemma 7.3 ensures that ψ(F₁) < b - 3ε":
  --   phase confinement: phiMinus(F₁) > ψ(F₁) - ε
  --   σ-Hom vanishing contrapositive: phiMinus(F₁) ≤ phiPlus(E) (since Hom(F₁,E) ≠ 0)
  --   E ∈ P((a+2ε, b-4ε)): phiPlus(E) < b - 4ε
  --   combining: ψ(F₁) - ε < phiMinus(F₁) ≤ phiPlus(E) < b - 4ε → ψ(F₁) < b - 3ε
  have hψ₁_bound : G.φ ⟨0, hGn⟩ < b - 3 * ε := by
    -- Strategy: phiPlus chain monotonicity. Show phiPlus(chain(1)) ≤ phiPlus(E) < b-4ε,
    -- then chain(1) ≅ F₁ gives phiPlus(F₁) < b-4ε, combined with phase confinement
    -- ψ₁ - ε < phiMinus(F₁) ≤ phiPlus(F₁) yields ψ₁ < b - 3ε.
    have hfactors_ab : ∀ i, σ.slicing.intervalProp C a b (P.factor i) :=
      fun i ↦ (G.semistable i).1
    have hPn : P.n = G.n := rfl
    have hchain_int : ∀ k (hk : k ≤ P.n),
        σ.slicing.intervalProp C a b (P.chain.obj' k (by lia)) :=
      fun k hk ↦ intervalProp_chain_of_postnikovTower σ.slicing (C := C) P hfactors_ab k hk
    have hab1 : b ≤ a + 1 := by linarith [Fact.out (p := b - a ≤ 1)]
    -- chain(1) is nonzero: chain(0) = 0, first triangle ⟹ chain(1) ≅ F₁ ≠ 0
    have hchain1_ne : ¬IsZero (P.chain.obj' 1 (by lia)) := by
      intro hZ
      let T0 := P.triangle ⟨0, hGn⟩
      have hobj₂_z : IsZero T0.obj₂ :=
        (Iso.isZero_iff (Classical.choice (P.triangle_obj₂ ⟨0, hGn⟩))).mpr hZ
      haveI : IsIso T0.mor₂ :=
        (Triangle.isZero₁_iff_isIso₂ T0 (P.triangle_dist ⟨0, hGn⟩)).mp
          ((Iso.isZero_iff (Classical.choice (P.triangle_obj₁ ⟨0, hGn⟩))).mpr P.base_isZero)
      exact hF₁_ne ((Iso.isZero_iff (asIso T0.mor₂)).mp hobj₂_z)
    -- Backward induction: phiPlus(chain(k)) ≤ phiPlus(E) for 1 ≤ k ≤ P.n
    suffices hmain : ∀ d k (hle : k ≤ P.n), k + d = P.n → 0 < k →
        (hne : ¬IsZero (P.chain.obj' k (by lia))) →
        σ.slicing.phiPlus C (P.chain.obj' k (by lia)) hne ≤
          σ.slicing.phiPlus C E hE by
      have h1_le := hmain (P.n - 1) 1 (by lia) (by lia) (by lia) hchain1_ne
      -- Transport: phiPlus(F₁) = phiPlus(chain(1))
      obtain ⟨Fch, hnch, hnech⟩ := HNFiltration.exists_nonzero_first C σ.slicing hchain1_ne
      have hIsIso0 : IsIso (P.triangle ⟨0, hGn⟩).mor₂ :=
        (Triangle.isZero₁_iff_isIso₂ _ (P.triangle_dist ⟨0, hGn⟩)).mp
          ((Iso.isZero_iff (Classical.choice (P.triangle_obj₁ ⟨0, hGn⟩))).mpr P.base_isZero)
      have h_F₁_eq : σ.slicing.phiPlus C (P.factor ⟨0, hGn⟩) hF₁_ne = Fch.φ ⟨0, hnch⟩ :=
        σ.slicing.phiPlus_eq C _ hF₁_ne
          (Fch.ofIso C ((Classical.choice (P.triangle_obj₂ ⟨0, hGn⟩)).symm.trans
            (@asIso _ _ _ _ (P.triangle ⟨0, hGn⟩).mor₂ hIsIso0))) hnch hnech
      have h_ch1_eq := σ.slicing.phiPlus_eq C _ hchain1_ne Fch hnch hnech
      linarith [hψ₁_conf.1, σ.slicing.phiMinus_le_phiPlus C (P.factor ⟨0, hGn⟩) hF₁_ne]
    intro d; induction d with
    | zero =>
      intro k hle hk _ hne
      have hkG : k = P.n := by lia
      subst hkG
      exact le_of_eq (by
        obtain ⟨F, hn, hneF⟩ := HNFiltration.exists_nonzero_first C σ.slicing hne
        rw [σ.slicing.phiPlus_eq C _ hne F hn hneF,
            σ.slicing.phiPlus_eq C _ hE (F.ofIso C (Classical.choice P.top_iso)) hn hneF]
        simp [HNFiltration.ofIso])
    | succ d ih =>
      intro k hle hk hkpos hne
      have hkn : k < P.n := by lia
      let Tk := P.triangle ⟨k, hkn⟩
      let ek₁ := Classical.choice (P.triangle_obj₁ ⟨k, hkn⟩)
      let ek₂ := Classical.choice (P.triangle_obj₂ ⟨k, hkn⟩)
      have hTk_ne₁ : ¬IsZero Tk.obj₁ := fun hZ ↦ hne ((Iso.isZero_iff ek₁).mp hZ)
      -- chain(k+1) must be nonzero (if zero: factor(k) ≅ chain(k)[1] has σ-phases
      -- in (a+1, b+1), disjoint from (a, b), contradicting factor(k) ∈ P((a,b)))
      by_cases hk1z : IsZero (P.chain.obj' (k + 1) (by lia))
      · exfalso
        have hTk_obj2_z : IsZero Tk.obj₂ := (Iso.isZero_iff ek₂).mpr hk1z
        haveI : IsIso Tk.mor₃ :=
          (Triangle.isZero₂_iff_isIso₃ Tk (P.triangle_dist ⟨k, hkn⟩)).mp hTk_obj2_z
        have hfact_ne : ¬IsZero (P.factor ⟨k, hkn⟩) := by
          intro hfz; exact hTk_ne₁
            ((Triangle.isZero₁_iff _ (P.triangle_dist ⟨k, hkn⟩)).mpr
              ⟨hTk_obj2_z.eq_of_tgt _ _, hfz.eq_of_src _ _⟩)
        have hfact_shift : σ.slicing.intervalProp C (a + 1) (b + 1) (P.factor ⟨k, hkn⟩) := by
          rcases hchain_int k (by lia) with hZ | ⟨F, hF⟩
          · exact absurd hZ hne
          · exact Or.inr
              ⟨((F.ofIso C ek₁.symm).shiftHN C σ.slicing 1).ofIso C (asIso Tk.mor₃).symm,
                fun i ↦ by
                  simp only [HNFiltration.ofIso, HNFiltration.shiftHN, Int.cast_one]
                  constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
        have hid := σ.slicing.intervalHom_eq_zero C hfact_shift (hfactors_ab ⟨k, hkn⟩) hab1
          (𝟙 (P.factor ⟨k, hkn⟩))
        apply hfact_ne
        rw [IsZero.iff_id_eq_zero]
        exact hid
      · -- chain(k+1) nonzero: phiPlus_triangle_le + iso transport + IH
        have hk1ne : ¬IsZero (P.chain.obj' (k + 1) (by lia)) := hk1z
        have hTk_ne₂ : ¬IsZero Tk.obj₂ := fun hZ ↦ hk1ne ((Iso.isZero_iff ek₂).mp hZ)
        have hTk_obj1_int : σ.slicing.intervalProp C a b Tk.obj₁ :=
          (σ.slicing.intervalProp_closedUnderIso C _ _).of_iso ek₁.symm
            (hchain_int k (by lia))
        have hle_step := σ.slicing.phiPlus_triangle_le C hTk_ne₁ hTk_ne₂
          hab1 hTk_obj1_int (hfactors_ab ⟨k, hkn⟩) (P.triangle_dist ⟨k, hkn⟩)
        have hk1_le := ih (k + 1) (by lia) (by lia) (by lia) hk1ne
        have h_eq₁ : σ.slicing.phiPlus C Tk.obj₁ hTk_ne₁ =
            σ.slicing.phiPlus C _ hne := by
          obtain ⟨F, hn, hneF⟩ := HNFiltration.exists_nonzero_first C σ.slicing hTk_ne₁
          rw [σ.slicing.phiPlus_eq C _ hTk_ne₁ F hn hneF,
              σ.slicing.phiPlus_eq C _ hne (F.ofIso C ek₁) hn hneF]
          simp [HNFiltration.ofIso]
        have h_eq₂ : σ.slicing.phiPlus C Tk.obj₂ hTk_ne₂ =
            σ.slicing.phiPlus C _ hk1ne := by
          obtain ⟨F, hn, hneF⟩ := HNFiltration.exists_nonzero_first C σ.slicing hTk_ne₂
          rw [σ.slicing.phiPlus_eq C _ hTk_ne₂ F hn hneF,
              σ.slicing.phiPlus_eq C _ hk1ne (F.ofIso C ek₂) hn hneF]
          simp [HNFiltration.ofIso]
        linarith
  -- Combine: all phases < G.φ ⟨0, hGn⟩ < b - 3ε < b - ε
  refine ⟨G, fun j ↦ ⟨(hGφ j).1, ?_⟩⟩
  calc G.φ j ≤ G.φ ⟨0, hGn⟩ := by
        rcases Nat.eq_or_lt_of_le (Nat.zero_le j.val) with hj | hj
        · exact le_of_eq (congrArg G.φ (Fin.ext hj.symm))
        · exact le_of_lt (G.hφ (Fin.mk_lt_mk.mpr hj))
    _ < b - ε := by linarith

/-- **Lemma 7.7 interior HN** (deformedPred version). Derives a `deformedPred`-typed
HN filtration from `interior_has_enveloped_HN_ssf` by wrapping each `ssf.Semistable`
factor with the enveloping interval `(a, b)` as the `deformedPred` witness.

The phase bounds are `(a+ε, b−ε)` (open, matching the paper), since each factor's
`ssf.Semistable` data directly provides the `deformedPred` witness with `(a, b)` as
the enveloping interval. -/
theorem interior_has_enveloped_HN
    [IsTriangulated C]
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ε : ℝ} (hε : 0 < ε) (hε10 : ε < 1 / 10)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hFL : ThinFiniteLengthInInterval (C := C) σ a b)
    {E : C} (hE : ¬IsZero E)
    (hInt : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) E) :
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε) E,
      ∀ j, a + ε < G.φ j ∧ G.φ j < b - ε := by
  have hε2 : ε < 1 / 4 := by linarith
  let ssf := σ.skewedStabilityFunction_of_near C W hW hab
  obtain ⟨G, hGφ⟩ := interior_has_enveloped_HN_ssf (C := C) σ W hW hab
    hε hε10 hthin hsin hFL hE hInt
  let GQ : HNFiltration C (σ.deformedPred C W hW ε) E :=
    { n := G.n
      chain := G.chain
      triangle := G.triangle
      triangle_dist := G.triangle_dist
      triangle_obj₁ := G.triangle_obj₁
      triangle_obj₂ := G.triangle_obj₂
      base_isZero := G.base_isZero
      top_iso := G.top_iso
      zero_isZero := G.zero_isZero
      φ := G.φ
      hφ := G.hφ
      semistable := fun j ↦ by
        change IsZero (G.factor j) ∨
          ∃ (a' b' : ℝ) (hab' : a' < b') (_ : b' - a' + 2 * ε < 1)
            (_ : a' + ε ≤ G.φ j) (_ : G.φ j ≤ b' - ε),
            (σ.skewedStabilityFunction_of_near C W hW hab').Semistable C (G.factor j) (G.φ j)
        refine Or.inr ⟨a, b, hab, hthin, by linarith [(hGφ j).1], by linarith [(hGφ j).2], ?_⟩
        simpa [ssf] using G.semistable j }
  exact ⟨GQ, hGφ⟩

/-! ### σ-semistable objects have Q-HN filtrations -/

/-- **σ-semistable objects have Q-HN filtrations** (Bridgeland p.24). For E ∈ P(φ),
embed E in P((φ−3ε, φ+5ε)) and apply `interior_has_enveloped_HN`. The Q-HN phases
lie in `(φ−2ε, φ+4ε)`.

Two parameters: `ε₀` (local finiteness, < 1/10) and `ε` (perturbation, `ε < ε₀`).
`ThinFiniteLengthInInterval` is derived from `WideSectorFiniteLength` via `of_wide`. -/
theorem sigmaSemistable_hasDeformedHN
    [IsTriangulated C]
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε) E,
      ∀ j, φ - 2 * ε < G.φ j ∧ G.φ j < φ + 4 * ε := by
  -- Bridgeland p.24: embed E in P((φ-3ε, φ+5ε)), apply interior_has_enveloped_HN.
  set a := φ - 3 * ε with ha_def
  set b := φ + 5 * ε with hb_def
  have hab : a < b := by linarith
  have hε₀8 : ε₀ < 1 / 8 := by linarith
  haveI : Fact (a < b) := ⟨hab⟩
  haveI : Fact (b - a ≤ 1) := ⟨by linarith⟩
  have hthin : b - a + 2 * ε < 1 := by linarith
  -- ThinFiniteLengthInInterval via of_wide (center t = φ + ε)
  have hFL : ThinFiniteLengthInInterval (C := C) σ a b :=
    ThinFiniteLengthInInterval.of_wide (C := C) σ hε₀ hε₀8
      (show (φ + ε) - 4 * ε₀ ≤ a by linarith)
      (show b ≤ (φ + ε) + 4 * ε₀ by linarith) hWide
  -- E ∈ P(φ) ⊂ P((a+2ε, b-4ε)) = P((φ-ε, φ+ε))
  have hInt : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) E := by
    have ha2 : a + 2 * ε = φ - ε := by ring
    have hb4 : b - 4 * ε = φ + ε := by ring
    rw [ha2, hb4]
    have ⟨hp, hm⟩ := σ.slicing.phiPlus_eq_phiMinus_of_semistable C hP hE
    exact σ.slicing.intervalProp_of_intrinsic_phases C hE
      (by rw [hm]; linarith) (by rw [hp]; linarith)
  -- Apply interior_has_enveloped_HN
  obtain ⟨G, hGφ⟩ := interior_has_enveloped_HN (C := C) σ W hW hab
    hε (by linarith : ε < 1 / 10) hthin hsin hFL hE hInt
  -- Phase bounds: a+ε < G.φ j < b-ε gives φ-2ε < G.φ j < φ+4ε
  exact ⟨G, fun j ↦ ⟨by linarith [(hGφ j).1], by linarith [(hGφ j).2]⟩⟩


end CategoryTheory.Triangulated
