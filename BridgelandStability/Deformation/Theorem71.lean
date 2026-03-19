/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Deformation.TStructure
import Mathlib.CategoryTheory.Triangulated.Deformation.PPhiAbelian
import Mathlib.CategoryTheory.Triangulated.Deformation.PhiPlusReduction

/-!
# Deformation of Stability Conditions — Theorem71

Deformed slicing construction, main theorem, Theorem 1.2
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### Intermediate lemmas (Bridgeland §7, p.23–24) -/

variable [IsTriangulated C] in
/-- **Lemma 7.7 interior HN** (ssf version, Bridgeland p.23). Every nonzero object in
the interior `P((a+2ε, b−4ε))` of a thin finite-length interval `P((a,b))` has an HN
filtration whose factors are `ssf.Semistable` in `P((a,b))` with phases in `(a+ε, b−ε)`.

**Sorry**: Core of Lemma 7.7 — requires class G/H induction on the Noetherian strict
subobject lattice, propagating phase bounds via Lemma 7.3 (phase confinement). -/
theorem interior_has_enveloped_HN_ssf
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
    stabSeminorm_lt_cos_of_hsin_hthin (C := C) (σ := σ) (W := W) hab hε hε2 hthin hsin
  -- W ≠ 0 for nonzero interval objects
  have hW_ne : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0 := by
    intro F hF hFne
    exact σ.W_ne_zero_of_intervalProp C W hthin' hsmall hFne hF
  -- Perturbation bounds for global window (stated in terms of W and (a+b)/2 directly)
  have hW_ne_sem : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b → W (K₀.of C F) ≠ 0 := by
    intro F φ hP hFne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
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
        wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b + ε := by
    intro F hF hFne
    exact ⟨wPhaseOf_gt_of_intervalProp C σ hFne W
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
    exact hE (G.toPostnikovTower.zero_isZero (show G.n = 0 by omega))
  set P := G.toPostnikovTower with hP_def
  -- F₁ = factor 0 is ssf-semistable with phase G.φ ⟨0, hGn⟩
  have hF₁_ss : ssf.Semistable C (P.factor ⟨0, hGn⟩) (G.φ ⟨0, hGn⟩) :=
    G.semistable ⟨0, hGn⟩
  have hF₁_ne : ¬IsZero (P.factor ⟨0, hGn⟩) := hF₁_ss.2.1
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
        σ.slicing.intervalProp C a b (P.chain.obj' k (by omega)) :=
      fun k hk ↦ intervalProp_chain_of_postnikovTower σ.slicing (C := C) P hfactors_ab k hk
    have hab1 : b ≤ a + 1 := by linarith [Fact.out (p := b - a ≤ 1)]
    -- chain(1) is nonzero: chain(0) = 0, first triangle ⟹ chain(1) ≅ F₁ ≠ 0
    have hchain1_ne : ¬IsZero (P.chain.obj' 1 (by omega)) := by
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
        (hne : ¬IsZero (P.chain.obj' k (by omega))) →
        σ.slicing.phiPlus C (P.chain.obj' k (by omega)) hne ≤
          σ.slicing.phiPlus C E hE by
      have h1_le := hmain (P.n - 1) 1 (by omega) (by omega) (by omega) hchain1_ne
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
      have hkG : k = P.n := by omega
      subst hkG
      exact le_of_eq (by
        obtain ⟨F, hn, hneF⟩ := HNFiltration.exists_nonzero_first C σ.slicing hne
        rw [σ.slicing.phiPlus_eq C _ hne F hn hneF,
            σ.slicing.phiPlus_eq C _ hE (F.ofIso C (Classical.choice P.top_iso)) hn hneF]
        simp [HNFiltration.ofIso])
    | succ d ih =>
      intro k hle hk hkpos hne
      have hkn : k < P.n := by omega
      let Tk := P.triangle ⟨k, hkn⟩
      let ek₁ := Classical.choice (P.triangle_obj₁ ⟨k, hkn⟩)
      let ek₂ := Classical.choice (P.triangle_obj₂ ⟨k, hkn⟩)
      have hTk_ne₁ : ¬IsZero Tk.obj₁ := fun hZ ↦ hne ((Iso.isZero_iff ek₁).mp hZ)
      -- chain(k+1) must be nonzero (if zero: factor(k) ≅ chain(k)[1] has σ-phases
      -- in (a+1, b+1), disjoint from (a, b), contradicting factor(k) ∈ P((a,b)))
      by_cases hk1z : IsZero (P.chain.obj' (k + 1) (by omega))
      · exfalso
        have hTk_obj2_z : IsZero Tk.obj₂ := (Iso.isZero_iff ek₂).mpr hk1z
        haveI : IsIso Tk.mor₃ :=
          (Triangle.isZero₂_iff_isIso₃ Tk (P.triangle_dist ⟨k, hkn⟩)).mp hTk_obj2_z
        have hfact_ne : ¬IsZero (P.factor ⟨k, hkn⟩) := by
          intro hfz; exact hTk_ne₁
            ((Triangle.isZero₁_iff _ (P.triangle_dist ⟨k, hkn⟩)).mpr
              ⟨hTk_obj2_z.eq_of_tgt _ _, hfz.eq_of_src _ _⟩)
        have hfact_shift : σ.slicing.intervalProp C (a + 1) (b + 1) (P.factor ⟨k, hkn⟩) := by
          rcases hchain_int k (by omega) with hZ | ⟨F, hF⟩
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
        have hk1ne : ¬IsZero (P.chain.obj' (k + 1) (by omega)) := hk1z
        have hTk_ne₂ : ¬IsZero Tk.obj₂ := fun hZ ↦ hk1ne ((Iso.isZero_iff ek₂).mp hZ)
        have hTk_obj1_int : σ.slicing.intervalProp C a b Tk.obj₁ :=
          (σ.slicing.intervalProp_closedUnderIso C _ _).of_iso ek₁.symm
            (hchain_int k (by omega))
        have hle_step := σ.slicing.phiPlus_triangle_le C hTk_ne₁ hTk_ne₂
          hab1 hTk_obj1_int (hfactors_ab ⟨k, hkn⟩) (P.triangle_dist ⟨k, hkn⟩)
        have hk1_le := ih (k + 1) (by omega) (by omega) (by omega) hk1ne
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

variable [IsTriangulated C] in
/-- **Lemma 7.7 interior HN** (deformedPred version). Derives a `deformedPred`-typed
HN filtration from `interior_has_enveloped_HN_ssf` by wrapping each `ssf.Semistable`
factor with the enveloping interval `(a, b)` as the `deformedPred` witness.

The phase bounds are `(a+ε, b−ε)` (open, matching the paper), since each factor's
`ssf.Semistable` data directly provides the `deformedPred` witness with `(a, b)` as
the enveloping interval. -/
theorem interior_has_enveloped_HN
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
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε hε (by linarith) hsin) E,
      ∀ j, a + ε < G.φ j ∧ G.φ j < b - ε := by
  have hε2 : ε < 1 / 4 := by linarith
  let ssf := σ.skewedStabilityFunction_of_near C W hW hab
  obtain ⟨G, hGφ⟩ := interior_has_enveloped_HN_ssf (C := C) σ W hW hab
    hε hε10 hthin hsin hFL hE hInt
  let GQ : HNFiltration C (σ.deformedPred C W hW ε hε (by linarith) hsin) E :=
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

variable [IsTriangulated C] in
/-- **σ-semistable objects have Q-HN filtrations** (Bridgeland p.24). For E ∈ P(φ),
embed E in P((φ−3ε, φ+5ε)) and apply `interior_has_enveloped_HN`. The Q-HN phases
lie in `(φ−2ε, φ+4ε)`.

Two parameters: `ε₀` (local finiteness, < 1/10) and `ε` (perturbation, `ε < ε₀`).
`ThinFiniteLengthInInterval` is derived from `WideSectorFiniteLength` via `of_wide`. -/
theorem sigmaSemistable_hasDeformedHN
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε hε (by linarith) hsin) E,
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

/-! ### P(s) ⊂ Q(>t) and P(s) ⊂ Q(<t) -/

variable [IsTriangulated C] in
/-- **P(s) ⊂ Q(>t) for s ≥ t + ε** (Bridgeland p.24 ¶3). A σ-semistable object of
phase `s ≥ t + ε` lies in `Q(>t)`: get Q-HN via `sigmaSemistable_hasDeformedHN`,
split at `t`, then show the Q(≤t) part vanishes by the phiMinus/phiPlus squeeze
(Lemma 3.4 gives σ.φ⁻ ≥ s, phase confinement gives σ.φ⁺ ≤ t+ε, and s ≥ t+ε). -/
theorem P_in_deformedGtPred
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {s t : ℝ} (hst : s ≥ t + ε)
    {E : C} (hP : σ.slicing.P s E) (hE : ¬IsZero E) :
    σ.deformedGtPred C W hW ε hε (by linarith) hsin t E := by
  -- Step 1: Q-HN filtration with phases in (s-2ε, s+4ε)
  obtain ⟨G, hGφ⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin hP hE
  have hGn : 0 < G.n := by
    by_contra h; push_neg at h
    exact hE (G.toPostnikovTower.zero_isZero (show G.n = 0 by omega))
  set P := G.toPostnikovTower
  -- Step 2: All factors have σ-intervalProp
  have hfactors_int : ∀ j, σ.slicing.intervalProp C (s - 3 * ε) (s + 5 * ε)
      (P.factor j) := fun j ↦ by
    by_cases hj : IsZero (P.factor j)
    · exact Or.inl hj
    · rcases G.semistable j with hZ | ⟨a', b', hab', hthin', _, _, hSS'⟩
      · exact absurd hZ hj
      · have hc := phase_confinement_from_stabSeminorm C σ W hW hab' hε
          (by linarith) hthin' hsin hSS'
        exact σ.slicing.intervalProp_of_intrinsic_phases C hj
          (by linarith [(hGφ j).1, hc.1]) (by linarith [(hGφ j).2, hc.2])
  -- Step 3: Find last nonzero factor j₀, prove G.φ j₀ > s - ε ≥ t via Lemma 3.4.
  -- All factors after j₀ are zero, so chain(j₀+1) ≅ E, giving σ.φ⁻(chain(j₀+1)) = s.
  -- Lemma 3.4: s = σ.φ⁻(chain(j₀+1)) ≤ σ.φ⁻(factor j₀) ≤ σ.φ⁺(factor j₀) < G.φ j₀ + ε.
  classical
  let S := (Finset.univ : Finset (Fin G.n)).filter (fun i => ¬IsZero (P.factor i))
  have hSne : S.Nonempty := by
    obtain ⟨j, hj⟩ := G.exists_nonzero_factor C hE
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  set j₀ := S.max' hSne
  have hj₀ne : ¬IsZero (P.factor j₀) :=
    (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
  have hj₀_max : ∀ i : Fin G.n, ¬IsZero (P.factor i) → i ≤ j₀ :=
    fun i hi ↦ Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hzero_suffix : ∀ i : Fin G.n, j₀.val < i.val → IsZero (P.factor i) := by
    intro i hi; by_contra hine; exact absurd (hj₀_max i hine) (by omega)
  -- chain(j₀+1) has P s via downward induction (zero factors → iso → closedUnderIso)
  have hj₀_lt : j₀.val < G.n := j₀.isLt
  have hPchain : σ.slicing.P s (P.chain.obj' (j₀.val + 1) (by omega)) := by
    have : ∀ d k (hle : k ≤ G.n), k + d = G.n → j₀.val < k →
        σ.slicing.P s (P.chain.obj' k (by omega)) := by
      intro d; induction d with
      | zero =>
        intro k hle hk _
        have hkG : k = G.n := by omega
        subst hkG
        exact (σ.slicing.closedUnderIso s).of_iso
          (Classical.choice P.top_iso).symm hP
      | succ d ih =>
        intro k hle hk hjk
        have hkn : k < G.n := by omega
        have hfz : IsZero (P.factor ⟨k, hkn⟩) := hzero_suffix ⟨k, hkn⟩ (by omega)
        let Tk := P.triangle ⟨k, hkn⟩
        haveI : IsIso Tk.mor₁ :=
          (Triangle.isZero₃_iff_isIso₁ Tk (P.triangle_dist ⟨k, hkn⟩)).mp hfz
        let e₁ := Classical.choice (P.triangle_obj₁ ⟨k, hkn⟩)
        let e₂ := Classical.choice (P.triangle_obj₂ ⟨k, hkn⟩)
        exact (σ.slicing.closedUnderIso s).of_iso
          (e₁.symm.trans ((asIso Tk.mor₁).trans e₂)).symm
          (ih (k + 1) (by omega) (by omega) (by omega))
    exact this (G.n - (j₀.val + 1)) (j₀.val + 1) (by omega) (by omega) (by omega)
  -- chain(j₀+1) is nonzero (zero would propagate to chain(n) ≅ E, contradicting hE)
  have hchain_ne : ¬IsZero (P.chain.obj' (j₀.val + 1) (by omega)) := by
    intro hZ; apply hE
    have : ∀ m k (hle : k ≤ G.n), k = j₀.val + 1 + m →
        IsZero (P.chain.obj' k (by omega)) := by
      intro m; induction m with
      | zero => intro k hle hk; exact hk ▸ hZ
      | succ m ihm =>
        intro k hle hk
        have hk1 : k - 1 < G.n := by omega
        have hj₀k : j₀.val < k - 1 := by omega
        have hZprev := ihm (k - 1) (by omega) (by omega)
        let Tk1 := P.triangle ⟨k - 1, hk1⟩
        have hobj1_z : IsZero Tk1.obj₁ :=
          (Iso.isZero_iff (Classical.choice (P.triangle_obj₁ ⟨k - 1, hk1⟩))).mpr hZprev
        have hfz : IsZero Tk1.obj₃ := hzero_suffix ⟨k - 1, hk1⟩ hj₀k
        have hobj2_z : IsZero Tk1.obj₂ :=
          (Triangle.isZero₂_iff _ (P.triangle_dist ⟨k - 1, hk1⟩)).mpr
            ⟨hobj1_z.eq_of_src _ _, hfz.eq_of_tgt _ _⟩
        have := (Iso.isZero_iff (Classical.choice (P.triangle_obj₂ ⟨k - 1, hk1⟩))).mp hobj2_z
        simp only [Fin.val_mk, show k - 1 + 1 = k from by omega] at this
        exact this
    exact (Iso.isZero_iff (Classical.choice P.top_iso)).mp
      (this (G.n - (j₀.val + 1)) G.n le_rfl (by omega))
  -- Apply Lemma 3.4 to the triangle at j₀
  let ej₁ := Classical.choice (P.triangle_obj₁ j₀)
  let ej₂ := Classical.choice (P.triangle_obj₂ j₀)
  have hTj₂_ne : ¬IsZero (P.triangle j₀).obj₂ :=
    fun hZ ↦ hchain_ne ((Iso.isZero_iff ej₂).mp hZ)
  have hTj₁_int : σ.slicing.intervalProp C (s - 3 * ε) (s + 5 * ε) (P.triangle j₀).obj₁ := by
    have hchain_int := intervalProp_chain_of_postnikovTower σ.slicing (C := C) (P := P)
      hfactors_int j₀.val (show j₀.val ≤ G.n from by omega)
    rcases hchain_int with hZ | ⟨F, hF⟩
    · exact Or.inl ((Iso.isZero_iff ej₁.symm).mp hZ)
    · exact Or.inr ⟨F.ofIso C ej₁.symm, hF⟩
  have h34 := σ.slicing.phiMinus_triangle_le C hj₀ne hTj₂_ne
    (by linarith [hεε₀, hε₀10] : s + 5 * ε ≤ s - 3 * ε + 1) hTj₁_int (hfactors_int j₀)
    (P.triangle_dist j₀)
  -- σ.φ⁻(T.obj₂) = s via P s transport
  have hTj₂_phiMinus : σ.slicing.phiMinus C (P.triangle j₀).obj₂ hTj₂_ne = s :=
    (σ.slicing.phiPlus_eq_phiMinus_of_semistable C
      ((σ.slicing.closedUnderIso s).of_iso ej₂.symm hPchain) hTj₂_ne).2
  -- Phase confinement on factor j₀
  rcases G.semistable j₀ with hZ₀ | ⟨a₀, b₀, hab₀, hthin₀, _, _, hSS₀⟩
  · exact absurd hZ₀ hj₀ne
  · have hconf₀ := phase_confinement_from_stabSeminorm C σ W hW hab₀ hε
      (by linarith) hthin₀ hsin hSS₀
    -- s ≤ φ⁻(factor j₀) ≤ φ⁺(factor j₀) < G.φ j₀ + ε
    have hj₀_gt : s - ε < G.φ j₀ := by
      have h1 : s ≤ σ.slicing.phiMinus C (P.triangle j₀).obj₃ hj₀ne := by
        rw [← hTj₂_phiMinus]; exact h34
      have h2 := σ.slicing.phiMinus_le_phiPlus C (P.triangle j₀).obj₃ hj₀ne
      have h3 : σ.slicing.phiPlus C (P.triangle j₀).obj₃ hj₀ne < G.φ j₀ + ε := by
        have := hconf₀.2
        exact this
      linarith
    -- Step 4: of_postnikovTower — zero factors get any ψ > t, nonzero get G.φ j > t
    exact _root_.CategoryTheory.ObjectProperty.ExtensionClosure.of_postnikovTower P
      (fun j ↦ by
        by_cases hfz : IsZero (P.factor j)
        · exact ⟨t + 1, by linarith, Or.inl hfz⟩
        · exact ⟨G.φ j, by linarith [G.hφ.antitone (hj₀_max j hfz)], G.semistable j⟩)

variable [IsTriangulated C] in
/-- **P(s) ⊂ Q(<t) for s ≤ t − ε** (Bridgeland p.24 ¶3, dual). -/
theorem P_in_deformedLtPred
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {s t : ℝ} (hst : s ≤ t - ε)
    {E : C} (hP : σ.slicing.P s E) (hE : ¬IsZero E) :
    σ.deformedLtPred C W hW ε hε (by linarith) hsin t E := by
  -- Dual of P_in_deformedGtPred: get Q-HN, show all phases < t
  obtain ⟨G, hGφ⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin hP hE
  have hGn : 0 < G.n := by
    by_contra h; push_neg at h
    exact hE (G.toPostnikovTower.zero_isZero (show G.n = 0 by omega))
  set P := G.toPostnikovTower
  -- All factors have σ-intervalProp
  have hfactors_int : ∀ j, σ.slicing.intervalProp C (s - 3 * ε) (s + 5 * ε)
      (P.factor j) := fun j ↦ by
    by_cases hj : IsZero (P.factor j)
    · exact Or.inl hj
    · rcases G.semistable j with hZ | ⟨a', b', hab', hthin', _, _, hSS'⟩
      · exact absurd hZ hj
      · have hc := phase_confinement_from_stabSeminorm C σ W hW hab' hε
          (by linarith) hthin' hsin hSS'
        exact σ.slicing.intervalProp_of_intrinsic_phases C hj
          (by linarith [(hGφ j).1, hc.1]) (by linarith [(hGφ j).2, hc.2])
  -- Find first nonzero factor j₁ (min index). Dual of P_in_deformedGtPred:
  -- σ.φ⁺(factor j₁) ≤ σ.φ⁺(E) = s, phase confinement gives G.φ j₁ < s + ε ≤ t.
  classical
  let S := (Finset.univ : Finset (Fin G.n)).filter (fun i => ¬IsZero (P.factor i))
  have hSne : S.Nonempty := by
    obtain ⟨j, hj⟩ := G.exists_nonzero_factor C hE
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  set j₁ := S.min' hSne
  have hj₁ne : ¬IsZero (P.factor j₁) :=
    (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
  have hj₁_min : ∀ i : Fin G.n, ¬IsZero (P.factor i) → j₁ ≤ i :=
    fun i hi ↦ Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  -- Phase confinement on factor j₁
  rcases G.semistable j₁ with hZ₁ | ⟨a₁, b₁, hab₁, hthin₁, _, _, hSS₁⟩
  · exact absurd hZ₁ hj₁ne
  · have hconf₁ := phase_confinement_from_stabSeminorm C σ W hW hab₁ hε
      (by linarith) hthin₁ hsin hSS₁
    -- Dual Lemma 3.4: σ.φ⁺(factor j₁) ≤ σ.φ⁺(E) = s
    -- All factors before j₁ are zero → chain(j₁) ≅ 0 → chain(j₁+1) ≅ factor(j₁)
    -- then phiPlus monotone along chain to chain(n) ≅ E.
    -- Combined with phase confinement: G.φ j₁ - ε < σ.φ⁻ ≤ σ.φ⁺ ≤ s, so G.φ j₁ < s + ε ≤ t
    -- Show σ.φ⁺(factor j₁) ≤ s via phiPlus monotonicity along the PostnikovTower chain.
    -- chain(j₁) ≅ 0 (prefix zero), so chain(j₁+1) ≅ factor(j₁).
    -- phiPlus_triangle_le gives φ⁺(chain(k)) ≤ φ⁺(chain(k+1)) at each step,
    -- so φ⁺(chain(j₁+1)) ≤ φ⁺(chain(n)) = φ⁺(E) = s.
    have hzero_prefix : ∀ i : Fin G.n, i.val < j₁.val → IsZero (P.factor i) := by
      intro i hi; by_contra hine; exact absurd (hj₁_min i hine) (by omega)
    have hj₁_lt : j₁.val < G.n := j₁.isLt
    have hj₁_lt_n : j₁.val < G.n := j₁.isLt
    have hchain_j₁_zero : IsZero (P.chain.obj' j₁.val (by omega)) := by
      have : ∀ m (hle : m ≤ G.n), m ≤ j₁.val →
          (∀ i : Fin G.n, i.val < m → IsZero (P.factor i)) →
          IsZero (P.chain.obj' m (by omega)) := by
        intro m; induction m with
        | zero => intro _ _ _; exact P.base_isZero
        | succ k ih =>
          intro hle hkj₁ hpref
          have hkn : k < G.n := by omega
          have hfz : IsZero (P.factor ⟨k, hkn⟩) := hpref ⟨k, hkn⟩ (Nat.lt_succ_of_le le_rfl)
          let Tk := P.triangle ⟨k, hkn⟩
          have hobj1_z : IsZero Tk.obj₁ :=
            (Iso.isZero_iff (Classical.choice (P.triangle_obj₁ ⟨k, hkn⟩))).mpr
              (ih (by omega) (by omega) (fun i hi ↦ hpref i (by omega)))
          exact (Iso.isZero_iff (Classical.choice (P.triangle_obj₂ ⟨k, hkn⟩))).mp
            ((Triangle.isZero₂_iff _ (P.triangle_dist ⟨k, hkn⟩)).mpr
              ⟨hobj1_z.eq_of_src _ _, hfz.eq_of_tgt _ _⟩)
      exact this j₁.val (by omega) le_rfl hzero_prefix
    -- chain(j₁+1) ≅ factor(j₁) via isZero₁_iff_isIso₂ on the triangle at j₁
    let Tj₁ := P.triangle j₁
    have hTj₁_obj1_z : IsZero Tj₁.obj₁ :=
      (Iso.isZero_iff (Classical.choice (P.triangle_obj₁ j₁))).mpr hchain_j₁_zero
    haveI : IsIso Tj₁.mor₂ :=
      (Triangle.isZero₁_iff_isIso₂ Tj₁ (P.triangle_dist j₁)).mp hTj₁_obj1_z
    -- chain(j₁+1) is nonzero (since factor(j₁) is nonzero and chain(j₁+1) ≅ factor(j₁))
    let ej₁₂ := Classical.choice (P.triangle_obj₂ j₁)
    have hTj₁_obj2_ne : ¬IsZero Tj₁.obj₂ := fun hZ ↦
      hj₁ne ((Iso.isZero_iff (asIso Tj₁.mor₂)).mp hZ)
    have hchain_j₁1_ne : ¬IsZero (P.chain.obj' (j₁.val + 1) (by omega)) :=
      fun hZ ↦ hTj₁_obj2_ne ((Iso.isZero_iff ej₁₂).mpr hZ)
    -- φ⁺(chain(j₁+1)) ≤ s by downward induction from chain(n)
    -- At each step: phiPlus_triangle_le gives φ⁺(chain(k)) ≤ φ⁺(chain(k+1))
    -- φ⁺(chain(j₁+1)) ≤ φ⁺(chain(n)) = s by downward induction.
    -- At each step: phiPlus_triangle_le gives φ⁺(chain(k)) ≤ φ⁺(chain(k+1)).
    have hphiPlus_le : σ.slicing.phiPlus C (P.chain.obj' (j₁.val + 1) (by omega))
        hchain_j₁1_ne ≤ s := by
      -- Prove: for all k with j₁+1 ≤ k ≤ n, if chain(k) nonzero then φ⁺(chain(k)) ≤ s
      suffices hmain : ∀ d k (hle : k ≤ G.n), k + d = G.n → 0 < k →
          (hne : ¬IsZero (P.chain.obj' k (by omega))) →
          σ.slicing.phiPlus C (P.chain.obj' k (by omega)) hne ≤ s from
        hmain (G.n - (j₁.val + 1)) (j₁.val + 1) (by omega) (by omega) (by omega) hchain_j₁1_ne
      intro d; induction d with
      | zero =>
        intro k hle hk hkpos hne
        have hkG : k = G.n := by omega
        subst hkG
        exact le_of_eq (σ.slicing.phiPlus_eq_phiMinus_of_semistable C
          ((σ.slicing.closedUnderIso s).of_iso (Classical.choice P.top_iso).symm hP) hne).1
      | succ d ih =>
        intro k hle hk hkpos hne
        have hkn : k < G.n := by omega
        -- Triangle at k: chain(k) → chain(k+1) → factor(k) → chain(k)[1]
        let Tk := P.triangle ⟨k, hkn⟩
        let ek₁ := Classical.choice (P.triangle_obj₁ ⟨k, hkn⟩)
        let ek₂ := Classical.choice (P.triangle_obj₂ ⟨k, hkn⟩)
        have hTk_ne₁ : ¬IsZero Tk.obj₁ := fun hZ ↦ hne ((Iso.isZero_iff ek₁).mp hZ)
        by_cases hk1ne : IsZero (P.chain.obj' (k + 1) (show k + 1 ≤ G.n from by omega))
        · -- chain(k+1) = 0 → factor(k) ≅ chain(k)[1] → φ⁺(chain(k)) = φ⁺(factor(k)) - 1 < s
          have hTk_obj2_z : IsZero Tk.obj₂ :=
            (Iso.isZero_iff ek₂).mpr hk1ne
          haveI : IsIso Tk.mor₃ :=
            (Triangle.isZero₂_iff_isIso₃ Tk (P.triangle_dist ⟨k, hkn⟩)).mp hTk_obj2_z
          -- factor(k) ≅ chain(k)[1] via mor₃
          -- φ⁺(factor(k)) < s + 5ε from intervalProp
          have hfact_ne : ¬IsZero (P.factor ⟨k, hkn⟩) := by
            intro hfz
            -- If factor(k) = 0 and chain(k+1) = 0, then chain(k) = 0 (contradiction)
            -- isZero₁_iff: IsZero obj₁ ↔ (mor₁ = 0 ∧ mor₃ = 0)
            exact hTk_ne₁ ((Triangle.isZero₁_iff _ (P.triangle_dist ⟨k, hkn⟩)).mpr
              ⟨(hTk_obj2_z.eq_of_tgt _ _), hfz.eq_of_src _ _⟩)
          have hfact_phiPlus := σ.slicing.phiPlus_lt_of_intervalProp C hfact_ne
            (hfactors_int ⟨k, hkn⟩)
          -- φ⁺(chain(k)[1]) = φ⁺(chain(k)) + 1 via shiftHN
          have hshift_ne : ¬IsZero (Tk.obj₁⟦(1 : ℤ)⟧) :=
            fun hZ ↦ hTk_ne₁ (IsZero.of_full_of_faithful_of_isZero
              (shiftFunctor C (1 : ℤ)) _ hZ)
          -- factor(k) ≅ Tk.obj₁⟦1⟧ via asIso mor₃
          -- φ⁺(Tk.obj₁⟦1⟧) = φ⁺(Tk.obj₁) + 1
          obtain ⟨F, hnF, hneF⟩ := HNFiltration.exists_nonzero_first C σ.slicing hTk_ne₁
          have hphiPlus_shift : σ.slicing.phiPlus C (Tk.obj₁⟦(1 : ℤ)⟧) hshift_ne =
              σ.slicing.phiPlus C Tk.obj₁ hTk_ne₁ + 1 := by
            have hneF_shift : ¬IsZero ((F.shiftHN C σ.slicing 1).triangle ⟨0, hnF⟩).obj₃ := by
              change ¬IsZero ((shiftFunctor C (1 : ℤ)).obj (F.triangle ⟨0, hnF⟩).obj₃)
              exact fun hZ ↦ hneF (IsZero.of_full_of_faithful_of_isZero
                (shiftFunctor C (1 : ℤ)) _ hZ)
            rw [σ.slicing.phiPlus_eq C _ hshift_ne (F.shiftHN C σ.slicing 1) hnF hneF_shift]
            simp only [HNFiltration.shiftHN, HNFiltration.phiPlus, Int.cast_one]
            rw [σ.slicing.phiPlus_eq C _ hTk_ne₁ F hnF hneF]
          -- φ⁺(factor(k)) = φ⁺(Tk.obj₁⟦1⟧) via iso invariance
          have hiso_phiPlus : σ.slicing.phiPlus C (P.factor ⟨k, hkn⟩) hfact_ne =
              σ.slicing.phiPlus C (Tk.obj₁⟦(1 : ℤ)⟧) hshift_ne := by
            haveI : IsIso Tk.mor₃ :=
              (Triangle.isZero₂_iff_isIso₃ Tk (P.triangle_dist ⟨k, hkn⟩)).mp hTk_obj2_z
            let eTk₃ : Tk.obj₃ ≅ Tk.obj₁⟦(1 : ℤ)⟧ := asIso Tk.mor₃
            obtain ⟨F', hnF', hneF'⟩ := HNFiltration.exists_nonzero_first C σ.slicing hfact_ne
            rw [σ.slicing.phiPlus_eq C _ hfact_ne F' hnF' hneF',
                σ.slicing.phiPlus_eq C _ hshift_ne (F'.ofIso C eTk₃) hnF' hneF']
            simp [HNFiltration.ofIso]
          -- φ⁺(chain(k)) = φ⁺(Tk.obj₁) via iso invariance
          have hchain_phiPlus : σ.slicing.phiPlus C _ hne =
              σ.slicing.phiPlus C Tk.obj₁ hTk_ne₁ := by
            rw [σ.slicing.phiPlus_eq C _ hTk_ne₁ F hnF hneF,
                σ.slicing.phiPlus_eq C _ hne (F.ofIso C ek₁) hnF hneF]
            simp [HNFiltration.ofIso]
          -- Combine: φ⁺(chain(k)) = φ⁺(factor(k)) - 1 < (s + 5ε) - 1 ≤ s
          rw [hchain_phiPlus]
          have : σ.slicing.phiPlus C Tk.obj₁ hTk_ne₁ =
              σ.slicing.phiPlus C (P.factor ⟨k, hkn⟩) hfact_ne - 1 := by
            rw [hiso_phiPlus, hphiPlus_shift]; ring
          linarith
        · -- chain(k+1) nonzero: phiPlus_triangle_le gives φ⁺(chain(k)) ≤ φ⁺(chain(k+1)) ≤ s
          have hTk_ne₂ : ¬IsZero Tk.obj₂ := fun hZ ↦ hk1ne ((Iso.isZero_iff ek₂).mp hZ)
          have hTk_obj1_int : σ.slicing.intervalProp C (s - 3 * ε) (s + 5 * ε) Tk.obj₁ :=
            (σ.slicing.intervalProp_closedUnderIso C _ _).of_iso ek₁.symm
              (intervalProp_chain_of_postnikovTower σ.slicing (C := C) (P := P)
                hfactors_int k (show k ≤ G.n from by omega))
          have hle_step := σ.slicing.phiPlus_triangle_le C hTk_ne₁ hTk_ne₂
            (by linarith [hεε₀, hε₀10] : s + 5 * ε ≤ s - 3 * ε + 1) hTk_obj1_int
            (hfactors_int ⟨k, hkn⟩) (P.triangle_dist ⟨k, hkn⟩)
          -- hle_step : φ⁺(Tk.obj₁) ≤ φ⁺(Tk.obj₂)
          -- Transport: φ⁺(chain(k)) = φ⁺(Tk.obj₁), φ⁺(chain(k+1)) = φ⁺(Tk.obj₂)
          have hk1_le := ih (k + 1) (by omega) (by omega) (by omega) hk1ne
          -- φ⁺ is iso-invariant (closedUnderIso → phiPlus preserved)
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
    -- Transport: φ⁺(factor j₁) = φ⁺(chain(j₁+1)) since chain(j₁+1) ≅ factor(j₁)
    -- Combined: G.φ j₁ - ε < σ.φ⁻ ≤ σ.φ⁺ ≤ s, so G.φ j₁ < s + ε
    have hj₁_lt : G.φ j₁ < s + ε := by
      have hfact_phiPlus : σ.slicing.phiPlus C Tj₁.obj₃ hj₁ne ≤ s := by
        -- Tj₁.obj₃ ≅ Tj₁.obj₂ ≅ chain(j₁+1) via (asIso mor₂)⁻¹ and ej₁₂
        -- phiPlus is iso-invariant: transport HN filtration via ofIso
        obtain ⟨F, hnF, hneF⟩ := HNFiltration.exists_nonzero_first C σ.slicing hchain_j₁1_ne
        -- chain(j₁+1) ≅ Tj₁.obj₂ ≅ Tj₁.obj₃ = factor(j₁)
        -- ej₁₂.symm : chain(j₁+1) ≅ Tj₁.obj₂, asIso mor₂ : Tj₁.obj₂ ≅ Tj₁.obj₃
        haveI : IsIso Tj₁.mor₂ :=
          (Triangle.isZero₁_iff_isIso₂ Tj₁ (P.triangle_dist j₁)).mp hTj₁_obj1_z
        let ej₁23 : Tj₁.obj₂ ≅ Tj₁.obj₃ := asIso Tj₁.mor₂
        change σ.slicing.phiPlus C (P.factor j₁) hj₁ne ≤ s
        rw [σ.slicing.phiPlus_eq C _ hj₁ne
          ((F.ofIso C (ej₁₂.symm.trans ej₁23))) (by change 0 < F.n; exact hnF)
          (by change ¬IsZero _; exact hneF)]
        rw [σ.slicing.phiPlus_eq C _ hchain_j₁1_ne F hnF hneF] at hphiPlus_le
        simp only [HNFiltration.ofIso, HNFiltration.phiPlus] at hphiPlus_le ⊢
        exact hphiPlus_le
      have h1 : G.φ j₁ - ε < σ.slicing.phiMinus C Tj₁.obj₃ hj₁ne := hconf₁.1
      have h2 := σ.slicing.phiMinus_le_phiPlus C Tj₁.obj₃ hj₁ne
      linarith
    exact _root_.CategoryTheory.ObjectProperty.ExtensionClosure.of_postnikovTower P
      (fun j ↦ by
        by_cases hfz : IsZero (P.factor j)
        · exact ⟨t - 1, by linarith, Or.inl hfz⟩
        · exact ⟨G.φ j, by linarith [G.hφ.antitone (hj₁_min j hfz)], G.semistable j⟩)

/-! ### Q(>t)/Q(≤t) truncation triangles (Bridgeland p.24, Steps 1–2) -/

variable [IsTriangulated C] in
/-- **Step 1** (Bridgeland p.24): Every σ-semistable object E ∈ P(φ) admits a Q(>t)/Q(≤t)
truncation triangle for any t. Obtains a Q-HN filtration from
`sigmaSemistable_hasDeformedHN` and splits it at t via
`exists_deformedGt_deformedLe_triangle_of_hn`. -/
theorem sigmaSemistable_deformedGtLe_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε hε (by linarith) hsin t X ∧
      σ.deformedLePred C W hW ε hε (by linarith) hsin t Y := by
  obtain ⟨G, _⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin hP hE
  exact exists_deformedGt_deformedLe_triangle_of_hn C σ W hW hε (by linarith) hsin G t

variable [IsTriangulated C] in
/-- **Step 2** (Bridgeland p.24): If every σ-semistable object admits a Q(>t)/Q(≤t)
truncation triangle (Step 1), then EVERY object admits one. The proof reduces via σ-HN
to the semistable case and assembles the pieces via the octahedral axiom.

**Sorry**: Requires iterated octahedral assembly over σ-HN factors. -/
theorem deformedGtLe_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hStep1 : ∀ {E : C} {φ : ℝ}, σ.slicing.P φ E → ¬IsZero E → ∀ t : ℝ,
      ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧
        σ.deformedGtPred C W hW ε hε (by linarith) hsin t X ∧
        σ.deformedLePred C W hW ε hε (by linarith) hsin t Y)
    (E : C) (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε hε (by linarith) hsin t X ∧
      σ.deformedLePred C W hW ε hε (by linarith) hsin t Y := by
  sorry -- Bridgeland p.24: σ-HN + iterated octahedral

variable [IsTriangulated C] in
/-- **Q-HN existence** (Bridgeland p.24, Steps 1+2). Every object admits a Q-HN filtration.
Combines `deformedGtLe_triangle` (Step 2) with
`exists_hn_of_deformedGt_deformedLe_triangle`. -/
theorem deformedSlicing_hn_exists
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (E : C) :
    Nonempty (HNFiltration C (σ.deformedPred C W hW ε hε (by linarith) hsin) E) := by
  sorry -- Requires t-structure → slicing (Prop 5.3) + local finiteness

/-! ### Deformed slicing construction -/

variable [IsTriangulated C] in
/-- **Deformed slicing** (Node 7.Q + 7.6 + 7.7). The slicing `Q` with `Q(ψ) =
deformedPred σ W hW ε ψ`, where `ε` is the perturbation parameter (`ε < ε₀`) and
`ε₀` is the local finiteness parameter (< 1/10).

The `closedUnderIso` and `shift_iff` fields are complete. The `hom_vanishing` field
is Lemma 7.6 via `hom_eq_zero_of_deformedPred`. The `hn_exists` field delegates to
`deformedSlicing_hn_exists`, which combines `deformedGtLe_triangle` (sorry: iterated
octahedral assembly over σ-HN factors) with
`exists_hn_of_deformedGt_deformedLe_triangle`. -/
def StabilityCondition.deformedSlicing (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    Slicing C where
  P := σ.deformedPred C W hW ε hε (by linarith) hsin
  closedUnderIso := fun φ ↦ ⟨fun {E E'} e h ↦ by
    rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
    · exact Or.inl ((Iso.isZero_iff e).mp hZ)
    · refine Or.inr ⟨a, b, hab, hthin, henv_lo, henv_hi, ?_, fun h ↦ hSS.2.1
        ((Iso.isZero_iff e).mpr h), ?_, ?_, fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
      · -- intervalProp: transport via HNFiltration.ofIso
        rcases hSS.1 with hZ' | ⟨F, hF⟩
        · exact absurd hZ' hSS.2.1
        · exact Or.inr ⟨F.ofIso C e, hF⟩
      · -- W(K₀.of C E') ≠ 0
        rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]; exact hSS.2.2.1
      · -- wPhaseOf = φ
        rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]; exact hSS.2.2.2.1
      · -- semistability: compose triangle with iso
        have hT' : Triangle.mk (f₁ ≫ e.inv) (e.hom ≫ f₂) f₃ ∈ distTriang C :=
          isomorphic_distinguished _ hT _
            (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
              (by simp) (by simp) (by simp))
        exact hSS.2.2.2.2 hT' hK hQ hKne⟩
  zero_mem ψ := σ.deformedPred_zero C W hW ε hε (by linarith) hsin ψ (isZero_zero C)
  shift_iff := fun φ X ↦ by
    constructor
    · -- Forward: deformedPred φ X → deformedPred (φ+1) (X⟦1⟧)
      intro h
      rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
      · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
      · -- Use interval (a+1, b+1) with α' = (a+b)/2 + 1
        refine Or.inr ⟨a + 1, b + 1, by linarith, by linarith, by linarith, by linarith,
          ?_, fun h ↦ hSS.2.1
          (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) X h), ?_,
          ?_, fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
        · -- intervalProp C (a+1) (b+1) (X⟦1⟧)
          rcases hSS.1 with hZ' | ⟨F, hF⟩
          · exact absurd hZ' hSS.2.1
          · exact Or.inr ⟨F.shiftHN C σ.slicing 1, fun i ↦ by
              simp only [HNFiltration.shiftHN, Int.cast_one]
              constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
        · -- W(K₀.of C (X⟦1⟧)) ≠ 0
          rw [K₀.of_shift_one, map_neg]
          exact neg_ne_zero.mpr hSS.2.2.1
        · -- wPhaseOf(W(K₀.of C (X⟦1⟧))) ((a+b)/2 + 1) = φ + 1
          change wPhaseOf (W (K₀.of C (X⟦(1 : ℤ)⟧))) ((a + 1 + (b + 1)) / 2) = φ + 1
          rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by ring]
          rw [K₀.of_shift_one, map_neg]
          have hphase : wPhaseOf (W (K₀.of C X)) ((a + b) / 2) = φ := hSS.2.2.2.1
          have hWne : W (K₀.of C X) ≠ 0 := hSS.2.2.1
          exact (wPhaseOf_neg hWne _).trans (by linarith)
        · -- Semistability transport: shift K → X⟦1⟧ → Q by -1, compose with iso
          -- to get K⟦-1⟧ → X → Q⟦-1⟧ (dist), apply X's semistability
          have hT_sh := Triangle.shift_distinguished _ hT (-1 : ℤ)
          -- Build triangle with obj₂ = X via iso (X⟦1⟧)⟦-1⟧ ≅ X
          have h10 : (1 : ℤ) + (-1 : ℤ) = 0 := by omega
          let eX := (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) h10).app X
          let shT := (Triangle.shiftFunctor C (-1)).obj (Triangle.mk f₁ f₂ f₃)
          set T' := Triangle.mk (shT.mor₁ ≫ eX.hom) (eX.inv ≫ shT.mor₂) shT.mor₃
          have hT' : T' ∈ distTriang C :=
            isomorphic_distinguished _ hT_sh _
              (Triangle.isoMk T' shT
                (Iso.refl _) eX.symm (Iso.refl _)
                (by simp [T'])
                (by change (eX.inv ≫ shT.mor₂) ≫ 𝟙 _ = eX.symm.hom ≫ shT.mor₂
                    simp [Iso.symm])
                (by simp [T']))
          -- K⟦-1⟧ ∈ P((a,b)), Q⟦-1⟧ ∈ P((a,b))
          have hK1 : σ.slicing.intervalProp C a b (K⟦(-1 : ℤ)⟧) := by
            rcases hK with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing (-1), fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hQ1 : σ.slicing.intervalProp C a b (Q⟦(-1 : ℤ)⟧) := by
            rcases hQ with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing (-1), fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hKne1 : ¬IsZero (K⟦(-1 : ℤ)⟧) := fun h ↦
            hKne (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (-1 : ℤ)) K h)
          -- Apply X's semistability
          have hsem : wPhaseOf (W (K₀.of C (K⟦(-1 : ℤ)⟧))) ((a + b) / 2) ≤ φ :=
            hSS.2.2.2.2 hT' hK1 hQ1 hKne1
          rw [K₀.of_shift_neg_one, map_neg] at hsem
          -- hsem : wPhaseOf (-W (K₀.of C K)) ((a + b) / 2) ≤ φ
          change wPhaseOf (W (K₀.of C K)) ((a + 1 + (b + 1)) / 2) ≤ φ + 1
          rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by ring]
          by_cases hWK : W (K₀.of C K) = 0
          · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; linarith
          · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
            have key2 := wPhaseOf_add_two hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 2 = (a + b) / 2 + 1 from by ring] at key2
            linarith
    · -- Backward: deformedPred (φ+1) (X⟦1⟧) → deformedPred φ X
      intro h
      rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
      · exact Or.inl (IsZero.of_full_of_faithful_of_isZero
          (shiftFunctor C (1 : ℤ)) X hZ)
      · -- Use interval (a-1, b-1) with α' = (a+b)/2 - 1
        refine Or.inr ⟨a - 1, b - 1, by linarith, by linarith, by linarith, by linarith, ?_,
          fun h ↦ hSS.2.1 ((shiftFunctor C (1 : ℤ)).map_isZero h), ?_, ?_,
          fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
        · -- intervalProp C (a-1) (b-1) X from intervalProp C a b (X⟦1⟧)
          rcases hSS.1 with hZ' | ⟨F, hF⟩
          · exact absurd hZ' hSS.2.1
          · exact Or.inr ⟨(F.shiftHN C σ.slicing (-1)).ofIso C
              ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).app X),
              fun i ↦ by
                change a - 1 < (F.shiftHN C σ.slicing (-1)).φ i ∧
                  (F.shiftHN C σ.slicing (-1)).φ i < b - 1
                simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
        · -- W(K₀.of C X) ≠ 0
          change W (K₀.of C X) ≠ 0
          intro h; exact hSS.2.2.1 (show W (K₀.of C (X⟦(1 : ℤ)⟧)) = 0 from by
            rw [K₀.of_shift_one, map_neg, h, neg_zero])
        · -- wPhaseOf(W(K₀.of C X)) ((a-1+b-1)/2) = φ
          change wPhaseOf (W (K₀.of C X)) ((a - 1 + (b - 1)) / 2) = φ
          rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by ring]
          -- hSS.2.2.2.1 : wPhaseOf (W (K₀.of C (X⟦1⟧))) ((a+b)/2) = φ + 1
          have hphase : wPhaseOf (-W (K₀.of C X)) ((a + b) / 2) = φ + 1 := by
            have := hSS.2.2.2.1
            rwa [K₀.of_shift_one, map_neg] at this
          have hWne : W (K₀.of C X) ≠ 0 := by
            intro h; apply hSS.2.2.1
            change W (K₀.of C (X⟦(1 : ℤ)⟧)) = 0
            rw [K₀.of_shift_one, map_neg, neg_eq_zero]
            exact h
          have key := wPhaseOf_neg hWne ((a + b) / 2 - 1)
          rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
          linarith
        · -- Semistability: transport via ⟦1⟧
          -- Shift triangle K → X → Q by 1 to get K⟦1⟧ → X⟦1⟧ → Q⟦1⟧
          have hT' := Triangle.shift_distinguished _ hT (1 : ℤ)
          -- K⟦1⟧ ∈ P((a,b)), Q⟦1⟧ ∈ P((a,b))
          have hK1 : σ.slicing.intervalProp C a b (K⟦(1 : ℤ)⟧) := by
            rcases hK with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing 1, fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hQ1 : σ.slicing.intervalProp C a b (Q⟦(1 : ℤ)⟧) := by
            rcases hQ with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing 1, fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hKne1 : ¬IsZero (K⟦(1 : ℤ)⟧) := fun h ↦
            hKne (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) K h)
          -- Apply X⟦1⟧'s semistability
          have hsem : wPhaseOf (W (K₀.of C (K⟦(1 : ℤ)⟧))) ((a + b) / 2) ≤ φ + 1 :=
            hSS.2.2.2.2 hT' hK1 hQ1 hKne1
          rw [K₀.of_shift_one, map_neg] at hsem
          -- hsem : wPhaseOf (-W (K₀.of C K)) ((a + b) / 2) ≤ φ + 1
          change wPhaseOf (W (K₀.of C K)) ((a - 1 + (b - 1)) / 2) ≤ φ
          rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by ring]
          by_cases hWK : W (K₀.of C K) = 0
          · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; linarith
          · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
            linarith
  hom_vanishing ψ₁ ψ₂ A B hlt hA hB f :=
    σ.hom_eq_zero_of_deformedPred C W hW hε (by linarith) (by linarith) hsin hA hB hlt f
  hn_exists := fun E ↦
    deformedSlicing_hn_exists C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin E

variable [IsTriangulated C] in
/-- **W-compatibility of the deformed slicing.** For every nonzero Q-semistable object `E`
of Q-phase `ψ`, the central charge `W([E])` lies on the ray `ℝ₊ · exp(iπψ)`. This
follows directly from the `Semistable` definition, which stores
`wPhaseOf(W([E]), α) = ψ`. -/
theorem StabilityCondition.deformedSlicing_compat
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (ψ : ℝ) (E : C)
    (hQ : (σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin).P ψ E)
    (hE : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      W (K₀.of C E) = ↑m * Complex.exp (↑(Real.pi * ψ) * Complex.I) := by
  -- hQ : deformedPred, so either IsZero or ∃ a b hab hthin, Semistable
  rcases hQ with hEZ | ⟨a, b, hab, _, _, _, hSS⟩
  · exact absurd hEZ hE
  · exact ⟨‖W (K₀.of C E)‖, norm_pos_iff.mpr hSS.2.2.1, hSS.polar⟩

/-! #### Step A4: Main theorem -/

variable [IsTriangulated C] in
/-- **Reverse phase confinement**. If `E` is σ-semistable of phase `φ` and
`‖W - Z‖_σ < sin(πε)`, then `E` lies in the Q-interval `(φ - 2ε - δ, φ + 4ε + δ)`
for any `δ > 0`.

This replaces the incorrect statement `sigma_semistable_is_deformedPred` which claimed
σ-semistable implies Q-semistable. That is **false**: a σ-semistable object `E` can
decompose into W-semistable factors with different W-phases (e.g., `E = S₁ ⊕ S₂` with
`S₁, S₂` σ-stable of the same phase but different W-phases), so `E` need not be
Q-semistable. The correct statement is that `E` lies in the larger Q-interval
`(φ - 2ε - δ, φ + 4ε + δ)`.

The proof applies `sigmaSemistable_hasDeformedHN` to obtain a Q-HN filtration for `E`
whose factors have phases in `(φ - 2ε, φ + 4ε)`, then enlarges this by `δ`.
-/
theorem sigma_semistable_intervalProp
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    {δ : ℝ} (hδ : 0 < δ) :
    (σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin).intervalProp C
      (φ - 2 * ε - δ) (φ + 4 * ε + δ) E := by
  -- Apply sigmaSemistable_hasDeformedHN to get Q-HN with phases in (φ-2ε, φ+4ε).
  -- Then enlarge by δ to get the desired Q-interval bound.
  obtain ⟨G, hGφ⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin hP hE
  exact Or.inr ⟨G, fun j ↦ ⟨by linarith [(hGφ j).1], by linarith [(hGφ j).2]⟩⟩

theorem deformed_intervalProp_subset_sigma_intervalProp
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (t : ℝ) :
    (σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin).intervalProp C
        (t - ε₀) (t + ε₀) ≤
      σ.slicing.intervalProp C (t - 2 * ε₀) (t + 2 * ε₀) := by
  intro X hX
  rcases hX with hZ | ⟨F, hF⟩
  · exact Or.inl hZ
  · apply intervalProp_of_postnikovTower C σ.slicing F.toPostnikovTower
    intro i
    have hsem := F.semistable i
    change σ.deformedPred C W hW ε hε (by linarith) hsin (F.φ i) _ at hsem
    rcases hsem with hZ_i | ⟨a_i, b_i, hab_i, hthin_i, _, _, hSS_i⟩
    · exact Or.inl hZ_i
    · have ⟨hlo, hhi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab_i
        hε (by linarith) hthin_i hsin hSS_i
      exact σ.slicing.intervalProp_of_intrinsic_phases C hSS_i.2.1
        (by
          have hleft := (hF i).1
          linarith)
        (by
          have hright := (hF i).2
          linarith)

/-! ### Deformation theorem (Theorem 7.1) -/

variable [IsTriangulated C] in
/-- A quantitative helper for **Bridgeland's Theorem 7.1**. Given a
stability condition `σ = (Z, P)` on a triangulated category `D` and a group
homomorphism `W : K₀(D) → ℂ` with `‖W - Z‖_σ < sin(πε)` for some `0 < ε < ε₀`
(where `ε₀` comes from the local finiteness of `σ`), there exists a locally-finite
stability condition `τ = (W, Q)` with `d(P, Q) ≤ ε`.

The proof constructs the deformed slicing `Q` via `deformedSlicing`, then verifies:
1. **Hom-vanishing** (Lemma 7.6): `hom_eq_zero_of_deformedPred`
2. **HN filtrations** (Lemma 7.7 + Nodes 7.8–7.9): well-founded recursion in thin
   quasi-abelian categories, assembled via t-structures `Q(> t)`
3. **Compatibility**: `deformedSlicing_compat`
4. **Local finiteness**: inherited from `σ` via the interval inclusion
   `Q((t-ε₀,t+ε₀)) ⊆ P((t-2ε₀,t+2ε₀))`
5. **Distance bound**: `d(P, Q) ≤ ε` by phase confinement (Node 7.3)
-/
theorem bridgeland_7_1_le (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    ∃ (τ : StabilityCondition C), τ.Z = W ∧
      slicingDist C σ.slicing τ.slicing ≤ ENNReal.ofReal ε := by
  have hε₀8 : ε₀ < 1 / 8 := by linarith
  have hε₀2 : ε₀ < 1 / 4 := by linarith
  let hSector : SectorFiniteLength (C := C) σ ε₀ hε₀ hε₀2 :=
    SectorFiniteLength.of_wide (C := C) σ hε₀ hε₀2 hε₀8 hWide
  refine ⟨⟨σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin, W,
    σ.deformedSlicing_compat C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin, ?_⟩, rfl, ?_⟩
  · -- Local finiteness: inherited from σ via Q((t-ε₀,t+ε₀)) ⊆ P((t-2ε₀,t+2ε₀))
    constructor
    refine ⟨ε₀, hε₀, by linarith, fun t E ↦ ?_⟩
    letI : Fact (t - ε₀ < t + ε₀) := ⟨by linarith [hε₀]⟩
    letI : Fact ((t + ε₀) - (t - ε₀) ≤ 1) := ⟨by linarith [hε₀10]⟩
    letI : Fact (t - 2 * ε₀ < t + 2 * ε₀) := ⟨by linarith [hε₀]⟩
    letI : Fact ((t + 2 * ε₀) - (t - 2 * ε₀) ≤ 1) := ⟨by linarith [hε₀10]⟩
    have hIncl :
        (σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin).intervalProp C
            (t - ε₀) (t + ε₀) ≤
          σ.slicing.intervalProp C (t - 2 * ε₀) (t + 2 * ε₀) :=
      deformed_intervalProp_subset_sigma_intervalProp C σ W hW hε₀ hε₀10 hWide hε hεε₀
        hsin t
    have hbig :
        IsStrictArtinianObject ((ObjectProperty.ιOfLE hIncl).obj E) ∧
          IsStrictNoetherianObject ((ObjectProperty.ιOfLE hIncl).obj E) := by
      simpa [hSector] using hSector t ((ObjectProperty.ιOfLE hIncl).obj E)
    haveI : IsStrictArtinianObject ((ObjectProperty.ιOfLE hIncl).obj E) := hbig.1
    haveI : IsStrictNoetherianObject ((ObjectProperty.ιOfLE hIncl).obj E) := hbig.2
    have hstrictE :
        IsStrictArtinianObject E ∧ IsStrictNoetherianObject E :=
      interval_strictFiniteLength_of_inclusion_strict (C := C)
        (s₁ := σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin)
        (s₂ := σ.slicing)
        (a₁ := t - ε₀) (b₁ := t + ε₀) (a₂ := t - 2 * ε₀) (b₂ := t + 2 * ε₀)
        hIncl (X := E)
    haveI : IsStrictArtinianObject E := hstrictE.1
    haveI : IsStrictNoetherianObject E := hstrictE.2
    exact ⟨inferInstance, inferInstance⟩
  · -- Distance bound: d(P, Q) ≤ ε by phase confinement
    set Q := σ.deformedSlicing C W hW ε₀ hε₀ hε₀10 hWide ε hε hεε₀ hsin
    have deformedGtPred_subset_gtProp :
        ∀ {t : ℝ} {E : C},
          σ.deformedGtPred C W hW ε hε (by linarith) hsin t E →
            Q.gtProp C t E := by
      intro t E hE
      induction hE with
      | zero hZ =>
          exact Or.inl hZ
      | mem hE =>
          rename_i E'
          rcases hE with ⟨ψ, hψ, hQ⟩
          have hQ' : Q.P ψ E' := by
            simpa [Q, StabilityCondition.deformedSlicing] using hQ
          exact Q.gtProp_of_semistable C ψ t E' hQ' hψ
      | ext hT _ _ ihX ihY =>
          exact Q.gtProp_of_triangle C t ihX ihY hT
    have deformedLtPred_subset_ltProp :
        ∀ {t : ℝ} {E : C},
          σ.deformedLtPred C W hW ε hε (by linarith) hsin t E →
            Q.ltProp C t E := by
      intro t E hE
      induction hE with
      | zero hZ =>
          exact Or.inl hZ
      | mem hE =>
          rename_i E'
          rcases hE with ⟨ψ, hψ, hQ⟩
          have hQ' : Q.P ψ E' := by
            simpa [Q, StabilityCondition.deformedSlicing] using hQ
          exact Or.inr ⟨HNFiltration.single C E' ψ hQ',
            show 0 < 1 from by omega, hψ⟩
      | ext hT _ _ ihX ihY =>
          exact Q.ltProp_of_triangle C t ihX ihY hT
    -- Forward: Q-HN factors → phase confinement → σ-intervalProp
    have forward : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
        σ.slicing.intervalProp C
          (Q.phiMinus C E hE - ε - δ) (Q.phiPlus C E hE + ε + δ) E := by
      intro E hE δ hδ
      obtain ⟨G, hnG, hfirstG, hlastG⟩ := HNFiltration.exists_both_nonzero C Q hE
      apply intervalProp_of_postnikovTower C σ.slicing G.toPostnikovTower
      intro i
      by_cases hGi : IsZero (G.toPostnikovTower.factor i)
      · exact Or.inl hGi
      · have hsem := G.semistable i
        change σ.deformedPred C W hW ε hε (by linarith) hsin (G.φ i) _ at hsem
        rcases hsem with hZ_i | ⟨a_i, b_i, hab_i, hthin_i, _, _, hSS_i⟩
        · exact absurd hZ_i hGi
        · have ⟨hlo, hhi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab_i
            hε (by linarith) hthin_i hsin hSS_i
          have hGi_le : G.φ i ≤ Q.phiPlus C E hE := by
            rw [Q.phiPlus_eq C E hE G hnG hfirstG]
            exact G.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
          have hGi_ge : Q.phiMinus C E hE ≤ G.φ i := by
            rw [Q.phiMinus_eq C E hE G hnG hlastG]
            exact G.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
          exact σ.slicing.intervalProp_of_intrinsic_phases C hSS_i.2.1
            (by linarith) (by linarith)
    -- Reverse: σ-HN factors → reverse phase confinement → Q-intervalProp
    have reverse : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
        Q.intervalProp C
          (σ.slicing.phiMinus C E hE - ε - δ)
          (σ.slicing.phiPlus C E hE + ε + δ) E := by
      intro E hE δ hδ
      obtain ⟨F, hnF, hfirstF, hlastF⟩ :=
        HNFiltration.exists_both_nonzero C σ.slicing hE
      have hgt : Q.gtProp C (σ.slicing.phiMinus C E hE - ε - δ) E := by
        apply gtProp_of_postnikovTower (C := C) Q F.toPostnikovTower
        intro i
        by_cases hFi : IsZero (F.toPostnikovTower.factor i)
        · exact Or.inl hFi
        · have hFi_ge : σ.slicing.phiMinus C E hE ≤ F.φ i := by
            rw [σ.slicing.phiMinus_eq C E hE F hnF hlastF]
            exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
          exact deformedGtPred_subset_gtProp <|
            P_in_deformedGtPred C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin
              (by linarith [hFi_ge, hδ]) (F.semistable i) hFi
      have hlt : Q.ltProp C (σ.slicing.phiPlus C E hE + ε + δ) E := by
        apply ltProp_of_postnikovTower (C := C) Q F.toPostnikovTower
        intro i
        by_cases hFi : IsZero (F.toPostnikovTower.factor i)
        · exact Or.inl hFi
        · have hFi_le : F.φ i ≤ σ.slicing.phiPlus C E hE := by
            rw [σ.slicing.phiPlus_eq C E hE F hnF hfirstF]
            exact F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
          exact deformedLtPred_subset_ltProp <|
            P_in_deformedLtPred C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin
              (by linarith [hFi_le, hδ]) (F.semistable i) hFi
      exact Q.intervalProp_of_intrinsic_phases C hE
        (Q.phiMinus_gt_of_gtProp C hE hgt)
        (Q.phiPlus_lt_of_ltProp C hE hlt)
    -- Combine: |σ.phiPlus - Q.phiPlus| ≤ ε and |σ.phiMinus - Q.phiMinus| ≤ ε
    apply slicingDist_le_of_phase_bounds
    · -- |σ.phiPlus(E) - Q.phiPlus(E)| ≤ ε
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiPlus(E) ≤ σ.phiPlus(E) + ε
        by_contra h; push_neg at h
        have := Q.phiPlus_lt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < Q.phiPlus C E hE -
            σ.slicing.phiPlus C E hE - ε))
        linarith
      · -- σ.phiPlus(E) ≤ Q.phiPlus(E) + ε
        by_contra h; push_neg at h
        have := σ.slicing.phiPlus_lt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiPlus C E hE -
            Q.phiPlus C E hE - ε))
        linarith
    · -- |σ.phiMinus(E) - Q.phiMinus(E)| ≤ ε
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiMinus(E) - ε ≤ σ.phiMinus(E)
        by_contra h; push_neg at h
        have := σ.slicing.phiMinus_gt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < Q.phiMinus C E hE -
            σ.slicing.phiMinus C E hE - ε))
        linarith
      · -- σ.phiMinus(E) ≤ Q.phiMinus(E) + ε
        by_contra h; push_neg at h
        have := Q.phiMinus_gt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiMinus C E hE -
            Q.phiMinus C E hE - ε))
        linarith

variable [IsTriangulated C] in
/-- **Bridgeland's Theorem 7.1** (deformation of stability conditions). Under the
usual small-deformation hypothesis on `W`, there exists a locally-finite stability
condition `τ = (W, Q)` with `d(P, Q) < ε`.

This is obtained from `bridgeland_7_1_le` by shrinking `ε` slightly using the strict
hypothesis `‖W - Z‖_σ < sin(πε)`. -/
theorem bridgeland_7_1 (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    ∃ (τ : StabilityCondition C), τ.Z = W ∧
      slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε := by
  set x := (stabSeminorm C σ (W - σ.Z)).toReal
  have hx_lt : x < Real.sin (Real.pi * ε) := by
    dsimp [x]
    exact ENNReal.toReal_lt_of_lt_ofReal hsin
  have hε_half : ε < 1 / 2 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi * ε) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos, hε]
    · nlinarith [Real.pi_pos, hε_half]
  set y := (x + Real.sin (Real.pi * ε)) / 2
  have hy_between : x < y ∧ y < Real.sin (Real.pi * ε) := by
    dsimp [y]
    constructor <;> linarith
  have hy_pos : 0 < y := by
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      exact ENNReal.toReal_nonneg
    linarith
  have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · linarith
    · have hy_le : y ≤ Real.sin (Real.pi * ε) := le_of_lt hy_between.2
      exact le_trans hy_le (Real.sin_le_one _)
  set ε' : ℝ := Real.arcsin y / Real.pi
  have hε'_pos : 0 < ε' := by
    dsimp [ε']
    exact div_pos (Real.arcsin_pos.2 hy_pos) Real.pi_pos
  have hpiε_mem : Real.pi * ε ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos, hε_half]
  have hε'_lt : ε' < ε := by
    have harcsin_lt : Real.arcsin y < Real.pi * ε := by
      exact (Real.arcsin_lt_iff_lt_sin hy_mem hpiε_mem).2 hy_between.2
    have hdiv : Real.arcsin y / Real.pi < ε := by
      refine (div_lt_iff₀ Real.pi_pos).2 ?_
      nlinarith
    simpa [ε'] using hdiv
  have hε'ε₀ : ε' < ε₀ := by
    exact lt_trans hε'_lt hεε₀
  have hsin'_eq : Real.sin (Real.pi * ε') = y := by
    have hpiε' : Real.pi * ε' = Real.arcsin y := by
      dsimp [ε']
      field_simp [ne_of_gt Real.pi_pos]
    rw [hpiε']
    exact Real.sin_arcsin hy_mem.1 hy_mem.2
  have hsin'_pos : 0 < Real.sin (Real.pi * ε') := by
    rw [hsin'_eq]
    exact hy_pos
  have hsin' : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε')) := by
    have hx_ne_top : stabSeminorm C σ (W - σ.Z) ≠ ⊤ := ne_top_of_lt hsin
    have hx_lt' : (stabSeminorm C σ (W - σ.Z)).toReal <
        (ENNReal.ofReal (Real.sin (Real.pi * ε'))).toReal := by
      rw [ENNReal.toReal_ofReal (le_of_lt hsin'_pos)]
      simpa [x, hsin'_eq] using hy_between.1
    exact (ENNReal.toReal_lt_toReal hx_ne_top ENNReal.ofReal_ne_top).1 hx_lt'
  obtain ⟨τ, hτZ, hτdist⟩ :=
    bridgeland_7_1_le C σ W hW ε₀ hε₀ hε₀10 hWide ε' hε'_pos hε'ε₀ hsin'
  refine ⟨τ, hτZ, lt_of_le_of_lt hτdist ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hε'_lt

end CategoryTheory.Triangulated
