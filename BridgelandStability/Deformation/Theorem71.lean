/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.Deformation.TStructure
import Mathlib.CategoryTheory.Triangulated.Deformation.PPhiAbelian

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
filtration whose factors are `ssf.Semistable` in `P((a,b))` with phases in `[a+ε, b−ε]`.

**Sorry**: Core of Lemma 7.7 — requires class G/H induction on the Noetherian strict
subobject lattice, propagating phase bounds via Lemma 7.3 (phase confinement). -/
theorem interior_has_enveloped_HN_ssf
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hFL : ThinFiniteLengthInInterval (C := C) σ a b)
    {E : C} (hE : ¬IsZero E)
    (hInt : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) E) :
    let ssf := σ.skewedStabilityFunction_of_near C W hW hab
    ∃ G : HNFiltration C (fun ψ F => ssf.Semistable C F ψ) E,
      ∀ j, a + ε ≤ G.φ j ∧ G.φ j ≤ b - ε := by
  sorry -- Bridgeland Lemma 7.7: class G/H induction (p.23-24)

variable [IsTriangulated C] in
/-- **Lemma 7.7 interior HN** (deformedPred version). Derives a `deformedPred`-typed
HN filtration from `interior_has_enveloped_HN_ssf` by wrapping each `ssf.Semistable`
factor with the enveloping interval `(a, b)` as the `deformedPred` witness.

The phase bounds are `[a+ε, b−ε]` (closed, matching the paper), since each factor's
`ssf.Semistable` data directly provides the `deformedPred` witness with `(a, b)` as
the enveloping interval. -/
theorem interior_has_enveloped_HN
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 4)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hFL : ThinFiniteLengthInInterval (C := C) σ a b)
    {E : C} (hE : ¬IsZero E)
    (hInt : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) E) :
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε hε hε2 hsin) E,
      ∀ j, a + ε ≤ G.φ j ∧ G.φ j ≤ b - ε := by
  let ssf := σ.skewedStabilityFunction_of_near C W hW hab
  obtain ⟨G, hGφ⟩ := interior_has_enveloped_HN_ssf (C := C) σ W hW hab
    hε hε2 hthin hsin hFL hE hInt
  let GQ : HNFiltration C (σ.deformedPred C W hW ε hε hε2 hsin) E :=
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
        refine Or.inr ⟨a, b, hab, hthin, (hGφ j).1, (hGφ j).2, ?_⟩
        simpa [ssf] using G.semistable j }
  exact ⟨GQ, hGφ⟩

/-! ### σ-semistable objects have Q-HN filtrations -/

variable [IsTriangulated C] in
/-- **σ-semistable objects have Q-HN filtrations** (Bridgeland p.24). For E ∈ P(φ),
embed E in P((φ−3ε, φ+5ε)) and apply `interior_has_enveloped_HN`. The Q-HN phases
lie in (φ−2ε, φ+4ε) ⊂ (φ−ε₀, φ+ε₀) since 4ε < ε₀.

Two parameters: `ε₀` (local finiteness, < 1/8) and `ε` (perturbation, 4ε < ε₀).
`ThinFiniteLengthInInterval` is derived from `WideSectorFiniteLength` via `of_wide`. -/
theorem sigmaSemistable_hasDeformedHN
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε hε (by linarith) hsin) E,
      ∀ j, φ - ε₀ < G.φ j ∧ G.φ j < φ + ε₀ := by
  -- Bridgeland p.24: embed E in P((φ-3ε, φ+5ε)), apply interior_has_enveloped_HN.
  set a := φ - 3 * ε with ha_def
  set b := φ + 5 * ε with hb_def
  have hab : a < b := by linarith
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
    hε (by linarith : ε < 1 / 4) hthin hsin hFL hE hInt
  -- Phase bounds: a+ε ≤ G.φ j ≤ b-ε gives φ-2ε ≤ G.φ j ≤ φ+4ε
  -- Since 4ε < ε₀, we have [φ-2ε, φ+4ε] ⊂ (φ-ε₀, φ+ε₀)
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
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {s t : ℝ} (hst : s ≥ t + ε)
    {E : C} (hP : σ.slicing.P s E) (hE : ¬IsZero E) :
    σ.deformedGtPred C W hW ε hε (by linarith) hsin t E := by
  -- Step 1: Q-HN filtration with phases in (s-ε₀, s+ε₀)
  obtain ⟨G, hGφ⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀8 hWide hε hεε₀ hsin hP hE
  have hGn : 0 < G.n := by
    by_contra h; push_neg at h
    exact hE (G.toPostnikovTower.zero_isZero (show G.n = 0 by omega))
  set P := G.toPostnikovTower
  -- Step 2: All factors have σ-intervalProp
  have hfactors_int : ∀ j, σ.slicing.intervalProp C (s - ε₀ - ε) (s + ε₀ + ε)
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
  have hTj₁_int : σ.slicing.intervalProp C (s - ε₀ - ε) (s + ε₀ + ε) (P.triangle j₀).obj₁ := by
    have hchain_int := intervalProp_chain_of_postnikovTower σ.slicing (C := C) (P := P)
      hfactors_int j₀.val (show j₀.val ≤ G.n from by omega)
    rcases hchain_int with hZ | ⟨F, hF⟩
    · exact Or.inl ((Iso.isZero_iff ej₁.symm).mp hZ)
    · exact Or.inr ⟨F.ofIso C ej₁.symm, hF⟩
  have h34 := σ.slicing.phiMinus_triangle_le C hj₀ne hTj₂_ne
    (by linarith : s + ε₀ + ε ≤ s - ε₀ - ε + 1) hTj₁_int (hfactors_int j₀)
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
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {s t : ℝ} (hst : s ≤ t - ε)
    {E : C} (hP : σ.slicing.P s E) (hE : ¬IsZero E) :
    σ.deformedLtPred C W hW ε hε (by linarith) hsin t E := by
  -- Dual of P_in_deformedGtPred: get Q-HN, show all phases < t
  obtain ⟨G, hGφ⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀8 hWide hε hεε₀ hsin hP hE
  have hGn : 0 < G.n := by
    by_contra h; push_neg at h
    exact hE (G.toPostnikovTower.zero_isZero (show G.n = 0 by omega))
  set P := G.toPostnikovTower
  -- All factors have σ-intervalProp
  have hfactors_int : ∀ j, σ.slicing.intervalProp C (s - ε₀ - ε) (s + ε₀ + ε)
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
          -- φ⁺(factor(k)) < s + ε₀ + ε from intervalProp
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
            obtain ⟨F', hnF', hneF'⟩ := HNFiltration.exists_nonzero_first C σ.slicing hfact_ne
            rw [σ.slicing.phiPlus_eq C _ hfact_ne F' hnF' hneF',
                σ.slicing.phiPlus_eq C _ hshift_ne (F'.ofIso C (asIso Tk.mor₃)) hnF' hneF']
            simp [HNFiltration.ofIso]
          -- φ⁺(chain(k)) = φ⁺(Tk.obj₁) via iso invariance
          have hchain_phiPlus : σ.slicing.phiPlus C _ hne =
              σ.slicing.phiPlus C Tk.obj₁ hTk_ne₁ := by
            rw [σ.slicing.phiPlus_eq C _ hTk_ne₁ F hnF hneF,
                σ.slicing.phiPlus_eq C _ hne (F.ofIso C ek₁) hnF hneF]
            simp [HNFiltration.ofIso]
          -- Combine: φ⁺(chain(k)) = φ⁺(factor(k)) - 1 < (s + ε₀ + ε) - 1 ≤ s
          rw [hchain_phiPlus]
          have : σ.slicing.phiPlus C Tk.obj₁ hTk_ne₁ =
              σ.slicing.phiPlus C (P.factor ⟨k, hkn⟩) hfact_ne - 1 := by
            rw [hiso_phiPlus, hphiPlus_shift]; ring
          linarith
        · -- chain(k+1) nonzero: phiPlus_triangle_le gives φ⁺(chain(k)) ≤ φ⁺(chain(k+1)) ≤ s
          have hTk_ne₂ : ¬IsZero Tk.obj₂ := fun hZ ↦ hk1ne ((Iso.isZero_iff ek₂).mp hZ)
          have hTk_obj1_int : σ.slicing.intervalProp C (s - ε₀ - ε) (s + ε₀ + ε) Tk.obj₁ :=
            (σ.slicing.intervalProp_closedUnderIso C _ _).of_iso ek₁.symm
              (intervalProp_chain_of_postnikovTower σ.slicing (C := C) (P := P)
                hfactors_int k (show k ≤ G.n from by omega))
          have hle_step := σ.slicing.phiPlus_triangle_le C hTk_ne₁ hTk_ne₂
            (by linarith : s + ε₀ + ε ≤ s - ε₀ - ε + 1) hTk_obj1_int
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
        rw [σ.slicing.phiPlus_eq C _ hj₁ne
          ((F.ofIso C (ej₁₂.symm.trans (asIso Tj₁.mor₂)))) (by change 0 < F.n; exact hnF)
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
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε hε (by linarith) hsin t X ∧
      σ.deformedLePred C W hW ε hε (by linarith) hsin t Y := by
  obtain ⟨G, _⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀8 hWide hε hεε₀ hsin hP hE
  exact exists_deformedGt_deformedLe_triangle_of_hn C σ W hW hε (by linarith) hsin G t

variable [IsTriangulated C] in
/-- **Step 2** (Bridgeland p.24): If every σ-semistable object admits a Q(>t)/Q(≤t)
truncation triangle (Step 1), then EVERY object admits one. The proof reduces via σ-HN
to the semistable case and assembles the pieces via the octahedral axiom.

**Sorry**: Requires iterated octahedral assembly over σ-HN factors. -/
theorem deformedGtLe_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
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
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (E : C) :
    Nonempty (HNFiltration C (σ.deformedPred C W hW ε hε (by linarith) hsin) E) := by
  sorry -- Requires t-structure → slicing (Prop 5.3) + local finiteness

/-! ### Deformed slicing construction -/

variable [IsTriangulated C] in
/-- **Deformed slicing** (Node 7.Q + 7.6 + 7.7). The slicing `Q` with `Q(ψ) =
deformedPred σ W hW ε ψ`, where `ε` is the perturbation parameter (4ε < ε₀) and
`ε₀` is the local finiteness parameter (< 1/8).

The `closedUnderIso` and `shift_iff` fields are complete. The `hom_vanishing` field
is Lemma 7.6 via `hom_eq_zero_of_deformedPred`. The `hn_exists` field delegates to
`deformedSlicing_hn_exists`, which combines `deformedGtLe_triangle` (sorry: iterated
octahedral assembly over σ-HN factors) with
`exists_hn_of_deformedGt_deformedLe_triangle`. -/
def StabilityCondition.deformedSlicing (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
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
    deformedSlicing_hn_exists C σ W hW hε₀ hε₀8 hWide hε hεε₀ hsin E

variable [IsTriangulated C] in
/-- **W-compatibility of the deformed slicing.** For every nonzero Q-semistable object `E`
of Q-phase `ψ`, the central charge `W([E])` lies on the ray `ℝ₊ · exp(iπψ)`. This
follows directly from the `Semistable` definition, which stores
`wPhaseOf(W([E]), α) = ψ`. -/
theorem StabilityCondition.deformedSlicing_compat
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (ψ : ℝ) (E : C)
    (hQ : (σ.deformedSlicing C W hW ε₀ hε₀ hε₀8 hWide ε hε hεε₀ hsin).P ψ E)
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
`‖W - Z‖_σ < sin(πε₀)`, then `E` lies in the Q-interval `(φ - ε₀ - δ, φ + ε₀ + δ)`
for any `δ > 0`.

This replaces the incorrect statement `sigma_semistable_is_deformedPred` which claimed
σ-semistable implies Q-semistable. That is **false**: a σ-semistable object `E` can
decompose into W-semistable factors with different W-phases (e.g., `E = S₁ ⊕ S₂` with
`S₁, S₂` σ-stable of the same phase but different W-phases), so `E` need not be
Q-semistable. The correct statement is that `E` lies in a Q-interval of half-width
`ε₀ + δ` centered at `φ`.

The proof constructs a Q-HN filtration for `E` by decomposing it in the abelian
category `P(φ)` using the W-stability function restricted to `P(φ)`. Each W-HN
factor in `P(φ)` has W-phase within `ε₀` of `φ`, giving the desired interval bound.
-/
theorem sigma_semistable_intervalProp
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    {δ : ℝ} (hδ : 0 < δ) :
    (σ.deformedSlicing C W hW ε₀ hε₀ hε₀8 hWide ε hε hεε₀ hsin).intervalProp C
      (φ - ε₀ - δ) (φ + ε₀ + δ) E := by
  -- Apply sigmaSemistable_hasDeformedHN to get Q-HN with phases in (φ-ε₀, φ+ε₀).
  -- Then (φ-ε₀, φ+ε₀) ⊂ (φ-ε₀-δ, φ+ε₀+δ) gives the Q-interval bound.
  obtain ⟨G, hGφ⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀8 hWide hε hεε₀ hsin hP hE
  exact Or.inr ⟨G, fun j ↦ ⟨by linarith [(hGφ j).1], by linarith [(hGφ j).2]⟩⟩

/-! ### Deformation theorem (Theorem 7.1) -/

variable [IsTriangulated C] in
/-- **Bridgeland's Theorem 7.1** (deformation of stability conditions). Given a
stability condition `σ = (Z, P)` on a triangulated category `D` and a group
homomorphism `W : K₀(D) → ℂ` with `‖W - Z‖_σ < sin(πε₀)` (where `ε₀` comes from
the local finiteness of `σ`), there exists a locally-finite stability condition
`τ = (W, Q)` with `d(P, Q) ≤ ε₀`.

The proof constructs the deformed slicing `Q` via `deformedSlicing`, then verifies:
1. **Hom-vanishing** (Lemma 7.6): `hom_eq_zero_of_deformedPred`
2. **HN filtrations** (Lemma 7.7 + Nodes 7.8–7.9): well-founded recursion in thin
   quasi-abelian categories, assembled via t-structures `Q(> t)`
3. **Compatibility**: `deformedSlicing_compat`
4. **Local finiteness**: inherited from `σ` via phase confinement (Node 7.3)
5. **Distance bound**: `d(P, Q) ≤ ε₀` by phase confinement (Node 7.3)

The hypothesis `hε₀_lf` ensures `ε₀` is small enough relative to `σ`'s local finiteness
parameter, following Bridgeland's condition that intervals of half-width `ε₀ + δ` have
finite length. -/
theorem bridgeland_7_1 (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (ε : ℝ) (hε : 0 < ε) (hεε₀ : 4 * ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hε₀_lf : ∃ δ : ℝ, 0 < δ ∧ ε₀ + δ < 1 / 2 ∧ ∀ t : ℝ,
      ∀ (E :
        (σ.slicing.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ))).FullSubcategory),
        IsArtinianObject E ∧ IsNoetherianObject E) :
    ∃ (τ : StabilityCondition C), τ.Z = W ∧
      slicingDist C σ.slicing τ.slicing ≤ ENNReal.ofReal ε₀ := by
  have hε₀2 : ε₀ < 1 / 4 := by linarith
  let hSector : SectorFiniteLength (C := C) σ ε₀ hε₀ hε₀2 :=
    SectorFiniteLength.of_wide (C := C) σ hε₀ hε₀2 hε₀8 hWide
  refine ⟨⟨σ.deformedSlicing C W hW ε₀ hε₀ hε₀8 hWide ε hε hεε₀ hsin, W,
    σ.deformedSlicing_compat C W hW ε₀ hε₀ hε₀8 hWide ε hε hεε₀ hsin, ?_⟩, rfl, ?_⟩
  · -- Local finiteness: inherited from σ via phase confinement
    obtain ⟨δ, hδ, hδ_half, hlf_σ⟩ := hε₀_lf
    let δ' : ℝ := min (δ / 2) (1 / 4)
    constructor
    refine ⟨δ', by
      dsimp [δ']
      positivity, by
      dsimp [δ']
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun t E ↦ ?_⟩
    letI : Fact (t - δ' < t + δ') := ⟨by
      dsimp [δ']
      have : 0 < δ' := by
        dsimp [δ']
        positivity
      linarith⟩
    letI : Fact ((t + δ') - (t - δ') ≤ 1) := ⟨by
      dsimp [δ']
      have hδ' : δ' ≤ 1 / 4 := by
        dsimp [δ']
        exact min_le_right _ _
      linarith⟩
    have hIncl :
        (σ.deformedSlicing C W hW ε₀ hε₀ hε₀8 hWide ε hε hεε₀ hsin).intervalProp C
            (t - δ') (t + δ') ≤
          σ.slicing.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ)) := by
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
              dsimp [δ'] at hleft
              linarith [hlo, min_le_left (δ / 2) (1 / 4 : ℝ)])
            (by
              have hright := (hF i).2
              dsimp [δ'] at hright
              linarith [hhi, min_le_left (δ / 2) (1 / 4 : ℝ)])
    let I :
        (σ.deformedSlicing C W hW ε₀ hε₀ hε₀8 hWide ε hε hεε₀ hsin).IntervalCat C
            (t - δ') (t + δ') ⥤
          σ.slicing.IntervalCat C (t - (ε₀ + δ)) (t + (ε₀ + δ)) :=
      ObjectProperty.ιOfLE hIncl
    letI : Fact (t - (ε₀ + δ) < t + (ε₀ + δ)) := ⟨by linarith [hε₀, hδ]⟩
    letI : Fact ((t + (ε₀ + δ)) - (t - (ε₀ + δ)) ≤ 1) := ⟨by linarith [hδ_half]⟩
    have hI : IsArtinianObject (I.obj E) ∧ IsNoetherianObject (I.obj E) :=
      hlf_σ t (I.obj E)
    haveI : IsArtinianObject (I.obj E) := hI.1
    haveI : IsNoetherianObject (I.obj E) := hI.2
    have hstrictE :
        IsStrictArtinianObject E ∧ IsStrictNoetherianObject E :=
      interval_strictFiniteLength_of_inclusion (C := C)
        (s₁ := σ.deformedSlicing C W hW ε₀ hε₀ hε₀8 hWide ε hε hεε₀ hsin) (s₂ := σ.slicing)
        (a₁ := t - δ') (b₁ := t + δ') (a₂ := t - (ε₀ + δ)) (b₂ := t + (ε₀ + δ))
        hIncl (X := E)
    haveI : IsStrictArtinianObject E := hstrictE.1
    haveI : IsStrictNoetherianObject E := hstrictE.2
    exact ⟨inferInstance, inferInstance⟩
  · -- Distance bound: d(P, Q) ≤ ε₀ by phase confinement
    set Q := σ.deformedSlicing C W hW ε₀ hε₀ hε₀8 hWide ε hε hεε₀ hsin
    -- Forward: Q-HN factors → phase confinement → σ-intervalProp
    have forward : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
        σ.slicing.intervalProp C
          (Q.phiMinus C E hE - ε₀ - δ) (Q.phiPlus C E hE + ε₀ + δ) E := by
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
          (σ.slicing.phiMinus C E hE - ε₀ - δ)
          (σ.slicing.phiPlus C E hE + ε₀ + δ) E := by
      intro E hE δ hδ
      obtain ⟨F, hnF, hfirstF, hlastF⟩ :=
        HNFiltration.exists_both_nonzero C σ.slicing hE
      apply intervalProp_of_postnikovTower C Q F.toPostnikovTower
      intro i
      by_cases hFi : IsZero (F.toPostnikovTower.factor i)
      · exact Or.inl hFi
      · have hFi_le : F.φ i ≤ σ.slicing.phiPlus C E hE := by
          rw [σ.slicing.phiPlus_eq C E hE F hnF hfirstF]
          exact F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        have hFi_ge : σ.slicing.phiMinus C E hE ≤ F.φ i := by
          rw [σ.slicing.phiMinus_eq C E hE F hnF hlastF]
          exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
        -- Factor i is σ-semistable of phase F.φ i. By reverse phase confinement,
        -- it lies in Q-interval (F.φ i - ε₀ - δ, F.φ i + ε₀ + δ).
        have hQint := sigma_semistable_intervalProp C σ W hW
          hε₀ hε₀8 hWide hε hεε₀ hsin (F.semistable i) hFi hδ
        -- Widen to (phiMinus - ε₀ - δ, phiPlus + ε₀ + δ) using monotonicity
        exact Q.intervalProp_mono C (by linarith) (by linarith) hQint
    -- Combine: |σ.phiPlus - Q.phiPlus| ≤ ε₀ and |σ.phiMinus - Q.phiMinus| ≤ ε₀
    apply slicingDist_le_of_phase_bounds
    · -- |σ.phiPlus(E) - Q.phiPlus(E)| ≤ ε₀
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiPlus(E) ≤ σ.phiPlus(E) + ε₀
        by_contra h; push_neg at h
        have := Q.phiPlus_lt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < -(σ.slicing.phiPlus C E hE -
            Q.phiPlus C E hE) - ε₀))
        linarith
      · -- σ.phiPlus(E) ≤ Q.phiPlus(E) + ε₀
        by_contra h; push_neg at h
        have := σ.slicing.phiPlus_lt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiPlus C E hE -
            Q.phiPlus C E hE - ε₀))
        linarith
    · -- |σ.phiMinus(E) - Q.phiMinus(E)| ≤ ε₀
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiMinus(E) - ε₀ ≤ σ.phiMinus(E)
        by_contra h; push_neg at h
        have := σ.slicing.phiMinus_gt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < -(σ.slicing.phiMinus C E hE -
            Q.phiMinus C E hE) - ε₀))
        linarith
      · -- σ.phiMinus(E) ≤ Q.phiMinus(E) + ε₀
        by_contra h; push_neg at h
        have := Q.phiMinus_gt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiMinus C E hE -
            Q.phiMinus C E hE - ε₀))
        linarith

variable [IsTriangulated C] in
/-- **Local connectedness of `Stab(D)`**: every basis neighbourhood is contained in
the topological connected component of its centre.

This is the path-connectedness content of Bridgeland's Theorem 1.2 proof (§7).
For `τ ∈ basisNhd(σ, ε)`, the linear interpolation `W_t = Z(σ) + t·(Z(τ) − Z(σ))`
and `γ(t) = bridgeland_7_1(σ, W_t, ε₀)` define a path from `σ` to `τ`.
Path-continuity at `t₀` follows from applying Theorem 7.1 centred at `γ(t₀)` with
a small `ε′`, then **Lemma 6.4** (uniqueness for same `Z` and `d < 1`) identifies
the result with `γ(t)`. The image of `[0, 1]` is therefore preconnected. -/
theorem basisNhd_subset_connectedComponent (σ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    basisNhd C σ ε ⊆ {τ | ConnectedComponents.mk τ = ConnectedComponents.mk σ} := by
  -- Roadmap (Bridgeland §7, path-connectedness):
  -- For τ ∈ basisNhd(σ, ε), define the linear interpolation
  --   W_t := Z(σ) + t · (Z(τ) − Z(σ)),  t ∈ [0,1]
  -- and γ(t) := bridgeland_7_1(σ, W_t, ε₀). Then γ(0) = σ and γ(1) = τ.
  --
  -- Continuity at t₀: apply Theorem 7.1 centred at γ(t₀) with small ε',
  -- then Lemma 6.4 (eq_of_same_Z_near) identifies the result with γ(t).
  --
  -- Requires:
  -- 1. ‖W_t - Z(σ)‖_σ = t · ‖Z(τ) - Z(σ)‖_σ < sin(πε₀) for all t ∈ [0,1]
  -- 2. Continuity of t ↦ ‖W_t - Z(γ(t₀))‖_{γ(t₀)} near t₀
  -- 3. Lemma 6.2 (stabSeminorm_dominated_of_connected) for norm comparison
  -- The image of [0,1] under γ is connected, so τ and σ share a component.
  sorry


end CategoryTheory.Triangulated
