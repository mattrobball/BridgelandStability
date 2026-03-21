/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.HNExistence

/-!
# P(s) in Q(>t)/Q(<t) and Truncation Triangles

Embedding sigma-semistable objects into Q-predicates, and construction of
Q(>t)/Q(<=t) truncation triangles for arbitrary objects.
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
  [IsTriangulated C]


/-! ### P(s) ⊂ Q(>t) and P(s) ⊂ Q(<t) -/

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
    σ.deformedGtPred C W hW ε t E := by
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
        simp only [show k - 1 + 1 = k from by omega] at this
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
    σ.deformedLtPred C W hW ε t E := by
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
            simp only [HNFiltration.shiftHN, Int.cast_one]
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
          hneF]
        rw [σ.slicing.phiPlus_eq C _ hchain_j₁1_ne F hnF hneF] at hphiPlus_le
        simp only [HNFiltration.ofIso] at hphiPlus_le ⊢
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
      σ.deformedGtPred C W hW ε t X ∧
      σ.deformedLePred C W hW ε t Y := by
  obtain ⟨G, _⟩ := sigmaSemistable_hasDeformedHN C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin hP hE
  exact exists_deformedGt_deformedLe_triangle_of_hn C σ W hW G t

/-- **Step 2** (Bridgeland p.24): If every σ-semistable object admits a Q(>t)/Q(≤t)
truncation triangle (Step 1), then EVERY object admits one. The proof reduces via σ-HN
to the semistable case and assembles the pieces via the octahedral axiom.

The proof splits E into HIGH (σ-phases > t+ε), MID (σ-phases in (t-ε, t+ε]),
and LOW (σ-phases ≤ t-ε) using the σ-HN filtration and `split_hn_filtration_at_cutoff`.
HIGH ∈ Q(>t) via `P_in_deformedGtPred`, LOW ∈ Q(≤t) via `P_in_deformedLtPred`.
MID gets a Q-HN via `interior_has_enveloped_HN` (finite-length subcategory), giving
a truncation X_M → MID → Y_M. Two octahedrals combine:
  (1) X_M + LOW → V ∈ Q(≤t) (extension of Y_M and LOW), and
  (2) HIGH + X_M → Z ∈ Q(>t) (extension of HIGH and X_M). -/
theorem deformedGtLe_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ (by linarith [hε₀10]))
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (E : C) (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε t X ∧
      σ.deformedLePred C W hW ε t Y := by
  -- Step 0: Get σ-HN of E
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  -- Step 1: Split σ-HN at cutoff (t + ε)
  obtain ⟨HIGH, REST, GH, GR, fH, gR, hR, hT1, hprops1⟩ :=
    split_hn_filtration_at_cutoff (C := C) F (t + ε)
  have hH_phases := And.left hprops1
  have hR_phases := And.left (And.right hprops1)
  -- Step 2: Split REST's filtration at cutoff (t - ε)
  obtain ⟨MID, LOW, GM, GL, fM, gL, hL, hT2, hprops2⟩ :=
    split_hn_filtration_at_cutoff (C := C) GR (t - ε)
  have hM_phases := And.left hprops2
  have hL_phases := And.left (And.right hprops2)
  have hGM_contain := And.right (And.right (And.right hprops2))
  -- Helper: ExtensionClosure is idempotent
  have ec_idem_gt : ∀ {X : C},
      (σ.deformedGtPred C W hW ε t).ExtensionClosure X →
      σ.deformedGtPred C W hW ε t X := by
    intro X hX; induction hX with
    | zero hZ => exact .zero hZ
    | mem h => exact h
    | ext hT _ _ ihX ihY => exact .ext hT ihX ihY
  have ec_idem_le : ∀ {X : C},
      (σ.deformedLePred C W hW ε t).ExtensionClosure X →
      σ.deformedLePred C W hW ε t X := by
    intro X hX; induction hX with
    | zero hZ => exact .zero hZ
    | mem h => exact h
    | ext hT _ _ ihX ihY => exact .ext hT ihX ihY
  -- Step 3: HIGH ∈ Q(>t) — each factor has phase > t+ε ≥ t+ε, use P_in_deformedGtPred
  have hHIGH : σ.deformedGtPred C W hW ε t HIGH := by
    apply ec_idem_gt
    exact ObjectProperty.ExtensionClosure.of_postnikovTower GH.toPostnikovTower (fun j ↦ by
      by_cases hjz : IsZero (GH.toPostnikovTower.factor j)
      · exact ObjectProperty.ExtensionClosure.zero hjz
      · exact P_in_deformedGtPred C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin
          (show GH.φ j ≥ t + ε by linarith [hH_phases j]) (GH.semistable j) hjz)
  -- Step 4: LOW ∈ Q(≤t) — each factor has phase ≤ t-ε, use P_in_deformedLtPred → Q(≤t)
  have hLOW : σ.deformedLePred C W hW ε t LOW := by
    apply ec_idem_le
    exact ObjectProperty.ExtensionClosure.of_postnikovTower GL.toPostnikovTower (fun j ↦ by
      by_cases hjz : IsZero (GL.toPostnikovTower.factor j)
      · exact ObjectProperty.ExtensionClosure.zero hjz
      · exact σ.deformedLePred_of_deformedLtPred C W hW _ <|
          P_in_deformedLtPred C σ W hW hε₀ hε₀10 hWide hε hεε₀ hsin
            (show GL.φ j ≤ t - ε by linarith [hL_phases j]) (GL.semistable j) hjz)
  -- Step 5: Handle MID
  by_cases hMIDz : IsZero MID
  · -- MID = 0 ⟹ REST is extension of MID (zero) and LOW (∈ Q(≤t)), so REST ∈ Q(≤t).
    have hREST : σ.deformedLePred C W hW ε t REST :=
      .ext hT2 (.zero hMIDz) hLOW
    exact ⟨HIGH, REST, fH, gR, hR, hT1, hHIGH, hREST⟩
  · -- MID nonzero: get Q-HN of MID via finite-length subcategory, then truncation
    -- MID has σ-HN filtration GM with phases in (t-ε, t+ε]
    -- Step 5a: Get truncation of MID via embedding in P((t-3ε, t+5ε+δ))
    -- and applying interior_has_enveloped_HN + split_hn_filtration_at_cutoff
    have hMID_trunc :
        ∃ (XM YM : C) (fXM : XM ⟶ MID) (gYM : MID ⟶ YM) (hYM : YM ⟶ XM⟦(1 : ℤ)⟧),
          Triangle.mk fXM gYM hYM ∈ distTriang C ∧
          σ.deformedGtPred C W hW ε t XM ∧
          σ.deformedLePred C W hW ε t YM := by
      -- Each factor of MID is σ-semistable with phase in (t-ε, t+ε].
      -- Embed MID in P((t-ε₀, t+ε₀)) ⊂ P((t-2ε-ε₀, t+4ε+ε₀)) and use
      -- interior_has_enveloped_HN to get Q-HN of MID, then split at cutoff t.
      set a := t - 2 * ε - ε₀ with ha_def
      set b := t + 4 * ε + ε₀ with hb_def
      have hab : a < b := by linarith
      haveI : Fact (a < b) := ⟨hab⟩
      haveI : Fact (b - a ≤ 1) := ⟨by simp [a, b]; linarith⟩
      have hthin_ab : b - a + 2 * ε < 1 := by simp [a, b]; linarith
      -- ThinFiniteLengthInInterval from WideSectorFiniteLength (center t+ε₀)
      have hFL_ab : ThinFiniteLengthInInterval (C := C) σ a b :=
        ThinFiniteLengthInInterval.of_wide (C := C) σ hε₀ (by linarith)
          (show (t + ε₀) - 4 * ε₀ ≤ a by simp [a]; linarith)
          (show b ≤ (t + ε₀) + 4 * ε₀ by simp [b]; linarith) hWide
      -- MID ∈ intervalProp(a+2ε, b-4ε) = intervalProp(t-ε₀, t+ε₀)
      have hMID_int : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) MID := by
        -- GM's phases satisfy t-ε < φ_j (from hM_phases) and φ_j ≤ t+ε (inherited from GR).
        -- Since ε < ε₀: t-ε > t-ε₀ = a+2ε and t+ε < t+ε₀ = b-4ε. QED.
        right; refine ⟨GM, fun j ↦ ?_⟩
        constructor
        · -- a + 2ε = t - ε₀ < t - ε < GM.φ j
          have := hM_phases j; simp [a]; linarith
        · -- GM.φ j ≤ t + ε < t + ε₀ = b - 4ε
          -- GM's phases come from GR's phases (which satisfy ≤ t+ε)
          -- The split preserves this bound.
          have : GM.φ j ≤ t + ε := by
            obtain ⟨i, hi⟩ := hGM_contain j
            rw [hi]; exact hR_phases i
          simp [b]; linarith
      -- Apply interior_has_enveloped_HN to get Q-HN of MID
      have hMIDne : ¬IsZero MID := hMIDz
      obtain ⟨G_mid, hG_mid_phases⟩ := interior_has_enveloped_HN C σ W hW hab
        hε (by linarith : ε < 1 / 10) hthin_ab hsin hFL_ab hMIDne hMID_int
      -- Split Q-HN at cutoff t → truncation triangle
      exact exists_deformedGt_deformedLe_triangle_of_hn C σ W hW G_mid t
    obtain ⟨XM, YM, fXM, gYM, hYM, hTM, hXM, hYM_pred⟩ := hMID_trunc
    -- Step 5b: First octahedral — combine MID truncation with LOW to get REST's Q(≤t) part
    -- Compose: XM → MID → REST (= fXM ≫ fM)
    obtain ⟨V, vR, wV, hTV⟩ := distinguished_cocone_triangle (fXM ≫ fM)
    -- Octahedral: h₁₂ = XM → MID → YM, h₂₃ = MID → REST → LOW, h₁₃ = XM → REST → V
    let oct1 := Triangulated.someOctahedron rfl hTM hT2 hTV
    -- oct1.mem: YM → V → LOW → YM[1] (distinguished)
    have hV : σ.deformedLePred C W hW ε t V :=
      .ext oct1.mem hYM_pred hLOW
    -- Step 5c: Second octahedral — combine HIGH with REST's Q(>t) part
    -- Compose: E → REST → V (= gR ≫ vR) and use Octahedron' since gR is second morphism
    obtain ⟨Z13, vE, wZ13, hTZ⟩ := distinguished_cocone_triangle₁ (gR ≫ vR)
    -- Octahedron': h₁₂ = HIGH → E → REST, h₂₃ = XM → REST → V, h₁₃ = Z13 → E → V
    let oct2 := Triangulated.someOctahedron' rfl hT1 hTV hTZ
    -- oct2.mem: HIGH → Z13 → XM → HIGH[1] (distinguished)
    have hZ13 : σ.deformedGtPred C W hW ε t Z13 :=
      .ext oct2.mem hHIGH hXM
    exact ⟨Z13, V, vE, gR ≫ vR, wZ13, hTZ, hZ13, hV⟩


end CategoryTheory.Triangulated
