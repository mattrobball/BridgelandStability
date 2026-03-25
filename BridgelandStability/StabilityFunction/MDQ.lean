/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityFunction.HarderNarasimhan

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
# Maximally Destabilizing Quotients

The IsMDQ structure, MDQ existence from artinian+noetherian, and
HN filtration existence via MDQ recursion.
-/

/-- A quotient `q : E ⟶ B` is maximally destabilizing if it is an epimorphism onto a
nonzero semistable object of minimal phase among semistable quotients of `E`. -/
structure IsMDQ (Z : StabilityFunction A) {E B : A} (q : E ⟶ B) : Prop where
  epi : Epi q
  nonzero : ¬IsZero B
  semistable : Z.IsSemistable B
  minimal :
    ∀ {B' : A} (q' : E ⟶ B'), Epi q' → ¬IsZero B' → Z.IsSemistable B' →
      Z.phase B ≤ Z.phase B' ∧
        (Z.phase B' = Z.phase B → ∃ t : B ⟶ B', q' = q ≫ t)

/-- A semistable object is its own mdq. -/
private theorem IsMDQ.id_of_semistable (Z : StabilityFunction A) {E : A}
    (hss : Z.IsSemistable E) : IsMDQ Z (𝟙 E : E ⟶ E) where
  epi := by infer_instance
  nonzero := hss.1
  semistable := hss
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    haveI : Epi q' := hq'
    refine ⟨phase_le_of_epi Z q' hss hB'_nz, ?_⟩
    intro _hEq
    exact ⟨q', by simp⟩

/-- The phase of an mdq is bounded above by the phase of the source object. -/
private theorem IsMDQ.phase_le_of_exists_quotient
    (Z : StabilityFunction A) {E B : A} {q : E ⟶ B} (hq : IsMDQ Z q)
    [IsArtinianObject E] [IsNoetherianObject E] :
    Z.phase B ≤ Z.phase E := by
  have hE_nz : ¬IsZero E := by
    intro hE
    have hzero : q = 0 := zero_of_source_iso_zero _ hE.isoZero
    haveI : Epi q := hq.epi
    exact hq.nonzero (IsZero.of_epi_eq_zero q hzero)
  obtain ⟨Q, p, hp, hQ_nz, hQ_ss, hQ_phase⟩ :=
    exists_semistable_quotient_le_phase_of_artinian_noetherian Z hE_nz
  exact (hq.minimal p hp hQ_nz hQ_ss).1.trans hQ_phase

/-- An mdq has phase at most the phase of any nonzero quotient of its source.
This is the quotient-side comparison Bridgeland uses before the final kernel-recursion
diagram: reduce the arbitrary quotient to a semistable quotient of minimal phase. -/
private theorem IsMDQ.phase_le_of_quotient
    (Z : StabilityFunction A) {E B Q : A} {q : E ⟶ B} (hq : IsMDQ Z q)
    (p : E ⟶ Q) [Epi p] [IsArtinianObject Q] [IsNoetherianObject Q]
    (hQ : ¬IsZero Q) :
    Z.phase B ≤ Z.phase Q := by
  obtain ⟨R, r, hr, hR_nz, hR_ss, hR_phase⟩ :=
    exists_semistable_quotient_le_phase_of_artinian_noetherian Z (E := Q) hQ
  haveI : Epi r := hr
  have hcomp : Epi (p ≫ r) := by infer_instance
  exact (hq.minimal (p ≫ r) hcomp hR_nz hR_ss).1.trans hR_phase

/-- If a quotient of the source has the same phase as an mdq, then that quotient is already
semistable. Otherwise a destabilizing semistable subobject would produce a smaller-phase
quotient, contradicting minimality of the mdq. -/
private theorem IsMDQ.isSemistable_of_quotient_phase_eq
    (Z : StabilityFunction A) {E B Q : A} {q : E ⟶ B} (hq : IsMDQ Z q)
    (p : E ⟶ Q) [Epi p] [IsArtinianObject Q] [IsNoetherianObject Q]
    (hQ : ¬IsZero Q) (hEq : Z.phase Q = Z.phase B) :
    Z.IsSemistable Q := by
  by_contra hQ_ss
  obtain ⟨A', hA'_ne, hA'_ss, hA'_phase⟩ :=
    Z.exists_semistable_subobject_gt_phase_of_not_semistable (E := Q) hQ hQ_ss
  have hA'_top : A' ≠ ⊤ := by
    intro hA'_eq
    have hphase_eq : Z.phase (A' : A) = Z.phase Q := by
      rw [hA'_eq]
      exact Z.phase_eq_of_iso (asIso (⊤ : Subobject Q).arrow)
    grind
  letI : IsArtinianObject (cokernel A'.arrow) := isArtinianObject_of_epi (cokernel.π A'.arrow)
  letI : IsNoetherianObject (cokernel A'.arrow) := isNoetherianObject_of_epi (cokernel.π A'.arrow)
  have hQ'_nz : ¬IsZero (cokernel A'.arrow) := cokernel_nonzero_of_ne_top hA'_top
  have hcomp : Epi (p ≫ cokernel.π A'.arrow) := by infer_instance
  have hmin :
      Z.phase B ≤ Z.phase (cokernel A'.arrow) :=
    IsMDQ.phase_le_of_quotient Z hq (p ≫ cokernel.π A'.arrow) hQ'_nz
  have hlt :
      Z.phase (cokernel A'.arrow) < Z.phase B := by
    calc
      Z.phase (cokernel A'.arrow) < Z.phase Q :=
        phase_cokernel_lt_of_destabilizing_semistable_subobject Z hA'_ss hA'_phase hA'_top
      _ = Z.phase B := hEq
  exact (not_lt_of_ge hmin) hlt

/-- The semistable-target equality clause in the mdq definition extends to arbitrary
nonzero quotients of the same phase. -/
private theorem IsMDQ.factor_of_phase_eq_of_quotient
    (Z : StabilityFunction A) {E B Q : A} {q : E ⟶ B} (hq : IsMDQ Z q)
    (p : E ⟶ Q) [Epi p] [IsArtinianObject Q] [IsNoetherianObject Q]
    (hQ : ¬IsZero Q) (hEq : Z.phase Q = Z.phase B) :
    ∃ t : B ⟶ Q, p = q ≫ t := by
  have hQ_ss : Z.IsSemistable Q := IsMDQ.isSemistable_of_quotient_phase_eq Z hq p hQ hEq
  exact (hq.minimal p inferInstance hQ hQ_ss).2 hEq

/-- Precomposing an mdq with an isomorphism of source objects preserves the mdq property. -/
private theorem IsMDQ.precomposeIso
    (Z : StabilityFunction A) {E E' B : A} {q : E ⟶ B}
    (hq : IsMDQ Z q) (e : E' ≅ E) :
    IsMDQ Z (e.hom ≫ q) where
  epi := by
    haveI : Epi q := hq.epi
    letI : Epi e.hom := by infer_instance
    infer_instance
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    haveI : Epi q' := hq'
    let q'' : E ⟶ B' := e.inv ≫ q'
    have hq'' : Epi q'' := by infer_instance
    refine ⟨(hq.minimal q'' hq'' hB'_nz hB'_ss).1, ?_⟩
    intro hEq
    obtain ⟨t, ht⟩ := (hq.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
    refine ⟨t, ?_⟩
    change q' = (e.hom ≫ q) ≫ t
    calc
      q' = e.hom ≫ (e.inv ≫ q') := by simp
      _ = e.hom ≫ (q ≫ t) := by
          simpa [q''] using congrArg (fun f : E ⟶ B' => e.hom ≫ f) ht
      _ = (e.hom ≫ q) ≫ t := by rw [Category.assoc]

/-- If an mdq `E ↠ B` factors through an epi `E ↠ Q`, then the induced
quotient `Q ↠ B` is again an mdq. This is the quotient-side transport needed for
Bridgeland's Proposition 2.4e diagram. -/
private theorem IsMDQ.of_epi_factor
    (Z : StabilityFunction A) {E Q B : A} {q : E ⟶ B}
    (hq : IsMDQ Z q) {p : E ⟶ Q} [Epi p] {piQ : Q ⟶ B}
    (hfac : p ≫ piQ = q) :
    IsMDQ Z piQ where
  epi := by
    haveI : Epi q := hq.epi
    exact epi_of_epi_fac hfac
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    haveI : Epi q' := hq'
    have hcomp : Epi (p ≫ q') := by infer_instance
    refine ⟨(hq.minimal (p ≫ q') hcomp hB'_nz hB'_ss).1, ?_⟩
    intro hEq
    obtain ⟨t, ht⟩ := (hq.minimal (p ≫ q') hcomp hB'_nz hB'_ss).2 hEq
    refine ⟨t, ?_⟩
    apply (cancel_epi p).1
    calc
      p ≫ q' = q ≫ t := ht
      _ = (p ≫ piQ) ≫ t := by rw [← hfac]
      _ = p ≫ (piQ ≫ t) := by rw [Category.assoc]

/-- Recursive mdq step: a semistable destabilizing subobject lets us replace `E` by the
quotient `E/A`, recurse there, and then pull the mdq back to `E`. -/
private theorem IsMDQ.comp_of_destabilizing_semistable_subobject
    (Z : StabilityFunction A) {E : A} {A' : Subobject E}
    (hA'_ss : Z.IsSemistable (A' : A)) (hA'_phase : Z.phase E < Z.phase (A' : A))
    (hA'_top : A' ≠ ⊤) {B : A} {q : cokernel A'.arrow ⟶ B}
    [IsArtinianObject (cokernel A'.arrow)] [IsNoetherianObject (cokernel A'.arrow)]
    (hq : IsMDQ Z q) :
    IsMDQ Z (cokernel.π A'.arrow ≫ q) where
  epi := by
    haveI : Epi q := hq.epi
    infer_instance
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    have hB_le_cok : Z.phase B ≤ Z.phase (cokernel A'.arrow) :=
      IsMDQ.phase_le_of_exists_quotient Z hq
    have hB_lt_A : Z.phase B < Z.phase (A' : A) := by
      have hA'_cok_le :
          Z.phase (cokernel A'.arrow) ≤ Z.phase E :=
        phase_cokernel_le_of_destabilizing_semistable_subobject Z hA'_ss hA'_phase hA'_top
      grind
    by_cases hle : Z.phase B ≤ Z.phase B'
    · refine ⟨hle, ?_⟩
      intro hEq
      have hB'_lt_A : Z.phase B' < Z.phase (A' : A) := by
        rw [hEq]
        exact hB_lt_A
      have hzero : A'.arrow ≫ q' = 0 :=
        hom_zero_of_semistable_phase_gt Z hA'_ss hB'_ss hB'_lt_A _
      let q'' : cokernel A'.arrow ⟶ B' := cokernel.desc A'.arrow q' hzero
      have hq'' : Epi q'' := epi_of_epi_fac (cokernel.π_desc A'.arrow q' hzero)
      obtain ⟨t, ht⟩ := (hq.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
      refine ⟨t, ?_⟩
      calc
        q' = cokernel.π A'.arrow ≫ q'' := by
          symm
          exact cokernel.π_desc A'.arrow q' hzero
        _ = cokernel.π A'.arrow ≫ (q ≫ t) := by rw [ht]
        _ = (cokernel.π A'.arrow ≫ q) ≫ t := by rw [Category.assoc]
    · have hlt : Z.phase B' < Z.phase B := lt_of_not_ge hle
      have hB'_lt_A : Z.phase B' < Z.phase (A' : A) :=
        lt_of_lt_of_le hlt hB_lt_A.le
      have hzero : A'.arrow ≫ q' = 0 :=
        hom_zero_of_semistable_phase_gt Z hA'_ss hB'_ss hB'_lt_A _
      let q'' : cokernel A'.arrow ⟶ B' := cokernel.desc A'.arrow q' hzero
      have hq'' : Epi q'' := epi_of_epi_fac (cokernel.π_desc A'.arrow q' hzero)
      exact False.elim <| (not_lt_of_ge (hq.minimal q'' hq'' hB'_nz hB'_ss).1) hlt

/-- Existence of maximally destabilizing quotients under Artinian/Noetherian hypotheses. -/
theorem exists_mdq_of_artinian_noetherian
    (Z : StabilityFunction A) {E : A} [IsArtinianObject E] [IsNoetherianObject E]
    (hE : ¬IsZero E) :
    ∃ (B : A) (q : E ⟶ B), IsMDQ Z q := by
  suffices
      ∀ (S : Subobject E), ¬IsZero (cokernel S.arrow) →
        ∃ (B : A) (q : cokernel S.arrow ⟶ B), IsMDQ Z q by
    let e0 : cokernel (⊥ : Subobject E).arrow ≅ E := by
      simpa [Subobject.bot_arrow] using
        (cokernelZeroIsoTarget (X := ((⊥ : Subobject E) : A)) (Y := E))
    have hbot : ¬IsZero (cokernel (⊥ : Subobject E).arrow) := by
      intro hZ
      exact hE (hZ.of_iso e0.symm)
    obtain ⟨B, q, hq⟩ := this ⊥ hbot
    refine ⟨B, e0.inv ≫ q, ?_⟩
    exact IsMDQ.precomposeIso Z hq e0.symm
  intro S
  induction S using WellFoundedGT.induction with
  | ind S ih =>
      intro hQS_nz
      let QS := cokernel S.arrow
      haveI : IsArtinianObject QS := isArtinianObject_of_epi (cokernel.π S.arrow)
      haveI : IsNoetherianObject QS := isNoetherianObject_of_epi (cokernel.π S.arrow)
      by_cases hQS_ss : Z.IsSemistable QS
      · exact ⟨QS, 𝟙 _, IsMDQ.id_of_semistable Z hQS_ss⟩
      · obtain ⟨A', hA'_ne, hA'_ss, hA'_phase⟩ :=
          Z.exists_semistable_subobject_gt_phase_of_not_semistable (E := QS) hQS_nz hQS_ss
        have hA'_top : A' ≠ ⊤ := by
          intro hA'_eq
          have hphase_eq : Z.phase (A' : A) = Z.phase QS := by
            rw [hA'_eq]
            exact Z.phase_eq_of_iso (asIso (⊤ : Subobject QS).arrow)
          grind
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
        have hQT_nz : ¬IsZero (cokernel T.arrow) := by
          intro hZ
          exact (cokernel_nonzero_of_ne_top hA'_top) (hZ.of_iso eT.symm)
        obtain ⟨B, qT, hqT⟩ := ih T hST_lt hQT_nz
        let qA : cokernel A'.arrow ⟶ B := eT.inv ≫ qT
        have hqA : IsMDQ Z qA := IsMDQ.precomposeIso Z hqT eT.symm
        letI : IsArtinianObject (cokernel A'.arrow) := isArtinianObject_of_epi (cokernel.π A'.arrow)
        letI : IsNoetherianObject (cokernel A'.arrow) :=
          isNoetherianObject_of_epi (cokernel.π A'.arrow)
        exact ⟨B, cokernel.π A'.arrow ≫ qA,
          IsMDQ.comp_of_destabilizing_semistable_subobject Z hA'_ss hA'_phase hA'_top hqA⟩

/-- For an epimorphism `q`, the quotient by `kernelSubobject q` is canonically the target. -/
noncomputable def cokernelKernelSubobjectIsoTarget {E B : A} (q : E ⟶ B) [Epi q] :
    cokernel (kernelSubobject q).arrow ≅ B := by
  have himg : imageSubobject q = ⊤ := by
    haveI : Epi (imageSubobject q).arrow :=
      epi_of_epi_fac (imageSubobject_arrow_comp q)
    haveI : IsIso (imageSubobject q).arrow := isIso_of_mono_of_epi _
    exact Subobject.eq_top_of_isIso_arrow _
  haveI : IsIso (imageSubobject q).arrow := by
    rw [himg]
    infer_instance
  exact
    (cokernelIsoOfEq (kernelSubobject_arrow q)).symm ≪≫
      cokernelEpiComp (kernelSubobjectIso q).hom (kernel.ι q) ≪≫
      Abelian.coimageIsoImage' q ≪≫
      (imageSubobjectIso q).symm ≪≫
      asIso (imageSubobject q).arrow

/-- The kernel of a nonzero epi quotient is a proper subobject. -/
private lemma kernelSubobject_ne_top_of_epi_nonzero {E B : A} (q : E ⟶ B) [Epi q]
    (hB : ¬IsZero B) :
    kernelSubobject q ≠ ⊤ := by
  intro hK
  have hZ : IsZero (cokernel (kernelSubobject q).arrow) := by
    rw [hK]
    exact isZero_cokernel_of_epi ((⊤ : Subobject E).arrow)
  exact hB (hZ.of_iso (cokernelKernelSubobjectIsoTarget q).symm)

/-- If `E` is not semistable, the kernel of an mdq quotient of `E` is nonzero. -/
private lemma kernelSubobject_ne_bot_of_mdq_of_not_semistable
    (Z : StabilityFunction A) {E B : A} {q : E ⟶ B} (hq : IsMDQ Z q)
    (hns : ¬Z.IsSemistable E) :
    kernelSubobject q ≠ ⊥ := by
  intro hK
  have hKz : IsZero (kernelSubobject q : A) :=
    (StabilityFunction.subobject_isZero_iff_eq_bot _).2 hK
  have hker : IsZero (kernel q) := hKz.of_iso (kernelSubobjectIso q).symm
  have hιzero : kernel.ι q = 0 := zero_of_source_iso_zero _ hker.isoZero
  haveI : Mono q := Preadditive.mono_of_kernel_zero hιzero
  haveI : Epi q := hq.epi
  haveI : IsIso q := isIso_of_mono_of_epi q
  exact hns (Z.isSemistable_of_iso (asIso q).symm hq.semistable)

/-- Bridgeland's Proposition 2.4e kernel-step inequality: the mdq of the kernel of an mdq
has strictly larger phase. -/
theorem IsMDQ.lt_phase_of_kernel_mdq
    (Z : StabilityFunction A) {E B B' : A} [IsArtinianObject E] [IsNoetherianObject E]
    {q : E ⟶ B} (hq : IsMDQ Z q)
    {qK : (kernelSubobject q : A) ⟶ B'} (hqK : IsMDQ Z qK) :
    Z.phase B < Z.phase B' := by
  haveI : Epi q := hq.epi
  haveI : Epi qK := hqK.epi
  let K : Subobject E := kernelSubobject q
  let K' : Subobject (K : A) := kernelSubobject qK
  let T : Subobject E := (Subobject.map K.arrow).obj K'
  let Q : A := cokernel T.arrow
  let p : E ⟶ Q := cokernel.π T.arrow
  have hKq : K.arrow ≫ q = 0 := by
    change (kernelSubobject q).arrow ≫ q = 0
    exact kernelSubobject_arrow_comp (f := q)
  have hT_mk : T = Subobject.mk (K'.arrow ≫ K.arrow) := by
    calc
      (Subobject.map K.arrow).obj K' = (Subobject.map K.arrow).obj (Subobject.mk K'.arrow) := by
        rw [Subobject.mk_arrow]
      _ = Subobject.mk (K'.arrow ≫ K.arrow) :=
        Subobject.map_mk K'.arrow K.arrow
  have hT_le_K : T ≤ K := by
    change (Subobject.map K.arrow).obj K' ≤ K
    simpa [K, Subobject.map_top] using
      (Subobject.map K.arrow).monotone le_top
  have hTq : T.arrow ≫ q = 0 := by
    rw [hT_mk]
    let e := Subobject.underlyingIso (K'.arrow ≫ K.arrow)
    have he : e.inv ≫ (Subobject.mk (K'.arrow ≫ K.arrow)).arrow = K'.arrow ≫ K.arrow :=
      Subobject.underlyingIso_arrow (K'.arrow ≫ K.arrow)
    have hpre : e.inv ≫ ((Subobject.mk (K'.arrow ≫ K.arrow)).arrow ≫ q) = 0 := by
      calc
        e.inv ≫ (Subobject.mk (K'.arrow ≫ K.arrow)).arrow ≫ q
            = (K'.arrow ≫ K.arrow) ≫ q := by
                simpa [Category.assoc] using congrArg (fun f => f ≫ q) he
        _ = 0 := by rw [Category.assoc, hKq]; simp
    calc
      (Subobject.mk (K'.arrow ≫ K.arrow)).arrow ≫ q
          = e.hom ≫ (e.inv ≫ ((Subobject.mk (K'.arrow ≫ K.arrow)).arrow ≫ q)) := by
              simp
      _ = 0 := by rw [hpre]; simp
  let πQ : Q ⟶ B := cokernel.desc T.arrow q hTq
  have hp_fac : p ≫ πQ = q := cokernel.π_desc T.arrow q hTq
  have hK'_ne_top : K' ≠ ⊤ := kernelSubobject_ne_top_of_epi_nonzero qK hqK.nonzero
  have hT_ne_K : T ≠ K := by
    intro hTK
    apply hK'_ne_top
    apply (Subobject.map_obj_injective K.arrow)
    simpa [T, K, Subobject.map_top] using hTK
  have hKp_ne_zero : K.arrow ≫ p ≠ 0 := by
    intro hzero
    have hKT : K ≤ T := Subobject.le_of_comm (Abelian.monoLift T.arrow K.arrow hzero)
      (Abelian.monoLift_comp T.arrow K.arrow hzero)
    exact hT_ne_K (le_antisymm hT_le_K hKT)
  have hK_ne_top : K ≠ ⊤ := kernelSubobject_ne_top_of_epi_nonzero q hq.nonzero
  have hT_ne_top : T ≠ ⊤ := by
    intro hT_top
    exact hK_ne_top (le_antisymm le_top (hT_top.symm ▸ hT_le_K))
  letI : IsArtinianObject Q := isArtinianObject_of_epi p
  letI : IsNoetherianObject Q := isNoetherianObject_of_epi p
  have hQ_nz : ¬IsZero Q := cokernel_nonzero_of_ne_top hT_ne_top
  have hQ_ge : Z.phase B ≤ Z.phase Q := IsMDQ.phase_le_of_quotient Z hq p hQ_nz
  have hQ_ne : Z.phase Q ≠ Z.phase B := by
    intro hEq
    obtain ⟨t, ht⟩ := IsMDQ.factor_of_phase_eq_of_quotient Z hq p hQ_nz hEq
    apply hKp_ne_zero
    calc
      K.arrow ≫ p = K.arrow ≫ (q ≫ t) := by rw [ht]
      _ = (K.arrow ≫ q) ≫ t := by rw [Category.assoc]
      _ = 0 := by rw [hKq, zero_comp]
  have hQ_gt : Z.phase B < Z.phase Q := lt_of_le_of_ne hQ_ge hQ_ne.symm
  let eT : (T : A) ≅ (K' : A) := Subobject.isoOfEqMk T (K'.arrow ≫ K.arrow) hT_mk
  have hT_eq : Z.Zobj (T : A) = Z.Zobj (K' : A) := Z.Zobj_eq_of_iso eT
  have hZ_T : Z.Zobj E = Z.Zobj (T : A) + Z.Zobj Q :=
    Z.additive _ (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel T.arrow)
      inferInstance inferInstance)
  have hZ_K0 : Z.Zobj E = Z.Zobj (K : A) + Z.Zobj (cokernel K.arrow) :=
    Z.additive _ (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel K.arrow)
      inferInstance inferInstance)
  have hZ_K : Z.Zobj E = Z.Zobj (K : A) + Z.Zobj B := by
    calc
      Z.Zobj E = Z.Zobj (K : A) + Z.Zobj (cokernel K.arrow) := hZ_K0
      _ = Z.Zobj (K : A) + Z.Zobj B := by
          rw [Z.Zobj_eq_of_iso (cokernelKernelSubobjectIsoTarget q)]
  have hZ_K'0 : Z.Zobj (K : A) = Z.Zobj (K' : A) + Z.Zobj (cokernel K'.arrow) :=
    Z.additive _ (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel K'.arrow)
      inferInstance inferInstance)
  have hZ_K' : Z.Zobj (K : A) = Z.Zobj (K' : A) + Z.Zobj B' := by
    calc
      Z.Zobj (K : A) = Z.Zobj (K' : A) + Z.Zobj (cokernel K'.arrow) := hZ_K'0
      _ = Z.Zobj (K' : A) + Z.Zobj B' := by
          rw [Z.Zobj_eq_of_iso (cokernelKernelSubobjectIsoTarget qK)]
  have hZ_Q : Z.Zobj Q = Z.Zobj B' + Z.Zobj B := by
    rw [hT_eq] at hZ_T
    linear_combination -hZ_T + hZ_K + hZ_K'
  by_contra hle
  push_neg at hle
  have hQ_le : Z.phase Q ≤ Z.phase B := by
    unfold StabilityFunction.phase
    rw [hZ_Q]
    have harg := arg_add_le_max (Z.upper B' hqK.nonzero) (Z.upper B hq.nonzero)
    calc
      (1 / Real.pi) * arg (Z.Zobj B' + Z.Zobj B)
          ≤ (1 / Real.pi) * max (arg (Z.Zobj B')) (arg (Z.Zobj B)) :=
            mul_le_mul_of_nonneg_left harg (div_nonneg one_pos.le Real.pi_pos.le)
      _ = max ((1 / Real.pi) * arg (Z.Zobj B')) ((1 / Real.pi) * arg (Z.Zobj B)) := by
            rw [mul_max_of_nonneg _ _ (div_nonneg one_pos.le Real.pi_pos.le)]
      _ = max (Z.phase B') (Z.phase B) := rfl
      _ = Z.phase B := max_eq_right hle
  exact (not_le_of_gt hQ_gt) hQ_le

section

omit [Abelian A]

private theorem Subobject.map_eq_mk {E : A} (K : Subobject E) (S : Subobject (K : A)) :
    (Subobject.map K.arrow).obj S = Subobject.mk (S.arrow ≫ K.arrow) := by
  calc
    (Subobject.map K.arrow).obj S = (Subobject.map K.arrow).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ K.arrow) :=
      Subobject.map_mk S.arrow K.arrow

private noncomputable def Subobject.mapSubIso {E : A} (K : Subobject E) (S : Subobject (K : A)) :
    ((Subobject.map K.arrow).obj S : A) ≅ (S : A) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ K.arrow) (Subobject.map_eq_mk K S)

private theorem Subobject.ofLE_map_comp_mapSubIso_hom {E : A} (K : Subobject E)
    {S T : Subobject (K : A)} (h : S ≤ T) :
    Subobject.ofLE ((Subobject.map K.arrow).obj S) ((Subobject.map K.arrow).obj T)
        ((Subobject.map K.arrow).monotone h) ≫ (Subobject.mapSubIso K T).hom =
      (Subobject.mapSubIso K S).hom ≫ Subobject.ofLE S T h := by
  apply Subobject.eq_of_comp_arrow_eq
  apply (cancel_mono K.arrow).1
  simp [Subobject.mapSubIso, Category.assoc]

end

private noncomputable def Subobject.cokernelMapIso {E : A} (K : Subobject E)
    {S T : Subobject (K : A)} (h : S ≤ T) :
    cokernel (Subobject.ofLE ((Subobject.map K.arrow).obj S) ((Subobject.map K.arrow).obj T)
      ((Subobject.map K.arrow).monotone h)) ≅
      cokernel (Subobject.ofLE S T h) :=
  cokernel.mapIso _ _ (Subobject.mapSubIso K S) (Subobject.mapSubIso K T)
    (by simpa [Category.assoc] using (Subobject.ofLE_map_comp_mapSubIso_hom K h))

private theorem phase_cokernel_map_eq (Z : StabilityFunction A) {E : A} (K : Subobject E)
    {S T : Subobject (K : A)} (h : S ≤ T) :
    Z.phase (cokernel (Subobject.ofLE ((Subobject.map K.arrow).obj S)
      ((Subobject.map K.arrow).obj T)
        ((Subobject.map K.arrow).monotone h))) =
      Z.phase (cokernel (Subobject.ofLE S T h)) :=
  Z.phase_eq_of_iso (Subobject.cokernelMapIso K h)

private theorem isSemistable_cokernel_map_of_iff (Z : StabilityFunction A) {E : A} (K : Subobject E)
    {S T : Subobject (K : A)} (h : S ≤ T) :
    Z.IsSemistable (cokernel (Subobject.ofLE ((Subobject.map K.arrow).obj S)
      ((Subobject.map K.arrow).obj T) ((Subobject.map K.arrow).monotone h))) ↔
      Z.IsSemistable (cokernel (Subobject.ofLE S T h)) := by
  constructor <;> intro hs
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapIso K h) hs
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapIso K h).symm hs

private noncomputable def Subobject.cokernelOfLEMapKernelIsoTarget
    {E B : A} (S : Subobject E) (q : (S : A) ⟶ B) [Epi q] :
    let T : Subobject E := (Subobject.map S.arrow).obj (kernelSubobject q)
    cokernel (Subobject.ofLE T S
      (by
        change (Subobject.map S.arrow).obj (kernelSubobject q) ≤ S
        simpa [Subobject.map_top] using
          (Subobject.map S.arrow).monotone le_top)) ≅ B := by
  let T : Subobject E := (Subobject.map S.arrow).obj (kernelSubobject q)
  let hT : T ≤ S := by
    change (Subobject.map S.arrow).obj (kernelSubobject q) ≤ S
    simpa [Subobject.map_top] using
      (Subobject.map S.arrow).monotone le_top
  let eT : (T : A) ≅ (kernelSubobject q : A) := Subobject.mapSubIso S (kernelSubobject q)
  let eQ : cokernel (Subobject.ofLE T S hT) ≅ cokernel (kernelSubobject q).arrow :=
    cokernel.mapIso _ _ eT (Iso.refl _)
      (by
        apply Subobject.eq_of_comp_arrow_eq
        simp [eT, T, Category.assoc, Subobject.mapSubIso])
  exact eQ ≪≫ cokernelKernelSubobjectIsoTarget q

section

omit [Abelian A]

private theorem Subobject.map_eq_mk_mono {X Y : A} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    (Subobject.map f).obj S = Subobject.mk (S.arrow ≫ f) := by
  calc
    (Subobject.map f).obj S = (Subobject.map f).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ f) :=
      Subobject.map_mk S.arrow f

private noncomputable def Subobject.mapMonoIso {X Y : A} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    ((Subobject.map f).obj S : A) ≅ (S : A) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ f) (Subobject.map_eq_mk_mono f S)

private theorem Subobject.ofLE_map_comp_mapMonoIso_hom {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
        ((Subobject.map f).monotone h) ≫ (Subobject.mapMonoIso f T).hom =
      (Subobject.mapMonoIso f S).hom ≫ Subobject.ofLE S T h := by
  apply Subobject.eq_of_comp_arrow_eq
  apply (cancel_mono f).1
  simp [Subobject.mapMonoIso, Category.assoc]

end

private noncomputable def Subobject.cokernelMapMonoIso {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h)) ≅
      cokernel (Subobject.ofLE S T h) :=
  cokernel.mapIso _ _ (Subobject.mapMonoIso f S) (Subobject.mapMonoIso f T)
    (by simpa [Category.assoc] using (Subobject.ofLE_map_comp_mapMonoIso_hom f h))

theorem phase_cokernel_mapMono_eq (Z : StabilityFunction A) {X Y : A} (f : X ⟶ Y)
    [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.phase (cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h))) =
      Z.phase (cokernel (Subobject.ofLE S T h)) :=
  Z.phase_eq_of_iso (Subobject.cokernelMapMonoIso f h)

theorem isSemistable_cokernel_mapMono_iff (Z : StabilityFunction A) {X Y : A}
    (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.IsSemistable (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
      ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) ↔
      Z.IsSemistable (cokernel (Subobject.ofLE S T h)) := by
  constructor <;> intro hs
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso f h) hs
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso f h).symm hs

theorem append_hn_filtration_of_mono (Z : StabilityFunction A) {X Y B : A}
    (i : X ⟶ Y) [Mono i] (F : AbelianHNFiltration Z X) (eB : cokernel i ≅ B)
    (hB : Z.IsSemistable B)
    (hlast : Z.phase B < F.φ ⟨F.n - 1, by have := F.hn; lia⟩) :
    ∃ G : AbelianHNFiltration Z Y, G.φ ⟨G.n - 1, by have := G.hn; lia⟩ = Z.phase B := by
  let K : Subobject Y := Subobject.mk i
  let eK : cokernel K.arrow ≅ B := by
    let eKi : cokernel K.arrow ≅ cokernel i := by
      refine cokernel.mapIso (f := K.arrow) (f' := i) (Subobject.underlyingIso i) (Iso.refl _)
        ?_
      calc
        K.arrow ≫ (Iso.refl Y).hom = K.arrow := by simp
        _ = (Subobject.underlyingIso i).hom ≫ i := by
            change (Subobject.mk i).arrow = (Subobject.underlyingIso i).hom ≫ i
            exact (Subobject.underlyingIso_hom_comp_eq_mk i).symm
    exact eKi ≪≫ eB
  have hK_ne_top : K ≠ ⊤ := by
    intro hK
    have hmk : Subobject.mk i = ⊤ := by simpa [K] using hK
    haveI : IsIso i := (Subobject.isIso_iff_mk_eq_top i).2 hmk
    exact hB.1 ((isZero_cokernel_of_epi i).of_iso eB.symm)
  have hK_lt_top : K < ⊤ := lt_of_le_of_ne le_top hK_ne_top
  let newChain : Fin (F.n + 2) → Subobject Y := fun j =>
    if h : (j : ℕ) ≤ F.n then
      (Subobject.map i).obj (F.chain ⟨j, by lia⟩)
    else ⊤
  have hNewBot : newChain ⟨0, by lia⟩ = ⊥ := by
    change (Subobject.map i).obj (F.chain ⟨0, by lia⟩) = ⊥
    rw [F.chain_bot]
    exact Subobject.map_bot i
  have hNewK : newChain ⟨F.n, by lia⟩ = K := by
    simp [newChain, K, Subobject.map_top, F.chain_top]
  have hNewTop : newChain ⟨F.n + 1, by lia⟩ = ⊤ := by
    simp [newChain]
  have hNewMono : StrictMono newChain := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    change newChain ⟨j, by lia⟩ < newChain ⟨j + 1, by lia⟩
    by_cases hjn : j = F.n
    · subst hjn
      rw [hNewK, hNewTop]
      exact hK_lt_top
    · have hjle : j + 1 ≤ F.n := by lia
      simp [newChain, show (j : ℕ) ≤ F.n by lia, hjle]
      apply (Subobject.map i).monotone.strictMono_of_injective (Subobject.map_obj_injective i)
      exact F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
  let φ : Fin (F.n + 1) → ℝ := fun j =>
    if h : (j : ℕ) < F.n then F.φ ⟨j, h⟩ else Z.phase B
  exact ⟨{
    n := F.n + 1
    hn := Nat.succ_pos _
    chain := newChain
    chain_strictMono := hNewMono
    chain_bot := hNewBot
    chain_top := hNewTop
    φ := φ
    φ_anti := by
      intro a b hab
      dsimp [φ]
      by_cases hb : (b : ℕ) < F.n
      · have ha : (a : ℕ) < F.n := lt_trans (Fin.mk_lt_mk.mp hab) hb
        simp [ha, hb]
        exact F.φ_anti (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hab))
      · have ha : (a : ℕ) < F.n := by lia
        have hlast_le :
            F.φ ⟨F.n - 1, by have := F.hn; lia⟩ ≤ F.φ ⟨a, ha⟩ :=
          F.φ_anti.antitone (Fin.mk_le_mk.mpr (by lia))
        simp [ha, hb]
        linarith
    factor_phase := by
      intro j
      by_cases hj : (j : ℕ) < F.n
      · let j' : Fin F.n := ⟨j, hj⟩
        have hcast :
            newChain j.castSucc = (Subobject.map i).obj (F.chain j'.castSucc) := by
          have hj_le : (j : ℕ) ≤ F.n := by lia
          simp [newChain, j', hj_le]
        have hsucc :
            newChain j.succ = (Subobject.map i).obj (F.chain j'.succ) := by
          have hj1_le : (j : ℕ) + 1 ≤ F.n := by lia
          simp [newChain, j', hj1_le]
        have hphase :
            Z.phase (cokernel (Subobject.ofLE ((Subobject.map i).obj (F.chain j'.castSucc))
              ((Subobject.map i).obj (F.chain j'.succ))
              ((Subobject.map i).monotone
                (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))))) =
              F.φ j' :=
          (phase_cokernel_mapMono_eq Z i
            (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).trans (F.factor_phase j')
        have hφj : φ j = F.φ j' := by
          simp [φ, hj, j']
        exact ((phase_cokernel_ofLE_congr Z hcast hsucc).trans hphase).trans hφj.symm
      · have hj_eq : (j : ℕ) = F.n := by lia
        have hcast : j.castSucc = ⟨F.n, by lia⟩ := Fin.ext hj_eq
        have hsucc : j.succ = ⟨F.n + 1, by lia⟩ := Fin.ext (by simp [hj_eq])
        have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
        have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
        have hφj : φ j = Z.phase B := by
          simp [φ, hj]
        have htarget :
            Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) =
              Z.phase (cokernel K.arrow) :=
          Z.phase_eq_of_iso
            ((cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _).symm)
        have htarget' : Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) = Z.phase B :=
          htarget.trans (Z.phase_eq_of_iso eK)
        exact ((phase_cokernel_ofLE_congr Z hcast_obj hsucc_obj).trans htarget').trans hφj.symm
    factor_semistable := by
      intro j
      by_cases hj : (j : ℕ) < F.n
      · let j' : Fin F.n := ⟨j, hj⟩
        have hcast :
            newChain j.castSucc = (Subobject.map i).obj (F.chain j'.castSucc) := by
          have hj_le : (j : ℕ) ≤ F.n := by lia
          simp [newChain, j', hj_le]
        have hsucc :
            newChain j.succ = (Subobject.map i).obj (F.chain j'.succ) := by
          have hj1_le : (j : ℕ) + 1 ≤ F.n := by lia
          simp [newChain, j', hj1_le]
        have hsemistable :
            Z.IsSemistable
              (cokernel (Subobject.ofLE ((Subobject.map i).obj (F.chain j'.castSucc))
                ((Subobject.map i).obj (F.chain j'.succ))
                ((Subobject.map i).monotone
                  (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))))) :=
          (isSemistable_cokernel_mapMono_iff Z i
            (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).2 (F.factor_semistable j')
        exact isSemistable_cokernel_ofLE_congr Z hcast hsucc hsemistable
      · have hj_eq : (j : ℕ) = F.n := by lia
        have hcast : j.castSucc = ⟨F.n, by lia⟩ := Fin.ext hj_eq
        have hsucc : j.succ = ⟨F.n + 1, by lia⟩ := Fin.ext (by simp [hj_eq])
        have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
        have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
        let eTop : B ≅ cokernel (Subobject.ofLE K ⊤ le_top) :=
          eK.symm ≪≫ (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _)
        exact isSemistable_cokernel_ofLE_congr Z hcast_obj hsucc_obj <|
          Z.isSemistable_of_iso eTop hB
  }, by simp [φ]⟩

/-- **Proposition 2.4** in the finite-length form used by Bridgeland: if every object is
Artinian and Noetherian, then the stability function has the HN property.

This is the public API needed by the deformation proof after replacing the old
`Finite (Subobject _)` surrogate with the paper-faithful finite-length hypothesis.
The actual recursive proof should follow the mdq-kernel construction immediately above.
During the local-finiteness refactor we keep the corrected statement in place and leave
the proof body as a focused TODO. -/
theorem exists_hn_with_last_phase_of_semistable (Z : StabilityFunction A) {E : A}
    (hss : Z.IsSemistable E) :
    ∃ F : AbelianHNFiltration Z E,
      F.φ ⟨F.n - 1, by have := F.hn; grind⟩ = Z.phase E := by
  refine ⟨{
    n := 1
    hn := Nat.one_pos
    chain := fun i ↦ if i = 0 then ⊥ else ⊤
    chain_strictMono := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ h
      simp only [Fin.lt_def] at h
      have hi0 : i = 0 := by grind
      have hj1 : j = 1 := by grind
      subst hi0; subst hj1
      simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ↓reduceIte,
        Fin.mk_one, one_ne_zero, gt_iff_lt]
      exact lt_of_le_of_ne bot_le
        (Ne.symm (StabilityFunction.subobject_top_ne_bot_of_not_isZero hss.1))
    chain_bot := by simp
    chain_top := by simp
    φ := fun _ ↦ Z.phase E
    φ_anti := fun a b h ↦ by exfalso; exact absurd h (by grind)
    factor_phase := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by grind
      subst hj0
      change Z.phase (cokernel (Subobject.ofLE ⊥ ⊤ _)) = Z.phase E
      rw [Z.phase_eq_of_iso (StabilityFunction.Subobject.cokernelBotIso ⊤ bot_le)]
      exact Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow)
    factor_semistable := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by grind
      subst hj0
      change Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ _))
      exact Z.isSemistable_of_iso
        ((asIso (⊤ : Subobject E).arrow).symm ≪≫
          (StabilityFunction.Subobject.cokernelBotIso ⊤ bot_le).symm) hss
  }, by
    simp⟩

theorem exists_hn_of_semistable (Z : StabilityFunction A) {E : A}
    (hss : Z.IsSemistable E) :
    Nonempty (AbelianHNFiltration Z E) :=
  ⟨(exists_hn_with_last_phase_of_semistable Z hss).choose⟩

/-- Transport an HN filtration across an isomorphism of the ambient object. -/
noncomputable def AbelianHNFiltration.ofIso {Z : StabilityFunction A} {E E' : A}
    (F : AbelianHNFiltration Z E) (e : E ≅ E') :
    AbelianHNFiltration Z E' where
  n := F.n
  hn := F.hn
  chain := fun i ↦ (Subobject.map e.hom).obj (F.chain i)
  chain_strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    apply (Subobject.map e.hom).monotone.strictMono_of_injective (Subobject.map_obj_injective e.hom)
    exact F.chain_strictMono j.castSucc_lt_succ
  chain_bot := by
    simpa [Subobject.map_bot] using congrArg ((Subobject.map e.hom).obj) F.chain_bot
  chain_top := by
    calc
      (Subobject.map e.hom).obj
        (F.chain ⟨F.n, F.n.lt_succ_iff.mpr le_rfl⟩) = Subobject.mk e.hom := by
        simpa [Subobject.map_top] using congrArg ((Subobject.map e.hom).obj) F.chain_top
      _ = ⊤ := Subobject.mk_eq_top_of_isIso e.hom
  φ := F.φ
  φ_anti := F.φ_anti
  factor_phase := by
    intro j
    exact (phase_cokernel_mapMono_eq Z e.hom
      (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))).trans (F.factor_phase j)
  factor_semistable := by
    intro j
    exact (isSemistable_cokernel_mapMono_iff Z e.hom
      (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))).2 (F.factor_semistable j)

private theorem exists_hn_with_mdq_of_artinian_noetherian_subobject
    (Z : StabilityFunction A) {E : A}
    [IsArtinianObject E] [IsNoetherianObject E] :
    ∀ (S : Subobject E), ¬IsZero (S : A) →
      ∃ (B : A) (q : (S : A) ⟶ B) (_hq : IsMDQ Z q)
        (F : AbelianHNFiltration Z (S : A)),
        F.φ ⟨F.n - 1, by have := F.hn; grind⟩ = Z.phase B := by
  intro S
  induction S using WellFoundedLT.induction with
  | ind S ih =>
      intro hS_nz
      letI : IsArtinianObject (S : A) := isArtinianObject_of_mono S.arrow
      letI : IsNoetherianObject (S : A) := isNoetherianObject_of_mono S.arrow
      by_cases hS_ss : Z.IsSemistable (S : A)
      · obtain ⟨F, hF⟩ := exists_hn_with_last_phase_of_semistable Z hS_ss
        exact ⟨(S : A), 𝟙 _, IsMDQ.id_of_semistable Z hS_ss, F, hF⟩
      · obtain ⟨B, q, hq⟩ := exists_mdq_of_artinian_noetherian Z (E := (S : A)) hS_nz
        haveI : Epi q := hq.epi
        let K : Subobject (S : A) := kernelSubobject q
        have hK_ne_bot : K ≠ ⊥ :=
          kernelSubobject_ne_bot_of_mdq_of_not_semistable Z hq hS_ss
        have hK_nz : ¬IsZero (K : A) := StabilityFunction.subobject_not_isZero_of_ne_bot hK_ne_bot
        have hK_ne_top : K ≠ ⊤ := kernelSubobject_ne_top_of_epi_nonzero q hq.nonzero
        let T : Subobject E := (Subobject.map S.arrow).obj K
        have hT_le : T ≤ S := by
          change (Subobject.map S.arrow).obj K ≤ S
          simpa [Subobject.map_top] using
            (Subobject.map S.arrow).monotone le_top
        have hT_ne : T ≠ S := by
          intro hTS
          apply hK_ne_top
          apply (Subobject.map_obj_injective S.arrow)
          simpa [T, Subobject.map_top] using hTS
        have hT_lt : T < S := lt_of_le_of_ne hT_le hT_ne
        have hT_nz : ¬IsZero (T : A) := by
          intro hT_z
          exact hK_nz (hT_z.of_iso (Subobject.mapSubIso S K).symm)
        obtain ⟨B', qT, hqT, FT, hFT⟩ := ih T hT_lt hT_nz
        have hqK : IsMDQ Z ((Subobject.mapSubIso S K).symm.hom ≫ qT) :=
          IsMDQ.precomposeIso Z hqT (Subobject.mapSubIso S K).symm
        have hlast : Z.phase B < FT.φ ⟨FT.n - 1, by have := FT.hn; grind⟩ := by
          rw [hFT]
          exact IsMDQ.lt_phase_of_kernel_mdq Z hq hqK
        have eB : cokernel (Subobject.ofLE T S hT_le) ≅ B := by
          simpa [T, hT_le] using (Subobject.cokernelOfLEMapKernelIsoTarget S q)
        obtain ⟨G, hG⟩ := append_hn_filtration_of_mono Z (Subobject.ofLE T S hT_le) FT eB
          hq.semistable hlast
        exact ⟨B, q, hq, G, hG⟩

theorem StabilityFunction.hasHN_of_artinian_noetherian (Z : StabilityFunction A)
    (hArt : ∀ E : A, IsArtinianObject E)
    (hNoeth : ∀ E : A, IsNoetherianObject E) :
    Z.HasHNProperty := by
  intro E hE
  letI : IsArtinianObject E := hArt E
  letI : IsNoetherianObject E := hNoeth E
  let S : Subobject E := Subobject.mk (𝟙 E)
  have hS_nz : ¬IsZero (S : A) := by
    intro hS_z
    exact hE (hS_z.of_iso (Subobject.underlyingIso (𝟙 E)).symm)
  obtain ⟨B, q, hq, F, hF⟩ :=
    exists_hn_with_mdq_of_artinian_noetherian_subobject Z (E := E) S hS_nz
  exact ⟨F.ofIso (Subobject.underlyingIso (𝟙 E))⟩


end CategoryTheory
