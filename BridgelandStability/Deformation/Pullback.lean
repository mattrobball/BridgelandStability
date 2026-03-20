/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStability.Deformation.BoundaryTriangle
import BridgelandStability.Deformation.IntervalSelection

/-!
# Deformation of Stability Conditions — Pullback

Pullback infrastructure, upper inclusion semistability, first strict SES
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-! ### Thin-interval pullback infrastructure -/

theorem interval_pullbackπ_strictEpi_of_strictEpi
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (p : X ⟶ Y) (hp : IsStrictEpi p)
    (B : Subobject Y) :
    IsStrictEpi (Subobject.pullbackπ p B) := by
  letI := s.intervalCat_quasiAbelian (C := C) (a := a) (b := b)
  let e := (Subobject.isPullback p B).isoPullback
  have hpb : IsStrictEpi (pullback.fst B.arrow p) :=
    QuasiAbelian.pullback_strictEpi B.arrow p hp
  have he : e.hom ≫ pullback.fst B.arrow p = Subobject.pullbackπ p B := by
    simpa [e] using (Subobject.isPullback p B).isoPullback_hom_fst
  have hcomp : IsStrictEpi (e.hom ≫ pullback.fst B.arrow p) :=
    Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := s) (a := a) (b := b) e.hom (pullback.fst B.arrow p)
      isStrictEpi_of_isIso hpb
  simpa [he] using hcomp

theorem interval_pullback_arrow_strictMono_of_strictMono
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (p : X ⟶ Y)
    (B : Subobject Y) (hB : IsStrictMono B.arrow) :
    IsStrictMono (((Subobject.pullback p).obj B).arrow) := by
  let pb := (Subobject.pullback p).obj B
  let sq := Subobject.isPullback p B
  let hKerB := hB.isLimitKernelFork
  letI : NormalMono pb.arrow :=
    { Z := cokernel B.arrow
      g := p ≫ cokernel.π B.arrow
      w := by
        calc
          pb.arrow ≫ (p ≫ cokernel.π B.arrow)
              = (pb.arrow ≫ p) ≫ cokernel.π B.arrow := by simp [Category.assoc]
          _ = (Subobject.pullbackπ p B ≫ B.arrow) ≫ cokernel.π B.arrow := by
              rw [sq.w]
          _ = Subobject.pullbackπ p B ≫ (B.arrow ≫ cokernel.π B.arrow) := by
              simp [Category.assoc]
          _ = 0 := by simp
      isLimit := KernelFork.IsLimit.ofι' pb.arrow
        (by
          calc
            pb.arrow ≫ (p ≫ cokernel.π B.arrow)
                = (pb.arrow ≫ p) ≫ cokernel.π B.arrow := by simp [Category.assoc]
            _ = (Subobject.pullbackπ p B ≫ B.arrow) ≫ cokernel.π B.arrow := by
                rw [sq.w]
            _ = Subobject.pullbackπ p B ≫ (B.arrow ≫ cokernel.π B.arrow) := by
                simp [Category.assoc]
            _ = 0 := by simp)
        (fun {W} g hg ↦ by
          let u : W ⟶ (B : s.IntervalCat C a b) :=
            hKerB.lift (KernelFork.ofι (g ≫ p) (by simpa [Category.assoc] using hg))
          have hu : u ≫ B.arrow = g ≫ p := by
            exact hKerB.fac _ Limits.WalkingParallelPair.zero
          exact ⟨sq.lift u g hu, by simpa [pb] using sq.lift_snd u g hu⟩) }
  exact isStrictMono_of_normalMono

lemma interval_le_pullback_cokernel
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X)
    (B : Subobject (cokernel M.arrow)) :
    M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  let sq := Subobject.isPullback q B
  refine Subobject.le_of_comm (sq.lift 0 M.arrow (by simpa [q] using cokernel.condition M.arrow)) ?_
  simpa [pbB] using sq.lift_snd 0 M.arrow (by simpa [q] using cokernel.condition M.arrow)

lemma interval_ofLE_pullbackπ_eq_zero
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X)
    (B : Subobject (cokernel M.arrow)) :
    Subobject.ofLE M _ (interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B) ≫
      Subobject.pullbackπ (cokernel.π M.arrow) B = 0 := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  let hle := interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B
  let sq := Subobject.isPullback q B
  apply (cancel_mono B.arrow).mp
  calc
    (Subobject.ofLE M pbB hle ≫ Subobject.pullbackπ q B) ≫ B.arrow
        = Subobject.ofLE M pbB hle ≫ (pbB.arrow ≫ q) := by
            rw [Category.assoc, sq.w]
    _ = (Subobject.ofLE M pbB hle ≫ pbB.arrow) ≫ q := by simp [Category.assoc]
    _ = M.arrow ≫ q := by rw [Subobject.ofLE_arrow]
    _ = 0 ≫ B.arrow := by
          rw [show M.arrow ≫ q = 0 by simpa [q] using cokernel.condition M.arrow]
          simp

theorem interval_strictShortExact_of_kernel_strictEpi
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (S : ShortComplex (s.IntervalCat C a b))
    (hKer : IsLimit (KernelFork.ofι S.f S.zero))
    (hg : IsStrictEpi S.g) :
    StrictShortExact S := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := t.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKer
  have hEpiL : Epi ((S.map FL).g) := by
    simpa [FL] using
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) S.g hg
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExactL : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKerL
  have hShortExactL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExactL (Fork.IsLimit.mono hKerL) hEpiL
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) hShortExactL
  exact Slicing.IntervalCat.strictShortExact_of_distTriang
    (C := C) (s := s) (a := a) (b := b) hT

theorem interval_strictShortExact_pullback_left
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {K E Q : s.IntervalCat C a b}
    {i : K ⟶ E} {q : E ⟶ Q}
    (hiq : i ≫ q = 0)
    (hKer : IsLimit (KernelFork.ofι i hiq))
    (hq : IsStrictEpi q)
    (B : Subobject Q) :
    let pb := (Subobject.pullback q).obj B
    let m : K ⟶ pb := by
      let hiB : B.Factors (i ≫ q) := by
        simpa [hiq] using (Subobject.factors_zero : B.Factors (0 : K ⟶ Q))
      exact pb.factorThru i (Limits.pullback_factors q B i hiB)
    StrictShortExact
      (ShortComplex.mk m (Subobject.pullbackπ q B) (by
        apply (cancel_mono B.arrow).mp
        calc
          (m ≫ Subobject.pullbackπ q B) ≫ B.arrow
              = m ≫ (Subobject.pullbackπ q B ≫ B.arrow) := by simp [Category.assoc]
          _ = m ≫ (((Subobject.pullback q).obj B).arrow ≫ q) := by
              rw [(Subobject.isPullback q B).w]
          _ = (m ≫ ((Subobject.pullback q).obj B).arrow) ≫ q := by simp [Category.assoc]
          _ = i ≫ q := by
              let hiB : B.Factors (i ≫ q) := by
                simpa [hiq] using (Subobject.factors_zero : B.Factors (0 : K ⟶ Q))
              change
                (((Subobject.pullback q).obj B).factorThru i (Limits.pullback_factors q B i hiB) ≫
                    ((Subobject.pullback q).obj B).arrow) ≫ q =
                  i ≫ q
              simpa [Category.assoc] using
                congrArg (fun t ↦ t ≫ q)
                  (Subobject.factorThru_arrow ((Subobject.pullback q).obj B) i
                    (Limits.pullback_factors q B i hiB))
          _ = 0 := hiq
          _ = 0 ≫ B.arrow := by simp)) := by
  let pb := (Subobject.pullback q).obj B
  let hiB : B.Factors (i ≫ q) := by
    simpa [hiq] using (Subobject.factors_zero : B.Factors (0 : K ⟶ Q))
  let hpb : pb.Factors i := Limits.pullback_factors q B i hiB
  let m : K ⟶ pb := by
    exact pb.factorThru i hpb
  have hm : m ≫ pb.arrow = i := by
    change pb.factorThru i hpb ≫ pb.arrow = i
    exact Subobject.factorThru_arrow pb i hpb
  let hcomp : m ≫ Subobject.pullbackπ q B = 0 := by
    apply (cancel_mono B.arrow).mp
    calc
      (m ≫ Subobject.pullbackπ q B) ≫ B.arrow
          = m ≫ (Subobject.pullbackπ q B ≫ B.arrow) := by simp [Category.assoc]
      _ = m ≫ (pb.arrow ≫ q) := by rw [(Subobject.isPullback q B).w]
      _ = (m ≫ pb.arrow) ≫ q := by simp [Category.assoc]
      _ = i ≫ q := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ q) hm
      _ = 0 := hiq
      _ = 0 ≫ B.arrow := by simp
  haveI : Mono i := Fork.IsLimit.mono hKer
  haveI : Mono m := mono_of_mono_fac hm
  have hKer' : IsLimit (KernelFork.ofι m hcomp) := by
    refine KernelFork.IsLimit.ofι' m hcomp (fun {W} g hg ↦ ?_)
    let u : W ⟶ K :=
      hKer.lift (KernelFork.ofι (g ≫ pb.arrow) (by
        calc
          (g ≫ pb.arrow) ≫ q = g ≫ (pb.arrow ≫ q) := by simp [Category.assoc]
          _ = g ≫ (Subobject.pullbackπ q B ≫ B.arrow) := by rw [(Subobject.isPullback q B).w]
          _ = (g ≫ Subobject.pullbackπ q B) ≫ B.arrow := by simp [Category.assoc]
          _ = 0 := by simp [hg]))
    have hu : u ≫ i = g ≫ pb.arrow := by
      exact hKer.fac _ Limits.WalkingParallelPair.zero
    refine ⟨u, ?_⟩
    apply (cancel_mono pb.arrow).1
    calc
      (u ≫ m) ≫ pb.arrow = u ≫ i := by
        simp [Category.assoc, hm]
      _ = g ≫ pb.arrow := hu
  have hπ : IsStrictEpi (Subobject.pullbackπ q B) :=
    interval_pullbackπ_strictEpi_of_strictEpi
      (C := C) (s := s) (a := a) (b := b) q hq B
  exact interval_strictShortExact_of_kernel_strictEpi
    (C := C) (s := s) (a := a) (b := b)
    (ShortComplex.mk m (Subobject.pullbackπ q B) hcomp) hKer' hπ

theorem interval_strictShortExact_pullback_right
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {E Q Y : s.IntervalCat C a b}
    (q : E ⟶ Q) (hq : IsStrictEpi q)
    (B : Subobject Q)
    (g : Q ⟶ Y) (hBg : B.arrow ≫ g = 0)
    (hBKer : IsLimit (KernelFork.ofι B.arrow hBg))
    (hg : IsStrictEpi g) :
    let pb := (Subobject.pullback q).obj B
    let p : E ⟶ Y := q ≫ g
    StrictShortExact
      (ShortComplex.mk pb.arrow p (by
        calc
          pb.arrow ≫ p = pb.arrow ≫ q ≫ g := by simp [p, Category.assoc]
          _ = (pb.arrow ≫ q) ≫ g := by simp [Category.assoc]
          _ = (Subobject.pullbackπ q B ≫ B.arrow) ≫ g := by
              rw [(Subobject.isPullback q B).w]
          _ = Subobject.pullbackπ q B ≫ B.arrow ≫ g := by simp [Category.assoc]
          _ = 0 := by simp [hBg, Category.assoc])) := by
  let pb := (Subobject.pullback q).obj B
  let p : E ⟶ Y := q ≫ g
  let hcomp : pb.arrow ≫ p = 0 := by
    calc
      pb.arrow ≫ p = pb.arrow ≫ q ≫ g := by simp [p, Category.assoc]
      _ = (pb.arrow ≫ q) ≫ g := by simp [Category.assoc]
      _ = (Subobject.pullbackπ q B ≫ B.arrow) ≫ g := by
          rw [(Subobject.isPullback q B).w]
      _ = Subobject.pullbackπ q B ≫ B.arrow ≫ g := by simp [Category.assoc]
      _ = 0 := by simp [hBg, Category.assoc]
  have hKer : IsLimit (KernelFork.ofι pb.arrow hcomp) := by
    refine KernelFork.IsLimit.ofι' pb.arrow hcomp (fun {W} k hk ↦ ?_)
    let u : W ⟶ (B : s.IntervalCat C a b) :=
      hBKer.lift (KernelFork.ofι (k ≫ q) (by
        simpa [p, Category.assoc] using hk))
    have hu : u ≫ B.arrow = k ≫ q := by
      exact hBKer.fac _ Limits.WalkingParallelPair.zero
    refine ⟨(Subobject.isPullback q B).lift u k hu, ?_⟩
    simpa [pb] using (Subobject.isPullback q B).lift_snd u k hu
  have hp : IsStrictEpi p :=
    Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := s) (a := a) (b := b) q g hq hg
  exact interval_strictShortExact_of_kernel_strictEpi
    (C := C) (s := s) (a := a) (b := b)
    (ShortComplex.mk pb.arrow p hcomp) hKer hp

theorem interval_strictShortExact_ofLE_pullbackπ_cokernel
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow)
    (B : Subobject (cokernel M.arrow)) :
    let pbB := (Subobject.pullback (cokernel.π M.arrow)).obj B
    let hle := interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B
    StrictShortExact
      (ShortComplex.mk
        (Subobject.ofLE M pbB hle)
        (Subobject.pullbackπ (cokernel.π M.arrow) B)
        (interval_ofLE_pullbackπ_eq_zero (C := C) (s := s) (a := a) (b := b) M B)) := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  let hle := interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B
  let hcomp := interval_ofLE_pullbackπ_eq_zero (C := C) (s := s) (a := a) (b := b) M B
  let i := Subobject.ofLE M pbB hle
  let π := Subobject.pullbackπ q B
  have hq : IsStrictEpi q := isStrictEpi_cokernel M.arrow
  have hπ : IsStrictEpi π :=
    interval_pullbackπ_strictEpi_of_strictEpi
      (C := C) (s := s) (a := a) (b := b) q hq B
  have hkey : ∀ {W : s.IntervalCat C a b} (g : W ⟶ pbB), g ≫ π = 0 →
      (g ≫ pbB.arrow) ≫ q = 0 := by
    intro W g hg
    calc
      (g ≫ pbB.arrow) ≫ q = g ≫ (pbB.arrow ≫ q) := by simp [Category.assoc]
      _ = g ≫ (π ≫ B.arrow) := by rw [(Subobject.isPullback q B).w]
      _ = (g ≫ π) ≫ B.arrow := by simp [Category.assoc]
      _ = 0 := by simp [hg]
  have hKer : IsLimit (KernelFork.ofι i hcomp) := by
    refine KernelFork.IsLimit.ofι' i hcomp (fun {W} g hg ↦ ?_)
    let k : W ⟶ (M : s.IntervalCat C a b) :=
      hM.isLimitKernelFork.lift (KernelFork.ofι (g ≫ pbB.arrow) (hkey g hg))
    have hk : k ≫ M.arrow = g ≫ pbB.arrow := by
      exact hM.isLimitKernelFork.fac _ Limits.WalkingParallelPair.zero
    refine ⟨k, ?_⟩
    apply (cancel_mono pbB.arrow).1
    simpa [i, Category.assoc, Subobject.ofLE_arrow] using hk
  let S : ShortComplex (s.IntervalCat C a b) := ShortComplex.mk i π hcomp
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := t.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKer
  have hEpiL : Epi ((S.map FL).g) := by
    simpa [S, FL] using
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) π hπ
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExactL : (S.map FL).Exact := ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKerL
  have hShortExactL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExactL (Fork.IsLimit.mono hKerL) hEpiL
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) hShortExactL
  exact Slicing.IntervalCat.strictShortExact_of_distTriang
    (C := C) (s := s) (a := a) (b := b) hT

noncomputable def interval_fIsKernel_of_strictShortExact
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {S : ShortComplex (s.IntervalCat C a b)} (hS : StrictShortExact S) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have := hS.shortExact.mono_f
  have := hS.shortExact.epi_g
  let h := hS.shortExact.exact.condition.choose
  let eHi : kernel S.g ≅ h.left.K :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.left.hi
  have heHi : eHi.inv ≫ kernel.ι S.g = h.left.i := by
    simpa [KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) h.left.hi
        Limits.WalkingParallelPair.zero
  haveI : Epi h.left.f' := hS.shortExact.exact.epi_f' h.left
  have hFRMono : Mono (FR.map h.left.f') := by
    haveI : Mono (FR.map S.f) :=
      Slicing.IntervalCat.mono_toRightHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) S.f
        ⟨inferInstance, hS.strict_f⟩
    have hFRComp : FR.map h.left.f' ≫ FR.map h.left.i = FR.map S.f := by
      calc
        FR.map h.left.f' ≫ FR.map h.left.i = FR.map (h.left.f' ≫ h.left.i) := by
          rw [← FR.map_comp]
        _ = FR.map S.f := by
          simp [h.left.f'_i]
    haveI : Mono (FR.map h.left.f' ≫ FR.map h.left.i) := by
      rw [hFRComp]
      infer_instance
    exact mono_of_mono (FR.map h.left.f') (FR.map h.left.i)
  have hf'Strict : IsStrictMono h.left.f' :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) h.left.f'
  haveI : IsIso h.left.f' := hf'Strict.isIso
  let eK : S.X₁ ≅ kernel S.g := asIso h.left.f' ≪≫ eHi.symm
  refine kernel.isoKernel S.g S.f eK ?_
  calc
    eK.hom ≫ kernel.ι S.g = h.left.f' ≫ h.left.i := by
        simp [eK, heHi, Category.assoc]
    _ = S.f := h.left.f'_i

noncomputable def interval_cokernel_pullbackTopIso
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X)
    {B : Subobject (cokernel M.arrow)} (hB : IsStrictMono B.arrow) :
    cokernel ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow ≅ cokernel B.arrow := by
  let q : X ⟶ cokernel M.arrow := cokernel.π M.arrow
  let pb : Subobject X := (Subobject.pullback q).obj B
  let p : X ⟶ cokernel B.arrow := q ≫ cokernel.π B.arrow
  let hcomp : pb.arrow ≫ p = 0 := by
    calc
      pb.arrow ≫ p = pb.arrow ≫ q ≫ cokernel.π B.arrow := by simp [p]
      _ = (pb.arrow ≫ q) ≫ cokernel.π B.arrow := by simp [Category.assoc]
      _ = (Subobject.pullbackπ q B ≫ B.arrow) ≫ cokernel.π B.arrow := by
          rw [(Subobject.isPullback q B).w]
      _ = Subobject.pullbackπ q B ≫ (B.arrow ≫ cokernel.π B.arrow) := by
          simp [Category.assoc]
      _ = 0 := by simp
  let S : ShortComplex (s.IntervalCat C a b) := ShortComplex.mk pb.arrow p hcomp
  have hS : StrictShortExact S := by
    simpa [S, pb, p, hcomp] using
      interval_strictShortExact_pullback_right
        (C := C) (s := s) (a := a) (b := b)
        q (isStrictEpi_cokernel M.arrow) B (cokernel.π B.arrow) (cokernel.condition B.arrow)
        hB.isLimitKernelFork (isStrictEpi_cokernel B.arrow)
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
    interval_fIsKernel_of_strictShortExact
      (C := C) (s := s) (a := a) (b := b) hS
  have hp : IsStrictEpi p := ⟨hS.shortExact.epi_g, hS.strict_g⟩
  let eK' : kernel p ≅ (pb : s.IntervalCat C a b) :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel p) hKer
  let eK : (pb : s.IntervalCat C a b) ≅ kernel p := eK'.symm
  have heK : eK.hom ≫ kernel.ι p = pb.arrow := by
    simpa [S, p, KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel p) hKer
        Limits.WalkingParallelPair.zero
  let eC : cokernel pb.arrow ≅ cokernel (kernel.ι p) :=
    cokernel.mapIso pb.arrow (kernel.ι p) eK (Iso.refl _)
      (by simpa [heK])
  let eQ : cokernel (kernel.ι p) ≅ cokernel B.arrow :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι p))
      hp.isColimitCokernelCofork
  exact eC ≪≫ eQ

theorem semistable_of_upper_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a b₁ b₂ ψ ε₀ : ℝ} (hab₁ : a < b₁) (hab₂ : a < b₂) (hb : b₁ ≤ b₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b₁ - ε₀)
    (hthin₂ : b₂ - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  have hEI₂ : σ.slicing.intervalProp C a b₂ E :=
    σ.slicing.intervalProp_mono C (show a ≤ a by linarith) hb hSS.1
  have henv_hi₂ : ψ ≤ b₂ - ε₀ := by
    linarith
  have hb₁_le : b₁ ≤ a + 1 := by
    linarith
  have hthin₂' : b₂ - a < 1 := by
    linarith
  have hsmall₂ :
      stabSeminorm C σ (W - σ.Z) <
        ENNReal.ofReal (Real.cos (Real.pi * (b₂ - a) / 2)) :=
    stabSeminorm_lt_cos_of_hsin_hthin
      (C := C) (σ := σ) (W := W) hab₂ hε₀ hε₀2 hthin₂ hsin
  let hpert₂ := hperturb_of_stabSeminorm C σ W hW hthin₂' hε₀ hε₀2 hsin
  have hW_ne₂ :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₂ → W (K₀.of C F) ≠ 0 := by
    intro F φ hP hFne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  have hpert₂_lo :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₂ →
        a - ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert₂ F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hpert₂_hi :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₂ →
        b₂ + ε₀ - 1 < wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) < b₂ + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert₂ F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hWindow₂ :
      ∀ {G : C}, σ.slicing.intervalProp C a b₂ G → ¬IsZero G →
        a - ε₀ < wPhaseOf (W (K₀.of C G)) ((a + b₂) / 2) ∧
          wPhaseOf (W (K₀.of C G)) ((a + b₂) / 2) < b₂ + ε₀ := by
    intro G hG hGne
    exact ⟨wPhaseOf_gt_of_intervalProp C σ hGne W (by linarith) hG hW_ne₂ hpert₂_lo,
      wPhaseOf_lt_of_intervalProp C σ hGne W (by linarith) hG hW_ne₂ hpert₂_hi⟩
  have hW_ne_big :
      ∀ {G : C}, σ.slicing.intervalProp C a b₂ G → ¬IsZero G → W (K₀.of C G) ≠ 0 := by
    intro G hG hGne
    exact σ.W_ne_zero_of_intervalProp C W hthin₂' hsmall₂ hGne hG
  refine semistable_of_target_envelope_triangleTest
    (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hSS hab₂ hEI₂ hε₀ henv_lo henv_hi₂
    hthin₂ ?_
  intro K Q f₁ f₂ f₃ hT hKI hQI hKne
  letI : Fact (a < b₂) := ⟨hab₂⟩
  letI : Fact (b₂ - a ≤ 1) := ⟨by linarith⟩
  let KI₂ : σ.slicing.IntervalCat C a b₂ := ⟨K, hKI⟩
  let EI₂ : σ.slicing.IntervalCat C a b₂ := ⟨E, hEI₂⟩
  let QI₂ : σ.slicing.IntervalCat C a b₂ := ⟨Q, hQI⟩
  let iK : KI₂ ⟶ EI₂ := ObjectProperty.homMk f₁
  let qE : EI₂ ⟶ QI₂ := ObjectProperty.homMk f₂
  let hcomp₀ : iK ≫ qE = 0 := by
    ext
    simpa [iK, qE] using comp_distTriang_mor_zero₁₂ _ hT
  let S₀ : ShortComplex (σ.slicing.IntervalCat C a b₂) := ShortComplex.mk iK qE hcomp₀
  have hT₀ : Triangle.mk S₀.f.hom S₀.g.hom f₃ ∈ distTriang C := by
    simpa [S₀, iK, qE] using hT
  have hS₀ : StrictShortExact S₀ :=
    Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b₂) hT₀
  have hS₀Ker : IsLimit (KernelFork.ofι iK hcomp₀) := by
    simpa [S₀] using
      interval_fIsKernel_of_strictShortExact
        (C := C) (s := σ.slicing) (a := a) (b := b₂) hS₀
  obtain ⟨X, Y, fX, gY, δY, hTQ, hX_ge, hY₁⟩ :=
    exists_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb hQI
  have hX₂ : σ.slicing.intervalProp C a b₂ X :=
    intervalProp_of_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb₁_le hQI hX_ge hY₁ hTQ
  have hY₂ : σ.slicing.intervalProp C a b₂ Y :=
    σ.slicing.intervalProp_mono C (show a ≤ a by linarith) hb hY₁
  let XI₂ : σ.slicing.IntervalCat C a b₂ := ⟨X, hX₂⟩
  let YI₂ : σ.slicing.IntervalCat C a b₂ := ⟨Y, hY₂⟩
  let xQ : XI₂ ⟶ QI₂ := ObjectProperty.homMk fX
  let qY : QI₂ ⟶ YI₂ := ObjectProperty.homMk gY
  let hcomp₁ : xQ ≫ qY = 0 := by
    ext
    simpa [xQ, qY] using comp_distTriang_mor_zero₁₂ _ hTQ
  let S₁ : ShortComplex (σ.slicing.IntervalCat C a b₂) := ShortComplex.mk xQ qY hcomp₁
  have hT₁ : Triangle.mk S₁.f.hom S₁.g.hom δY ∈ distTriang C := by
    simpa [S₁, xQ, qY] using hTQ
  have hS₁ : StrictShortExact S₁ :=
    Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b₂) hT₁
  by_cases hX_zero : IsZero X
  · have hQ₁ : σ.slicing.intervalProp C a b₁ Q :=
      σ.slicing.intervalProp_of_triangle C (Or.inl hX_zero) hY₁ hTQ
    have hQ_le : σ.slicing.leProp C (a + 1) Q := by
      exact ((σ.slicing.leProp_mono (C := C) (t₁ := b₁) (t₂ := a + 1) hb₁_le) Q)
        (σ.slicing.leProp_of_intervalProp C hQ₁)
    have hK_gt : σ.slicing.gtProp C a K := σ.slicing.gtProp_of_intervalProp C hKI
    have hK₁ : σ.slicing.intervalProp C a b₁ K :=
      σ.slicing.first_intervalProp_of_triangle C hab₁ hSS.1 hQ_le hK_gt hT
    have hK_phase₁ :
        wPhaseOf (W (K₀.of C K)) ((a + b₁) / 2) ≤ ψ :=
      hSS.2.2.2.2 hT hK₁ hQ₁ hKne
    have hK_eq :
        wPhaseOf (W (K₀.of C K)) ((a + b₁) / 2) =
          wPhaseOf (W (K₀.of C K)) ((a + b₂) / 2) :=
      wPhaseOf_eq_of_intervalProp_upper_inclusion
        (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hb hK₁ hKne
        hε₀ hε₀2 hthin₂ hsin
    rw [← hK_eq]
    exact hK_phase₁
  · haveI : Mono xQ := hS₁.shortExact.mono_f
    have hxQ_strict : IsStrictMono xQ := ⟨hS₁.shortExact.mono_f, hS₁.strict_f⟩
    have hqY_strict : IsStrictEpi qY := ⟨hS₁.shortExact.epi_g, hS₁.strict_g⟩
    have hqE_strict : IsStrictEpi qE := ⟨hS₀.shortExact.epi_g, hS₀.strict_g⟩
    let BX : Subobject QI₂ := Subobject.mk xQ
    let PB : Subobject EI₂ := (Subobject.pullback qE).obj BX
    let hBXfac : BX.Factors (iK ≫ qE) := by
      rw [hcomp₀]
      exact (Subobject.factors_zero : BX.Factors (0 : KI₂ ⟶ QI₂))
    let hPBfac : PB.Factors iK := Limits.pullback_factors qE BX iK hBXfac
    let mPB : KI₂ ⟶ PB := PB.factorThru iK hPBfac
    let hcompL : mPB ≫ Subobject.pullbackπ qE BX = 0 := by
      apply (cancel_mono BX.arrow).mp
      calc
        (mPB ≫ Subobject.pullbackπ qE BX) ≫ BX.arrow
            = mPB ≫ (Subobject.pullbackπ qE BX ≫ BX.arrow) := by
                simp [Category.assoc]
        _ = mPB ≫ (PB.arrow ≫ qE) := by rw [(Subobject.isPullback qE BX).w]
        _ = (mPB ≫ PB.arrow) ≫ qE := by simp [Category.assoc]
        _ = iK ≫ qE := by
            simpa [mPB, hPBfac] using Subobject.factorThru_arrow PB iK hPBfac
        _ = 0 := hcomp₀
        _ = 0 ≫ BX.arrow := by simp
    let SL : ShortComplex (σ.slicing.IntervalCat C a b₂) :=
      ShortComplex.mk mPB (Subobject.pullbackπ qE BX) hcompL
    have hLeft : StrictShortExact SL := by
      simpa [SL, PB, BX, mPB, hcompL] using
        interval_strictShortExact_pullback_left
          (C := C) (s := σ.slicing) (a := a) (b := b₂)
          (i := iK) (q := qE) hcomp₀ hS₀Ker hqE_strict BX
    have hBXcomp : BX.arrow ≫ qY = 0 := by
      calc
        BX.arrow ≫ qY = ((Subobject.underlyingIso xQ).hom ≫ xQ) ≫ qY := by
          rw [Subobject.underlyingIso_hom_comp_eq_mk xQ]
        _ = (Subobject.underlyingIso xQ).hom ≫ (xQ ≫ qY) := by simp [Category.assoc]
        _ = 0 := by simp [hcomp₁]
    have hBXKer : IsLimit (KernelFork.ofι BX.arrow hBXcomp) := by
      have hS₁Ker : IsLimit (KernelFork.ofι xQ hcomp₁) := by
        simpa [S₁] using
          interval_fIsKernel_of_strictShortExact
            (C := C) (s := σ.slicing) (a := a) (b := b₂) hS₁
      refine KernelFork.IsLimit.ofι' BX.arrow hBXcomp (fun {W} k hk ↦ ?_)
      let uX : W ⟶ XI₂ := hS₁Ker.lift (KernelFork.ofι k hk)
      refine ⟨uX ≫ (Subobject.underlyingIso xQ).inv, ?_⟩
      calc
        (uX ≫ (Subobject.underlyingIso xQ).inv) ≫ BX.arrow
            = uX ≫ xQ := by simp [Category.assoc, BX]
        _ = k := hS₁Ker.fac _ Limits.WalkingParallelPair.zero
    let pE : EI₂ ⟶ YI₂ := qE ≫ qY
    let hcompR : PB.arrow ≫ pE = 0 := by
      calc
        PB.arrow ≫ pE = PB.arrow ≫ qE ≫ qY := by simp [pE, Category.assoc]
        _ = (PB.arrow ≫ qE) ≫ qY := by simp [Category.assoc]
        _ = (Subobject.pullbackπ qE BX ≫ BX.arrow) ≫ qY := by
            rw [(Subobject.isPullback qE BX).w]
        _ = Subobject.pullbackπ qE BX ≫ BX.arrow ≫ qY := by
            simp [Category.assoc]
        _ = Subobject.pullbackπ qE BX ≫ (BX.arrow ≫ qY) := by simp [Category.assoc]
        _ = 0 := by simp [hBXcomp]
    let SR : ShortComplex (σ.slicing.IntervalCat C a b₂) :=
      ShortComplex.mk PB.arrow pE hcompR
    have hRight : StrictShortExact SR := by
      simpa [SR, PB, BX, pE, hcompR] using
        interval_strictShortExact_pullback_right
          (C := C) (s := σ.slicing) (a := a) (b := b₂) qE hqE_strict BX qY hBXcomp
          hBXKer hqY_strict
    haveI : Mono mPB := hLeft.shortExact.mono_f
    have hPB_ne : ¬IsZero (PB : σ.slicing.IntervalCat C a b₂).obj := by
      intro hPBZ
      have hm_zero_hom : mPB.hom = 0 := hPBZ.eq_of_tgt mPB.hom 0
      have hm_zero : mPB = 0 := by
        apply ObjectProperty.hom_ext
        simpa using hm_zero_hom
      have hId : 𝟙 KI₂ = 0 := by
        apply (cancel_mono mPB).1
        simpa [hm_zero]
      have hKZ : IsZero KI₂ := (IsZero.iff_id_eq_zero KI₂).mpr hId
      exact hKne (((σ.slicing.intervalProp C a b₂).ι).map_isZero hKZ)
    obtain ⟨δR, hTR⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := σ.slicing) (a := a) (b := b₂) hRight
    have hY_le : σ.slicing.leProp C (a + 1) Y := by
      exact ((σ.slicing.leProp_mono (C := C) (t₁ := b₁) (t₂ := a + 1) hb₁_le) Y)
        (σ.slicing.leProp_of_intervalProp C hY₁)
    have hPB_gt : σ.slicing.gtProp C a (PB : σ.slicing.IntervalCat C a b₂).obj :=
      σ.slicing.gtProp_of_intervalProp C
        (show σ.slicing.intervalProp C a b₂ (PB : σ.slicing.IntervalCat C a b₂).obj from
          (PB : σ.slicing.IntervalCat C a b₂).property)
    have hPB₁ : σ.slicing.intervalProp C a b₁ (PB : σ.slicing.IntervalCat C a b₂).obj :=
      σ.slicing.first_intervalProp_of_triangle C hab₁ hSS.1 hY_le hPB_gt
        (by simpa [SR, pE] using hTR)
    have hPB_phase₁ :
        wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₁) / 2) ≤ ψ :=
      hSS.2.2.2.2 (by simpa [SR, pE] using hTR) hPB₁ hY₁ hPB_ne
    have hPB_eq :
        wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₁) / 2) =
          wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₂) / 2) :=
      wPhaseOf_eq_of_intervalProp_upper_inclusion
        (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hb hPB₁ hPB_ne
        hε₀ hε₀2 hthin₂ hsin
    have hPB_phase_le :
        wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₂) / 2) ≤ ψ := by
      rw [← hPB_eq]
      exact hPB_phase₁
    have hX_phase_gt :
        ψ < wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) :=
      wPhaseOf_gt_of_upper_boundary_triangle
        (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hab₂ hb hQI hX_ge hY₁ hX_zero
        hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin hTQ
    have hPB_window := hWindow₂
      (show σ.slicing.intervalProp C a b₂ (PB : σ.slicing.IntervalCat C a b₂).obj from
        (PB : σ.slicing.IntervalCat C a b₂).property) hPB_ne
    have hK_window := hWindow₂ hKI hKne
    have hX_window := hWindow₂ hX₂ hX_zero
    let ψPB : ℝ := wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₂) / 2)
    have hBXW :
        W (K₀.of C (Subobject.underlying.obj BX).obj) = W (K₀.of C X) := by
      simpa [BX, XI₂] using
        congrArg W
          (K₀.of_iso C (((σ.slicing.intervalProp C a b₂).ι).mapIso (Subobject.underlyingIso xQ)))
    have hX_phase_gt_pb :
        ψPB < wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) := by
      dsimp [ψPB]
      linarith
    have hX_range_pb :
        wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) ∈ Set.Ioo (ψPB - 1) (ψPB + 1) := by
      constructor <;> dsimp [ψPB] <;> linarith [hX_window.1, hX_window.2, hPB_window.1,
        hPB_window.2, hthin₂]
    have hK_range_pb :
        wPhaseOf (W (K₀.of C K)) ((a + b₂) / 2) ∈ Set.Ioo (ψPB - 1) (ψPB + 1) := by
      constructor <;> dsimp [ψPB] <;> linarith [hK_window.1, hK_window.2, hPB_window.1,
        hPB_window.2, hthin₂]
    let ssf₂ := σ.skewedStabilityFunction_of_near C W hW hab₂
    have hsumL :
        W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj) =
          W (K₀.of C (KI₂ : σ.slicing.IntervalCat C a b₂).obj) +
            W (K₀.of C (XI₂ : σ.slicing.IntervalCat C a b₂).obj) := by
      have hsumL' :
          W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj) =
            W (K₀.of C (KI₂ : σ.slicing.IntervalCat C a b₂).obj) +
              W (K₀.of C (Subobject.underlying.obj BX).obj) := by
        simpa [StabilityCondition.skewedStabilityFunction_of_near, SL, PB, KI₂, map_add] using
          ssf₂.strict_additive (C := C) (s := σ.slicing) (a := a) (b := b₂) hLeft
      calc
        W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj) =
            W (K₀.of C (KI₂ : σ.slicing.IntervalCat C a b₂).obj) +
              W (K₀.of C (Subobject.underlying.obj BX).obj) := hsumL'
        _ = W (K₀.of C (KI₂ : σ.slicing.IntervalCat C a b₂).obj) +
              W (K₀.of C (XI₂ : σ.slicing.IntervalCat C a b₂).obj) := by
            rw [hBXW]
    have hX_Wne : W (K₀.of C X) ≠ 0 := hW_ne_big hX₂ hX_zero
    have hK_phase_lt_pb :
        wPhaseOf (W (K₀.of C K)) ((a + b₂) / 2) < ψPB := by
      dsimp [ψPB]
      exact wPhaseOf_seesaw_dual
        (by simpa [KI₂, XI₂, add_comm] using hsumL.symm)
        rfl hX_phase_gt_pb hX_Wne hX_range_pb hK_range_pb
    linarith

theorem SkewedStabilityFunction.semistable_of_iso
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    {E E' : C} (e : E ≅ E') {ψ : ℝ} (h : ssf.Semistable C E ψ) :
    ssf.Semistable C E' ψ := by
  refine ⟨(s.intervalProp C a b).prop_of_iso e h.1, ?_, ?_, ?_, ?_⟩
  · exact fun hE' ↦ h.2.1 ((Iso.isZero_iff e).mpr hE')
  · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
    exact h.2.2.1
  · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
    exact h.2.2.2.1
  · intro K Q f₁ f₂ f₃ hT hK hQ hKne
    have hT' : Triangle.mk (f₁ ≫ e.inv) (e.hom ≫ f₂) f₃ ∈ distTriang C :=
      isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
          (by simp) (by simp) (by simp))
    exact h.2.2.2.2 hT' hK hQ hKne

variable [IsTriangulated C] in
/-- A maximal-phase strict subobject of a non-semistable interval object cannot be `⊤`. -/
theorem SkewedStabilityFunction.maxPhase_strictSubobject_ne_top_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hM_ne : M ≠ ⊥) (hM_strict : IsStrictMono M.arrow)
    (hM_max : ∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    M ≠ ⊤ := by
  intro hM_top
  apply hns
  have hM_ss :=
    ssf.semistable_of_maxPhase_strictSubobject (C := C) (σ := σ)
      (a := a) (b := b) hM_ne hM_strict hM_max hW_interval
  subst hM_top
  have hphase :
      wPhaseOf
          (ssf.W
            (K₀.of C (((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj))) ssf.α =
        wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
    let eC :
        (((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj) ≅ X.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (asIso (⊤ : Subobject X).arrow)
    simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
  let eC :
      (((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj) ≅ X.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
      (asIso (⊤ : Subobject X).arrow)
  have hTop_ss := semistable_of_iso
    (C := C) (s := σ.slicing) (a := a) (b := b)
    eC hM_ss
  simpa [hphase] using hTop_ss

variable [IsTriangulated C] in
/-- In a non-semistable interval object, a maximal-phase strict subobject has strictly
larger phase than the ambient object. -/
theorem SkewedStabilityFunction.phase_gt_of_maxPhase_strictSubobject_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hX : ¬IsZero X)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hM_ne : M ≠ ⊥) (hM_strict : IsStrictMono M.arrow)
    (hM_max : ∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
  let phaseObj : σ.slicing.IntervalCat C a b → ℝ := fun Y ↦
    wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hX_obj : ¬IsZero X.obj := by
    intro hZ
    exact hX (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  by_contra hle
  push_neg at hle
  apply hns
  refine ⟨X.property, hX_obj, hW_interval X.property hX_obj, rfl, ?_⟩
  intro K Q f₁ f₂ f₃ hT hK hQ hKne
  let KI : σ.slicing.IntervalCat C a b := ⟨K, hK⟩
  let QI : σ.slicing.IntervalCat C a b := ⟨Q, hQ⟩
  let iKX : KI ⟶ X := ObjectProperty.homMk f₁
  let gXQ : X ⟶ QI := ObjectProperty.homMk f₂
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk iKX gXQ (by
      ext
      simpa [iKX, gXQ] using comp_distTriang_mor_zero₁₂ _ hT)
  have hT' : Triangle.mk S.f.hom S.g.hom f₃ ∈ distTriang C := by
    simpa [S, iKX, gXQ] using hT
  have hK_strict : IsStrictMono iKX :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b) hT').1
  letI : Mono iKX := hK_strict.mono
  let B : Subobject X := Subobject.mk iKX
  have hKI_ne : ¬IsZero KI := by
    intro hZ
    exact hKne (((σ.slicing.intervalProp C a b).ι).map_isZero hZ)
  have hB_ne : B ≠ ⊥ := by
    intro hB
    have hzero : iKX = 0 := by
      exact (Subobject.mk_eq_bot_iff_zero).mp
        (show Subobject.mk iKX = ⊥ by simpa [B] using hB)
    have hId : 𝟙 KI = 0 := by
      apply (cancel_mono iKX).1
      simpa [hzero]
    exact hKI_ne ((IsZero.iff_id_eq_zero KI).mpr hId)
  have hB_strict : IsStrictMono B.arrow := by
    simpa [B] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) iKX hK_strict)
  have hPhaseB : phaseObj KI ≤ phaseObj M := by
    have hPhaseSub : phaseObj (B : σ.slicing.IntervalCat C a b) ≤ phaseObj M :=
      hM_max B hB_ne hB_strict
    have hIsoK :
        phaseObj KI = phaseObj (B : σ.slicing.IntervalCat C a b) := by
      let eC : (B : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (Subobject.underlyingIso iKX)
      simpa [phaseObj] using congrArg (fun x => wPhaseOf (ssf.W x) ssf.α)
        (K₀.of_iso C eC).symm
    exact hIsoK.trans_le hPhaseSub
  simpa [phaseObj, KI] using hPhaseB.trans hle

variable [IsTriangulated C] in
/-- Strict-Artinian descent for the first strict short exact sequence: starting from a
non-semistable thin-interval object, repeatedly pass to a proper strict subobject of larger
phase until the descent terminates at a semistable strict subobject. This is the faithful
Section 7 substitute for the older finite-enumeration wrapper. -/
theorem SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} [IsStrictArtinianObject X] (hX : ¬IsZero X)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    ∃ M : Subobject X,
      M ≠ ⊥ ∧
      M ≠ ⊤ ∧
      IsStrictMono M.arrow ∧
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
      StrictShortExact
        (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) := by
  let phaseSub : StrictSubobject X → ℝ := fun B ↦
    wPhaseOf (ssf.W (K₀.of C ((B.1 : σ.slicing.IntervalCat C a b).obj))) ssf.α
  let P : StrictSubobject X → Prop := fun B =>
    ∀ hBne : ¬IsZero (B.1 : σ.slicing.IntervalCat C a b),
      ¬ ssf.Semistable C ((B.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub B) →
      ∃ D : StrictSubobject X,
        D < B ∧
        ssf.Semistable C ((D.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub D) ∧
        phaseSub B < phaseSub D
  have hP : ∀ B : StrictSubobject X, P B := by
    intro B
    refine (show WellFounded ((· < ·) : StrictSubobject X → StrictSubobject X → Prop) from
      wellFounded_lt).induction B ?_
    intro B ih hBne hnsB
    obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hphaseBA⟩ :=
      ssf.exists_phase_gt_strictSubobject_of_not_semistable
        (C := C) (σ := σ) (a := a) (b := b) (X := (B.1 : σ.slicing.IntervalCat C a b))
        hBne hW_interval hnsB
    let Csub : Subobject X := intervalLiftSub (C := C) (X := X) B.1 A
    have hC_ne_bot : Csub ≠ ⊥ :=
      intervalLiftSub_ne_bot (C := C) (X := X) B.1 hA_ne_bot
    have hC_strict : IsStrictMono Csub.arrow :=
      intervalLiftSub_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.2 hA_strict
    let Cstr : StrictSubobject X := ⟨Csub, hC_strict⟩
    have hC_lt_B : Cstr < B := by
      simpa [Cstr, Csub] using
        (intervalLiftSub_lt (C := C) (X := X) B.1 hA_ne_top)
    have hC_ne : ¬IsZero (Cstr.1 : σ.slicing.IntervalCat C a b) :=
      intervalSubobject_not_isZero_of_ne_bot
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hC_ne_bot
    have hphaseBC : phaseSub B < phaseSub Cstr := by
      dsimp [phaseSub, Cstr, Csub]
      rw [intervalLiftSub_wPhase_eq (C := C) (s := σ.slicing) (ssf := ssf) B.1 A]
      exact hphaseBA
    by_cases hssC :
        ssf.Semistable C ((Cstr.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub Cstr)
    · exact ⟨Cstr, hC_lt_B, hssC, hphaseBC⟩
    · obtain ⟨D, hD_lt_C, hssD, hphaseCD⟩ := ih Cstr hC_lt_B hC_ne hssC
      exact ⟨D, lt_trans hD_lt_C hC_lt_B, hssD, lt_trans hphaseBC hphaseCD⟩
  obtain ⟨B, hB_ne_bot, hB_ne_top, hB_strict, hphaseXB⟩ :=
    ssf.exists_phase_gt_strictSubobject_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hX hW_interval hns
  let Bstr : StrictSubobject X := ⟨B, hB_strict⟩
  have hB_ne : ¬IsZero (Bstr.1 : σ.slicing.IntervalCat C a b) :=
    intervalSubobject_not_isZero_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hB_ne_bot
  have hphaseXB' :
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α < phaseSub Bstr := by
    simpa [phaseSub, Bstr] using hphaseXB
  by_cases hssB :
      ssf.Semistable C ((Bstr.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub Bstr)
  · refine ⟨B, hB_ne_bot, hB_ne_top, hB_strict, ?_, hphaseXB, ?_⟩
    · simpa [phaseSub, Bstr] using hssB
    · exact interval_strictShortExact_cokernel_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.arrow hB_strict
  · obtain ⟨D, hD_lt_B, hssD, hphaseBD⟩ := hP Bstr hB_ne hssB
    have hD_ne_top : D.1 ≠ ⊤ := by
      intro hD
      have htop_le : (⊤ : Subobject X) ≤ B := by
        have hle : D.1 ≤ B := hD_lt_B.le
        simpa [hD] using hle
      exact hB_ne_top (top_le_iff.mp htop_le)
    have hD_ne_bot : D.1 ≠ ⊥ := by
      intro hD
      exact hssD.2.1
        (((σ.slicing.intervalProp C a b).ι).map_isZero
          ((intervalSubobject_isZero_iff_eq_bot
            (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) D.1).mpr hD))
    refine ⟨D.1, hD_ne_bot, hD_ne_top, D.2, ?_, ?_, ?_⟩
    · simpa [phaseSub] using hssD
    · exact lt_trans hphaseXB' hphaseBD
    · exact interval_strictShortExact_cokernel_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) D.1.arrow D.2

variable [IsTriangulated C] in
/-- Finiteness of subobjects in the left-heart image of an interval object implies finiteness of
its strict-subobject set in the thin interval category. This is the paper-faithful local
finite-length input for the first strict short exact sequence. -/
theorem Slicing.IntervalCat.finite_strictSubobjects_of_finite_leftHeartSubobjects
    (s : Slicing C) {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b}
    (hX : Finite (Subobject ((Slicing.IntervalCat.toLeftHeart
      (C := C) (s := s) a b (Fact.out : b - a ≤ 1)).obj X))) :
    Finite {B : Subobject X // B ≠ ⊥ ∧ IsStrictMono B.arrow} := by
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let φ : {B : Subobject X // B ≠ ⊥ ∧ IsStrictMono B.arrow} → Subobject (FL.obj X) :=
    fun B ↦ by
      letI : Mono (FL.map B.1.arrow) :=
        Slicing.IntervalCat.mono_toLeftHeart_of_strictMono
          (C := C) (s := s) (a := a) (b := b) B.1.arrow B.2.2
      exact Subobject.mk (FL.map B.1.arrow)
  exact Finite.of_injective φ (fun B₁ B₂ hEq ↦ by
    letI : Mono (FL.map B₁.1.arrow) :=
      Slicing.IntervalCat.mono_toLeftHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) B₁.1.arrow B₁.2.2
    letI : Mono (FL.map B₂.1.arrow) :=
      Slicing.IntervalCat.mono_toLeftHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) B₂.1.arrow B₂.2.2
    apply Subtype.ext
    simpa [Subobject.mk_arrow] using Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
      (FL.preimageIso (Subobject.isoOfMkEqMk _ _ hEq))
      (FL.map_injective (by
        simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
        exact Subobject.ofMkLEMk_comp hEq.le)))

variable [IsTriangulated C] in
/-- Bridgeland's first strict short exact sequence in a thin category: if an interval object is
not `W`-semistable, there is a proper strict subobject of maximal `W`-phase, and its inclusion
gives a strict short exact sequence `0 → A → E → B → 0`.

The faithful local-finiteness input here is finiteness of the thin category's
strict-subobject set, not an ambient `Finite (Subobject X.obj)` statement in `C`. -/
theorem SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hT_fin : Set.Finite {M : Subobject X | M ≠ ⊥ ∧ IsStrictMono M.arrow})
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    ∃ M : Subobject X,
      M ≠ ⊥ ∧
      M ≠ ⊤ ∧
      IsStrictMono M.arrow ∧
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
      StrictShortExact
        (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) := by
  obtain ⟨M, hM_ne, hM_strict, hM_max, _⟩ :=
    ssf.exists_maxPhase_maximal_strictSubobject_of_finite
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hX hT_fin
  have hM_ne_top : M ≠ ⊤ :=
    ssf.maxPhase_strictSubobject_ne_top_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hns hM_ne hM_strict hM_max hW_interval
  have hM_ss :
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) :=
    ssf.semistable_of_maxPhase_strictSubobject
      (C := C) (σ := σ) (a := a) (b := b) hM_ne hM_strict hM_max hW_interval
  have hphase_gt :
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
    ssf.phase_gt_of_maxPhase_strictSubobject_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hX hns hM_ne hM_strict hM_max hW_interval
  have hS : StrictShortExact
      (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) :=
    interval_strictShortExact_cokernel_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) M.arrow hM_strict
  exact ⟨M, hM_ne, hM_ne_top, hM_strict, hM_ss, hphase_gt, hS⟩


end CategoryTheory.Triangulated
