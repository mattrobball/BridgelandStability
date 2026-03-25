/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.BoundaryTriangle
public import BridgelandStability.Deformation.IntervalSelection

/-!
# Deformation of Stability Conditions — Pullback

Pullback infrastructure, upper inclusion semistability, first strict SES
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
  have he : e.hom ≫ pullback.fst B.arrow p = Subobject.pullbackπ p B :=
    (Subobject.isPullback p B).isoPullback_hom_fst
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
            hKerB.lift (KernelFork.ofι (g ≫ p) (by
              rw [Category.assoc]
              exact hg))
          have hu : u ≫ B.arrow = g ≫ p :=
            hKerB.fac _ Limits.WalkingParallelPair.zero
          exact ⟨sq.lift u g hu, sq.lift_snd u g hu⟩) }
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
  refine Subobject.le_of_comm (sq.lift 0 M.arrow (by
    dsimp [q]
    rw [zero_comp]
    exact (cokernel.condition M.arrow).symm)) ?_
  exact sq.lift_snd 0 M.arrow (by
    dsimp [q]
    rw [zero_comp]
    exact (cokernel.condition M.arrow).symm)

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
    _ = (Subobject.ofLE M pbB hle ≫ pbB.arrow) ≫ q := by simp
    _ = M.arrow ≫ q := by rw [Subobject.ofLE_arrow]
    _ = 0 ≫ B.arrow := by
          rw [show M.arrow ≫ q = 0 by
            dsimp [q]
            exact cokernel.condition M.arrow]
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
                ((((Subobject.pullback q).obj B).factorThru i (Limits.pullback_factors q B i hiB)) ≫
                    ((Subobject.pullback q).obj B).arrow) ≫ q =
                  i ≫ q
              exact congrArg (fun t ↦ t ≫ q)
                (Subobject.factorThru_arrow ((Subobject.pullback q).obj B) i
                  (Limits.pullback_factors q B i hiB))
          _ = 0 := hiq
          _ = 0 ≫ B.arrow := by simp)) := by
  let pb := (Subobject.pullback q).obj B
  let hiB : B.Factors (i ≫ q) := by
    simpa [hiq] using (Subobject.factors_zero : B.Factors (0 : K ⟶ Q))
  let hpb : pb.Factors i := Limits.pullback_factors q B i hiB
  let m : K ⟶ pb :=
    pb.factorThru i hpb
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
      _ = i ≫ q := congrArg (fun t ↦ t ≫ q) hm
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
    have hu : u ≫ i = g ≫ pb.arrow :=
      hKer.fac _ Limits.WalkingParallelPair.zero
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
          pb.arrow ≫ p = pb.arrow ≫ q ≫ g := by simp [p]
          _ = (pb.arrow ≫ q) ≫ g := by simp [Category.assoc]
          _ = (Subobject.pullbackπ q B ≫ B.arrow) ≫ g := by
              rw [(Subobject.isPullback q B).w]
          _ = Subobject.pullbackπ q B ≫ B.arrow ≫ g := by simp
          _ = 0 := by simp [hBg])) := by
  let pb := (Subobject.pullback q).obj B
  let p : E ⟶ Y := q ≫ g
  let hcomp : pb.arrow ≫ p = 0 := by
    calc
      pb.arrow ≫ p = pb.arrow ≫ q ≫ g := by simp [p]
      _ = (pb.arrow ≫ q) ≫ g := by simp [Category.assoc]
      _ = (Subobject.pullbackπ q B ≫ B.arrow) ≫ g := by
          rw [(Subobject.isPullback q B).w]
      _ = Subobject.pullbackπ q B ≫ B.arrow ≫ g := by simp
      _ = 0 := by simp [hBg]
  have hKer : IsLimit (KernelFork.ofι pb.arrow hcomp) := by
    refine KernelFork.IsLimit.ofι' pb.arrow hcomp (fun {W} k hk ↦ ?_)
    let u : W ⟶ (B : s.IntervalCat C a b) :=
      hBKer.lift (KernelFork.ofι (k ≫ q) (by
        simpa [p, Category.assoc] using hk))
    have hu : u ≫ B.arrow = k ≫ q :=
      hBKer.fac _ Limits.WalkingParallelPair.zero
    refine ⟨(Subobject.isPullback q B).lift u k hu, ?_⟩
    exact (Subobject.isPullback q B).lift_snd u k hu
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
    have hk : k ≫ M.arrow = g ≫ pbB.arrow :=
      hM.isLimitKernelFork.fac _ Limits.WalkingParallelPair.zero
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

/-- The first map in a strict short exact sequence in a thin interval category is a kernel. -/
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

/-- Pulling back a strict subobject along a cokernel map preserves the cokernel object up to iso. -/
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
      (by simp [heK])
  let eQ : cokernel (kernel.ι p) ≅ cokernel B.arrow :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι p))
      hp.isColimitCokernelCofork
  exact eC ≪≫ eQ

theorem semistable_of_upper_inclusion
    [IsTriangulated C]
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
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
    σ.slicing.intervalProp_mono C (show a ≤ a by grind) hb hSS.1
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
      (C := C) (σ := σ) (W := W) hab₂ hε₀ hthin₂ hsin
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
    exact ⟨by linarith, by grind⟩
  have hpert₂_hi :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₂ →
        b₂ + ε₀ - 1 < wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) < b₂ + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert₂ F φ hP hFne haφ hφb
    exact ⟨by linarith, by grind⟩
  have hWindow₂ :
      ∀ {G : C}, σ.slicing.intervalProp C a b₂ G → ¬IsZero G →
        a - ε₀ < wPhaseOf (W (K₀.of C G)) ((a + b₂) / 2) ∧
          wPhaseOf (W (K₀.of C G)) ((a + b₂) / 2) < b₂ + ε₀ := by
    intro G hG hGne
    exact ⟨wPhaseOf_gt_of_intervalProp C σ hGne W (by grind) hG hW_ne₂ hpert₂_lo,
      wPhaseOf_lt_of_intervalProp C σ hGne W (by grind) hG hW_ne₂ hpert₂_hi⟩
  have hW_ne_big :
      ∀ {G : C}, σ.slicing.intervalProp C a b₂ G → ¬IsZero G → W (K₀.of C G) ≠ 0 := by
    intro G hG hGne
    exact σ.W_ne_zero_of_intervalProp C W hthin₂' hsmall₂ hGne hG
  refine semistable_of_target_envelope_triangleTest
    (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hSS hab₂ hEI₂ hε₀ henv_lo henv_hi₂
    hthin₂ ?_
  intro K Q f₁ f₂ f₃ hT hKI hQI hKne
  letI : Fact (a < b₂) := ⟨hab₂⟩
  letI : Fact (b₂ - a ≤ 1) := ⟨by grind⟩
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
      hab₁ hQI
  have hX₂ : σ.slicing.intervalProp C a b₂ X :=
    intervalProp_of_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb₁_le hQI hX_ge hY₁ hTQ
  have hY₂ : σ.slicing.intervalProp C a b₂ Y :=
    σ.slicing.intervalProp_mono C (show a ≤ a by grind) hb hY₁
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
    have hQ_le : σ.slicing.leProp C (a + 1) Q :=
      ((σ.slicing.leProp_mono (C := C) (t₁ := b₁) (t₂ := a + 1) hb₁_le) Q)
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
            have hmPB : mPB ≫ PB.arrow = iK :=
              Subobject.factorThru_arrow PB iK hPBfac
            change (mPB ≫ PB.arrow) ≫ qE = iK ≫ qE
            rw [hmPB]
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
        _ = (Subobject.underlyingIso xQ).hom ≫ (xQ ≫ qY) := by simp
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
        PB.arrow ≫ pE = PB.arrow ≫ qE ≫ qY := by simp [pE]
        _ = (PB.arrow ≫ qE) ≫ qY := by simp [Category.assoc]
        _ = (Subobject.pullbackπ qE BX ≫ BX.arrow) ≫ qY := by
            rw [(Subobject.isPullback qE BX).w]
        _ = Subobject.pullbackπ qE BX ≫ BX.arrow ≫ qY := by
            simp
        _ = Subobject.pullbackπ qE BX ≫ (BX.arrow ≫ qY) := by simp
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
        rw [hm_zero]
        simp
      have hKZ : IsZero KI₂ := (IsZero.iff_id_eq_zero KI₂).mpr hId
      exact hKne (((σ.slicing.intervalProp C a b₂).ι).map_isZero hKZ)
    obtain ⟨δR, hTR⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := σ.slicing) (a := a) (b := b₂) hRight
    have hY_le : σ.slicing.leProp C (a + 1) Y :=
      ((σ.slicing.leProp_mono (C := C) (t₁ := b₁) (t₂ := a + 1) hb₁_le) Y)
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


end CategoryTheory.Triangulated
