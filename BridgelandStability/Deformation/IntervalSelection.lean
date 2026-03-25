/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.Deformation.WPhase

/-!
# Deformation of Stability Conditions — IntervalSelection

Thin-interval selection, subobject lifting, finite length
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

/-! ### Thin-interval Phase 3 selection infrastructure -/

section

@[simp] lemma intervalSubobject_isZero_iff_eq_bot
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b} (B : Subobject X) :
    IsZero (B : s.IntervalCat C a b) ↔ B = ⊥ := by
  constructor
  · intro hZ
    have : B.arrow = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rwa [← Subobject.mk_arrow B, Subobject.mk_eq_bot_iff_zero]
  · intro h
    subst h
    exact (isZero_zero (s.IntervalCat C a b)).of_iso Subobject.botCoeIsoZero

lemma intervalSubobject_not_isZero_of_ne_bot
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b} {B : Subobject X}
    (h : B ≠ ⊥) : ¬IsZero (B : s.IntervalCat C a b) :=
  fun hZ ↦ h ((intervalSubobject_isZero_iff_eq_bot
    (C := C) (s := s) (a := a) (b := b) (X := X) B).mp hZ)

lemma intervalSubobject_top_ne_bot_of_not_isZero
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (hX : ¬IsZero X) : (⊤ : Subobject X) ≠ ⊥ := by
  intro h
  apply hX
  have hZ : IsZero ((⊤ : Subobject X) : s.IntervalCat C a b) :=
    (intervalSubobject_isZero_iff_eq_bot
      (C := C) (s := s) (a := a) (b := b) (X := X) _).mpr h
  exact hZ.of_iso (asIso (⊤ : Subobject X).arrow).symm

end

section

variable [IsTriangulated C]

lemma intervalSubobject_arrow_strictMono_of_strictMono
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (f : Y ⟶ X) (hf : IsStrictMono f) :
    letI : Mono f := hf.mono
    IsStrictMono (Subobject.mk f).arrow := by
  letI : Mono f := hf.mono
  let e := Subobject.underlyingIso f
  have he : IsStrictMono e.hom := isStrictMono_of_isIso
  have hcomp : IsStrictMono (e.hom ≫ f) :=
    Slicing.IntervalCat.comp_strictMono
      (C := C) (s := s) (a := a) (b := b) e.hom f he hf
  have harr : e.hom ≫ f = (Subobject.mk f).arrow :=
    Subobject.underlyingIso_hom_comp_eq_mk f
  rw [← harr]
  exact hcomp

theorem interval_strictShortExact_cokernel_of_strictMono
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (f : Y ⟶ X) (hf : IsStrictMono f) :
    StrictShortExact (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) := by
  let S : ShortComplex (s.IntervalCat C a b) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S, KernelFork.ofι] using hf.isLimitKernelFork
  have hEpi : Epi ((S.map FL).g) := by
    simpa [S, FL] using
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) (cokernel.π f) (isStrictEpi_cokernel f)
  have hKer :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExact : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKer
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) hL
  exact Slicing.IntervalCat.strictShortExact_of_distTriang
    (C := C) (s := s) (a := a) (b := b) hT

theorem intervalInclusion_map_strictMono
    {s₁ s₂ : Slicing C}
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X Y : s₁.IntervalCat C a₁ b₁} (f : X ⟶ Y) (hf : IsStrictMono f) :
    IsStrictMono ((ObjectProperty.ιOfLE h).map f) := by
  let S : ShortComplex (s₁.IntervalCat C a₁ b₁) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : StrictShortExact S :=
    interval_strictShortExact_cokernel_of_strictMono
      (C := C) (s := s₁) (a := a₁) (b := b₁) f hf
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := s₁) (a := a₁) (b := b₁) hS
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  let S' : ShortComplex (s₂.IntervalCat C a₂ b₂) := S.map I
  have hT' : Triangle.mk S'.f.hom S'.g.hom δ ∈ distTriang C := by
    simpa [I, S, S'] using hT
  exact
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := s₂) (a := a₂) (b := b₂) hT').1

theorem interval_strictArtinianObject_of_inclusion
    {s₁ s₂ : Slicing C}
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsArtinianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictArtinianObject X := by
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  exact isStrictArtinianObject_of_faithful_map_strictMono I (fun f hf ↦
    intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h f hf)

theorem interval_strictNoetherianObject_of_inclusion
    {s₁ s₂ : Slicing C}
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsNoetherianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictNoetherianObject X := by
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  exact isStrictNoetherianObject_of_faithful_map_strictMono I (fun f hf ↦
    intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h f hf)

theorem interval_strictFiniteLength_of_inclusion
    {s₁ s₂ : Slicing C}
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsArtinianObject ((ObjectProperty.ιOfLE h).obj X)]
    [IsNoetherianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictArtinianObject X ∧ IsStrictNoetherianObject X :=
  ⟨interval_strictArtinianObject_of_inclusion (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h,
    interval_strictNoetherianObject_of_inclusion (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h⟩

theorem interval_thinFiniteLength_of_inclusion
    {s₁ s₂ : Slicing C}
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    (hFinite : ∀ Y : s₂.IntervalCat C a₂ b₂,
      IsArtinianObject Y ∧ IsNoetherianObject Y) :
    ∀ X : s₁.IntervalCat C a₁ b₁,
      IsStrictArtinianObject X ∧ IsStrictNoetherianObject X := by
  intro X
  have hBig := hFinite ((ObjectProperty.ιOfLE h).obj X)
  letI : IsArtinianObject ((ObjectProperty.ιOfLE h).obj X) := hBig.1
  letI : IsNoetherianObject ((ObjectProperty.ιOfLE h).obj X) := hBig.2
  simpa using
    (interval_strictFiniteLength_of_inclusion
      (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h (X := X))

theorem interval_strictArtinianObject_of_inclusion_strict
    {s₁ s₂ : Slicing C}
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsStrictArtinianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictArtinianObject X := by
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  let F : StrictSubobject X → StrictSubobject (I.obj X) := fun B ↦ by
    let hstrict : IsStrictMono (I.map B.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B.1.arrow B.2
    letI : Mono (I.map B.1.arrow) := hstrict.mono
    exact ⟨Subobject.mk (I.map B.1.arrow),
      intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s₂) (a := a₂) (b := b₂) (I.map B.1.arrow) hstrict⟩
  have hF_inj : Function.Injective F := by
    intro B₁ B₂ hEq
    let hstrict₁ : IsStrictMono (I.map B₁.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₁.1.arrow B₁.2
    let hstrict₂ : IsStrictMono (I.map B₂.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₂.1.arrow B₂.2
    letI : Mono (I.map B₁.1.arrow) := hstrict₁.mono
    letI : Mono (I.map B₂.1.arrow) := hstrict₂.mono
    apply Subtype.ext
    have hEq' : Subobject.mk (I.map B₁.1.arrow) = Subobject.mk (I.map B₂.1.arrow) :=
      congrArg Subtype.val hEq
    simpa [Subobject.mk_arrow] using
      (Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
        (I.preimageIso (Subobject.isoOfMkEqMk _ _ hEq'))
        (I.map_injective (by
          simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
          exact Subobject.ofMkLEMk_comp hEq'.le)))
  have hF_mono : Monotone F := by
    intro B₁ B₂ hB
    let hstrict₁ : IsStrictMono (I.map B₁.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₁.1.arrow B₁.2
    let hstrict₂ : IsStrictMono (I.map B₂.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₂.1.arrow B₂.2
    letI : Mono (I.map B₁.1.arrow) := hstrict₁.mono
    letI : Mono (I.map B₂.1.arrow) := hstrict₂.mono
    change Subobject.mk (I.map B₁.1.arrow) ≤ Subobject.mk (I.map B₂.1.arrow)
    have hmk : Subobject.mk B₁.1.arrow ≤ Subobject.mk B₂.1.arrow := by
      simpa [Subobject.mk_arrow] using (show B₁.1 ≤ B₂.1 from hB)
    exact Subobject.mk_le_mk_of_comm (I.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk)) (by
      rw [← I.map_comp]
      exact congrArg I.map (Subobject.ofMkLEMk_comp hmk))
  exact
    (show isStrictArtinianObject.Is X from
      ObjectProperty.is_of_prop _
        (show WellFoundedLT (StrictSubobject X) from by
          rw [← wellFoundedGT_dual_iff, wellFoundedGT_iff_monotone_chain_condition]
          intro f
          let g : ℕ →o (StrictSubobject (I.obj X))ᵒᵈ :=
            ⟨fun n ↦ OrderDual.toDual (F (f n)),
              fun i j hij ↦ by
                change F (f j) ≤ F (f i)
                exact hF_mono (f.2 hij)⟩
          obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
          exact ⟨n, fun m hm ↦ hF_inj (by
            simpa using congrArg OrderDual.ofDual (hn m hm))⟩))

theorem interval_strictNoetherianObject_of_inclusion_strict
    {s₁ s₂ : Slicing C}
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsStrictNoetherianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictNoetherianObject X := by
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  let F : StrictSubobject X → StrictSubobject (I.obj X) := fun B ↦ by
    let hstrict : IsStrictMono (I.map B.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B.1.arrow B.2
    letI : Mono (I.map B.1.arrow) := hstrict.mono
    exact ⟨Subobject.mk (I.map B.1.arrow),
      intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s₂) (a := a₂) (b := b₂) (I.map B.1.arrow) hstrict⟩
  have hF_inj : Function.Injective F := by
    intro B₁ B₂ hEq
    let hstrict₁ : IsStrictMono (I.map B₁.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₁.1.arrow B₁.2
    let hstrict₂ : IsStrictMono (I.map B₂.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₂.1.arrow B₂.2
    letI : Mono (I.map B₁.1.arrow) := hstrict₁.mono
    letI : Mono (I.map B₂.1.arrow) := hstrict₂.mono
    apply Subtype.ext
    have hEq' : Subobject.mk (I.map B₁.1.arrow) = Subobject.mk (I.map B₂.1.arrow) :=
      congrArg Subtype.val hEq
    simpa [Subobject.mk_arrow] using
      (Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
        (I.preimageIso (Subobject.isoOfMkEqMk _ _ hEq'))
        (I.map_injective (by
          simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
          exact Subobject.ofMkLEMk_comp hEq'.le)))
  have hF_mono : Monotone F := by
    intro B₁ B₂ hB
    let hstrict₁ : IsStrictMono (I.map B₁.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₁.1.arrow B₁.2
    let hstrict₂ : IsStrictMono (I.map B₂.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₂.1.arrow B₂.2
    letI : Mono (I.map B₁.1.arrow) := hstrict₁.mono
    letI : Mono (I.map B₂.1.arrow) := hstrict₂.mono
    change Subobject.mk (I.map B₁.1.arrow) ≤ Subobject.mk (I.map B₂.1.arrow)
    have hmk : Subobject.mk B₁.1.arrow ≤ Subobject.mk B₂.1.arrow := by
      simpa [Subobject.mk_arrow] using (show B₁.1 ≤ B₂.1 from hB)
    exact Subobject.mk_le_mk_of_comm (I.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk)) (by
      rw [← I.map_comp]
      exact congrArg I.map (Subobject.ofMkLEMk_comp hmk))
  exact
    (show isStrictNoetherianObject.Is X from
      ObjectProperty.is_of_prop _
        (show WellFoundedGT (StrictSubobject X) from by
          rw [wellFoundedGT_iff_monotone_chain_condition]
          intro f
          let g : ℕ →o StrictSubobject (I.obj X) :=
            ⟨fun n ↦ F (f n),
              fun i j hij ↦ hF_mono (f.2 hij)⟩
          obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
          exact ⟨n, fun m hm ↦ hF_inj (hn m hm)⟩))

theorem interval_strictFiniteLength_of_inclusion_strict
    {s₁ s₂ : Slicing C}
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsStrictArtinianObject ((ObjectProperty.ιOfLE h).obj X)]
    [IsStrictNoetherianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictArtinianObject X ∧ IsStrictNoetherianObject X :=
  ⟨interval_strictArtinianObject_of_inclusion_strict (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h,
    interval_strictNoetherianObject_of_inclusion_strict (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h⟩

theorem interval_thinFiniteLength_of_inclusion_strict
    {s₁ s₂ : Slicing C}
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    (hFinite : ∀ Y : s₂.IntervalCat C a₂ b₂,
      IsStrictArtinianObject Y ∧ IsStrictNoetherianObject Y) :
    ∀ X : s₁.IntervalCat C a₁ b₁,
      IsStrictArtinianObject X ∧ IsStrictNoetherianObject X := by
  intro X
  have hBig := hFinite ((ObjectProperty.ιOfLE h).obj X)
  letI : IsStrictArtinianObject ((ObjectProperty.ιOfLE h).obj X) := hBig.1
  letI : IsStrictNoetherianObject ((ObjectProperty.ιOfLE h).obj X) := hBig.2
  simpa using
    (interval_strictFiniteLength_of_inclusion_strict
      (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h (X := X))

theorem SectorFiniteLength.of_wide
    (σ : StabilityCondition C) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8) :
    SectorFiniteLength (C := C) σ ε₀ hε₀ hε₀2 := by
  intro t
  dsimp [SectorFiniteLength, WideSectorFiniteLength] at hWide ⊢
  intro E
  letI : Fact (t - 2 * ε₀ < t + 2 * ε₀) := ⟨by grind⟩
  letI : Fact ((t + 2 * ε₀) - (t - 2 * ε₀) ≤ 1) := ⟨by grind⟩
  letI : Fact (t - 4 * ε₀ < t + 4 * ε₀) := ⟨by grind⟩
  letI : Fact ((t + 4 * ε₀) - (t - 4 * ε₀) ≤ 1) := ⟨by grind⟩
  let hIncl :
      σ.slicing.intervalProp C (t - 2 * ε₀) (t + 2 * ε₀) ≤
        σ.slicing.intervalProp C (t - 4 * ε₀) (t + 4 * ε₀) := by
    intro F hF
    exact σ.slicing.intervalProp_mono C (by grind) (by grind) hF
  exact interval_thinFiniteLength_of_inclusion_strict
    (C := C) (s₁ := σ.slicing) (s₂ := σ.slicing)
    (a₁ := t - 2 * ε₀) (b₁ := t + 2 * ε₀)
    (a₂ := t - 4 * ε₀) (b₂ := t + 4 * ε₀) hIncl (hWide t) E

theorem interval_K0_of_strictMono
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (f : Y ⟶ X) (hf : IsStrictMono f) :
    K₀.of C X.obj = K₀.of C Y.obj + K₀.of C (cokernel f).obj := by
  simpa using
    Slicing.IntervalCat.K0_of_strictShortExact (C := C) (s := s) (a := a) (b := b)
      (interval_strictShortExact_cokernel_of_strictMono
        (C := C) (s := s) (a := a) (b := b) f hf)

section

omit [IsTriangulated C]

lemma interval_card_subobject_lt_of_ne_top
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b} {M : Subobject X}
    (hM : M ≠ ⊤) [Finite (Subobject X)] :
    Nat.card (Subobject (M : s.IntervalCat C a b)) < Nat.card (Subobject X) := by
  let φ := (Subobject.map M.arrow).obj
  haveI : Finite (Subobject (M : s.IntervalCat C a b)) :=
    Finite.of_injective φ (Subobject.map_obj_injective M.arrow)
  haveI := Fintype.ofFinite (Subobject X)
  haveI := Fintype.ofFinite (Subobject (M : s.IntervalCat C a b))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem (b := ⊤) φ
    (Subobject.map_obj_injective M.arrow) (by
    simp only [Set.mem_range, not_exists]
    intro B hB
    have hle : φ B ≤ M := by
      calc
        φ B ≤ φ ⊤ := (Subobject.map M.arrow).monotone le_top
        _ = M := by simp [φ]
    have htop_le : (⊤ : Subobject X) ≤ M := by
      simpa only [hB] using hle
    exact hM (top_le_iff.mp htop_le))

/-- Lift a subobject of an interval subobject `M` back to a subobject of the ambient
interval object `X` by composing the two defining arrows. -/
def intervalLiftSub
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) (A : Subobject (M : s.IntervalCat C a b)) : Subobject X :=
  Subobject.mk (A.arrow ≫ M.arrow)

lemma intervalLiftSub_le
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) (A : Subobject (M : s.IntervalCat C a b)) :
    intervalLiftSub (C := C) (X := X) M A ≤ M := by
  have h := Subobject.mk_le_mk_of_comm A.arrow
    (show A.arrow ≫ M.arrow = A.arrow ≫ M.arrow from rfl)
  rwa [Subobject.mk_arrow] at h

lemma intervalLiftSub_bot
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) :
    intervalLiftSub (C := C) (X := X) M (⊥ : Subobject (M : s.IntervalCat C a b)) = ⊥ := by
  apply (Subobject.mk_eq_bot_iff_zero).mpr
  simp [Subobject.bot_arrow]

lemma intervalLiftSub_ne_bot
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) {A : Subobject (M : s.IntervalCat C a b)} (hA : A ≠ ⊥) :
    intervalLiftSub (C := C) (X := X) M A ≠ ⊥ := by
  intro h
  apply hA
  rw [← Subobject.mk_arrow A]
  apply (Subobject.mk_eq_bot_iff_zero).mpr
  apply (cancel_mono M.arrow).1
  simpa [intervalLiftSub, Subobject.mk_arrow] using
    (Subobject.mk_eq_bot_iff_zero.mp h)

lemma intervalLiftSub_mono
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) {A B : Subobject (M : s.IntervalCat C a b)} (h : A ≤ B) :
    intervalLiftSub (C := C) (X := X) M A ≤ intervalLiftSub (C := C) (X := X) M B := by
  refine Subobject.mk_le_mk_of_comm (Subobject.ofLE A B h) ?_
  dsimp [intervalLiftSub]
  simp

lemma intervalLiftSub_lt
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) {A : Subobject (M : s.IntervalCat C a b)} (hA : A ≠ ⊤) :
    intervalLiftSub (C := C) (X := X) M A < M := by
  refine lt_of_le_of_ne (intervalLiftSub_le (C := C) (X := X) M A) ?_
  intro hEq
  apply hA
  apply (Subobject.map_obj_injective M.arrow)
  rw [show (Subobject.map M.arrow).obj A = intervalLiftSub (C := C) (X := X) M A by
    simpa [intervalLiftSub] using (Subobject.map_mk A.arrow M.arrow)]
  rw [show (Subobject.map M.arrow).obj (⊤ : Subobject (M : s.IntervalCat C a b)) = M by
    simp]
  exact hEq

end

lemma intervalSubobject_bot_arrow_strictMono
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} :
    IsStrictMono ((⊥ : Subobject X).arrow) := by
  let f : ((⊥ : Subobject X) : s.IntervalCat C a b) ⟶ X := (⊥ : Subobject X).arrow
  have hzero : f = 0 := by simp [f, Subobject.bot_arrow]
  letI : IsIso (cokernel.π f) := by
    rw [hzero]
    infer_instance
  apply isStrictMono_of_isLimitKernelFork
  refine KernelFork.IsLimit.ofMonoOfIsZero
    (KernelFork.ofι f (cokernel.condition f)) inferInstance ?_
  exact (isZero_zero (s.IntervalCat C a b)).of_iso Subobject.botCoeIsoZero

lemma intervalLiftSub_arrow_strictMono_of_strictMono
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X}
    (hM : IsStrictMono M.arrow) {A : Subobject (M : s.IntervalCat C a b)}
    (hA : IsStrictMono A.arrow) :
    IsStrictMono (intervalLiftSub (C := C) (X := X) M A).arrow := by
  have hcomp : IsStrictMono (A.arrow ≫ M.arrow) :=
    Slicing.IntervalCat.comp_strictMono
      (C := C) (s := s) (a := a) (b := b) A.arrow M.arrow hA hM
  simpa [intervalLiftSub] using
    (intervalSubobject_arrow_strictMono_of_strictMono
      (C := C) (s := s) (a := a) (b := b) (A.arrow ≫ M.arrow) hcomp)

section

omit [IsTriangulated C]

lemma intervalLiftSub_wPhase_eq
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    {X : s.IntervalCat C a b} (M : Subobject X)
    (A : Subobject (M : s.IntervalCat C a b)) :
    wPhaseOf
        (ssf.W
          (K₀.of C (((intervalLiftSub (C := C) (X := X) M A : Subobject X) :
            s.IntervalCat C a b).obj))) ssf.α =
      wPhaseOf (ssf.W (K₀.of C ((A : s.IntervalCat C a b).obj))) ssf.α := by
  let eI :
      ((intervalLiftSub (C := C) (X := X) M A : Subobject X) : s.IntervalCat C a b) ≅
        (A : s.IntervalCat C a b) :=
    Subobject.underlyingIso (A.arrow ≫ M.arrow)
  let eC :
      (((intervalLiftSub (C := C) (X := X) M A : Subobject X) : s.IntervalCat C a b).obj) ≅
        (A : s.IntervalCat C a b).obj :=
    (Slicing.IntervalCat.ι (C := C) (s := s) a b).mapIso eI
  simpa [eI, eC] using
    congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)

end

/-- A non-semistable thin-interval object contains a proper strict subobject of strictly larger
`W`-phase. This is the paper-faithful first step in Bridgeland's descent argument: the witness
is extracted directly from the failure of the semistability triangle test, not by finite
enumeration of subobjects. -/
theorem SkewedStabilityFunction.exists_phase_gt_strictSubobject_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α)) :
    ∃ B : Subobject X, B ≠ ⊥ ∧ B ≠ ⊤ ∧ IsStrictMono B.arrow ∧
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
  let phaseObj : σ.slicing.IntervalCat C a b → ℝ := fun Y ↦
    wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hX_obj : ¬IsZero X.obj := by
    intro hZ
    exact hX (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hW_X : ssf.W (K₀.of C X.obj) ≠ 0 := hW_interval X.property hX_obj
  have htri :
      ¬ ∀ ⦃K Q : C⦄ ⦃f₁ : K ⟶ X.obj⦄ ⦃f₂ : X.obj ⟶ Q⦄ ⦃f₃ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
          Triangle.mk f₁ f₂ f₃ ∈ distTriang C →
          σ.slicing.intervalProp C a b K →
          σ.slicing.intervalProp C a b Q →
          ¬IsZero K →
          wPhaseOf (ssf.W (K₀.of C K)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
    intro hsem
    exact hns ⟨X.property, hX_obj, hW_X, rfl,
      fun {K Q} {f₁} {f₂} {f₃} hT hK hQ hKne ↦ hsem hT hK hQ hKne⟩
  push_neg at htri
  obtain ⟨K, Q, f₁, f₂, f₃, hT, hK, hQ, hKne, hgt⟩ := htri
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
  have hB_ne_bot : B ≠ ⊥ := by
    intro hB
    have hBZ : IsZero (B : σ.slicing.IntervalCat C a b) :=
      (intervalSubobject_isZero_iff_eq_bot
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) B).mpr hB
    exact hKne (((σ.slicing.intervalProp C a b).ι).map_isZero
      (hBZ.of_iso (Subobject.underlyingIso iKX).symm))
  have hB_strict : IsStrictMono B.arrow := by
    simpa [B] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) iKX hK_strict)
  have hB_ne_top : B ≠ ⊤ := by
    intro hB
    have hIsoK :
        phaseObj KI = phaseObj ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) := by
      let eI :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) ≅ KI :=
        eqToIso (by
          simpa [B] using congrArg
            (fun Z : Subobject X => (Z : σ.slicing.IntervalCat C a b)) hB.symm) ≪≫
          Subobject.underlyingIso iKX
      let eC :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
      simpa [phaseObj] using
        congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC).symm
    have hIsoTop :
        phaseObj ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) = phaseObj X := by
      let eC :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj ≅ X.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (asIso (⊤ : Subobject X).arrow)
      simpa [phaseObj] using
        congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
    have hEqPhase : phaseObj KI = phaseObj X := hIsoK.trans hIsoTop
    have : phaseObj X < phaseObj X := by
      simpa [phaseObj, KI] using hgt.trans_eq hEqPhase
    exact lt_irrefl _ this
  have hB_phase_eq :
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α =
        wPhaseOf (ssf.W (K₀.of C K)) ssf.α := by
    let eC :
        (B : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
      (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
        (Subobject.underlyingIso iKX)
    simpa [B, KI] using
      congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
  refine ⟨B, hB_ne_bot, hB_ne_top, hB_strict, ?_⟩
  rwa [hB_phase_eq]

/-- The quotient induced by a lifted subobject morphism is canonically identified with the
quotient of the original subobject morphism inside the smaller interval object. -/
def intervalLiftSubCokernelIso
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)] {X : s.IntervalCat C a b}
    (M : Subobject X) {A B : Subobject (M : s.IntervalCat C a b)} (h : A ≤ B) :
    cokernel (Subobject.ofLE
      (intervalLiftSub (C := C) (X := X) M A) (intervalLiftSub (C := C) (X := X) M B)
      (intervalLiftSub_mono (C := C) (X := X) M h)) ≅
      cokernel (Subobject.ofLE A B h) := by
  let fLift := Subobject.ofLE
    (intervalLiftSub (C := C) (X := X) M A)
    (intervalLiftSub (C := C) (X := X) M B)
    (intervalLiftSub_mono (C := C) (X := X) M h)
  let fBase := Subobject.ofLE A B h
  let eA :
      ((intervalLiftSub (C := C) (X := X) M A : Subobject X) : s.IntervalCat C a b) ≅
        (A : s.IntervalCat C a b) := Subobject.underlyingIso (A.arrow ≫ M.arrow)
  let eB :
      ((intervalLiftSub (C := C) (X := X) M B : Subobject X) : s.IntervalCat C a b) ≅
        (B : s.IntervalCat C a b) := Subobject.underlyingIso (B.arrow ≫ M.arrow)
  have hwBase : fBase ≫ (B.arrow ≫ M.arrow) = A.arrow ≫ M.arrow := by
    change Subobject.ofLE A B h ≫ (B.arrow ≫ M.arrow) = A.arrow ≫ M.arrow
    rw [← Category.assoc]
    exact congrArg (fun k => k ≫ M.arrow) (Subobject.ofLE_arrow h)
  have hArrow :
      fLift = eA.hom ≫ fBase ≫ eB.inv := by
    simpa [intervalLiftSub, eA, eB, Category.assoc] using
      (Subobject.ofLE_mk_le_mk_of_comm
        fBase
        hwBase :
          Subobject.ofLE
              (Subobject.mk (A.arrow ≫ M.arrow))
              (Subobject.mk (B.arrow ≫ M.arrow))
              (Subobject.mk_le_mk_of_comm (Subobject.ofLE A B h)
                hwBase) =
            (Subobject.underlyingIso (A.arrow ≫ M.arrow)).hom ≫
              fBase ≫
                (Subobject.underlyingIso (B.arrow ≫ M.arrow)).inv)
  have hw :
      fLift ≫ eB.hom = eA.hom ≫ fBase := by
    rw [hArrow]
    simp
  exact cokernel.mapIso (f := fLift) (f' := fBase) eA eB hw

/-- Among the proper strict kernels of a non-semistable interval object, there is one whose
strict quotient has minimal `W`-phase, and among those minimal-phase kernels we may choose one
that is maximal for inclusion. This is the quotient-recursion selection step for Phase 3. -/
theorem SkewedStabilityFunction.exists_minPhase_maximal_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    [Finite (Subobject X)] :
    ∃ M : Subobject X, M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
      (∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
        wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) ∧
      (∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow → M < B →
        wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) := by
  let phaseQ : Subobject X → ℝ := fun B ↦
    wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α
  let phaseObj : σ.slicing.IntervalCat C a b → ℝ := fun Y ↦
    wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hX_obj : ¬IsZero X.obj := by
    intro hZ
    exact hX (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hW_X : ssf.W (K₀.of C X.obj) ≠ 0 := hW_interval X.property hX_obj
  have htri :
      ¬ ∀ ⦃K Q : C⦄ ⦃f₁ : K ⟶ X.obj⦄ ⦃f₂ : X.obj ⟶ Q⦄ ⦃f₃ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
          Triangle.mk f₁ f₂ f₃ ∈ distTriang C →
          σ.slicing.intervalProp C a b K →
          σ.slicing.intervalProp C a b Q →
          ¬IsZero K →
          wPhaseOf (ssf.W (K₀.of C K)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
    intro hsem
    exact hns ⟨X.property, hX_obj, hW_X, rfl,
      fun {K Q} {f₁} {f₂} {f₃} hT hK hQ hKne ↦ hsem hT hK hQ hKne⟩
  push_neg at htri
  obtain ⟨K, Q, f₁, f₂, f₃, hT, hK, hQ, hKne, hgt⟩ := htri
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
  have hB_strict : IsStrictMono B.arrow := by
    simpa [B] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) iKX hK_strict)
  have hB_ne_top : B ≠ ⊤ := by
    intro hB
    have hIsoK :
        phaseObj KI = phaseObj ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) := by
      let eI :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) ≅ KI :=
        eqToIso (by
          simpa [B] using congrArg
            (fun Z : Subobject X => (Z : σ.slicing.IntervalCat C a b)) hB.symm) ≪≫
          Subobject.underlyingIso iKX
      let eC :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
      simpa [phaseObj] using
        congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC).symm
    have hIsoTop :
        phaseObj ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) = phaseObj X := by
      let eC :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj ≅ X.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (asIso (⊤ : Subobject X).arrow)
      simpa [phaseObj] using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
    have hEqPhase : phaseObj KI = phaseObj X := hIsoK.trans hIsoTop
    have hEqPhase' :
        wPhaseOf (ssf.W (K₀.of C K)) ssf.α =
          wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
      simpa [phaseObj, KI] using hEqPhase
    simp [hEqPhase'] at hgt
  let T : Set (Subobject X) := {B | B ≠ ⊤ ∧ IsStrictMono B.arrow}
  have hT_ne : T.Nonempty := ⟨B, hB_ne_top, hB_strict⟩
  have hT_fin : T.Finite := Set.toFinite _
  obtain ⟨M₀, hM₀T, hM₀min⟩ := Set.exists_min_image T phaseQ hT_fin hT_ne
  let S : Set (Subobject X) := {B | B ∈ T ∧ phaseQ B = phaseQ M₀}
  have hS_ne : S.Nonempty := ⟨M₀, hM₀T, rfl⟩
  have hS_fin : S.Finite := Set.toFinite _
  obtain ⟨M, ⟨hMT, hM_phase⟩, hM_max⟩ := hS_fin.exists_maximal hS_ne
  refine ⟨M, hMT.1, hMT.2, ?_, ?_⟩
  · intro B hB hB_strict
    change phaseQ M ≤ phaseQ B
    rw [hM_phase]
    exact hM₀min B ⟨hB, hB_strict⟩
  · intro B hB hB_strict hMB
    have hBT : B ∈ T := ⟨hB, hB_strict⟩
    have hle : phaseQ M ≤ phaseQ B := by
      rw [hM_phase]
      exact hM₀min B hBT
    exact lt_of_le_of_ne hle (fun hEq ↦
      absurd (hM_max ⟨hBT, hEq.symm.trans hM_phase⟩ hMB.le) (not_le_of_gt hMB))

/-- Among the proper strict kernels of a non-semistable interval object, there is one whose
strict quotient has minimal `W`-phase, and among the kernels achieving that minimal quotient
phase we may choose one that is minimal for inclusion. This is the mdq-oriented selection
step needed to force strict phase drop in the kernel recursion. -/
theorem SkewedStabilityFunction.exists_minPhase_minimal_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    [Finite (Subobject X)] :
    ∃ M : Subobject X, M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
      (∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
        wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) ∧
      (∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow → B < M →
        wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) := by
  let phaseQ : Subobject X → ℝ := fun B ↦
    wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α
  obtain ⟨M₀, hM₀_top, hM₀_strict, hM₀_min, _⟩ :=
    ssf.exists_minPhase_maximal_strictKernel
      (C := C) (σ := σ) (a := a) (b := b) hX hW_interval hns
  let T : Set (Subobject X) := {B | B ≠ ⊤ ∧ IsStrictMono B.arrow}
  let S : Set (Subobject X) := {B | B ∈ T ∧ phaseQ B = phaseQ M₀}
  have hS_ne : S.Nonempty := ⟨M₀, ⟨hM₀_top, hM₀_strict⟩, rfl⟩
  have hS_fin : S.Finite := Set.toFinite _
  obtain ⟨M, ⟨hMT, hM_phase⟩, hM_min⟩ := hS_fin.exists_minimal hS_ne
  refine ⟨M, hMT.1, hMT.2, ?_, ?_⟩
  · intro B hB hB_strict
    change phaseQ M ≤ phaseQ B
    rw [hM_phase]
    exact hM₀_min B hB hB_strict
  · intro B hB hB_strict hBM
    have hBT : B ∈ T := ⟨hB, hB_strict⟩
    have hle : phaseQ M ≤ phaseQ B := by
      rw [hM_phase]
      exact hM₀_min B hB hB_strict
    exact lt_of_le_of_ne hle (fun hEq ↦
      absurd (hM_min ⟨hBT, hEq.symm.trans hM_phase⟩ hBM.le) (not_le_of_gt hBM))

/-- Among the nonzero strict subobjects of a thin-interval object, there is one with maximal
W-phase, and among those maximal-phase candidates we may choose one that is maximal for
inclusion. This is the strict-subobject selection step needed for the thin-interval HN
recursion. -/
theorem SkewedStabilityFunction.exists_maxPhase_maximal_strictSubobject_of_finite
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hT_fin : Set.Finite {B : Subobject X | B ≠ ⊥ ∧ IsStrictMono B.arrow}) :
    ∃ M : Subobject X, M ≠ ⊥ ∧ IsStrictMono M.arrow ∧
      (∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      (∀ B : Subobject X, IsStrictMono B.arrow → M < B →
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) := by
  let phase : Subobject X → ℝ := fun B ↦
    wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α
  let T : Set (Subobject X) := {B | B ≠ ⊥ ∧ IsStrictMono B.arrow}
  have hT_ne : T.Nonempty := by
    refine ⟨⊤,
      intervalSubobject_top_ne_bot_of_not_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hX, ?_⟩
    exact isStrictMono_of_isIso
  have hT_fin' : T.Finite := by
    simpa [T] using hT_fin
  obtain ⟨M₀, hM₀T, hM₀max⟩ := Set.exists_max_image T phase hT_fin' hT_ne
  let S : Set (Subobject X) := {B | B ∈ T ∧ phase B = phase M₀}
  have hS_ne : S.Nonempty := ⟨M₀, hM₀T, rfl⟩
  have hS_fin : S.Finite := hT_fin'.subset (by
    intro B hB
    exact hB.1)
  obtain ⟨M, ⟨hMT, hM_phase⟩, hM_max⟩ := hS_fin.exists_maximal hS_ne
  refine ⟨M, hMT.1, hMT.2, ?_, ?_⟩
  · intro B hB hBstrict
    change phase B ≤ phase M
    rw [hM_phase]
    exact hM₀max B ⟨hB, hBstrict⟩
  · intro B hBstrict hMB
    have hBT : B ∈ T := ⟨ne_bot_of_gt hMB, hBstrict⟩
    have hle : phase B ≤ phase M := by
      rw [hM_phase]
      exact hM₀max B hBT
    change phase B < phase M
    exact lt_of_le_of_ne hle (fun hEq ↦
      absurd (hM_max ⟨hBT, hEq.trans hM_phase⟩ hMB.le) (not_le_of_gt hMB))

/-- Among the nonzero strict subobjects of a thin-interval object, there is one with maximal
W-phase, and among those maximal-phase candidates we may choose one that is maximal for
inclusion. This is the strict-subobject selection step needed for the thin-interval HN
recursion. -/
theorem SkewedStabilityFunction.exists_maxPhase_maximal_strictSubobject
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    [Finite (Subobject X)] :
    ∃ M : Subobject X, M ≠ ⊥ ∧ IsStrictMono M.arrow ∧
      (∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      (∀ B : Subobject X, IsStrictMono B.arrow → M < B →
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) :=
  ssf.exists_maxPhase_maximal_strictSubobject_of_finite
    (C := C) (σ := σ) (a := a) (b := b) (X := X) hX (Set.toFinite _)

/-- A nonzero strict subobject that is maximal for W-phase among all nonzero strict subobjects
is W-semistable. -/
theorem SkewedStabilityFunction.semistable_of_maxPhase_strictSubobject
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne : M ≠ ⊥) (hM_strict : IsStrictMono M.arrow)
    (hM_max : ∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
      (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) := by
  let phaseObj : σ.slicing.IntervalCat C a b → ℝ := fun Y ↦
    wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hMint_ne : ¬IsZero (M : σ.slicing.IntervalCat C a b) :=
    intervalSubobject_not_isZero_of_ne_bot (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne
  have hMobj_ne : ¬IsZero (M : σ.slicing.IntervalCat C a b).obj := by
    intro hZ
    exact hMint_ne <|
      Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ
  refine ⟨(M : σ.slicing.IntervalCat C a b).property, hMobj_ne,
    hW_interval (M : σ.slicing.IntervalCat C a b).property hMobj_ne, rfl, ?_⟩
  intro K Q f₁ f₂ f₃ hT hK hQ hKne
  let KI : σ.slicing.IntervalCat C a b := ⟨K, hK⟩
  let QI : σ.slicing.IntervalCat C a b := ⟨Q, hQ⟩
  let iKM : KI ⟶ (M : σ.slicing.IntervalCat C a b) := ObjectProperty.homMk f₁
  let gMQ : (M : σ.slicing.IntervalCat C a b) ⟶ QI := ObjectProperty.homMk f₂
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk iKM gMQ (by
      ext
      simpa [iKM, gMQ] using comp_distTriang_mor_zero₁₂ _ hT)
  have hT' : Triangle.mk S.f.hom S.g.hom f₃ ∈ distTriang C := by
    simpa [S, iKM, gMQ] using hT
  have hK_strict : IsStrictMono iKM :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b) hT').1
  have hComp_strict : IsStrictMono (iKM ≫ M.arrow) :=
    Slicing.IntervalCat.comp_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) iKM M.arrow hK_strict hM_strict
  haveI : Mono (iKM ≫ M.arrow) := hComp_strict.mono
  let B : Subobject X := Subobject.mk (iKM ≫ M.arrow)
  have hKI_ne : ¬IsZero KI := by
    intro hZ
    exact hKne (((σ.slicing.intervalProp C a b).ι).map_isZero hZ)
  have hB_ne : B ≠ ⊥ := by
    intro hB
    have hzero : iKM ≫ M.arrow = 0 :=
      (Subobject.mk_eq_bot_iff_zero).mp
        (show Subobject.mk (iKM ≫ M.arrow) = ⊥ by simpa [B] using hB)
    have hId : 𝟙 KI = 0 := by
      apply (cancel_mono (iKM ≫ M.arrow)).1
      rw [hzero]
      simp
    exact hKI_ne ((IsZero.iff_id_eq_zero KI).mpr hId)
  have hB_strict : IsStrictMono B.arrow := by
    let e := Subobject.underlyingIso (iKM ≫ M.arrow)
    have he_strict : IsStrictMono e.hom := isStrictMono_of_isIso
    have htmp : IsStrictMono (e.hom ≫ (iKM ≫ M.arrow)) :=
      Slicing.IntervalCat.comp_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) e.hom (iKM ≫ M.arrow) he_strict hComp_strict
    have hArrow : e.hom ≫ (iKM ≫ M.arrow) = B.arrow :=
      Subobject.underlyingIso_hom_comp_eq_mk (iKM ≫ M.arrow)
    rw [← hArrow]
    exact htmp
  have hPhaseB : phaseObj KI ≤ phaseObj (M : σ.slicing.IntervalCat C a b) := by
    have hPhaseSub : phaseObj (B : σ.slicing.IntervalCat C a b) ≤
        phaseObj (M : σ.slicing.IntervalCat C a b) :=
      hM_max B hB_ne hB_strict
    have hIsoK :
        phaseObj KI = phaseObj (B : σ.slicing.IntervalCat C a b) := by
      let eC : (B : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (Subobject.underlyingIso (iKM ≫ M.arrow))
      simpa [phaseObj] using congrArg (fun x => wPhaseOf (ssf.W x) ssf.α)
        (K₀.of_iso C eC).symm
    exact hIsoK.trans_le hPhaseSub
  simpa [phaseObj, KI]
    using hPhaseB

end

end CategoryTheory.Triangulated
