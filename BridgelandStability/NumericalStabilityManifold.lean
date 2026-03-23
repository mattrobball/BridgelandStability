/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.LocalHomeomorphism
public import BridgelandStability.EulerForm
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.LocalAtTarget

/-!
# Numerical Stability Manifolds

This file isolates the manifold-level packaging behind Bridgeland's Corollary 1.3.

The current statement of `bridgelandCorollary_1_3` only exports a local homeomorphism into an
additive subgroup with a bare topology. For the actual complex-manifold corollary, we want to
separate the work into the following stages:

1. Produce a topological complex-linear local model for each connected component of numerical
   stability conditions.
2. Replace that topological model by a finite-dimensional normed complex model space.
3. Build the `ChartedSpace` and `IsManifold` structures from the resulting local homeomorphism.

The declarations in this file are the intended interfaces for those steps. Once they are proved,
Corollary 1.3 should be mechanical assembly.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped Manifold Topology

universe w v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- The type of numerical stability conditions in a fixed connected component. -/
abbrev NumericalComponent (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (NumericalStabilityCondition C χ)) :=
  {σ : NumericalStabilityCondition C χ // ConnectedComponents.mk σ = cc}

/-- The ambient complex charge space for numerical stability conditions. -/
abbrev NumericalChargeSpace (χ : K₀ C →+ K₀ C →+ ℤ) :=
  NumericalK₀ C χ →+ ℂ

/-- The ambient Bridgeland charge space `Hom_ℤ(K₀(D), ℂ)` before passing to numerical charges. -/
abbrev AmbientChargeSpace :=
  K₀ C →+ ℂ

/-- The quotient map `K₀(D) → N(D)`. -/
abbrev numericalQuotientMap (χ : K₀ C →+ K₀ C →+ ℤ) :
    K₀ C →+ NumericalK₀ C χ :=
  QuotientAddGroup.mk' (eulerFormRad C χ)

/-- Precomposition with the quotient map `K₀(D) → N(D)`. -/
def precomposeNumericalQuotient (χ : K₀ C →+ K₀ C →+ ℤ) :
    NumericalChargeSpace C χ →ₗ[ℂ] AmbientChargeSpace C where
  toFun := fun Z' => Z'.comp (numericalQuotientMap C χ)
  map_add' Z₁ Z₂ := by
    ext x
    rfl
  map_smul' a Z := by
    ext x
    rfl

/-- The subspace of ambient charges that factor through `N(D)`. -/
def numericalFactorSubmodule (χ : K₀ C →+ K₀ C →+ ℤ) :
    Submodule ℂ (AmbientChargeSpace C) :=
  LinearMap.range (precomposeNumericalQuotient C χ)

section

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

@[simp]
theorem mem_numericalFactorSubmodule_iff {χ : K₀ C →+ K₀ C →+ ℤ} {Z : AmbientChargeSpace C} :
    Z ∈ numericalFactorSubmodule C χ ↔
      ∃ Z' : NumericalChargeSpace C χ, Z = Z'.comp (numericalQuotientMap C χ) := by
  rw [numericalFactorSubmodule, LinearMap.mem_range]
  constructor
  · rintro ⟨Z', rfl⟩
    exact ⟨Z', rfl⟩
  · rintro ⟨Z', rfl⟩
    exact ⟨Z', rfl⟩

/-- `Hom_ℤ(N(D), ℂ)` identifies with the subspace of ambient charges factoring through `N(D)`. -/
noncomputable def numericalChargeSpaceEquivFactorSubmodule (χ : K₀ C →+ K₀ C →+ ℤ) :
    NumericalChargeSpace C χ ≃ₗ[ℂ] numericalFactorSubmodule C χ :=
  LinearEquiv.ofInjective (precomposeNumericalQuotient C χ) <| by
    intro Z₁ Z₂ h
    ext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (eulerFormRad C χ) x
    exact congrArg (fun f : AmbientChargeSpace C => f y) h

end

/-- A numerical stability condition has ambient central charge in the numerical factor subspace. -/
theorem NumericalStabilityCondition.charge_mem_numericalFactorSubmodule
    {χ : K₀ C →+ K₀ C →+ ℤ} (σ : NumericalStabilityCondition C χ) :
    σ.toStabilityCondition.Z ∈ numericalFactorSubmodule C χ := by
  rcases σ.factors with ⟨Z', hZ'⟩
  rw [mem_numericalFactorSubmodule_iff]
  exact ⟨Z', hZ'⟩

theorem NumericalStabilityCondition.ext_toStabilityCondition
    {χ : K₀ C →+ K₀ C →+ ℤ} {σ τ : NumericalStabilityCondition C χ}
    (h : σ.toStabilityCondition = τ.toStabilityCondition) :
    σ = τ := by
  cases σ
  cases τ
  cases h
  simp

/-- The inclusion of numerical stability conditions into ordinary stability conditions is continuous
for the induced topology. -/
theorem NumericalStabilityCondition.continuous_toStabilityCondition
    (χ : K₀ C →+ K₀ C →+ ℤ) :
    Continuous
      (NumericalStabilityCondition.toStabilityCondition :
        NumericalStabilityCondition C χ → StabilityCondition C) :=
  continuous_induced_dom

/-- The map on connected components induced by the inclusion
`Stab_N(D) ⟶ Stab(D)`. -/
noncomputable def NumericalStabilityCondition.ambientComponentMap
    (χ : K₀ C →+ K₀ C →+ ℤ) :
    ConnectedComponents (NumericalStabilityCondition C χ) →
      ConnectedComponents (StabilityCondition C) :=
  (NumericalStabilityCondition.continuous_toStabilityCondition (C := C) χ).connectedComponentsMap

@[simp]
theorem NumericalStabilityCondition.ambientComponentMap_apply
    (χ : K₀ C →+ K₀ C →+ ℤ) (σ : NumericalStabilityCondition C χ) :
    NumericalStabilityCondition.ambientComponentMap (C := C) χ (ConnectedComponents.mk σ) =
      ConnectedComponents.mk σ.toStabilityCondition := by
  simp [NumericalStabilityCondition.ambientComponentMap, Continuous.connectedComponentsMap]

/-- Restricting a local homeomorphism to the preimage of an arbitrary subset of the codomain.

This is the general topological ingredient behind the restriction step from Bridgeland's Theorem
1.2 to Corollary 1.3. -/
theorem IsLocalHomeomorph.codRestrict_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) (s : Set Y) :
    @IsLocalHomeomorph {x : X // f x ∈ s} s inferInstance inferInstance
      (fun x => ⟨f x.1, x.2⟩) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  obtain ⟨e, hxe, hfe⟩ := hf x.1
  let U : Set {x : X // f x ∈ s} := Subtype.val ⁻¹' e.source
  refine ⟨U, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ ?_
    · exact e.open_source.preimage continuous_subtype_val
    · exact hxe
  · let comm : U ≃ₜ {y : e.source // e y.1 ∈ s} := {
      toFun := fun y => ⟨⟨y.1.1, y.2⟩, by simpa [hfe] using y.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, by simpa [hfe] using y.2⟩, y.1.2⟩
      left_inv y := by
        cases y
        rfl
      right_inv y := by
        cases y
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop
      }
    let emb : Topology.IsOpenEmbedding (s.restrictPreimage (e.source.restrict e)) :=
      Set.restrictPreimage_isOpenEmbedding s e.isOpenEmbedding_restrict
    have hcomp :
        s.restrictPreimage (e.source.restrict e) ∘ comm =
          U.restrict (fun x : {x : X // f x ∈ s} => (⟨f x.1, x.2⟩ : s)) := by
      funext y
      apply Subtype.ext
      have hy : (comm y).1.1 = y.1.1 := rfl
      simpa [hfe] using congrArg e hy
    simpa [hcomp] using emb.comp comm.isOpenEmbedding

section

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Numerical finiteness implies that the numerical charge space is finite-dimensional over `ℂ`.
This is the algebraic input behind Bridgeland's Corollary 1.3. -/
theorem numericalChargeSpace_finiteDimensional (χ : K₀ C →+ K₀ C →+ ℤ)
    [NumericallyFinite C χ] :
    FiniteDimensional ℂ (NumericalChargeSpace C χ) := by
  let A := NumericalK₀ C χ
  have hfg : AddGroup.FG A := NumericallyFinite.fg (C := C) (χ := χ)
  have htopfg : (⊤ : AddSubgroup A).FG := (AddGroup.fg_def).mp hfg
  rcases (AddSubgroup.fg_iff_exists_fin_addMonoidHom (H := (⊤ : AddSubgroup A))).mp htopfg with
    ⟨n, g, hg_range⟩
  have hg : Function.Surjective g := by
    intro x
    have hx : x ∈ AddMonoidHom.range g := by
      rw [hg_range]
      simp
    rcases hx with ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  let precomp : NumericalChargeSpace C χ →ₗ[ℂ] ((Fin n → ℤ) →+ ℂ) := {
    toFun := fun Z => Z.comp g
    map_add' := by
      intro Z₁ Z₂
      ext x
      rfl
    map_smul' := by
      intro a Z
      ext x
      rfl }
  have hprecomp : Function.Injective precomp := by
    intro Z₁ Z₂ hZ
    ext x
    obtain ⟨y, rfl⟩ := hg x
    exact DFunLike.congr_fun hZ y
  let eval : ((Fin n → ℤ) →+ ℂ) →ₗ[ℂ] (Fin n → ℂ) := {
    toFun := fun Z i => Z (Pi.single i 1)
    map_add' := by
      intro Z₁ Z₂
      ext i
      rfl
    map_smul' := by
      intro a Z
      ext i
      rfl }
  have heval : Function.Injective eval := by
    intro Z₁ Z₂ hZ
    apply AddMonoidHom.toIntLinearMap_injective
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro i
    simpa [eval, Pi.basisFun_apply] using congr_fun hZ i
  exact FiniteDimensional.of_injective (eval ∘ₗ precomp) (heval.comp hprecomp)

end

variable (k : Type w) [Field k]

/-- The part of `Stab_N(D)` lying over a fixed connected component of `Stab(D)`. -/
abbrev NumericalAmbientLocus (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (StabilityCondition C)) :=
  {σ : NumericalStabilityCondition C χ //
    ConnectedComponents.mk σ.toStabilityCondition = cc}

/-- The ambient numerical locus is open inside `Stab_N(D)` because ambient connected components
of `StabilityCondition C` are open. -/
theorem isOpen_numericalAmbientLocus (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (StabilityCondition C)) :
    IsOpen {σ : NumericalStabilityCondition C χ |
      ConnectedComponents.mk σ.toStabilityCondition = cc} := by
  let σ₀ := componentRep C cc
  have hσ₀ : ConnectedComponents.mk σ₀ = cc := by
    dsimp [σ₀]
    exact mk_componentRep C cc
  have hopen : IsOpen (connectedComponent σ₀) := stabilityCondition_isOpen_connectedComponent C σ₀
  have hset :
      {σ : NumericalStabilityCondition C χ |
        ConnectedComponents.mk σ.toStabilityCondition = cc} =
        NumericalStabilityCondition.toStabilityCondition ⁻¹' connectedComponent σ₀ := by
    ext σ
    rw [Set.mem_setOf_eq, Set.mem_preimage, ← ConnectedComponents.coe_eq_coe']
    constructor
    · intro h
      exact h.trans hσ₀.symm
    · intro h
      exact h.trans hσ₀
  rw [hset]
  exact hopen.preimage (NumericalStabilityCondition.continuous_toStabilityCondition (C := C) χ)

namespace ComponentTopologicalLinearLocalModel

variable {cc : ConnectedComponents (StabilityCondition C)}

/-- The numerical part of the ambient codomain `V(Σ)`, cut out as a submodule of `V(Σ)` itself.

Keeping this codomain inside `M.V` avoids any induced-instance transport on the numerical charge
side; it inherits its normed complex-vector-space structure directly as a submodule. -/
def ambientNumericalFactorSubmodule (χ : K₀ C →+ K₀ C →+ ℤ)
    (M : ComponentTopologicalLinearLocalModel C cc) :
    Submodule ℂ M.V :=
  (numericalFactorSubmodule C χ).comap M.V.subtype

/-- The charge map on the ambient numerical locus `Σ ∩ Stab_N(D)`. -/
def ambientNumericalChargeMap (χ : K₀ C →+ K₀ C →+ ℤ)
    (M : ComponentTopologicalLinearLocalModel C cc) :
    NumericalAmbientLocus C χ cc → ambientNumericalFactorSubmodule C χ M :=
  fun σ => ⟨⟨σ.1.toStabilityCondition.Z, M.mem_charge _ σ.2⟩, by
    change σ.1.toStabilityCondition.Z ∈ numericalFactorSubmodule C χ
    exact σ.1.charge_mem_numericalFactorSubmodule⟩

/-- The ambient numerical locus is exactly the preimage of the numerical codomain subset under the
ambient component charge map. -/
noncomputable def numericalAmbientLocusHomeomorphChargePreimage
    (χ : K₀ C →+ K₀ C →+ ℤ) (M : ComponentTopologicalLinearLocalModel C cc) :
    NumericalAmbientLocus C χ cc ≃ₜ
      {x : componentStabilityCondition C cc //
        ComponentTopologicalLinearLocalModel.chargeMap (C := C) M x ∈
          ambientNumericalFactorSubmodule C χ M} where
  toFun := fun σ => ⟨⟨σ.1.toStabilityCondition, σ.2⟩, by
    change σ.1.toStabilityCondition.Z ∈ numericalFactorSubmodule C χ
    exact σ.1.charge_mem_numericalFactorSubmodule⟩
  invFun := fun x => by
    have hx : x.1.1.Z ∈ numericalFactorSubmodule C χ := by
      change (((ComponentTopologicalLinearLocalModel.chargeMap (C := C) M x.1 : M.V) :
        AmbientChargeSpace C) ∈ numericalFactorSubmodule C χ)
      exact x.2
    have hx' := (mem_numericalFactorSubmodule_iff (C := C) (χ := χ) (Z := x.1.1.Z)).mp hx
    exact ⟨⟨x.1.1, ⟨Classical.choose hx', Classical.choose_spec hx'⟩⟩, x.1.2⟩
  left_inv σ := by
    apply Subtype.ext
    exact NumericalStabilityCondition.ext_toStabilityCondition (C := C) rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk
      (Continuous.subtype_mk
        ((NumericalStabilityCondition.continuous_toStabilityCondition (C := C) χ).comp
          continuous_subtype_val)
        (fun σ => σ.2))
      (fun σ => by
        change σ.1.toStabilityCondition.Z ∈ numericalFactorSubmodule C χ
        exact σ.1.charge_mem_numericalFactorSubmodule)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ (fun x => x.1.2)
    refine continuous_induced_rng.2 ?_
    exact continuous_subtype_val.comp continuous_subtype_val

/-- Bridgeland's Theorem 1.2 restricted to the ambient numerical locus `Σ ∩ Stab_N(D)`. -/
theorem ambientNumericalChargeMap_isLocalHomeomorph (χ : K₀ C →+ K₀ C →+ ℤ)
    (M : ComponentTopologicalLinearLocalModel C cc) :
    IsLocalHomeomorph (ambientNumericalChargeMap (C := C) χ M) := by
  let e := numericalAmbientLocusHomeomorphChargePreimage (C := C) χ M
  let hf :=
    (IsLocalHomeomorph.codRestrict_preimage M.isLocalHomeomorph_chargeMap
      (s := ambientNumericalFactorSubmodule (C := C) χ M))
  simpa [ambientNumericalChargeMap, ComponentTopologicalLinearLocalModel.chargeMap, e]
    using hf.comp e.isLocalHomeomorph

end ComponentTopologicalLinearLocalModel

/-- A chosen representative of a connected component of numerical stability conditions. -/
def numericalComponentRep (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (NumericalStabilityCondition C χ)) :
    NumericalStabilityCondition C χ :=
  Classical.choose cc.exists_rep

@[simp] theorem mk_numericalComponentRep (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (NumericalStabilityCondition C χ)) :
    ConnectedComponents.mk (numericalComponentRep C χ cc) = cc :=
  Classical.choose_spec cc.exists_rep

/-- The chosen representative of a numerical connected component, regarded inside the ambient
numerical locus. -/
abbrev numericalAmbientLocusRep (χ : K₀ C →+ K₀ C →+ ℤ)
    (cc : ConnectedComponents (NumericalStabilityCondition C χ)) :
    NumericalAmbientLocus C χ (NumericalStabilityCondition.ambientComponentMap (C := C) χ cc) :=
  ⟨numericalComponentRep C χ cc, by
    simpa [mk_numericalComponentRep (C := C) χ cc] using
      (NumericalStabilityCondition.ambientComponentMap_apply
        (C := C) χ (numericalComponentRep C χ cc)).symm⟩

/-- Inside `Stab_N(D)`, the connected component `cc` is exactly the connected component of a
chosen representative inside the ambient restriction `Σ ∩ Stab_N(D)`. -/
theorem numericalComponent_set_eq_connectedComponentIn_numericalAmbientLocus
    {χ : K₀ C →+ K₀ C →+ ℤ}
    (cc : ConnectedComponents (NumericalStabilityCondition C χ)) :
    {σ : NumericalStabilityCondition C χ | ConnectedComponents.mk σ = cc} =
      connectedComponentIn
        {σ : NumericalStabilityCondition C χ |
          ConnectedComponents.mk σ.toStabilityCondition =
            NumericalStabilityCondition.ambientComponentMap (C := C) χ cc}
        (numericalComponentRep C χ cc) := by
  let ambientcc := NumericalStabilityCondition.ambientComponentMap (C := C) χ cc
  let x0 := numericalComponentRep C χ cc
  let F : Set (NumericalStabilityCondition C χ) := {σ |
    ConnectedComponents.mk σ.toStabilityCondition = ambientcc}
  ext σ
  constructor
  · intro hσ
    have hx0F : x0 ∈ F := by
      change ConnectedComponents.mk x0.toStabilityCondition = ambientcc
      simpa [ambientcc, x0, mk_numericalComponentRep (C := C) χ cc] using
        (NumericalStabilityCondition.ambientComponentMap_apply (C := C) χ x0).symm
    have hσconn : σ ∈ connectedComponent x0 := by
      apply (ConnectedComponents.coe_eq_coe').1
      rw [hσ, mk_numericalComponentRep (C := C) χ cc]
    have hsub : connectedComponent x0 ⊆ F := by
      intro τ hτ
      have hτcc : ConnectedComponents.mk τ = cc := by
        rw [← mk_numericalComponentRep (C := C) χ cc]
        exact (ConnectedComponents.coe_eq_coe').2 hτ
      change ConnectedComponents.mk τ.toStabilityCondition = ambientcc
      rw [← NumericalStabilityCondition.ambientComponentMap_apply (C := C) χ τ, hτcc]
    exact (isPreconnected_connectedComponent.subset_connectedComponentIn
      mem_connectedComponent hsub) hσconn
  · intro hσ
    have hσconn : σ ∈ connectedComponent x0 := by
      exact isPreconnected_connectedComponentIn.subset_connectedComponent
        (mem_connectedComponentIn <| by
          change ConnectedComponents.mk x0.toStabilityCondition = ambientcc
          simpa [ambientcc, x0, mk_numericalComponentRep (C := C) χ cc] using
            (NumericalStabilityCondition.ambientComponentMap_apply (C := C) χ x0).symm)
        hσ
    have : ConnectedComponents.mk σ = ConnectedComponents.mk x0 :=
      (ConnectedComponents.coe_eq_coe').2 hσconn
    simpa [x0, mk_numericalComponentRep (C := C) χ cc] using this

/-- The actual numerical connected component is homeomorphic to the connected component of the
chosen basepoint inside the ambient numerical locus. -/
noncomputable def connectedComponentNumericalAmbientLocusRepHomeomorphNumericalComponent
    {χ : K₀ C →+ K₀ C →+ ℤ}
    (cc : ConnectedComponents (NumericalStabilityCondition C χ)) :
    connectedComponent (numericalAmbientLocusRep (C := C) (χ := χ) cc) ≃ₜ
      NumericalComponent C χ cc := by
  let ambientcc := NumericalStabilityCondition.ambientComponentMap (C := C) χ cc
  let x0 : NumericalAmbientLocus C χ ambientcc := numericalAmbientLocusRep (C := C) (χ := χ) cc
  let F : Set (NumericalStabilityCondition C χ) := {σ |
    ConnectedComponents.mk σ.toStabilityCondition = ambientcc}
  let hEmb : Topology.IsOpenEmbedding
      ((↑) : NumericalAmbientLocus C χ ambientcc → NumericalStabilityCondition C χ) :=
    (isOpen_numericalAmbientLocus (C := C) (χ := χ) ambientcc).isOpenEmbedding_subtypeVal
  let hImage :
      connectedComponent x0 ≃ₜ
        {σ : NumericalStabilityCondition C χ //
          σ ∈ connectedComponentIn F x0.1} :=
    (hEmb.toIsEmbedding.homeomorphImage (connectedComponent x0)).trans
      (Homeomorph.setCongr <| by
        simpa [F, x0] using (connectedComponentIn_eq_image (F := F) x0.2).symm)
  let hEq :
      {σ : NumericalStabilityCondition C χ | ConnectedComponents.mk σ = cc} =
      connectedComponentIn F x0.1 :=
    numericalComponent_set_eq_connectedComponentIn_numericalAmbientLocus
      (C := C) (χ := χ) cc
  exact hImage.trans (Homeomorph.ofEqSubtypes hEq.symm)

/-- The ambient numerical codomain is finite-dimensional whenever `C` is numerically finite. -/
theorem ambientNumericalFactorSubmodule_finiteDimensional
    {χ : K₀ C →+ K₀ C →+ ℤ} [NumericallyFinite C χ]
    {cc : ConnectedComponents (StabilityCondition C)}
    (M : ComponentTopologicalLinearLocalModel C cc) :
    FiniteDimensional ℂ
      (ComponentTopologicalLinearLocalModel.ambientNumericalFactorSubmodule (C := C) χ M) := by
  let toFactor :
      ComponentTopologicalLinearLocalModel.ambientNumericalFactorSubmodule (C := C) χ M →ₗ[ℂ]
        numericalFactorSubmodule C χ := {
    toFun := fun v => ⟨((v.1 : M.V) : AmbientChargeSpace C), v.2⟩
    map_add' := by
      intro v w
      ext x
      rfl
    map_smul' := by
      intro a v
      ext x
      rfl }
  have htoFactor : Function.Injective toFactor := by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : numericalFactorSubmodule C χ => (z : AmbientChargeSpace C)) h
  let toNumerical :
      ComponentTopologicalLinearLocalModel.ambientNumericalFactorSubmodule (C := C) χ M →ₗ[ℂ]
        NumericalChargeSpace C χ :=
    (numericalChargeSpaceEquivFactorSubmodule (C := C) χ).symm.toLinearMap.comp toFactor
  letI : FiniteDimensional ℂ (NumericalChargeSpace C χ) :=
    numericalChargeSpace_finiteDimensional (C := C) χ
  exact FiniteDimensional.of_injective toNumerical
    ((numericalChargeSpaceEquivFactorSubmodule (C := C) χ).symm.injective.comp htoFactor)

/-- A generic manifold-construction theorem for complex local homeomorphisms into a normed model
space. The genuinely nontrivial step is to build a charted space whose transition maps are
restrictions of the identity. -/
theorem exists_chartedSpace_and_hasGroupoid_idRestr_of_isLocalHomeomorph_to_complex_model
    {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    (f : M → E) (hf : IsLocalHomeomorph f) :
    ∃ _ : ChartedSpace E M, HasGroupoid M (@idRestrGroupoid E _) := by
  classical
  let chartAt : M → OpenPartialHomeomorph M E := fun x => Classical.choose (hf x)
  have mem_chart_source : ∀ x : M, x ∈ (chartAt x).source := fun x =>
    (Classical.choose_spec (hf x)).1
  have chartAt_eq : ∀ x : M, f = chartAt x := fun x =>
    (Classical.choose_spec (hf x)).2
  let charted : ChartedSpace E M := {
    atlas := Set.range chartAt
    chartAt := chartAt
    mem_chart_source := mem_chart_source
    chart_mem_atlas x := ⟨x, rfl⟩ }
  letI : ChartedSpace E M := charted
  refine ⟨charted, ?_⟩
  constructor
  intro e e' he he'
  rcases he with ⟨x, rfl⟩
  rcases he' with ⟨y, rfl⟩
  let g : OpenPartialHomeomorph E E := (chartAt x).symm ≫ₕ chartAt y
  have hchart_eq : (chartAt y : M → E) = chartAt x := by
    exact (chartAt_eq y).symm.trans (chartAt_eq x)
  have hg :
      g ≈ OpenPartialHomeomorph.ofSet g.source g.open_source := by
    constructor
    · rfl
    · intro z hz
      change chartAt y ((chartAt x).symm z) = z
      rw [hchart_eq]
      exact (chartAt x).right_inv hz.1
  exact (@idRestrGroupoid E _).mem_of_eqOnSource (idRestrGroupoid_mem g.open_source) hg

/-- Once a charted space has transition maps in the restriction groupoid, it is automatically a
complex manifold. This is the fully generic part of the manifold assembly. -/
theorem isManifold_of_hasGroupoid_idRestr
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
    [ChartedSpace E M] [HasGroupoid M (@idRestrGroupoid E _)] :
    IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞) M := by
  have hle : @idRestrGroupoid E _ ≤ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓘(ℂ, E)) :=
    (closedUnderRestriction_iff_id_le _).mp inferInstance
  letI : HasGroupoid M (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓘(ℂ, E))) :=
    hasGroupoid_of_le (M := M) (G₁ := @idRestrGroupoid E _)
      (G₂ := contDiffGroupoid _ (𝓘(ℂ, E)))
      inferInstance hle
  exact IsManifold.mk' (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞) M

/-- A generic manifold-construction theorem for complex local homeomorphisms into a normed model
space. This is the abstract topological-to-manifold bridge needed to keep Corollary 1.3 small. -/
theorem exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
    (f : M → E) (hf : IsLocalHomeomorph f) :
    ∃ _ : ChartedSpace E M, IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞) M := by
  rcases
      exists_chartedSpace_and_hasGroupoid_idRestr_of_isLocalHomeomorph_to_complex_model
        (E := E) (M := M) f hf with
    ⟨_instChartedSpace, _instHasGroupoid⟩
  exact ⟨_instChartedSpace, isManifold_of_hasGroupoid_idRestr (E := E) (M := M)⟩

/-- A mechanical-assembly version of Bridgeland's Corollary 1.3: once the topological linear local
model and the generic manifold bridge are available, the complex-manifold conclusion should follow
without a large bespoke proof. -/
theorem bridgelandCorollary_1_3_complexManifold [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    (hnum : NumericallyFinite C (eulerForm k C))
    (cc : ConnectedComponents (NumericalStabilityCondition C (eulerForm k C))) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (NumericalComponent C (eulerForm k C) cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (NumericalComponent C (eulerForm k C) cc) := by
  let χ := eulerForm k C
  let ambientcc := NumericalStabilityCondition.ambientComponentMap (C := C) χ cc
  let M := componentTopologicalLinearLocalModel C ambientcc
  letI : Module ℂ M.V := M.instNormedSpace.toModule
  have hTower : IsScalarTower ℂ ℂ M.V := {
    smul_assoc := by
      intro a b x
      simpa [smul_eq_mul] using (mul_smul a b x) }
  letI : IsScalarTower ℂ ℂ M.V := hTower
  let V := ComponentTopologicalLinearLocalModel.ambientNumericalFactorSubmodule (C := C) χ M
  let E := ↥V
  letI : Module ℂ E := V.module
  letI : NormedSpace ℂ E := by
    exact @Submodule.normedSpace ℂ ℂ (inferInstance : SMul ℂ ℂ) inferInstance inferInstance M.V
      inferInstance M.instNormedSpace M.instNormedSpace.toModule hTower V
  letI : FiniteDimensional ℂ E := ambientNumericalFactorSubmodule_finiteDimensional
    (C := C) (χ := χ) (M := M)
  let f₀ : NumericalAmbientLocus C χ ambientcc → E :=
    ComponentTopologicalLinearLocalModel.ambientNumericalChargeMap (C := C) χ M
  have hf₀ : IsLocalHomeomorph f₀ :=
    ComponentTopologicalLinearLocalModel.ambientNumericalChargeMap_isLocalHomeomorph
      (C := C) χ M
  let x0 : NumericalAmbientLocus C χ ambientcc := numericalAmbientLocusRep (C := C) (χ := χ) cc
  have hopenCC : IsOpen (connectedComponent x0 : Set (NumericalAmbientLocus C χ ambientcc)) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨e, hy_source, hfe⟩ := hf₀ y
    have hy_target : f₀ y ∈ e.target := by
      simpa [hfe] using e.map_source hy_source
    letI : NormedSpace ℝ E := NormedSpace.complexToReal
    obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp e.open_target (f₀ y) hy_target
    let B : Set E := Metric.ball (f₀ y) r
    let Bsub : Set e.target := Subtype.val ⁻¹' B
    have hBconn : _root_.IsConnected B := Metric.isConnected_ball hrpos
    have hBsubconn : _root_.IsConnected Bsub := by
      refine hBconn.preimage_of_isOpenMap Subtype.val_injective
        (e.open_target.isOpenEmbedding_subtypeVal.isOpenMap) ?_
      intro z hz
      exact ⟨⟨z, hrsub hz⟩, rfl⟩
    let Wsource : Set e.source := e.toHomeomorphSourceTarget ⁻¹' Bsub
    have hWsourceconn : _root_.IsConnected Wsource := by
      rw [e.toHomeomorphSourceTarget.isConnected_preimage]
      exact hBsubconn
    have hBsubopen : IsOpen Bsub := by
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    have hWsourceopen : IsOpen Wsource := hBsubopen.preimage e.toHomeomorphSourceTarget.continuous
    let W : Set (NumericalAmbientLocus C χ ambientcc) := Subtype.val '' Wsource
    have hWopen : IsOpen W :=
      e.open_source.isOpenEmbedding_subtypeVal.isOpenMap _ hWsourceopen
    have hyWsource : ⟨y, hy_source⟩ ∈ Wsource := by
      change e.toHomeomorphSourceTarget ⟨y, hy_source⟩ ∈ Bsub
      change e y ∈ B
      simpa [B, hfe] using (Metric.mem_ball_self (x := f₀ y) hrpos)
    have hyW : y ∈ W := ⟨⟨y, hy_source⟩, hyWsource, rfl⟩
    have hWconn : _root_.IsConnected W := hWsourceconn.image _ continuous_subtype_val.continuousOn
    have hWsub_y : W ⊆ connectedComponent y := hWconn.subset_connectedComponent hyW
    have hcc_eq : connectedComponent x0 = connectedComponent y := connectedComponent_eq hy
    have hWsub_x0 : W ⊆ connectedComponent x0 := by
      simpa [W, hcc_eq] using hWsub_y
    exact mem_nhds_iff.mpr ⟨W, hWsub_x0, hWopen, hyW⟩
  let hcc :=
    connectedComponentNumericalAmbientLocusRepHomeomorphNumericalComponent
      (C := C) (χ := χ) cc
  let i : connectedComponent x0 → NumericalAmbientLocus C χ ambientcc := Subtype.val
  have hi : IsLocalHomeomorph i :=
    hopenCC.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  let f : NumericalComponent C χ cc → E :=
    fun x => f₀ (i (hcc.symm x))
  have hf : IsLocalHomeomorph f := by
    simpa [f, f₀, i] using hf₀.comp (hi.comp hcc.symm.isLocalHomeomorph)
  let hNum :=
    exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model
      (E := E) (M := NumericalComponent C χ cc) f hf
  refine ⟨(show Type _ from E), (show NormedAddCommGroup E from inferInstance),
    (show NormedSpace ℂ E from inferInstance), (show FiniteDimensional ℂ E from inferInstance),
    Classical.choose hNum, ?_⟩
  exact Classical.choose_spec hNum

end CategoryTheory.Triangulated
