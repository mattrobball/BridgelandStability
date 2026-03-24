/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.StabilityCondition.LocalHomeomorphism
public import BridgelandStability.NumericalStability.Basic
public import BridgelandStability.EulerForm.Defs
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.LocalAtTarget

/-!
# Numerical Stability Manifolds

This file isolates the manifold-level packaging behind Bridgeland's Corollary 1.3.

The current proposition-object
`NumericalStabilityCondition.CentralChargeIsLocalHomeomorphOnConnectedComponents`
only exports a local homeomorphism into a complex-linear subspace. For the actual
complex-manifold corollary, we want to separate the work into the following stages:

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

universe w v u u'

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]

/-- The type of class-map stability conditions in a fixed connected component. -/
abbrev ClassMapComponent (v : K₀ C →+ Λ)
    (cc : ConnectedComponents (ClassMapStabilityCondition C v)) :=
  {σ : ClassMapStabilityCondition C v // ConnectedComponents.mk σ = cc}

namespace StabilityCondition.WithClassMap

/-- Under surjectivity of `v`, the bundled class-map stability conditions are homeomorphic to the
factorization subtype. -/
noncomputable def homeomorphClassMapStabilityCondition {v : K₀ C →+ Λ}
    (hv : Function.Surjective v) :
    letI := StabilityCondition.WithClassMap.topologicalSpace (C := C) (v := v)
    StabilityCondition.WithClassMap C v ≃ₜ ClassMapStabilityCondition C v := by
  let e := StabilityCondition.WithClassMap.equivClassMapStabilityCondition
    (C := C) (v := v) hv
  have hcomp :
      ((↑) : ClassMapStabilityCondition C v → StabilityCondition C) ∘ e =
        StabilityCondition.WithClassMap.toStabilityCondition (C := C) (v := v) := by
    rfl
  have hgf :
      Topology.IsInducing (((↑) : ClassMapStabilityCondition C v → StabilityCondition C) ∘ e) := by
    simpa [hcomp] using
      (Topology.IsInducing.induced
        (StabilityCondition.WithClassMap.toStabilityCondition (C := C) (v := v)))
  have he : Topology.IsInducing e :=
    Topology.IsInducing.of_comp
      (f := e)
      (g := ((↑) : ClassMapStabilityCondition C v → StabilityCondition C))
      (hf := StabilityCondition.WithClassMap.continuous_toClassMapStabilityCondition
        (C := C) (v := v))
      (hg := continuous_subtype_val)
      hgf
  exact e.toHomeomorphOfIsInducing he

/-- Under surjectivity of `v`, connected components of the bundled class-map space correspond to
connected components of the factorization subtype. -/
noncomputable def componentIndexEquivClassMapStabilityCondition {v : K₀ C →+ Λ}
    (hv : Function.Surjective v) :
    StabilityCondition.WithClassMap.ComponentIndex C v ≃
      _root_.ConnectedComponents (ClassMapStabilityCondition C v) := by
  letI := StabilityCondition.WithClassMap.topologicalSpace (C := C) (v := v)
  let e := StabilityCondition.WithClassMap.homeomorphClassMapStabilityCondition
    (C := C) (v := v) hv
  refine
    { toFun := e.continuous.connectedComponentsMap
      invFun := e.symm.continuous.connectedComponentsMap
      left_inv := ?_
      right_inv := ?_ }
  · refine _root_.ConnectedComponents.surjective_coe.forall.2 ?_
    intro σ
    simp [e, Continuous.connectedComponentsMap]
  · refine _root_.ConnectedComponents.surjective_coe.forall.2 ?_
    intro σ
    simp [e, Continuous.connectedComponentsMap]

/-- Under surjectivity of `v`, a connected component of bundled class-map stability conditions is
homeomorphic to the corresponding connected component of the factorization subtype. -/
noncomputable def homeomorphClassMapComponent {v : K₀ C →+ Λ}
    (hv : Function.Surjective v) (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :
    StabilityCondition.WithClassMap.Component C v cc ≃ₜ
      ClassMapComponent C v
        (StabilityCondition.WithClassMap.componentIndexEquivClassMapStabilityCondition
          (C := C) (v := v) hv cc) := by
  letI := StabilityCondition.WithClassMap.topologicalSpace (C := C) (v := v)
  let e := StabilityCondition.WithClassMap.homeomorphClassMapStabilityCondition
    (C := C) (v := v) hv
  let ce := StabilityCondition.WithClassMap.componentIndexEquivClassMapStabilityCondition
    (C := C) (v := v) hv
  refine
    { toFun := fun σ => ⟨e σ.1, by
          change e.continuous.connectedComponentsMap (_root_.ConnectedComponents.mk σ.1) = ce cc
          simpa [ce, Continuous.connectedComponentsMap] using
            congrArg (e.continuous.connectedComponentsMap) σ.2⟩
      invFun := fun σ => ⟨e.symm σ.1, by
          change e.symm.continuous.connectedComponentsMap (_root_.ConnectedComponents.mk σ.1) = cc
          have hσ := congrArg ce.symm σ.2
          simpa [ce, Continuous.connectedComponentsMap] using hσ⟩
      left_inv := by
        intro σ
        apply Subtype.ext
        simp [e]
      right_inv := by
        intro σ
        apply Subtype.ext
        simp [e]
      continuous_toFun := by
        refine Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) (fun σ => by
          change e.continuous.connectedComponentsMap (_root_.ConnectedComponents.mk σ.1) = ce cc
          simpa [ce, Continuous.connectedComponentsMap] using
            congrArg (e.continuous.connectedComponentsMap) σ.2)
      continuous_invFun := by
        refine Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) (fun σ => by
          change e.symm.continuous.connectedComponentsMap (_root_.ConnectedComponents.mk σ.1) = cc
          have hσ := congrArg ce.symm σ.2
          simpa [ce, Continuous.connectedComponentsMap] using hσ)
      }

end StabilityCondition.WithClassMap

/-- The ambient complex charge space attached to a class lattice `Λ`. -/
abbrev ClassMapChargeSpace (Λ : Type u') [AddCommGroup Λ] :=
  Λ →+ ℂ

/-- The ambient Bridgeland charge space `Hom_ℤ(K₀(D), ℂ)` before passing to numerical charges. -/
abbrev AmbientChargeSpace :=
  K₀ C →+ ℂ

/-- Precomposition with the class map `v : K₀(C) → Λ`. -/
def precomposeClassMap (v : K₀ C →+ Λ) :
    ClassMapChargeSpace Λ →ₗ[ℂ] AmbientChargeSpace C where
  toFun := fun Z' => Z'.comp v
  map_add' Z₁ Z₂ := by
    ext x
    rfl
  map_smul' a Z := by
    ext x
    rfl

/-- The subspace of ambient charges that factor through `v`. -/
def classMapFactorSubmodule (v : K₀ C →+ Λ) :
    Submodule ℂ (AmbientChargeSpace C) :=
  LinearMap.range (precomposeClassMap C v)

section

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

@[simp]
theorem mem_classMapFactorSubmodule_iff {v : K₀ C →+ Λ} {Z : AmbientChargeSpace C} :
    Z ∈ classMapFactorSubmodule C v ↔
      ∃ Z' : ClassMapChargeSpace Λ, Z = Z'.comp v := by
  rw [classMapFactorSubmodule, LinearMap.mem_range]
  constructor
  · rintro ⟨Z', rfl⟩
    exact ⟨Z', rfl⟩
  · rintro ⟨Z', rfl⟩
    exact ⟨Z', rfl⟩

end

/-- A class-map stability condition has ambient central charge in the class-map factor subspace. -/
theorem ClassMapStabilityCondition.charge_mem_classMapFactorSubmodule
    {v : K₀ C →+ Λ} (σ : ClassMapStabilityCondition C v) :
    (σ : StabilityCondition C).Z ∈ classMapFactorSubmodule C v := by
  rcases σ.factors with ⟨Z', hZ'⟩
  rw [mem_classMapFactorSubmodule_iff]
  exact ⟨Z', hZ'⟩

theorem ClassMapStabilityCondition.ext_toStabilityCondition
    {v : K₀ C →+ Λ} {σ τ : ClassMapStabilityCondition C v}
    (h : (σ : StabilityCondition C) = τ) :
    σ = τ := by
  exact Subtype.ext h

/-- The inclusion of class-map stability conditions into ordinary stability conditions is
continuous for the induced topology. -/
theorem ClassMapStabilityCondition.continuous_toStabilityCondition
    (v : K₀ C →+ Λ) :
    Continuous
      ((↑) :
        ClassMapStabilityCondition C v → StabilityCondition C) :=
  continuous_subtype_val

/-- The map on connected components induced by the inclusion
`Stab_v(D) ⟶ Stab(D)`. -/
noncomputable def ClassMapStabilityCondition.ambientComponentMap
    (v : K₀ C →+ Λ) :
    ConnectedComponents (ClassMapStabilityCondition C v) →
      ConnectedComponents (StabilityCondition C) :=
  (ClassMapStabilityCondition.continuous_toStabilityCondition (C := C) v).connectedComponentsMap

@[simp]
theorem ClassMapStabilityCondition.ambientComponentMap_apply
    (v : K₀ C →+ Λ) (σ : ClassMapStabilityCondition C v) :
    ClassMapStabilityCondition.ambientComponentMap (C := C) v (ConnectedComponents.mk σ) =
      ConnectedComponents.mk (σ : StabilityCondition C) := by
  simp [ClassMapStabilityCondition.ambientComponentMap, Continuous.connectedComponentsMap]

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

/-- A finite-rank class lattice has finite-dimensional complex charge space. -/
theorem classMapChargeSpace_finiteDimensional (Λ : Type u') [AddCommGroup Λ] [AddGroup.FG Λ] :
    FiniteDimensional ℂ (ClassMapChargeSpace Λ) := by
  let A := Λ
  have hfg : AddGroup.FG A := inferInstance
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
  let precomp : ClassMapChargeSpace Λ →ₗ[ℂ] ((Fin n → ℤ) →+ ℂ) := {
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

/-- The part of `Stab_v(D)` lying over a fixed connected component of `Stab(D)`. -/
abbrev ClassMapAmbientLocus (v : K₀ C →+ Λ)
    (cc : ConnectedComponents (StabilityCondition C)) :=
  {σ : ClassMapStabilityCondition C v //
    ConnectedComponents.mk (σ : StabilityCondition C) = cc}

/-- The ambient class-map locus is open inside `Stab_v(D)` because ambient connected components
of `StabilityCondition C` are open. -/
theorem isOpen_classMapAmbientLocus (v : K₀ C →+ Λ)
    (cc : ConnectedComponents (StabilityCondition C)) :
    IsOpen {σ : ClassMapStabilityCondition C v |
      ConnectedComponents.mk (σ : StabilityCondition C) = cc} := by
  let σ₀ := componentRep C cc
  have hσ₀ : ConnectedComponents.mk σ₀ = cc := by
    dsimp [σ₀]
    exact mk_componentRep C cc
  have hopen : IsOpen (connectedComponent σ₀) := stabilityCondition_isOpen_connectedComponent C σ₀
  have hset :
      {σ : ClassMapStabilityCondition C v |
        ConnectedComponents.mk (σ : StabilityCondition C) = cc} =
        ((↑) : ClassMapStabilityCondition C v → StabilityCondition C) ⁻¹' connectedComponent σ₀ := by
    ext σ
    rw [Set.mem_setOf_eq, Set.mem_preimage, ← ConnectedComponents.coe_eq_coe']
    constructor
    · intro h
      exact h.trans hσ₀.symm
    · intro h
      exact h.trans hσ₀
  rw [hset]
  exact hopen.preimage (ClassMapStabilityCondition.continuous_toStabilityCondition (C := C) v)

namespace ComponentTopologicalLinearLocalModel

variable {cc : ConnectedComponents (StabilityCondition C)}

/-- The class-map part of the ambient codomain `V(Σ)`, cut out as a submodule of `V(Σ)` itself.

Keeping this codomain inside `M.V` avoids any induced-instance transport on the class-map charge
side; it inherits its normed complex-vector-space structure directly as a submodule. -/
def ambientClassMapFactorSubmodule (v : K₀ C →+ Λ)
    (M : ComponentTopologicalLinearLocalModel C cc) :
    Submodule ℂ M.V :=
  (classMapFactorSubmodule C v).comap M.V.subtype

/-- The charge map on the ambient class-map locus `Σ ∩ Stab_v(D)`. -/
def ambientClassMapChargeMap (v : K₀ C →+ Λ)
    (M : ComponentTopologicalLinearLocalModel C cc) :
    ClassMapAmbientLocus C v cc → ambientClassMapFactorSubmodule C v M :=
  fun σ => ⟨⟨σ.1.1.Z, M.mem_charge _ σ.2⟩, by
    change σ.1.1.Z ∈ classMapFactorSubmodule C v
    exact σ.1.charge_mem_classMapFactorSubmodule⟩

/-- The ambient class-map locus is exactly the preimage of the class-map codomain subset under the
ambient component charge map. -/
noncomputable def classMapAmbientLocusHomeomorphChargePreimage
    (v : K₀ C →+ Λ) (M : ComponentTopologicalLinearLocalModel C cc) :
    ClassMapAmbientLocus C v cc ≃ₜ
      {x : componentStabilityCondition C cc //
        ComponentTopologicalLinearLocalModel.chargeMap (C := C) M x ∈
          ambientClassMapFactorSubmodule C v M} where
  toFun := fun σ => ⟨⟨σ.1.1, σ.2⟩, by
    change σ.1.1.Z ∈ classMapFactorSubmodule C v
    exact σ.1.charge_mem_classMapFactorSubmodule⟩
  invFun := fun x => by
    have hx : x.1.1.Z ∈ classMapFactorSubmodule C v := by
      change (((ComponentTopologicalLinearLocalModel.chargeMap (C := C) M x.1 : M.V) :
        AmbientChargeSpace C) ∈ classMapFactorSubmodule C v)
      exact x.2
    have hx' := (mem_classMapFactorSubmodule_iff (C := C) (v := v) (Z := x.1.1.Z)).mp hx
    exact ⟨⟨x.1.1, ⟨Classical.choose hx', Classical.choose_spec hx'⟩⟩, x.1.2⟩
  left_inv σ := by
    apply Subtype.ext
    exact ClassMapStabilityCondition.ext_toStabilityCondition (C := C) rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk
      (Continuous.subtype_mk
        ((ClassMapStabilityCondition.continuous_toStabilityCondition (C := C) v).comp
          continuous_subtype_val)
        (fun σ => σ.2))
      (fun σ => by
        change σ.1.1.Z ∈ classMapFactorSubmodule C v
        exact ClassMapStabilityCondition.charge_mem_classMapFactorSubmodule
          (C := C) (v := v) σ.1)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ (fun x => x.1.2)
    refine Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun x => by
      change StabilityCondition.FactorsThrough C v x.1.1
      exact (mem_classMapFactorSubmodule_iff
        (C := C) (v := v) (Z := x.1.1.Z)).mp x.2)

/-- Bridgeland's Theorem 1.2 restricted to the ambient class-map locus `Σ ∩ Stab_v(D)`. -/
theorem ambientClassMapChargeMap_isLocalHomeomorph (v : K₀ C →+ Λ)
    (M : ComponentTopologicalLinearLocalModel C cc) :
    IsLocalHomeomorph (ambientClassMapChargeMap (C := C) v M) := by
  let e := classMapAmbientLocusHomeomorphChargePreimage (C := C) v M
  let hf :=
    (IsLocalHomeomorph.codRestrict_preimage M.isLocalHomeomorph_chargeMap
      (s := ambientClassMapFactorSubmodule (C := C) v M))
  simpa [ambientClassMapChargeMap, ComponentTopologicalLinearLocalModel.chargeMap, e]
    using hf.comp e.isLocalHomeomorph

end ComponentTopologicalLinearLocalModel

/-- A chosen representative of a connected component of class-map stability conditions. -/
def classMapComponentRep (v : K₀ C →+ Λ)
    (cc : ConnectedComponents (ClassMapStabilityCondition C v)) :
    ClassMapStabilityCondition C v :=
  Classical.choose cc.exists_rep

@[simp] theorem mk_classMapComponentRep (v : K₀ C →+ Λ)
    (cc : ConnectedComponents (ClassMapStabilityCondition C v)) :
    ConnectedComponents.mk (classMapComponentRep C v cc) = cc :=
  Classical.choose_spec cc.exists_rep

/-- The chosen representative of a class-map connected component, regarded inside the ambient
class-map locus. -/
abbrev classMapAmbientLocusRep (v : K₀ C →+ Λ)
    (cc : ConnectedComponents (ClassMapStabilityCondition C v)) :
    ClassMapAmbientLocus C v (ClassMapStabilityCondition.ambientComponentMap (C := C) v cc) :=
  ⟨classMapComponentRep C v cc, by
    simpa [mk_classMapComponentRep (C := C) v cc] using
      (ClassMapStabilityCondition.ambientComponentMap_apply
        (C := C) v (classMapComponentRep C v cc)).symm⟩

/-- Inside `Stab_v(D)`, the connected component `cc` is exactly the connected component of a
chosen representative inside the ambient restriction `Σ ∩ Stab_v(D)`. -/
theorem classMapComponent_set_eq_connectedComponentIn_classMapAmbientLocus
    {v : K₀ C →+ Λ}
    (cc : ConnectedComponents (ClassMapStabilityCondition C v)) :
    {σ : ClassMapStabilityCondition C v | ConnectedComponents.mk σ = cc} =
      connectedComponentIn
        {σ : ClassMapStabilityCondition C v |
          ConnectedComponents.mk (σ : StabilityCondition C) =
            ClassMapStabilityCondition.ambientComponentMap (C := C) v cc}
        (classMapComponentRep C v cc) := by
  let ambientcc := ClassMapStabilityCondition.ambientComponentMap (C := C) v cc
  let x0 := classMapComponentRep C v cc
  let F : Set (ClassMapStabilityCondition C v) := {σ |
    ConnectedComponents.mk (σ : StabilityCondition C) = ambientcc}
  ext σ
  constructor
  · intro hσ
    have hx0F : x0 ∈ F := by
      change ConnectedComponents.mk (x0 : StabilityCondition C) = ambientcc
      simpa [ambientcc, x0, mk_classMapComponentRep (C := C) v cc] using
        (ClassMapStabilityCondition.ambientComponentMap_apply (C := C) v x0).symm
    have hσconn : σ ∈ connectedComponent x0 := by
      apply (ConnectedComponents.coe_eq_coe').1
      rw [hσ, mk_classMapComponentRep (C := C) v cc]
    have hsub : connectedComponent x0 ⊆ F := by
      intro τ hτ
      have hτcc : ConnectedComponents.mk τ = cc := by
        rw [← mk_classMapComponentRep (C := C) v cc]
        exact (ConnectedComponents.coe_eq_coe').2 hτ
      change ConnectedComponents.mk (τ : StabilityCondition C) = ambientcc
      rw [← ClassMapStabilityCondition.ambientComponentMap_apply (C := C) v τ, hτcc]
    exact (isPreconnected_connectedComponent.subset_connectedComponentIn
      mem_connectedComponent hsub) hσconn
  · intro hσ
    have hσconn : σ ∈ connectedComponent x0 := by
      exact isPreconnected_connectedComponentIn.subset_connectedComponent
        (mem_connectedComponentIn <| by
          change ConnectedComponents.mk (x0 : StabilityCondition C) = ambientcc
          simpa [ambientcc, x0, mk_classMapComponentRep (C := C) v cc] using
            (ClassMapStabilityCondition.ambientComponentMap_apply (C := C) v x0).symm)
        hσ
    have : ConnectedComponents.mk σ = ConnectedComponents.mk x0 :=
      (ConnectedComponents.coe_eq_coe').2 hσconn
    simpa [x0, mk_classMapComponentRep (C := C) v cc] using this

/-- The actual class-map connected component is homeomorphic to the connected component of the
chosen basepoint inside the ambient class-map locus. -/
noncomputable def connectedComponentClassMapAmbientLocusRepHomeomorphClassMapComponent
    {v : K₀ C →+ Λ}
    (cc : ConnectedComponents (ClassMapStabilityCondition C v)) :
    connectedComponent (classMapAmbientLocusRep (C := C) (v := v) cc) ≃ₜ
      ClassMapComponent C v cc := by
  let ambientcc := ClassMapStabilityCondition.ambientComponentMap (C := C) v cc
  let x0 : ClassMapAmbientLocus C v ambientcc := classMapAmbientLocusRep (C := C) (v := v) cc
  let F : Set (ClassMapStabilityCondition C v) := {σ |
    ConnectedComponents.mk (σ : StabilityCondition C) = ambientcc}
  let hEmb : Topology.IsOpenEmbedding
      ((↑) : ClassMapAmbientLocus C v ambientcc → ClassMapStabilityCondition C v) :=
    (isOpen_classMapAmbientLocus (C := C) (v := v) ambientcc).isOpenEmbedding_subtypeVal
  let hImage :
      connectedComponent x0 ≃ₜ
        {σ : ClassMapStabilityCondition C v //
          σ ∈ connectedComponentIn F x0.1} :=
    (hEmb.toIsEmbedding.homeomorphImage (connectedComponent x0)).trans
      (Homeomorph.setCongr <| by
        simpa [F, x0] using (connectedComponentIn_eq_image (F := F) x0.2).symm)
  let hEq :
      {σ : ClassMapStabilityCondition C v | ConnectedComponents.mk σ = cc} =
      connectedComponentIn F x0.1 :=
    classMapComponent_set_eq_connectedComponentIn_classMapAmbientLocus
      (C := C) (v := v) cc
  exact hImage.trans (Homeomorph.ofEqSubtypes hEq.symm)

/-- The ambient class-map codomain is finite-dimensional whenever the class lattice is. -/
theorem ambientClassMapFactorSubmodule_finiteDimensional
    {v : K₀ C →+ Λ} [AddGroup.FG Λ]
    {cc : ConnectedComponents (StabilityCondition C)}
    (M : ComponentTopologicalLinearLocalModel C cc) :
    FiniteDimensional ℂ
      (ComponentTopologicalLinearLocalModel.ambientClassMapFactorSubmodule (C := C) v M) := by
  letI : FiniteDimensional ℂ (ClassMapChargeSpace Λ) :=
    classMapChargeSpace_finiteDimensional Λ
  have hFactor :
      FiniteDimensional ℂ (classMapFactorSubmodule C v) :=
    LinearMap.finiteDimensional_range (precomposeClassMap C v)
  let toFactor :
      ComponentTopologicalLinearLocalModel.ambientClassMapFactorSubmodule (C := C) v M →ₗ[ℂ]
        classMapFactorSubmodule C v := {
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
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : classMapFactorSubmodule C v => (z : AmbientChargeSpace C)) h
  exact FiniteDimensional.of_injective toFactor htoFactor

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

/-- A connected component of the factorization subtype admits a local homeomorphism into a finite-
dimensional complex normed space. This is the actual topological content behind the later manifold
assembly. -/
theorem ClassMapStabilityCondition.existsLocalHomeomorphToComplexModelOnConnectedComponent
    {Λ : Type u'} [AddCommGroup Λ] [AddGroup.FG Λ]
    (v : K₀ C →+ Λ)
    (cc : ConnectedComponents (ClassMapStabilityCondition C v)) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (f : ClassMapComponent C v cc → E),
      IsLocalHomeomorph f := by
  let ambientcc := ClassMapStabilityCondition.ambientComponentMap (C := C) v cc
  let M := componentTopologicalLinearLocalModel C ambientcc
  letI : Module ℂ M.V := M.instNormedSpace.toModule
  have hTower : IsScalarTower ℂ ℂ M.V := {
    smul_assoc := by
      intro a b x
      simpa [smul_eq_mul] using (mul_smul a b x) }
  letI : IsScalarTower ℂ ℂ M.V := hTower
  let V := ComponentTopologicalLinearLocalModel.ambientClassMapFactorSubmodule (C := C) v M
  let E := ↥V
  letI : Module ℂ E := V.module
  letI : NormedSpace ℂ E := by
    exact @Submodule.normedSpace ℂ ℂ (inferInstance : SMul ℂ ℂ) inferInstance inferInstance M.V
      inferInstance M.instNormedSpace M.instNormedSpace.toModule hTower V
  letI : FiniteDimensional ℂ E := ambientClassMapFactorSubmodule_finiteDimensional
    (C := C) (v := v) (M := M)
  let f₀ : ClassMapAmbientLocus C v ambientcc → E :=
    ComponentTopologicalLinearLocalModel.ambientClassMapChargeMap (C := C) v M
  have hf₀ : IsLocalHomeomorph f₀ :=
    ComponentTopologicalLinearLocalModel.ambientClassMapChargeMap_isLocalHomeomorph
      (C := C) v M
  let x0 : ClassMapAmbientLocus C v ambientcc := classMapAmbientLocusRep (C := C) (v := v) cc
  have hopenCC : IsOpen (connectedComponent x0 : Set (ClassMapAmbientLocus C v ambientcc)) := by
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
    let W : Set (ClassMapAmbientLocus C v ambientcc) := Subtype.val '' Wsource
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
    connectedComponentClassMapAmbientLocusRepHomeomorphClassMapComponent
      (C := C) (v := v) cc
  let i : connectedComponent x0 → ClassMapAmbientLocus C v ambientcc := Subtype.val
  have hi : IsLocalHomeomorph i :=
    hopenCC.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  let f : ClassMapComponent C v cc → E :=
    fun x => f₀ (i (hcc.symm x))
  have hf : IsLocalHomeomorph f := by
    simpa [f, f₀, i] using hf₀.comp (hi.comp hcc.symm.isLocalHomeomorph)
  refine ⟨(show Type _ from E), (show NormedAddCommGroup E from inferInstance),
    (show NormedSpace ℂ E from inferInstance), (show FiniteDimensional ℂ E from inferInstance), f,
    hf⟩

/-- A mechanical-assembly version of the complex-manifold conclusion for connected components of
class-map stability conditions. Once the local homeomorphism is available, the remaining argument
is the generic manifold bridge. -/
theorem ClassMapStabilityCondition.existsComplexManifoldOnConnectedComponent
    {Λ : Type u'} [AddCommGroup Λ] [AddGroup.FG Λ]
    (v : K₀ C →+ Λ)
    (cc : ConnectedComponents (ClassMapStabilityCondition C v)) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (ClassMapComponent C v cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (ClassMapComponent C v cc) := by
  rcases
      ClassMapStabilityCondition.existsLocalHomeomorphToComplexModelOnConnectedComponent
        (C := C) (v := v) cc with
    ⟨E, _instNormedAddCommGroup, _instNormedSpace, _instFiniteDimensional, f, hf⟩
  rcases
      exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model
        (E := E) (M := ClassMapComponent C v cc) f hf with
    ⟨_instChartedSpace, hmanifold⟩
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hmanifold⟩

/-- The public class-map-first manifold theorem. It is obtained by transporting the internal
factorization-subtype theorem across the homeomorphism coming from surjectivity of `v`. -/
theorem StabilityCondition.WithClassMap.existsComplexManifoldOnConnectedComponent
    {Λ : Type u'} [AddCommGroup Λ] [AddGroup.FG Λ]
    {v : K₀ C →+ Λ} (hv : Function.Surjective v)
    (cc : StabilityCondition.WithClassMap.ComponentIndex C v) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (StabilityCondition.WithClassMap.Component C v cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (StabilityCondition.WithClassMap.Component C v cc) := by
  let cc' :=
    StabilityCondition.WithClassMap.componentIndexEquivClassMapStabilityCondition
      (C := C) (v := v) hv cc
  let e :=
    StabilityCondition.WithClassMap.homeomorphClassMapComponent
      (C := C) (v := v) hv cc
  rcases
      ClassMapStabilityCondition.existsLocalHomeomorphToComplexModelOnConnectedComponent
        (C := C) (v := v) cc' with
    ⟨E, _instNormedAddCommGroup, _instNormedSpace, _instFiniteDimensional, f₀, hf₀⟩
  let f : StabilityCondition.WithClassMap.Component C v cc → E := fun x => f₀ (e x)
  have hf : IsLocalHomeomorph f := by
    simpa [f] using hf₀.comp e.isLocalHomeomorph
  rcases
      exists_chartedSpace_and_complexManifold_of_isLocalHomeomorph_to_complex_model
        (E := E) (M := StabilityCondition.WithClassMap.Component C v cc) f hf with
    ⟨_instChartedSpace, hmanifold⟩
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hmanifold⟩

/-- The complex-manifold conclusion of Bridgeland's Corollary 1.3, obtained by specializing the
generic class-map theorem to the canonical numerical quotient `K₀(C) → N(C)`. -/
theorem NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent
    [Linear k C] [IsFiniteType k C]
    [(shiftFunctor C (1 : ℤ)).Linear k]
    [NumericallyFinite k C]
    (cc : StabilityCondition.WithClassMap.ComponentIndex C (numericalQuotientMap k C)) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : FiniteDimensional ℂ E)
      (_ : ChartedSpace E (NumericalComponent (k := k) C cc)),
      IsManifold (𝓘(ℂ, E)) (⊤ : WithTop ℕ∞)
        (NumericalComponent (k := k) C cc) := by
  let hsurj : Function.Surjective (numericalQuotientMap k C) :=
    QuotientAddGroup.mk'_surjective (eulerFormRad k C)
  simpa [NumericalComponent] using
    (StabilityCondition.WithClassMap.existsComplexManifoldOnConnectedComponent
      (C := C) (v := numericalQuotientMap k C) hsurj cc)

end CategoryTheory.Triangulated
