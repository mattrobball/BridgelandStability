/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.CategoryTheory.Simple
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import BridgelandStability.ForMathlib.Analysis.SpecialFunctions.Complex.ArgConvexity
public import Mathlib.Order.Minimal
public import Mathlib.Data.Fintype.Lattice

/-!
# Stability Functions on Abelian Categories

We define stability functions on abelian categories following Bridgeland (2007), §2.
A stability function assigns to each nonzero object of an abelian category a complex
number in the semi-closed upper half plane `H ∪ ℝ₋`, and is additive on short exact
sequences.

## Main definitions

* `CategoryTheory.upperHalfPlaneUnion`: the set `{im > 0} ∪ {im = 0 ∧ re < 0}` in `ℂ`
* `CategoryTheory.StabilityFunction`: a stability function on an abelian category
* `CategoryTheory.StabilityFunction.phase`: the phase of an object, in `(0, 1]` when nonzero
* `CategoryTheory.StabilityFunction.IsSemistable`: semistability predicate
* `CategoryTheory.AbelianHNFiltration`: HN filtration as a chain of subobjects
* `CategoryTheory.StabilityFunction.HasHNProperty`: every nonzero object admits an HN filtration

## Main results

* `CategoryTheory.StabilityFunction.hasHN_of_finiteLength`: **Proposition 2.4** (Bridgeland).
  If every object has finite length, then any stability function has the HN property.
* `CategoryTheory.StabilityFunction.hn_unique`: **Proposition 2.3** (Bridgeland).
  The number of factors in the HN filtration is unique.

## References

* Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007, §2
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex Real

universe v u

namespace CategoryTheory

/-! ### Stability functions -/

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A stability function on an abelian category `A` assigns to each object a complex number
such that nonzero objects map into the semi-closed upper half plane, and the assignment
is additive on short exact sequences (Bridgeland, Definition 2.1).

We use an object-level function `Zobj : A → ℂ` rather than a K₀-level homomorphism,
since the Grothendieck group `K₀` in the current formalization is defined only for
pretriangulated categories, not abelian categories. -/
structure StabilityFunction (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The central charge on objects. -/
  Zobj : A → ℂ
  /-- The zero object maps to zero. -/
  map_zero' : ∀ (X : A), IsZero X → Zobj X = 0
  /-- Additivity on short exact sequences: `Z(B) = Z(A) + Z(C)` for `0 → A → B → C → 0`. -/
  additive : ∀ (S : ShortComplex A), S.ShortExact → Zobj S.X₂ = Zobj S.X₁ + Zobj S.X₃
  /-- Every nonzero object maps into the semi-closed upper half plane. -/
  upper : ∀ (E : A), ¬IsZero E → Zobj E ∈ upperHalfPlaneUnion

/-! ### Phase -/

namespace StabilityFunction

variable (Z : StabilityFunction A)

/-- The phase of an object `E`, defined as `(1/π) · arg(Z(E))`.
For a nonzero object, `Z(E) ∈ upperHalfPlaneUnion` implies `arg(Z(E)) ∈ (0, π]`,
so the phase lies in `(0, 1]`. For a zero object, the phase is `0`. -/
def phase (E : A) : ℝ :=
  (1 / Real.pi) * arg (Z.Zobj E)

lemma phase_pos (E : A) (hE : ¬IsZero E) : 0 < Z.phase E := by
  unfold phase
  exact mul_pos (div_pos one_pos Real.pi_pos)
    (arg_pos_of_mem_upperHalfPlaneUnion (Z.upper E hE))

lemma phase_le_one (E : A) : Z.phase E ≤ 1 := by
  unfold phase
  rw [div_mul_eq_mul_div, one_mul]
  exact div_le_one_of_le₀ (arg_le_pi (Z.Zobj E)) (le_of_lt Real.pi_pos)

lemma phase_mem_Ioc (E : A) (hE : ¬IsZero E) :
    Z.phase E ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨Z.phase_pos E hE, Z.phase_le_one E⟩

/-! ### Semistability -/

/-- An object `E` of an abelian category is *semistable* with respect to a stability
function `Z` if it is nonzero and for every nonzero subobject `A ↪ E`, the phase of
`A` is at most the phase of `E` (Bridgeland, Definition 2.2). -/
def IsSemistable (E : A) : Prop :=
  ¬IsZero E ∧ ∀ (B : Subobject E), ¬IsZero (B : A) →
    Z.phase (B : A) ≤ Z.phase E

/-- An object is *stable* if it is nonzero and every nonzero proper subobject has
strictly smaller phase. -/
def IsStable (E : A) : Prop :=
  ¬IsZero E ∧ ∀ (B : Subobject E), ¬IsZero (B : A) →
    B ≠ ⊤ → Z.phase (B : A) < Z.phase E

/-- A nonzero object that is not semistable has a destabilizing subobject: a nonzero
subobject with strictly larger phase. -/
lemma exists_destabilizing_of_not_semistable (E : A) (hE : ¬IsZero E)
    (hns : ¬Z.IsSemistable E) :
    ∃ (B : Subobject E), ¬IsZero (B : A) ∧ Z.phase E < Z.phase (B : A) := by
  simp only [IsSemistable, not_and_or, not_forall, not_le, exists_prop] at hns
  rcases hns with hns | ⟨B, hB_nz, hB_phase⟩
  · exact absurd hE hns
  · exact ⟨B, hB_nz, hB_phase⟩

/-! ### Phase see-saw -/

/-- **Phase see-saw (upper bound)**: For a short exact sequence `0 → A → B → C → 0`
with `A, C` nonzero, the phase of `B` is at most the maximum of the phases of `A` and `C`.
This follows from `Z(B) = Z(A) + Z(C)` and `arg_add_le_max`. -/
lemma phase_le_max_of_shortExact (S : ShortComplex A) (hse : S.ShortExact)
    (hA : ¬IsZero S.X₁) (hC : ¬IsZero S.X₃) :
    Z.phase S.X₂ ≤ max (Z.phase S.X₁) (Z.phase S.X₃) := by
  unfold phase
  have hadd : Z.Zobj S.X₂ = Z.Zobj S.X₁ + Z.Zobj S.X₃ := Z.additive S hse
  rw [hadd]
  have h₁ := Z.upper S.X₁ hA
  have h₃ := Z.upper S.X₃ hC
  have harg := arg_add_le_max h₁ h₃
  calc (1 / Real.pi) * arg (Z.Zobj S.X₁ + Z.Zobj S.X₃)
      ≤ (1 / Real.pi) * max (arg (Z.Zobj S.X₁)) (arg (Z.Zobj S.X₃)) := by
        apply mul_le_mul_of_nonneg_left harg (div_nonneg one_pos.le Real.pi_pos.le)
    _ = max ((1 / Real.pi) * arg (Z.Zobj S.X₁)) ((1 / Real.pi) * arg (Z.Zobj S.X₃)) := by
        rw [mul_max_of_nonneg _ _ (div_nonneg one_pos.le Real.pi_pos.le)]

/-- **Phase see-saw (lower bound)**: For a short exact sequence `0 → A → B → C → 0`
with `A, C` nonzero, the phase of `B` is at least the minimum of the phases of `A` and `C`.
This follows from `Z(B) = Z(A) + Z(C)` and `min_arg_le_arg_add`. -/
lemma min_phase_le_of_shortExact (S : ShortComplex A) (hse : S.ShortExact)
    (hA : ¬IsZero S.X₁) (hC : ¬IsZero S.X₃) :
    min (Z.phase S.X₁) (Z.phase S.X₃) ≤ Z.phase S.X₂ := by
  unfold phase
  have hadd : Z.Zobj S.X₂ = Z.Zobj S.X₁ + Z.Zobj S.X₃ := Z.additive S hse
  rw [hadd]
  have h₁ := Z.upper S.X₁ hA
  have h₃ := Z.upper S.X₃ hC
  have harg := min_arg_le_arg_add h₁ h₃
  calc min ((1 / Real.pi) * arg (Z.Zobj S.X₁)) ((1 / Real.pi) * arg (Z.Zobj S.X₃))
      = (1 / Real.pi) * min (arg (Z.Zobj S.X₁)) (arg (Z.Zobj S.X₃)) := by
        rw [mul_min_of_nonneg _ _ (div_nonneg one_pos.le Real.pi_pos.le)]
    _ ≤ (1 / Real.pi) * arg (Z.Zobj S.X₁ + Z.Zobj S.X₃) := by
        apply mul_le_mul_of_nonneg_left harg (div_nonneg one_pos.le Real.pi_pos.le)

/-! ### Z and phase invariance under isomorphisms -/

/-- `Z` sends isomorphic objects to the same value. Uses additivity on the
short exact sequence `0 → E → F → 0` induced by the isomorphism. -/
lemma Zobj_eq_of_iso {E F : A} (e : E ≅ F) : Z.Zobj E = Z.Zobj F := by
  have hS : (ShortComplex.mk e.hom (cokernel.π e.hom) (by simp)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel e.hom) inferInstance inferInstance
  have hadd := Z.additive _ hS
  have hcok : IsZero (cokernel e.hom) := isZero_cokernel_of_epi e.hom
  rw [Z.map_zero' _ hcok, add_zero] at hadd
  exact hadd.symm

/-- Phase is invariant under isomorphisms. -/
lemma phase_eq_of_iso {E F : A} (e : E ≅ F) : Z.phase E = Z.phase F := by
  unfold phase; rw [Z.Zobj_eq_of_iso e]

/-- In an abelian category, for any morphism `f`, the short complex
`X →f→ Y →cokernel.π→ cokernel f` is exact. If `f` is mono, it is short exact. -/
lemma shortExact_of_mono {X Y : A} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (by simp)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f) inferInstance inferInstance

/-- `IsSemistable` is invariant under isomorphisms. -/
lemma isSemistable_of_iso {X Y : A} (e : X ≅ Y) (h : Z.IsSemistable X) :
    Z.IsSemistable Y := by
  refine ⟨fun hY ↦ h.1 (hY.of_iso e), fun B hB ↦ ?_⟩
  -- B : Subobject Y. Transport to a subobject of X via e.
  have hBX : ¬IsZero ((Subobject.mk (B.arrow ≫ e.inv)) : A) := by
    intro hZ
    exact hB (hZ.of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv)).symm)
  have hle := h.2 (Subobject.mk (B.arrow ≫ e.inv)) hBX
  rw [Z.phase_eq_of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv))] at hle
  rwa [Z.phase_eq_of_iso e] at hle

/-! ### Subobject lifting and bot/top helpers -/

/-- A subobject is zero iff it equals ⊥. -/
lemma subobject_isZero_iff_eq_bot {E : A} (B : Subobject E) :
    IsZero (B : A) ↔ B = ⊥ := by
  constructor
  · intro hZ
    have : B.arrow = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rwa [← Subobject.mk_arrow B, Subobject.mk_eq_bot_iff_zero]
  · intro h
    subst h
    exact (isZero_zero A).of_iso Subobject.botCoeIsoZero

/-- A nonzero subobject is not ⊥. -/
lemma subobject_ne_bot_of_not_isZero {E : A} {B : Subobject E}
    (h : ¬IsZero (B : A)) : B ≠ ⊥ :=
  fun h' ↦ h ((subobject_isZero_iff_eq_bot B).mpr h')

/-- ⊥ as a subobject is zero. -/
lemma subobject_not_isZero_of_ne_bot {E : A} {B : Subobject E}
    (h : B ≠ ⊥) : ¬IsZero (B : A) :=
  fun hZ ↦ h ((subobject_isZero_iff_eq_bot B).mp hZ)

/-- In a nontrivial category, ⊤ ≠ ⊥ as subobjects of a nonzero object. -/
lemma subobject_top_ne_bot_of_not_isZero {E : A} (hE : ¬IsZero E) :
    (⊤ : Subobject E) ≠ ⊥ := by
  intro h
  apply hE
  have hZ : IsZero ((⊤ : Subobject E) : A) := (subobject_isZero_iff_eq_bot _).mpr h
  exact hZ.of_iso (asIso (⊤ : Subobject E).arrow).symm

/-- `ofLE ⊥ S h` is the zero morphism (since the source is a zero object). -/
lemma Subobject.ofLE_bot {E : A} (S : Subobject E) (h : ⊥ ≤ S) :
    Subobject.ofLE ⊥ S h = 0 :=
  zero_of_source_iso_zero _ Subobject.botCoeIsoZero

/-- The cokernel of `ofLE ⊥ S _` is isomorphic to `(S : A)`. -/
def Subobject.cokernelBotIso {E : A} (S : Subobject E) (h : ⊥ ≤ S) :
    cokernel (Subobject.ofLE ⊥ S h) ≅ (S : A) := by
  have : Subobject.ofLE ⊥ S h = 0 := Subobject.ofLE_bot S h
  rw [this]
  exact cokernelZeroIsoTarget

/-- Given B : Subobject E and C : Subobject (B : A), lift C to a subobject of E
by composing the arrows. -/
def liftSub {E : A} (B : Subobject E) (C : Subobject (B : A)) :
    Subobject E :=
  Subobject.mk (C.arrow ≫ B.arrow)

omit [Abelian A] in
/-- The lifted subobject is below B. -/
lemma liftSub_le {E : A} (B : Subobject E) (C : Subobject (B : A)) :
    liftSub B C ≤ B := by
  have h := Subobject.mk_le_mk_of_comm C.arrow
    (show C.arrow ≫ B.arrow = C.arrow ≫ B.arrow from rfl)
  rwa [Subobject.mk_arrow] at h

/-- The phase of the lifted subobject equals the phase of C. -/
lemma phase_liftSub {E : A} (B : Subobject E) (C : Subobject (B : A)) :
    Z.phase (liftSub B C : A) = Z.phase (C : A) :=
  Z.phase_eq_of_iso (Subobject.underlyingIso _)

/-- Lifting ⊥ gives ⊥. -/
lemma liftSub_bot {E : A} (B : Subobject E) :
    liftSub B ⊥ = ⊥ := by
  apply (Subobject.mk_eq_bot_iff_zero).mpr
  simp [Subobject.bot_arrow]

/-- Lifting a nonzero subobject gives a nonzero subobject. -/
lemma liftSub_ne_bot {E : A} (B : Subobject E)
    (C : Subobject (B : A)) (hC : C ≠ ⊥) :
    liftSub B C ≠ ⊥ := by
  intro h
  apply hC
  rw [← subobject_isZero_iff_eq_bot] at h ⊢
  exact h.of_iso (Subobject.underlyingIso (C.arrow ≫ B.arrow)).symm

/-! ### Simple objects are semistable -/

/-- A simple object is semistable: its only nonzero subobject is `⊤ ≅ E` itself,
so the phase condition `φ(B) ≤ φ(E)` holds trivially. -/
lemma simple_isSemistable {E : A} (hS : Simple E) : Z.IsSemistable E := by
  refine ⟨Simple.not_isZero E, fun B hB ↦ ?_⟩
  have : IsSimpleOrder (Subobject E) := (simple_iff_subobject_isSimpleOrder E).mp hS
  rcases IsSimpleOrder.eq_bot_or_eq_top B with h | h
  · exact absurd ((subobject_isZero_iff_eq_bot B).mpr h) hB
  · rw [h]; exact le_of_eq (Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow))

variable {Z}

/-- In an Artinian object, repeated destabilizing subobjects terminate. Hence every nonzero
subobject contains a semistable subobject of at least the same phase. This is the first
chain-condition step in Bridgeland's Proposition 2.4. -/
theorem exists_semistable_subobject_ge_phase_of_artinian {E : A}
    [IsArtinianObject E] {B : Subobject E} (hB : B ≠ ⊥) :
    ∃ C : Subobject E, C ≤ B ∧ C ≠ ⊥ ∧ Z.IsSemistable (C : A) ∧
      Z.phase (B : A) ≤ Z.phase (C : A) := by
  induction B using WellFoundedLT.induction with
  | ind B ih =>
      by_cases hB' : B = ⊥
      · exfalso
        exact hB hB'
      · have hB_nz : ¬IsZero (B : A) := subobject_not_isZero_of_ne_bot hB'
        by_cases hss : Z.IsSemistable (B : A)
        · exact ⟨B, le_rfl, hB', hss, le_rfl⟩
        · obtain ⟨D, hD_nz, hphase⟩ :=
            Z.exists_destabilizing_of_not_semistable (B : A) hB_nz hss
          have hD_ne_bot : D ≠ ⊥ := subobject_ne_bot_of_not_isZero hD_nz
          let D' : Subobject E := liftSub B D
          have hD'_le : D' ≤ B := liftSub_le B D
          have hD'_ne : D' ≠ ⊥ := liftSub_ne_bot B D hD_ne_bot
          have hD'_lt : D' < B := by
            refine lt_of_le_of_ne hD'_le ?_
            intro hEq
            have hphase_eq : Z.phase (D : A) = Z.phase (B : A) := by
              calc
                Z.phase (D : A) = Z.phase (D' : A) := (Z.phase_liftSub B D).symm
                _ = Z.phase (B : A) := by
                    simpa [D'] using
                      congrArg (fun X : Subobject E => Z.phase (X : A)) hEq
            linarith
          rcases ih D' hD'_lt hD'_ne with ⟨C, hCB, hC_ne, hC_ss, hBC⟩
          refine ⟨C, hCB.trans hD'_le, hC_ne, hC_ss, ?_⟩
          have hBD : Z.phase (B : A) < Z.phase (D' : A) := by
            rw [Z.phase_liftSub]
            exact hphase
          exact le_of_lt <| lt_of_lt_of_le hBD hBC

/-- In a non-semistable Artinian object, there is a semistable destabilizing subobject. -/
theorem exists_semistable_subobject_gt_phase_of_not_semistable {E : A}
    [IsArtinianObject E] (hE : ¬IsZero E) (hns : ¬ Z.IsSemistable E) :
    ∃ B : Subobject E, B ≠ ⊥ ∧ Z.IsSemistable (B : A) ∧ Z.phase E < Z.phase (B : A) := by
  obtain ⟨B, hB_nz, hB_phase⟩ := Z.exists_destabilizing_of_not_semistable E hE hns
  have hB_ne : B ≠ ⊥ := subobject_ne_bot_of_not_isZero hB_nz
  obtain ⟨C, hCB, hC_ne, hC_ss, hBC⟩ :=
    Z.exists_semistable_subobject_ge_phase_of_artinian hB_ne
  refine ⟨C, hC_ne, hC_ss, ?_⟩
  exact lt_of_lt_of_le hB_phase hBC

variable (Z)

/-! ### Max phase and MDS construction -/

/-- Among all nonzero subobjects of a nonzero object with finite subobject lattice,
there exists one with maximal phase. -/
lemma exists_maxPhase_subobject (E : A) (hE : ¬IsZero E)
    [hFin : Finite (Subobject E)] :
    ∃ M : Subobject E, M ≠ ⊥ ∧
      ∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A) := by
  have hne : ∃ B : Subobject E, B ≠ ⊥ :=
    ⟨⊤, subobject_top_ne_bot_of_not_isZero hE⟩
  haveI : Nonempty {B : Subobject E // B ≠ ⊥} :=
    ⟨⟨⊤, subobject_top_ne_bot_of_not_isZero hE⟩⟩
  haveI : Finite {B : Subobject E // B ≠ ⊥} := Finite.of_injective
    (fun x ↦ (x : Subobject E)) Subtype.val_injective
  obtain ⟨⟨M, hM⟩, hmax⟩ := Finite.exists_max (fun (x : {B : Subobject E // B ≠ ⊥}) ↦
    Z.phase ((x : Subobject E) : A))
  exact ⟨M, hM, fun B hB ↦ hmax ⟨B, hB⟩⟩

/-- If `M` has maximal phase among all nonzero subobjects of `E`, then `M` is
semistable as an object. This is because any destabilizing subobject of `(M : A)`
lifts to a nonzero subobject of `E` with higher phase, contradicting maximality. -/
lemma maxPhase_isSemistable {E : A} {M : Subobject E} (hM : M ≠ ⊥)
    (hmax : ∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A)) :
    Z.IsSemistable (M : A) := by
  refine ⟨subobject_not_isZero_of_ne_bot hM, fun C hC ↦ ?_⟩
  -- C : Subobject (M : A). Lift to a subobject of E via liftSub.
  have hC_ne : C ≠ ⊥ := subobject_ne_bot_of_not_isZero hC
  have hL := liftSub_ne_bot M C hC_ne
  calc Z.phase (C : A)
      = Z.phase (liftSub M C : A) := (Z.phase_liftSub M C).symm
    _ ≤ Z.phase (M : A) := hmax (liftSub M C) hL

/-- The max-phase subobject `M` is not `⊤` when `E` is not semistable and `M ≠ ⊤`,
which happens when `φ(M) > φ(E)`. Since `φ(⊤) = φ(E)` (via the iso `⊤ ≅ E`),
`φ(M) > φ(E)` implies `M ≠ ⊤`. -/
lemma maxPhase_ne_top_of_not_semistable {E : A}
    (hns : ¬Z.IsSemistable E) :
    ∀ M : Subobject E, M ≠ ⊥ →
      (∀ B : Subobject E, B ≠ ⊥ → Z.phase (B : A) ≤ Z.phase (M : A)) →
      M ≠ ⊤ := by
  intro M hM hmax hMtop
  apply hns
  have hMS := Z.maxPhase_isSemistable hM hmax
  subst hMtop
  exact Z.isSemistable_of_iso (asIso (⊤ : Subobject E).arrow) hMS

end StabilityFunction

end CategoryTheory
