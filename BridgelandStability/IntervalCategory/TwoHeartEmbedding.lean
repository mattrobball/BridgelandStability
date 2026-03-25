/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public import BridgelandStability.IntervalCategory.Basic

/-!
# Two-Heart Embedding for Interval Categories

Heart containment, phase bounds for triangles with semistable middle term,
kernel/image/cokernel containment in thin intervals (Lemma 4.3 and consequences).
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

/-! ### Heart containment — Two-heart embedding (Lemma 4.3 foundations)

Objects in a thin interval `P((a, b))` with `b - a ≤ 1` lie in two different abelian hearts:
* **Left heart** `P((a, a+1])` — the heart of the slicing shifted by `a`.
  Controls kernels and images.
* **Right heart** `P((b-1, b])` — the heart of the slicing shifted by `b-1`.
  Controls cokernels and coimages.

This is the foundation of Bridgeland's Lemma 4.3 and is why the interval category
is quasi-abelian: one heart cannot handle both kernels and cokernels, but together
the two hearts make up for each other's deficiencies.
-/

section TwoHeartEmbedding

/-- **Interval to gtProp.** If all HN phases lie in `(a, b)`, then phiMinus > `a`. -/
lemma Slicing.gtProp_of_intervalProp (s : Slicing C) {a b : ℝ} {E : C}
    (hE : s.intervalProp C a b E) : s.gtProp C a E := by
  rcases hE with hZ | ⟨F, hF⟩
  · exact Or.inl hZ
  · by_cases hn : 0 < F.n
    · exact Or.inr ⟨F, hn, (hF ⟨F.n - 1, by lia⟩).1⟩
    · exact Or.inl (F.toPostnikovTower.zero_isZero (by lia))

/-- **Interval to leProp.** If all HN phases lie in `(a, b)`, then phiPlus ≤ `b`. -/
lemma Slicing.leProp_of_intervalProp (s : Slicing C) {a b : ℝ} {E : C}
    (hE : s.intervalProp C a b E) : s.leProp C b E := by
  rcases hE with hZ | ⟨F, hF⟩
  · exact Or.inl hZ
  · by_cases hn : 0 < F.n
    · exact Or.inr ⟨F, hn, le_of_lt (hF ⟨0, hn⟩).2⟩
    · exact Or.inl (F.toPostnikovTower.zero_isZero (by lia))

section HeartContainment

variable [IsTriangulated C]

/-- **Left heart containment (Lemma 4.3a).** If `b - a ≤ 1` and `E ∈ P((a, b))`,
then `E` lies in the heart of the t-structure induced by the slicing shifted by `a`.
This heart is the half-open interval `P((a, a+1])`.

The proof is immediate: phases in `(a, b)` satisfy `> a` (for `gtProp`) and
`< b ≤ a + 1` (for `leProp`). -/
theorem Slicing.intervalProp_implies_leftHeart (s : Slicing C) {a b : ℝ}
    (hab : b - a ≤ 1) {E : C} (hE : s.intervalProp C a b E) :
    ((s.phaseShift C a).toTStructure).heart E := by
  rw [(s.phaseShift C a).toTStructure_heart_iff]
  constructor
  · -- gtProp C 0 for shifted slicing ↔ gtProp C a for original
    rw [s.phaseShift_gtProp_zero]
    exact s.gtProp_of_intervalProp C hE
  · -- leProp C 1 for shifted slicing: construct shifted HN filtration
    rcases hE with hZ | ⟨F, hF⟩
    · exact Or.inl hZ
    · by_cases hn : 0 < F.n
      · right
        refine ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i - a,
          fun i j h ↦ by linarith [F.hφ h], fun j ↦ ?_⟩, hn, ?_⟩
        · change s.P (F.φ j - a + a) _
          rw [show F.φ j - a + a = F.φ j from by ring]
          exact F.semistable j
        · dsimp [HNFiltration.phiPlus]
          grind
      · exact Or.inl (F.toPostnikovTower.zero_isZero (by lia))

/-- **Right heart containment (Lemma 4.3b).** If `b - a ≤ 1` and `E ∈ P((a, b))`,
then `E` lies in the heart of the dual half-open t-structure induced by the slicing
shifted by `b - 1`. This heart is the half-open interval `P([b-1, b))`.

Together with `intervalProp_implies_leftHeart`, this establishes the two-heart
embedding: every object in a thin interval lies in both an abelian heart that
controls kernels (left heart) and one that controls cokernels (right heart). -/
theorem Slicing.intervalProp_implies_rightHeart (s : Slicing C) {a b : ℝ}
    (hab : b - a ≤ 1) {E : C} (hE : s.intervalProp C a b E) :
    ((s.phaseShift C (b - 1)).toTStructureGE).heart E := by
  rw [(s.phaseShift C (b - 1)).toTStructureGE_heart_iff]
  constructor
  · rw [s.phaseShift_geProp_zero]
    have hgt : s.gtProp C a E := s.gtProp_of_intervalProp C hE
    have hge : s.geProp C a E := (s.geProp_of_gtProp (C := C) (t := a)) E hgt
    exact (s.geProp_anti (C := C) (t₁ := b - 1) (t₂ := a) (by linarith)) E hge
  · rw [s.phaseShift_ltProp]
    simpa [show 1 + (b - 1) = b by linarith] using s.ltProp_of_intervalProp C hE

/-- The fully faithful embedding of `P((a,b))` into the left heart `P((a,a+1])`. -/
abbrev Slicing.IntervalCat.toLeftHeart (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤ ((s.phaseShift C a).toTStructure).heart.FullSubcategory where
  obj X := ⟨X.obj, s.intervalProp_implies_leftHeart C hab X.property⟩
  map f := ObjectProperty.homMk f.hom

instance Slicing.IntervalCat.toLeftHeart_full (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    Functor.Full (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_surjective {_ _} f := ⟨ObjectProperty.homMk f.hom, rfl⟩

instance Slicing.IntervalCat.toLeftHeart_faithful (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Faithful (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_injective := by
    intro X Y f g h
    cases f
    cases g
    cases h
    rfl

/-- The fully faithful embedding of `P((a,b))` into the right heart `P([b-1,b))`. -/
abbrev Slicing.IntervalCat.toRightHeart (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤ ((s.phaseShift C (b - 1)).toTStructureGE).heart.FullSubcategory where
  obj X := ⟨X.obj, s.intervalProp_implies_rightHeart C hab X.property⟩
  map f := ObjectProperty.homMk f.hom

instance Slicing.IntervalCat.toRightHeart_full (s : Slicing C) (a b : ℝ) (hab : b - a ≤ 1) :
    Functor.Full (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_surjective {_ _} f := ⟨ObjectProperty.homMk f.hom, rfl⟩

instance Slicing.IntervalCat.toRightHeart_faithful (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Faithful (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_injective := by
    intro X Y f g h
    cases f
    cases g
    cases h
    rfl

end HeartContainment

/-- **Right-window bounds.** If `b - a ≤ 1` and `E ∈ P((a, b))`, then `E` satisfies
the phase-window conditions `geProp (b - 1)` and `ltProp b`.

This is the half-open interval `[b - 1, b)` needed for the future right-heart
convention controlling cokernels. -/
theorem Slicing.intervalProp_implies_rightWindow (s : Slicing C) {a b : ℝ}
    (hab : b - a ≤ 1) {E : C} (hE : s.intervalProp C a b E) :
    s.geProp C (b - 1) E ∧ s.ltProp C b E := by
  constructor
  · have hgt : s.gtProp C a E := s.gtProp_of_intervalProp C hE
    have hge : s.geProp C a E := (s.geProp_of_gtProp (C := C) (t := a)) E hgt
    exact (s.geProp_anti (C := C) (t₁ := b - 1) (t₂ := a) (by linarith)) E hge
  · exact s.ltProp_of_intervalProp C hE

/-! ### Phase bounds for triangles with semistable middle term

For a distinguished triangle `K → F → Q → K⟦1⟧` where `F ∈ P(φ)` is σ-semistable
and `K, Q ∈ P((a, b))` lie in a thin interval containing `φ`, Lemma 3.4 gives:
- `φ⁺(K) ≤ φ` (the top phase of K is bounded by F's phase)
- `φ⁻(Q) ≥ φ` (the bottom phase of Q is bounded below by F's phase)

These are the foundational phase bounds for the deformation theorem's triangle test.
Combined with interval membership, they give:
- K has all σ-phases in `(a, φ]`
- Q has all σ-phases in `[φ, b)`

The Z-ray consequence (Im(Z(K)·rot) ≤ 0 and Im(Z(Q)·rot) ≥ 0) does NOT suffice
to force K, Q ∈ P(φ) — the terms have opposite signs, so sum = 0 allows both nonzero.
See the counterexample in `HeartEquivalence.lean`. The full triangle test requires
the quasi-abelian theory or W-semistability arguments.
-/

/-- **Phase upper bound from Lemma 3.4.** In a triangle `K → F → Q → K⟦1⟧` with
`F ∈ P(φ)` σ-semistable and `K, Q` in a thin interval `P((a, b))` with `b ≤ a + 1`
and `φ ∈ (a, b)`, if `K` is nonzero then `φ⁺(K) ≤ φ`. -/
theorem Slicing.phiPlus_le_of_semistable_triangle (s : Slicing C) {φ : ℝ}
    {K F Q : C} {f₁ : K ⟶ F} {f₂ : F ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C)
    (hPφ : (s.P φ) F) (hFne : ¬IsZero F) (hKne : ¬IsZero K)
    {a b : ℝ} (hab : b ≤ a + 1)
    (hKI : s.intervalProp C a b K) (hQI : s.intervalProp C a b Q) :
    s.phiPlus C K hKne ≤ φ := by
  have hFplus : s.phiPlus C F hFne = φ :=
    (s.phiPlus_eq_phiMinus_of_semistable C hPφ hFne).1
  rw [← hFplus]
  exact s.phiPlus_triangle_le C hKne hFne hab hKI hQI hT

/-- **Phase lower bound from Lemma 3.4.** In a triangle `K → F → Q → K⟦1⟧` with
`F ∈ P(φ)` σ-semistable and `K, Q` in a thin interval `P((a, b))` with `b ≤ a + 1`,
if `Q` is nonzero then `φ ≤ φ⁻(Q)`. -/
theorem Slicing.phiMinus_ge_of_semistable_triangle (s : Slicing C) {φ : ℝ}
    {K F Q : C} {f₁ : K ⟶ F} {f₂ : F ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C)
    (hPφ : (s.P φ) F) (hFne : ¬IsZero F) (hQne : ¬IsZero Q)
    {a b : ℝ} (hab : b ≤ a + 1)
    (hKI : s.intervalProp C a b K) (hQI : s.intervalProp C a b Q) :
    φ ≤ s.phiMinus C Q hQne := by
  have hFminus : s.phiMinus C F hFne = φ :=
    (s.phiPlus_eq_phiMinus_of_semistable C hPφ hFne).2
  rw [← hFminus]
  exact s.phiMinus_triangle_le C hQne hFne hab hKI hQI hT

/-! ### One-sided phase bounds for triangles (generalizing Lemma 3.4)

These lemmas generalize `phiPlus_triangle_le` and `phiMinus_triangle_le` by replacing
the `intervalProp` condition on one vertex with a weaker `leProp` or `gtProp` condition.
The key application is kernel/image containment: when a morphism `f : E → F` between
interval objects has its kernel/image computed in an abelian heart, the heart membership
gives only a `leProp`/`gtProp` bound, not full `intervalProp`. These lemmas recover
the full interval containment from the weaker one-sided bound.
-/

/-- **Phase upper bound from one-sided containment.** In a triangle `K → E → Q → K⟦1⟧`,
if `E` has `φ⁺(E) < b` and `Q` satisfies `leProp c` (all phases ≤ c) with `c < b + 1`,
then if `K` is nonzero, `φ⁺(K) < b`.

This strengthens `phiPlus_triangle_le` by requiring only a `leProp` bound on `Q` rather
than full `intervalProp`. The condition `c < b + 1` ensures `Q⟦-1⟧` has all phases
`≤ c - 1 < b`, providing the hom-vanishing gap for the coyoneda factoring argument.

**Key application**: kernel containment in the left heart. If `f : E → F` with both
in `P((a, b))`, the heart's SES `ker(f) → E → im(f)` gives a triangle where `im(f)`
is in the heart with `leProp (a + 1)`. Since `a + 1 < b + 1`, this lemma bounds
`φ⁺(ker(f)) < b`, placing the kernel in `P((a, b))`. -/
theorem Slicing.phiPlus_lt_of_triangle_with_leProp (s : Slicing C)
    {K E Q : C} (hK : ¬IsZero K) {b : ℝ}
    (hE_lt : ∀ (hE : ¬IsZero E), s.phiPlus C E hE < b)
    {c : ℝ} (hQ_le : s.leProp C c Q) (hcb : c < b + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.phiPlus C K hK < b := by
  obtain ⟨FK, hnK, hneK⟩ := HNFiltration.exists_nonzero_first C s hK
  rw [s.phiPlus_eq C K hK FK hnK hneK]
  by_contra hge
  push_neg at hge
  -- hge : b ≤ FK.φ ⟨0, hnK⟩ (top factor has phase ≥ b)
  -- Show all maps from FK's top factor to K are zero
  have hK_factor_zero : ∀ α : (FK.triangle ⟨0, hnK⟩).obj₃ ⟶ K, α = 0 := by
    intro α
    -- Step 1: α ≫ f₁ = 0 (top factor → E is zero by hom-vanishing)
    have hαf : α ≫ f₁ = 0 := by
      by_cases hEZ : IsZero E
      · exact hEZ.eq_of_tgt (α ≫ f₁) 0
      · obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_first C s hEZ
        have hE_gap : ∀ j : Fin FE.n, FE.φ j < FK.φ ⟨0, hnK⟩ := fun j ↦ by
          have h1 : FE.φ j ≤ FE.φ ⟨0, hnE⟩ := by
            apply FE.hφ.antitone; grind
          have h2 : FE.φ ⟨0, hnE⟩ = s.phiPlus C E hEZ :=
            (s.phiPlus_eq C E hEZ FE hnE hneE).symm
          grind
        exact s.hom_eq_zero_of_gt_phases C (FK.semistable ⟨0, hnK⟩) FE hE_gap _
    -- Step 2: By coyoneda on invRotate, α factors through Q⟦-1⟧
    let T := Triangle.mk f₁ f₂ f₃
    obtain ⟨β, hβ⟩ := Triangle.coyoneda_exact₂ T.invRotate
      (inv_rot_of_distTriang _ hT) α hαf
    -- Step 3: β = 0 (top factor → Q⟦-1⟧ is zero by hom-vanishing)
    suffices hβ0 : β = 0 by rw [hβ, hβ0, zero_comp]; rfl
    by_cases hQZ : IsZero Q
    · exact ((shiftFunctor C (-1 : ℤ)).map_isZero hQZ).eq_of_tgt β 0
    · rcases hQ_le with hQZ' | ⟨GQ, hnQ, hGQ_le⟩
      · exact absurd hQZ' hQZ
      · -- Shift GQ by -1 to get filtration of Q⟦-1⟧
        let GQs := GQ.shiftHN C s (-1 : ℤ)
        -- GQs.φ(j) = GQ.φ(j) - 1 ≤ c - 1 < b ≤ FK.φ(0)
        have hQs_gap : ∀ j : Fin GQs.n, GQs.φ j < FK.φ ⟨0, hnK⟩ := by
          intro j
          change GQ.φ j + ((-1 : ℤ) : ℝ) < FK.φ ⟨0, hnK⟩
          have h1 : GQ.φ j ≤ GQ.φ ⟨0, hnQ⟩ := by
            apply GQ.hφ.antitone; grind
          have h2 : GQ.φ ⟨0, hnQ⟩ ≤ c := hGQ_le
          have h3 : ((-1 : ℤ) : ℝ) = -1 := by norm_num
          linarith
        exact s.hom_eq_zero_of_gt_phases C (FK.semistable ⟨0, hnK⟩) GQs hQs_gap β
  -- Top factor is zero — contradiction
  exact hneK (FK.isZero_factor_zero_of_hom_eq_zero C s hnK hK_factor_zero)

/-- **Phase lower bound from one-sided containment** (dual of
`phiPlus_lt_of_triangle_with_leProp`). In a triangle `K → E → Q → K⟦1⟧`,
if `E` has `φ⁻(E) > a` and `K` satisfies `gtProp c` (all phases > c) with `a < c + 1`,
then if `Q` is nonzero, `a < φ⁻(Q)`.

**Key application**: cokernel/quotient lower bound. In a heart SES, the quotient object
satisfies `gtProp` from heart membership, and this lemma gives the lower phase bound
needed for interval containment. -/
theorem Slicing.phiMinus_gt_of_triangle_with_gtProp (s : Slicing C)
    {K E Q : C} (hQ : ¬IsZero Q) {a : ℝ}
    (hE_gt : ∀ (hE : ¬IsZero E), a < s.phiMinus C E hE)
    {c : ℝ} (hK_gt : s.gtProp C c K) (hca : a < c + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    a < s.phiMinus C Q hQ := by
  obtain ⟨FQ, hnQ, hneQ⟩ := HNFiltration.exists_nonzero_last C s hQ
  rw [s.phiMinus_eq C Q hQ FQ hnQ hneQ]
  by_contra hle
  push_neg at hle
  -- hle : FQ.φ ⟨FQ.n - 1, _⟩ ≤ a (bottom factor has phase ≤ a)
  -- Show all maps from Q to FQ's bottom factor are zero
  have hQ_factor_zero :
      ∀ β : Q ⟶ (FQ.triangle ⟨FQ.n - 1, by lia⟩).obj₃, β = 0 := by
    intro β
    -- Step 1: f₂ ≫ β = 0 (E → bottom_factor is zero by hom-vanishing)
    have hfβ : f₂ ≫ β = 0 := by
      by_cases hEZ : IsZero E
      · exact hEZ.eq_of_src (f₂ ≫ β) 0
      · obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_last C s hEZ
        have hE_gap : ∀ j : Fin FE.n,
            FQ.φ ⟨FQ.n - 1, by lia⟩ < FE.φ j := fun j ↦ by
          have h1 : a < FE.φ ⟨FE.n - 1, by lia⟩ := by
            have := hE_gt hEZ; rwa [s.phiMinus_eq C E hEZ FE hnE hneE] at this
          have h2 : FE.φ ⟨FE.n - 1, by lia⟩ ≤ FE.φ j := by
            apply FE.hφ.antitone; grind
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FQ.semistable ⟨FQ.n - 1, by lia⟩) FE hE_gap _
    -- Step 2: By yoneda_exact₃, β factors through K⟦1⟧
    obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₃ (Triangle.mk f₁ f₂ f₃) hT β hfβ
    -- Step 3: γ = 0 (K⟦1⟧ → bottom_factor is zero by hom-vanishing)
    suffices hγ0 : γ = 0 by rw [hγ, hγ0]; exact comp_zero
    by_cases hKZ : IsZero K
    · exact ((shiftFunctor C (1 : ℤ)).map_isZero hKZ).eq_of_src γ 0
    · rcases hK_gt with hKZ' | ⟨GK, hnGK, hGK_gt⟩
      · exact absurd hKZ' hKZ
      · -- Shift GK by 1 to get filtration of K⟦1⟧
        let GKs := GK.shiftHN C s (1 : ℤ)
        -- GKs.φ(j) = GK.φ(j) + 1 > c + 1 > a ≥ FQ.φ(n-1)
        have hKs_gap : ∀ j : Fin GKs.n,
            FQ.φ ⟨FQ.n - 1, by lia⟩ < GKs.φ j := by
          intro j
          change FQ.φ ⟨FQ.n - 1, by lia⟩ < GK.φ j + ((1 : ℤ) : ℝ)
          have h1 : GK.φ ⟨GK.n - 1, by lia⟩ ≤ GK.φ j := by
            apply GK.hφ.antitone
            change j.val ≤ GK.n - 1
            have := j.isLt; have : GKs.n = GK.n := rfl; lia
          have h2 : c < GK.φ ⟨GK.n - 1, by lia⟩ := hGK_gt
          have h3 : ((1 : ℤ) : ℝ) = 1 := by norm_num
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FQ.semistable ⟨FQ.n - 1, by lia⟩) GKs hKs_gap γ
  -- Bottom factor is zero — contradiction
  exact hneQ (FQ.isZero_factor_last_of_hom_eq_zero C s hnQ hQ_factor_zero)

/-! ### Kernel and image containment in thin intervals (Lemma 4.3 consequences)

In a thin interval `P((a, b))` with `b - a ≤ 1`, the left heart `P((a, a+1])` computes
kernels and images of morphisms between interval objects. The resulting kernels and images
**stay in the interval** `P((a, b))`:

* **Upper bound** (`phiPlus < b`): from `phiPlus_lt_of_triangle_with_leProp`, using
  that the third vertex of the heart SES triangle has `leProp(a+1)` from heart membership.
* **Lower bound** (`phiMinus > a`): directly from left heart membership, since all
  phases in `P((a, a+1])` are `> a`.

This does NOT extend to cokernels in the left heart: a quotient of an interval object
in the left heart can have phases up to `a + 1 > b`. For cokernels, the right heart
`P((b-1, b])` is needed, and the strict upper bound `phiPlus < b` requires the
quasi-abelian theory (Bridgeland §4).
-/

/-- **Kernel/image containment in thin intervals.** In a distinguished triangle
`K → E → Q → K[1]` where `E ∈ P((a,b))` and both `K` and `Q` satisfy basic phase
bounds (`gtProp a` and `leProp (a+1)`), then `K ∈ P((a, b))`.

The upper bound `phiPlus(K) < b` comes from `phiPlus_lt_of_triangle_with_leProp`.
The lower bound `phiMinus(K) > a` comes from `gtProp a`.

**Key applications**:
* **Kernels**: In the heart SES `0 → ker(f) → E → im(f) → 0`, both `ker(f)` and
  `im(f)` are in the left heart, hence satisfy `gtProp a` and `leProp (a+1)`.
* **Images**: In the heart SES `0 → im(f) → F → coker(f) → 0`, similarly. -/
theorem Slicing.first_intervalProp_of_triangle (s : Slicing C)
    {a b : ℝ} (hab' : a < b)
    {K E Q : C}
    (hE : s.intervalProp C a b E)
    (hQ_le : s.leProp C (a + 1) Q)
    (hK_gt : s.gtProp C a K)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.intervalProp C a b K := by
  by_cases hK : IsZero K
  · exact Or.inl hK
  · -- phiPlus(K) < b: from phiPlus_lt_of_triangle_with_leProp
    have hK_lt : s.phiPlus C K hK < b :=
      s.phiPlus_lt_of_triangle_with_leProp C hK
        (fun hE' ↦ s.phiPlus_lt_of_intervalProp C hE' hE)
        hQ_le (by linarith) hT
    -- phiMinus(K) > a: from gtProp via phiMinus_gt_of_gtProp
    have hK_minus : a < s.phiMinus C K hK :=
      s.phiMinus_gt_of_gtProp C hK hK_gt
    -- Combine: K has all phases in (a, b)
    obtain ⟨FK, hnK, hfirstK, hlastK⟩ := HNFiltration.exists_both_nonzero C s hK
    right
    exact ⟨FK, fun i ↦ by
      constructor
      · calc a < s.phiMinus C K hK := hK_minus
          _ = FK.φ ⟨FK.n - 1, by lia⟩ := s.phiMinus_eq C K hK FK hnK hlastK
          _ ≤ FK.φ i := FK.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc FK.φ i ≤ FK.φ ⟨0, hnK⟩ :=
              FK.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = s.phiPlus C K hK := (s.phiPlus_eq C K hK FK hnK hfirstK).symm
          _ < b := hK_lt⟩

/-- **Extension closure for thin intervals.** In a distinguished triangle
`A → E → B → A[1]` where `A` and `B` are in `P((a, b))` with `b - a ≤ 1`,
then `E ∈ P((a, b))`.

This follows from `phiPlus_lt_of_triangle` and `phiMinus_gt_of_triangle`. It shows
that `P((a, b))` is extension-closed in the triangulated category when `b - a ≤ 1`.
This is a special case of the general extension closure for interval categories. -/
theorem Slicing.intervalProp_extension_closed (s : Slicing C)
    {a b : ℝ}
    {A E B : C}
    (hA : s.intervalProp C a b A) (hB : s.intervalProp C a b B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a b E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  · right
    have hPlus : s.phiPlus C E hE < b :=
      s.phiPlus_lt_of_triangle C hE
        (fun hA' ↦ s.phiPlus_lt_of_intervalProp C hA' hA)
        (fun hB' ↦ s.phiPlus_lt_of_intervalProp C hB' hB) hT
    have hMinus : a < s.phiMinus C E hE :=
      s.phiMinus_gt_of_triangle C hE
        (fun hA' ↦ s.phiMinus_gt_of_intervalProp C hA' hA)
        (fun hB' ↦ s.phiMinus_gt_of_intervalProp C hB' hB) hT
    obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C s hE
    exact ⟨F, fun i ↦ by
      constructor
      · calc a < s.phiMinus C E hE := hMinus
          _ = F.φ ⟨F.n - 1, by lia⟩ := s.phiMinus_eq C E hE F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
              F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = s.phiPlus C E hE := (s.phiPlus_eq C E hE F hn hfirst).symm
          _ < b := hPlus⟩

/-! ### Cokernel/quotient containment via the right heart (Lemma 4.3 dual)

In a thin interval `P((a, b))` with `b - a ≤ 1`, the **right heart** `P([b-1, b))` controls
cokernels. Objects in the right heart satisfy `geProp(b-1)` (phases ≥ b-1) and `ltProp(b)`
(phases < b). The key property is:

Given a triangle `K → E → Q → K[1]` with `E ∈ P((a, b))`, if `K` has `geProp(b-1)` (so
`K[1]` has phases ≥ b) and `Q` has `ltProp(b)` (phases < b), then `Q ∈ P((a, b))`.

* **Upper bound** (`φ⁺(Q) < b`): immediate from the `ltProp(b)` hypothesis.
* **Lower bound** (`φ⁻(Q) > a`): by contradiction. If Q has a bottom factor with phase ≤ a,
  then f₂ ≫ β = 0 by hom-vanishing (E phases > a), and β factors through K[1] via
  yoneda_exact₃. Since K[1] has phases ≥ b > a, the factoring morphism vanishes too.
-/

/-- **Phase lower bound from non-strict one-sided containment.** In a triangle
`K → E → Q → K[1]`, if `E` has `φ⁻(E) > a` and `K` satisfies `geProp c` (all phases ≥ c)
with `a < c + 1`, then if `Q` is nonzero, `a < φ⁻(Q)`.

This generalizes `phiMinus_gt_of_triangle_with_gtProp` by replacing `gtProp` (strict)
with `geProp` (non-strict). The key application is cokernel containment via the right
heart, where objects satisfy `geProp(b-1)` rather than `gtProp(b-1)`. -/
theorem Slicing.phiMinus_gt_of_triangle_with_geProp (s : Slicing C)
    {K E Q : C} (hQ : ¬IsZero Q) {a : ℝ}
    (hE_gt : ∀ (hE : ¬IsZero E), a < s.phiMinus C E hE)
    {c : ℝ} (hK_ge : s.geProp C c K) (hca : a < c + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    a < s.phiMinus C Q hQ := by
  obtain ⟨FQ, hnQ, hneQ⟩ := HNFiltration.exists_nonzero_last C s hQ
  rw [s.phiMinus_eq C Q hQ FQ hnQ hneQ]
  by_contra hle
  push_neg at hle
  -- hle : FQ.φ ⟨FQ.n - 1, _⟩ ≤ a (bottom factor has phase ≤ a)
  have hQ_factor_zero :
      ∀ β : Q ⟶ (FQ.triangle ⟨FQ.n - 1, by lia⟩).obj₃, β = 0 := by
    intro β
    -- Step 1: f₂ ≫ β = 0 (E → bottom_factor is zero by hom-vanishing)
    have hfβ : f₂ ≫ β = 0 := by
      by_cases hEZ : IsZero E
      · exact hEZ.eq_of_src (f₂ ≫ β) 0
      · obtain ⟨FE, hnE, hneE⟩ := HNFiltration.exists_nonzero_last C s hEZ
        have hE_gap : ∀ j : Fin FE.n,
            FQ.φ ⟨FQ.n - 1, by lia⟩ < FE.φ j := fun j ↦ by
          have h1 : a < FE.φ ⟨FE.n - 1, by lia⟩ := by
            have := hE_gt hEZ; rwa [s.phiMinus_eq C E hEZ FE hnE hneE] at this
          have h2 : FE.φ ⟨FE.n - 1, by lia⟩ ≤ FE.φ j :=
            FE.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FQ.semistable ⟨FQ.n - 1, by lia⟩) FE hE_gap _
    -- Step 2: By yoneda_exact₃, β factors through K⟦1⟧
    obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₃ (Triangle.mk f₁ f₂ f₃) hT β hfβ
    -- Step 3: γ = 0 (K⟦1⟧ → bottom_factor is zero by hom-vanishing)
    suffices hγ0 : γ = 0 by rw [hγ, hγ0]; exact comp_zero
    by_cases hKZ : IsZero K
    · exact ((shiftFunctor C (1 : ℤ)).map_isZero hKZ).eq_of_src γ 0
    · rcases hK_ge with hKZ' | ⟨GK, hnGK, hGK_ge⟩
      · exact absurd hKZ' hKZ
      · -- Shift GK by 1 to get filtration of K⟦1⟧
        let GKs := GK.shiftHN C s (1 : ℤ)
        -- GKs.φ(j) = GK.φ(j) + 1 ≥ c + 1 > a ≥ FQ.φ(n-1)
        have hKs_gap : ∀ j : Fin GKs.n,
            FQ.φ ⟨FQ.n - 1, by lia⟩ < GKs.φ j := by
          intro j
          change FQ.φ ⟨FQ.n - 1, by lia⟩ < GK.φ j + ((1 : ℤ) : ℝ)
          have h1 : GK.φ ⟨GK.n - 1, by lia⟩ ≤ GK.φ j := by
            apply GK.hφ.antitone
            change j.val ≤ GK.n - 1
            have := j.isLt; have : GKs.n = GK.n := rfl; lia
          have h2 : c ≤ GK.φ ⟨GK.n - 1, by lia⟩ := hGK_ge
          have h3 : ((1 : ℤ) : ℝ) = 1 := by norm_num
          linarith
        exact s.hom_eq_zero_of_lt_phases C
          (FQ.semistable ⟨FQ.n - 1, by lia⟩) GKs hKs_gap γ
  -- Bottom factor is zero — contradiction
  exact hneQ (FQ.isZero_factor_last_of_hom_eq_zero C s hnQ hQ_factor_zero)

/-- **Cokernel/quotient containment in thin intervals (Lemma 4.3 dual).** In a
distinguished triangle `K → E → Q → K[1]` where `E ∈ P((a,b))` and `K` has
`geProp(b-1)` (from right heart membership) and `Q` has `ltProp(b)` (from right
heart membership), then `Q ∈ P((a, b))`.

This is the key property that ensures cokernels computed in the right heart
`P([b-1, b))` stay in the interval `P((a, b))`. Together with
`first_intervalProp_of_triangle` (kernel containment via the left heart), this
establishes that `P((a, b))` is quasi-abelian (Bridgeland Lemma 4.3). -/
theorem Slicing.third_intervalProp_of_triangle (s : Slicing C)
    {a b : ℝ} (hab' : a < b)
    {K E Q : C}
    (hE : s.intervalProp C a b E)
    (hK_ge : s.geProp C (b - 1) K)
    (hQ_lt : s.ltProp C b Q)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.intervalProp C a b Q := by
  by_cases hQ : IsZero Q
  · exact Or.inl hQ
  · -- φ⁺(Q) < b: from ltProp(b) hypothesis
    have hQ_plus : s.phiPlus C Q hQ < b := s.phiPlus_lt_of_ltProp C hQ hQ_lt
    -- φ⁻(Q) > a: from phiMinus_gt_of_triangle_with_geProp
    have hQ_minus : a < s.phiMinus C Q hQ :=
      s.phiMinus_gt_of_triangle_with_geProp C hQ
        (fun hE' ↦ s.phiMinus_gt_of_intervalProp C hE' hE)
        hK_ge (by linarith) hT
    exact s.intervalProp_of_intrinsic_phases C hQ hQ_minus hQ_plus

section HeartClosure

variable [IsTriangulated C] {a b : ℝ} [Fact (a < b)]

/-- If `f : X ⟶ Y` is a monomorphism in the left heart `P((a, a + 1])` and `Y` lies in the
thin interval `P((a, b))`, then `X` also lies in `P((a, b))`. This is the concrete
kernel-side closure condition from Bridgeland Lemma 4.2. -/
theorem Slicing.intervalProp_of_mono_leftHeart (s : Slicing C)
    {X Y : ((s.phaseShift C a).toTStructure).heart.FullSubcategory}
    (hY : s.intervalProp C a b Y.obj) (f : X ⟶ Y) [Mono f] :
    s.intervalProp C a b X.obj := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let q : Y ⟶ cokernel f := cokernel.π f
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) q
  have hKGtShift :
      (s.phaseShift C a).gtProp C 0 K.obj :=
    ((Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a) K.obj).mp
      K.property).1
  have hKGt : s.gtProp C a K.obj := (s.phaseShift_gtProp_zero C a K.obj).mp hKGtShift
  have hQLeShift :
      (s.phaseShift C a).leProp C 1 (cokernel f).obj :=
    ((Slicing.toTStructure_heart_iff (C := C) (s := s.phaseShift C a)
      (cokernel f).obj).mp
      (cokernel f).property).2
  have hQLe : s.leProp C (a + 1) (cokernel f).obj := by
    simpa [add_comm] using
      (s.phaseShift_leProp C a 1 (cokernel f).obj).mp hQLeShift
  have hT' : Pretriangulated.Triangle.mk i.hom q.hom δ ∈ distTriang C := by
    simpa using hT
  have hK_mem_aux : s.intervalProp C a b K.obj :=
    s.first_intervalProp_of_triangle C (Fact.out : a < b) hY hQLe hKGt hT'
  have hKer : IsLimit (KernelFork.ofι f (cokernel.condition f)) :=
    Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ q (cokernel.condition f))
      (cokernelIsCokernel f)
  let e : X ≅ K := IsLimit.conePointUniqueUpToIso hKer
    (Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (TStructure.heart_hι t) i q δ hT)
  exact (s.intervalProp C a b).prop_of_iso
    ⟨e.inv.hom, e.hom.hom,
      by
        exact congrArg InducedCategory.Hom.hom e.inv_hom_id,
      by
        exact congrArg InducedCategory.Hom.hom e.hom_inv_id⟩
    hK_mem_aux

/-- If `f : X ⟶ Y` is an epimorphism in the right heart `P([b - 1, b))` and `X` lies in the
thin interval `P((a, b))`, then `Y` also lies in `P((a, b))`. This is the concrete
cokernel-side closure condition from Bridgeland Lemma 4.2. -/
theorem Slicing.intervalProp_of_epi_rightHeart (s : Slicing C)
    {X Y : ((s.phaseShift C (b - 1)).toTStructureGE).heart.FullSubcategory}
    (hX : s.intervalProp C a b X.obj) (f : X ⟶ Y) [Epi f] :
    s.intervalProp C a b Y.obj := by
  let t := (s.phaseShift C (b - 1)).toTStructureGE
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  obtain ⟨K, i, δ, hT⟩ :=
    Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) f
  have hKGeShift :
      (s.phaseShift C (b - 1)).geProp C 0 K.obj :=
    ((Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) K.obj).mp
      K.property).1
  have hKGe : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp hKGeShift
  have hYLtShift :
      (s.phaseShift C (b - 1)).ltProp C 1 Y.obj :=
    ((Slicing.toTStructureGE_heart_iff (C := C) (s := s.phaseShift C (b - 1)) Y.obj).mp
      Y.property).2
  have hYLt : s.ltProp C b Y.obj := by
    simpa [show 1 + (b - 1) = b by linarith] using
      (s.phaseShift_ltProp C (b - 1) 1 Y.obj).mp hYLtShift
  have hT' : Pretriangulated.Triangle.mk i.hom f.hom δ ∈ distTriang C := by
    simpa using hT
  exact s.third_intervalProp_of_triangle C (Fact.out : a < b) hX hKGe hYLt hT'

end HeartClosure

end TwoHeartEmbedding

end CategoryTheory.Triangulated
