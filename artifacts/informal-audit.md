# Audit: `@[informal]` Alignments on `origin/claude/issue-11-20260403-1552`

**Paper:** Bridgeland, "Stability conditions on triangulated categories" (math/0212237v3, Annals 2007)
**Branch:** `origin/claude/issue-11-20260403-1552` (1 commit: `8dc7be0`)
**Auditor:** Claude Opus 4.6, reviewed by Codex (gpt-5.4)
**Date:** 2026-04-03

## Summary

The branch applies 17 `@[informal]` tags to declarations across 10 files (21 lines added, 1 changed).
One tag was *corrected* (`HNFiltration`: "Definition 5.7" → "Definition 3.3").
The paper contains **36** numbered declarations total.

### Statement vs proof distinction

Some tags land on **statement definitions** (`def ... : Prop`) rather than on the **proof**
(`theorem`/`noncomputable def`) that discharges them. These must be flagged because a reader
seeing `@[informal "Theorem 7.1"]` on a `Prop`-valued `def` may assume the theorem is proved
there, when it is only *stated* there. The table below marks each tag as:

- **structure/def** — defines a mathematical object (definition-aligned tags are fine here)
- **statement** — a `Prop`-valued `def` that *states* a theorem/proposition without proving it
- **theorem** — an actual proof

## Tag-by-tag audit

| # | Tag | Lean declaration | Kind | Paper decl | Verdict |
|---|-----|-----------------|------|-----------|---------|
| 1 | `"Definition 2.1"` | `StabilityFunction` | structure | Def 2.1: stability function | **Correct.** |
| 2 | `"Definition 2.2"` | `StabilityFunction.IsSemistable` | def (Prop) | Def 2.2: semistable object | **Correct.** |
| 3 | `"Proposition 2.4"` | `HasHNProperty` | def (Prop) | Prop 2.4: HN existence | **Wrong** — this is a *definition* (Def 2.3), not Prop 2.4. |
| 4 | `"Proposition 2.4"` | `hasHN_of_finiteLength` | theorem | Prop 2.4: HN existence | **Questionable** — finite-subobject-lattice special case, not Prop 2.4's chain conditions. |
| 5 | `"Proposition 2.3"` | `hn_unique` | theorem | — | **Wrong** — no Proposition 2.3 exists. Uniqueness is unnumbered text. |
| 6 | `"Definition 3.3"` | `HNFiltration` | structure | Def 3.3: slicing | **Wrong** — Def 3.3 is the *slicing*, not HN filtrations. |
| 7 | `"Definition 4.1"` | `Slicing.intervalProp` | def | Def 4.1: quasi-abelian category | **Wrong** — Def 4.1 = quasi-abelian; P((a,b)) is unnumbered. |
| 8 | `"Definition 4.1"` | `Slicing.IntervalCat` | abbrev | Def 4.1: quasi-abelian category | **Wrong** — same. |
| 9 | `"Definition 4.4"` | `SkewedStabilityFunction` | structure | Def 4.4: skewed stability function | **Questionable** — Lean structure only packages W, α, and nonvanishing on σ-semistable objects; Def 4.4 requires *every* nonzero object to land in a strict half-plane. |
| 10 | `"Definition 5.1"` | `PreStabilityCondition.WithClassMap` | structure | Def 5.1: stability condition | **Correct** (class-map generalization). |
| 11 | `"Definition 5.7"` | `Slicing.IsLocallyFinite` | structure (Prop) | Def 5.7: locally-finite | **Correct.** |
| 12 | `"Definition 5.7"` | `StabilityCondition.WithClassMap` | structure | Def 5.7: locally-finite stab. cond. | **Correct.** |
| 13 | `"Theorem 1.2"` | `CentralChargeIsLocalHomeomorphOnConnectedComponents` | **def (Prop)** | Thm 1.2: local homeomorphism | **STATEMENT ONLY** — this is the *statement* of Thm 1.2, not its proof. The proof is `componentTopologicalLinearLocalModel` in `LocalHomeomorphism.lean:309`. Tag or docstring should say "Statement of Theorem 1.2". |
| 14 | `"Theorem 7.1"` | `exists_eq_Z_and_slicingDist_lt_...` | theorem | Thm 7.1: deformation | **Questionable** — this takes ε₀ as given; the paper existentially produces it. But this *is* a `theorem`, so it's a proof of a variant. |
| 15 | `"Corollary 1.3"` | `WithClassMap.existsComplexManifoldOnConnectedComponent` | theorem | Cor 1.3 | **Questionable** — class-map generalization; states only manifold consequence, not the full local-homeomorphism + manifold of Cor 1.3. |
| 16 | `"Corollary 1.3"` | `NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent` | theorem | Cor 1.3 | **Correct** — numerical specialization. |
| 17 | `"Corollary 1.3"` | `NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent` (Spec.lean) | theorem | Cor 1.3 | **Correct** — standalone spec theorem (not a re-export). |

### Issues found

#### 1. **WRONG: `HNFiltration` tagged as "Definition 3.3"**

The commit *changes* the tag from `@[informal "Definition 5.7"]` to `@[informal "Definition 3.3"]`.

- **Definition 3.3** in the paper is the definition of a **slicing** (full additive subcategories P(φ) with shift, Hom-vanishing, and HN decompositions).
- `HNFiltration` is a structure for an HN filtration with phase data and strictly decreasing phases.
- Neither "Definition 3.3" nor the original "Definition 5.7" is correct. The closest is **Definition 2.3** (abelian HN filtrations) or the filtration data from Definition 3.3(c).

**Fix:** Tag as `"Definition 2.3"` or `"Definition 3.3(c)"`.

#### 2. **WRONG: `Slicing.intervalProp` and `Slicing.IntervalCat` tagged as "Definition 4.1"**

- **Definition 4.1** = quasi-abelian category. P((a,b)) is introduced as unnumbered notation after Def 3.3.

**Fix:** Remove tag or use free-text reference. Closest numbered declaration using this concept is Lemma 4.3.

#### 3. **WRONG: `StabilityFunction.hn_unique` tagged as "Proposition 2.3"**

- **No Proposition 2.3 exists.** Uniqueness is unnumbered text between Def 2.3 and Prop 2.4.
- Codex notes the theorem also only proves factor-count equality, not full filtration uniqueness.

**Fix:** Remove tag.

#### 4. **WRONG: `HasHNProperty` tagged as "Proposition 2.4"**

- `HasHNProperty` is a *definition* — the HN property predicate from Definition 2.3 (last sentence). Proposition 2.4 is the *theorem* proving existence.

**Fix:** Change to `"Definition 2.3"`.

#### 5. **STATEMENT-ONLY: `CentralChargeIsLocalHomeomorphOnConnectedComponents` tagged as "Theorem 1.2"**

- This is a `def ... : Prop` — it *states* Theorem 1.2 but does not prove it.
- The actual proof is `componentTopologicalLinearLocalModel` in `LocalHomeomorphism.lean:309`.
- A reader seeing `@[informal "Theorem 1.2"]` on a `Prop`-valued `def` will assume the theorem is proved here.

**Fix:** Tag should say `"Theorem 1.2 (statement)"` or `"Proposition 6.3 (statement)"`, and the proof declaration `componentTopologicalLinearLocalModel` should get its own `@[informal "Theorem 1.2"]` tag.

#### 6. **Questionable: `hasHN_of_finiteLength` tagged as "Proposition 2.4"** (Codex finding)

- Prop 2.4 in the paper assumes chain conditions (artinian+noetherian). The Lean theorem assumes finite subobject lattices — a special case.

#### 7. **Questionable: `SkewedStabilityFunction` tagged as "Definition 4.4"** (Codex finding)

- Def 4.4 requires every nonzero object to land in a strict half-plane. The Lean structure only packages W, α, and nonvanishing on σ-semistable objects — strictly weaker.

#### 8. **Questionable: `exists_eq_Z_and_slicingDist_lt_...` tagged as "Theorem 7.1"** (Codex finding)

- The paper's Theorem 7.1 existentially produces ε₀ from local finiteness. The Lean theorem takes ε₀ as a given parameter.

#### 9. **Questionable: `WithClassMap.existsComplexManifoldOnConnectedComponent` tagged as "Corollary 1.3"** (Codex finding)

- This is a broader class-map generalization that states only the manifold consequence, not the full local-homeomorphism + manifold statement of Corollary 1.3.

## Classification summary

| Verdict | Count | Tags |
|---------|-------|------|
| **Correct** | 8 | Def 2.1, Def 2.2, Def 5.1, Def 5.7 (×2), Cor 1.3 (numerical, ×2) |
| **Statement-only** | 1 | Thm 1.2 on `CentralChargeIsLocalHomeomorphOnConnectedComponents` |
| **Questionable** | 4 | Prop 2.4 on `hasHN_of_finiteLength`, Def 4.4, Thm 7.1, Cor 1.3 (class-map) |
| **Wrong** | 4 | Def 3.3 on `HNFiltration`, Def 4.1 (×2), Prop 2.3, Prop 2.4 on `HasHNProperty` |

## Coverage: formalized but untagged (26 missing paper declarations)

Codex-verified status of each. **14 confirmed missed**, 2 partial, 6 not formalized, 4 other.

Note: `@[informal]` takes a comment string, so partial matches and statement-only tags can
use comments like `"Proposition 5.3" "forward: stab cond → heart data"` to be precise.

| Paper decl | Lean declaration | File | Status | Proposed tag |
|-----------|-----------------|------|--------|-------------|
| **Def 1.1** | (= Def 5.1, already tagged) | Defs.lean:59 | covered | — |
| **Def 2.3** | `AbelianHNFiltration` + `HasHNProperty` | HarderNarasimhan.lean:48,71 | **MISSED** | `"Definition 2.3" "HN filtration structure"` and `"Definition 2.3" "HN property predicate"` |
| **Def 3.1** | `TStructure` (Mathlib) | Mathlib | external | — |
| **Lemma 3.2** | — | — | **not formalized** | — |
| **Def 3.3** | `Slicing` | Slicing/Defs.lean:82 | **MISSED** | `"Definition 3.3"` |
| **Lemma 3.4** | `phiPlus_triangle_le`, `phiMinus_triangle_le` | Slicing/ExtensionClosure.lean:324,387 | **MISSED** | `"Lemma 3.4" "left inequality"`, `"Lemma 3.4" "right inequality"` |
| **Def 4.1** | `QuasiAbelian` | QuasiAbelian/Basic.lean:278 | **MISSED** | `"Definition 4.1"` |
| **Lemma 4.2** | — | — | **not formalized** | — |
| **Lemma 4.3** | interval quasi-abelian instance + SES↔triangle | IntervalCategory/FiniteLength.lean:209,618 | **MISSED** | `"Lemma 4.3" "P(I) quasi-abelian"`, `"Lemma 4.3" "strict SES ↔ triangle"` |
| **Lemma 5.2** | `P_phi_abelian` | Deformation/IntervalAbelian.lean:805 | **MISSED** | `"Lemma 5.2"` |
| **Prop 5.3** | `toHeartStabilityData`, `toPhasePackage`, `roundtrip` | HeartEquivalence/Reverse.lean:251,695,715,723 | **PARTIAL** | `"Proposition 5.3" "forward: stab cond → heart data"` on `toHeartStabilityData`; `"Proposition 5.3" "reverse: partial, missing central charge + HN"` on `toPhasePackage` |
| **Ex 5.4–5.6** | — | — | not formalized | — |
| **Lemma 6.1** | `intervalProp_of_semistable_slicingDist` | Seminorm.lean:142 | **MISSED** | `"Lemma 6.1"` |
| **Lemma 6.2** | `sector_bound`, `stabSeminorm_dominated_of_basisNhd` | Seminorm.lean:226, Deformation.lean:219,338 | **MISSED** | `"Lemma 6.2" "sector bound"`, `"Lemma 6.2" "seminorm domination"` |
| **Prop 6.3** | `ComponentTopologicalLinearLocalModel`, `componentTopologicalLinearLocalModel` | LocalHomeomorphism.lean:53,270,309 | **MISSED** | `"Proposition 6.3" "V(Σ) packaging"`, `"Proposition 6.3" "local homeomorphism construction"` |
| **Lemma 6.4** | `bridgeland_lemma_6_4`, `eq_of_same_Z_near` | Topology.lean:673, Deformation.lean:529 | **MISSED** | `"Lemma 6.4"`, `"Lemma 6.4" "corollary: σ = τ"` |
| **Def 7.2** | `Slicing.IntervalCat` + thinness hyps | IntervalCategory/Basic.lean:77 | implicit | `"Definition 7.2" "thin subcategory = P((a,b)) with b-a+2ε < 1"` on interval + Setup |
| **Lemma 7.3** | `phase_confinement_from_stabSeminorm` | TargetEnvelope.lean:37 | **MISSED** | `"Lemma 7.3"` |
| **Def 7.4** | — (no standalone predicate) | — | **not formalized** | — |
| **Lemma 7.5** | `semistable_of_target_envelope` | StrictShortExactSequence.lean:731 | **MISSED** | `"Lemma 7.5" "one direction; other by symmetry"` |
| **Lemma 7.6** | `hom_eq_zero_of_deformedPred` | HomVanishing.lean:194 | **MISSED** | `"Lemma 7.6"` |
| **Lemma 7.7** | `interior_has_enveloped_HN`, `interior_has_enveloped_HN_ssf` | HNExistence.lean:45,265 | **MISSED** | `"Lemma 7.7"`, `"Lemma 7.7" "ssf version"` |
| **Prop 8.1** | `slicingDist` (phase part only, no mass term) | Defs.lean:123–156 | **PARTIAL** | `"Proposition 8.1" "slicing metric only; mass term not formalized"` |
| **Lemma 8.2** | — | — | not formalized | — |
| **Thm 9.1** | — | — | not formalized | — |

### Proof of Theorem 1.2 not tagged

The actual proof `componentTopologicalLinearLocalModel` (`LocalHomeomorphism.lean:309`) has no
`@[informal]` tag. Only the statement (`CentralChargeIsLocalHomeomorphOnConnectedComponents`,
a `def ... : Prop`) is tagged. Proposed fix:
- `@[informal "Theorem 1.2" "statement only"]` on the `Prop`-valued `def`
- `@[informal "Theorem 1.2"]` on `componentTopologicalLinearLocalModel`

### Summary

- **14 explicit declarations confirmed MISSED** by the branch
- **2 partially formalized** (Prop 5.3 forward only; Prop 8.1 slicing metric only)
- **6 not formalized** (Ex 5.4–5.6, Lemma 3.2, Lemma 4.2, Def 7.4, Lemma 8.2, Thm 9.1)

## Potential misformalizations

Declarations that claim (via docstrings or naming) to formalize paper results but do not
faithfully match the paper's hypotheses. These are NOT tagged `@[informal]` precisely because
the alignment is wrong.

| Declaration | Claims to be | Actual hypothesis | Paper hypothesis | Gap |
|------------|-------------|-------------------|-----------------|-----|
| `hasHN_of_finiteLength` | Proposition 2.4 | `∀ E, Finite (Subobject E)` | Phase-ordered chain conditions: no infinite subobject chains with strictly increasing phase, no infinite quotient chains with strictly decreasing phase | Finite subobject lattice is strictly stronger; excludes e.g. coherent sheaves on curves which satisfy Prop 2.4 |
| `hasHN_of_artinian_noetherian` | Proposition 2.4 | `∀ E, IsArtinianObject E` + `∀ E, IsNoetherianObject E` | Same phase-ordered chain conditions as above | Artinian + Noetherian forbids *all* infinite chains, not just phase-monotone ones; still strictly stronger than the paper |

**Proposition 2.4 is not faithfully formalized in this repo.** Both existing theorems assume
stronger hypotheses. A faithful formalization would need custom predicates for the phase-ordered
chain conditions.

### Missing parts of formalized declarations

| Paper decl | What's formalized | What's missing |
|-----------|------------------|---------------|
| Lemma 3.4 | φ⁺(A) ≤ φ⁺(E) (`phiPlus_triangle_le`), φ⁻(E) ≤ φ⁻(B) (`phiMinus_triangle_le`) | φ⁺(E) ≤ φ⁺(B) and φ⁻(A) ≤ φ⁻(E) — two of the four inequalities are absent |

### Cleaner statement TODO

| Declaration | Issue | Proposed fix |
|------------|-------|-------------|
| `exists_eq_Z_and_slicingDist_lt_of_stabSeminorm_lt_sin` | Takes ε₀ and `WideSectorFiniteLength` as parameters; paper derives ε₀ from local finiteness | Add a wrapper theorem that takes `σ.locallyFinite` and existentially produces ε₀, matching the paper's Theorem 7.1 statement exactly |
| `HeartStabilityData.toPhasePackage` | Partial reverse of Proposition 5.3: constructs P(φ) with shift + Hom-vanishing but missing central charge construction and HN existence | Complete the reverse direction to produce a full `StabilityCondition` from `HeartStabilityData` |
| Lemma 7.3 (`phase_confinement_of_wSemistable`) | Conclusion uses φ⁻/φ⁺ bounds instead of paper's E ∈ P((ψ−ε,ψ+ε)); `hperturb` is explicit (paper derives from Section 7 setup) | State a wrapper with `intervalProp` conclusion and seminorm hypothesis matching the paper |
| Lemma 7.5 (`semistable_of_target_envelope`) | All Section 7 context (ε₀, seminorm, thinness, envelope bounds) made explicit; paper is just "E enveloped by B and C ⟹ W-ss in B iff W-ss in C" | State a clean wrapper matching the paper's statement |
| Lemma 7.6 (`hom_eq_zero_of_deformedPred`) | Uses `deformedPred` instead of Q(ψ); Section 7 context explicit; paper is just "E ∈ Q(ψ₁), F ∈ Q(ψ₂), ψ₁ > ψ₂ ⟹ Hom(E,F) = 0" | State a clean wrapper with Q(ψ) membership |
| Lemma 7.7 (`interior_has_enveloped_HN_ssf`, `interior_has_enveloped_HN`) | Section 7 context explicit; uses `ThinFiniteLengthInInterval` and `skewedStabilityFunction_of_near`; paper is clean: "A thin, finite length ⟹ interior objects have W-ss HN filtration enveloped by A" | State a clean wrapper matching the paper |
| `PseudoEMetricSpace (Slicing C)` (Lemma 6.1) | `slicingDist` uses sup of phase differences; paper defines d(P,Q) as inf of containment radii. Only `PseudoEMetricSpace` (missing separation d=0 → P=Q). Equivalence of the two formulations not proved. | Prove equivalence of sup/inf formulations; prove separation to upgrade to generalized metric |

## Recommendations

### Fix wrong tags (5 changes)

1. `HNFiltration`: `@[informal "Definition 3.3"]` → `@[informal "Definition 2.3" "HN filtration with phase data; cf. Def 3.3(c) for triangulated version"]`
2. `intervalProp`/`IntervalCat`: `@[informal "Definition 4.1"]` → remove (P((a,b)) is unnumbered in the paper)
3. `hn_unique`: `@[informal "Proposition 2.3"]` → remove (no Prop 2.3 exists; uniqueness is unnumbered)
4. `HasHNProperty`: `@[informal "Proposition 2.4"]` → `@[informal "Definition 2.3" "HN property predicate"]`
5. `CentralChargeIsLocalHomeomorphOnConnectedComponents`: `@[informal "Theorem 1.2"]` → `@[informal "Theorem 1.2" "statement only; proof is componentTopologicalLinearLocalModel"]`

### Qualify questionable tags with comments (4 changes)

6. `hasHN_of_finiteLength`: `@[informal "Proposition 2.4" "finite subobject lattice specialization; paper uses chain conditions"]`
7. `SkewedStabilityFunction`: `@[informal "Definition 4.4" "weaker: only σ-semistable nonvanishing, not all nonzero objects"]`
8. `exists_eq_Z_and_slicingDist_lt_...`: `@[informal "Theorem 7.1" "ε₀ taken as parameter; paper produces it existentially"]`
9. `WithClassMap.existsComplexManifoldOnConnectedComponent`: `@[informal "Corollary 1.3" "class-map generalization; manifold consequence only"]`

### Add missed tags (14+ new tags)

See the "Proposed tag" column in the coverage table above. Each uses a comment string
to specify the exact scope of the alignment (e.g. `"forward direction"`, `"left inequality"`,
`"ssf version"`).
