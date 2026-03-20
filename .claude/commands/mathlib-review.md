# Mathlib Review: Code Quality Audit

Review changed `.lean` files against Mathlib's conventions, style, documentation, proof quality,
and library design standards. Fix all issues found.

## Phase 1: Identify Changes

Run `git diff` (or `git diff HEAD` if there are staged changes) to see what changed. If there are
no git changes, review the most recently modified `.lean` files that the user mentioned or that you
edited earlier in this conversation. Filter to only `.lean` files — skip non-Lean changes entirely.

Read the full content of each changed file (not just the diff) so agents have surrounding context
for naming, imports, and structure analysis.

## Phase 2: Launch Four Review Agents in Parallel

Use the Agent tool to launch all four agents concurrently in a single message. Pass each agent the
full diff AND the full content of changed files so it has complete context.

### Agent 1: Style & Naming Review

Check every changed `.lean` file against Mathlib's formatting and naming rules. For each violation,
report the file, line number, the issue, and the fix.

**Formatting checks:**
1. Lines exceeding 100 characters — suggest where to break
2. `by` on its own line instead of at end of preceding line
3. Wrong indentation: should be 2 spaces standard, 4 for theorem statement continuations
4. Use of `$` operator — must use `<|` instead
5. Use of `lambda`/`λ` — must use `fun`
6. Use of `=>` in anonymous functions — prefer `mapsto` (`↦`)
7. Empty lines inside declarations (linter enforced)
8. Missing spaces around `:`, `:=`, infix operators, or after tactic names
9. Orphaned parentheses or poor alignment in calc blocks
10. Semicolons chaining tactics where newlines are preferred

**Naming checks:**
1. Theorems/lemmas not in `snake_case`
2. Types/structures/classes not in `UpperCamelCase`
3. Functions returning non-Prop not in `lowerCamelCase`
4. Lemma names that don't describe their conclusion (e.g., `helper1` instead of `mul_comm_of_sq`)
5. `of` not used to separate hypotheses in name (`C_of_A_of_B` pattern)
6. Use of `ge`/`gt` where `le`/`lt` is standard for first occurrence
7. Symbol dictionary violations (`+` should be `add`, `*` should be `mul`, `∈` should be `mem`, etc.)
8. Extensionality lemmas not using `.ext`/`.ext_iff` pattern with `@[ext]`
9. Injectivity not using `f_injective`/`f_inj` pattern
10. Non-American English spelling (`generalisation` instead of `generalization`)
11. File names not in `UpperCamelCase.lean`
12. Public declarations containing `aux` in the name
13. Instance names that are excessively long
14. `Type _` instead of `Type*` for universe polymorphism

### Agent 2: Documentation & File Structure Review

Check documentation completeness, accuracy, and file organization. For each issue, report file,
line, the problem, and the fix.

**Copyright & header:**
1. Missing or malformed copyright header (must be first line, Apache 2.0)
2. `Authors:` line missing, has period at end, or uses singular `Author:`
3. Blank line between copyright and imports (should be none)
4. Imports not immediately after copyright

**Module docstring:**
1. Missing `/-! ... -/` module docstring
2. Missing title (first-level `#` header)
3. Missing summary of file contents
4. Missing `## Main results` or `## Main definitions` section listing key declarations
5. Missing `## Notation` section when file introduces notation
6. Subsequent lines not indented by 2 spaces (Markdown in `/-!` requires this)

**Declaration docstrings:**
1. Definitions (`def`, `structure`, `class`, `instance`) without docstrings (linter: `docBlame`)
2. Major theorems without docstrings
3. Docstrings that are incomplete sentences or missing final period
4. Named theorems not **boldfaced** in docstrings
5. Docstrings referencing development history ("originally", "in earlier versions")
6. Docstrings bragging about being "axiom-free" or "sorry-free"

**Section comments:**
1. Missing `/-! ... -/` section headers to organize file
2. Section headers using wrong format (should use `###` inside `/-! -/`)

**File organization:**
1. Files exceeding ~1000 lines that should be split
2. Declarations that seem misplaced (would `#find_home` suggest elsewhere?)
3. Loosely-related sections that could be separate files
4. Duplicated `open` statements

**Import discipline:**
1. Imports that seem unnecessarily heavy (importing high-level files for low-level results)
2. Missing imports (declarations used but not imported)
3. Potential import creep: importing Analysis files into Algebra, etc.

### Agent 3: Proof Quality & Tactic Review

Review proof structure, tactic selection, and efficiency. For each issue, report file, line,
the problem, and suggested improvement.

**Proof structure:**
1. Monolithic proofs exceeding ~50 lines that should extract helper lemmas
2. Long `have` blocks (>30 lines) that should be separate lemmas
3. `by exact <term>` where plain term mode would suffice
4. Redundant tactic sequences: `rw [h]; assumption` should be `rwa [h]`
5. `refine` immediately followed by `exact` — likely should be single `exact`
6. Consecutive `subst` calls that could merge
7. Data being constructed using tactics instead of term mode
8. `if` in tactic mode where `by_cases` would be clearer

**Tactic selection:**
1. Opportunities for `gcongr` instead of manual `mul_le_mul_of_nonneg_left` style
2. Missing use of `positivity`, `fun_prop`, `measurability`, `continuity` where applicable
3. `erw` used where `rw` should work — signals missing API lemma
4. Manual `rfl` after opacity-respecting tactics — signals missing simp lemma
5. Potential for `grind` to close arithmetic or logical goals (instead of manual `omega`, `linarith`, `nlinarith`, or `decide` chains)
6. `simp` with very long lemma lists that could be simplified

**Attributes & API surface:**
1. Missing `@[simp]` on rewrite lemmas that normalize definitions
2. Missing `@[ext]` on extensionality lemmas
3. Missing `@[gcongr]` on monotonicity/congruence lemmas
4. Missing `@[simps]` on projection-heavy definitions (Equiv, bundled homs)
5. `@[simp]` on lemmas that aren't in simp normal form (would `SimpNF` linter flag it?)
6. Named instances never referenced elsewhere that could be anonymous

**Correctness:**
1. Any remaining `sorry` — flag prominently
2. Custom axioms (anything beyond `Classical.choice`, `propext`, `Quot.sound`)
3. `noncomputable` that might be avoidable

### Agent 4: Generality & Reusability Review

Review whether definitions and theorems are stated at the right level of generality for maximum
reusability. This is the hardest review criterion but often the most valuable. For each issue,
report the declaration, what's too specific, and how to generalize.

**Core principle — decomposition:** For every definition or structure, ask: can this be decomposed
into smaller, independently useful pieces that compose back to recover the original? The
decomposition is guided by two criteria:
- **Mathematical utility**: does each piece have standalone mathematical meaning?
- **Ergonomic utility**: does each piece integrate well with the system (typeclass inference,
  simp, the existing API)?

The anti-pattern is a monolithic definition that bakes together several concepts, forcing downstream
users to either accept all of it or rebuild from scratch. The test is: if someone working on a
different problem would benefit from one of the pieces in isolation, it should be factored out.
Conversely, if a decomposition creates pieces with no independent use, it is over-engineering.

Common instances of this principle:
- A `def : Prop` that is always used as an assumption should be a `class` (the piece "this property
  holds" becomes findable by instance resolution).
- A structure field that is always determined by other fields should be a derived `def` (eliminates
  coherence obligations at every construction site).
- A construction that composes two universal properties should expose each lift separately (the inner
  lift may be useful on its own).

**Generality of type class assumptions:**
1. Theorems assuming `Ring` where `Semiring` suffices
2. Theorems assuming `Field` where `DivisionRing` or `CommRing` suffices
3. Theorems assuming `[Fintype α]` where `[Finite α]` would work
4. Theorems on concrete types that hold for abstract algebraic structures
5. `[MetricSpace X]` where `[PseudoMetricSpace X]` or `[TopologicalSpace X]` suffices
6. `[MeasurableSpace Ω] [MeasureSpace Ω]` where just `[MeasurableSpace Ω] (μ : Measure Ω)` works
7. Unnecessary `Nonempty` or `Inhabited` assumptions

**Generality of definitions:**
1. Definitions hardcoded to specific types that could be parametric
2. Structures with fields that could be derived from weaker data
3. Bundled morphisms not using `FunLike` API
4. Subobject types not using `SetLike` API
5. Missing coercion instances to parent types

**Reusability patterns:**
1. Inline proofs that prove useful intermediate facts — should these be separate lemmas?
2. Helper lemmas marked `private` that could be useful elsewhere
3. Definitions that don't provide a complete API (missing `_iff`, `_comm`, `_assoc` companions)
4. Equiv/Iso declarations without corresponding map/hom declarations (or vice versa)
5. Theorems stated for specific operations when they hold for any morphism of a given type

**Simp normal form:**
1. Multiple equivalent representations without simp lemmas establishing canonical form
2. Coercion diamonds without `rfl`-proved simp lemmas connecting paths
3. Missing companion lemmas: if you define `foo`, do `foo_zero`, `foo_one`, `foo_add`, etc. exist?

**Future-proofing:**
1. Would the definition compose well with existing Mathlib infrastructure?
2. Are there obvious generalizations the literature suggests?
3. Does the definition align with Mathlib's preferred patterns for similar objects?

## Phase 3: Fix Issues

Wait for all four agents to complete. Aggregate their findings and:

1. **Fix each issue directly** by editing the files. If a finding is a false positive or not worth
   addressing (e.g., a naming suggestion that conflicts with mathematical convention), note it
   and move on — do not argue with the finding, just skip it.

2. **Run the Mathlib linter** after all fixes:
   ```bash
   lake exe runLinter <ModuleName>
   ```
   for each changed module. Fix any additional linter findings.

3. **Run `lake exe lint-style`** to catch remaining text-based style issues.

4. **Briefly summarize** what was fixed, organized by category (style, documentation, proof quality,
   generality). If the code was already clean, confirm that.
