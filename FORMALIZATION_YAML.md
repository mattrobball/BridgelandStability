# formalization.yaml — A Metadata Standard for Autoformalization


## Why this exists

As AI-assisted formalization scales, the community needs a shared way to report what was done, how it was done, and how much to trust the result. Without this, we get a landscape of repos with opaque provenance — some carefully human-reviewed, others autonomously generated with no semantic checking, and no way to tell which is which from the outside.

formalization.yaml is a self-reporting metadata file that lives in the root of a formalization project. Its purpose is not gatekeeping — it is transparency. The mere existence of `author_contacted: false` or `sorry_in_definitions: 3` makes gaps visible without shaming anyone.


## Acknowledgements

This schema was developed in collaboration with Kevin Buzzard, Johan Commelin, Fabian Glöckle, Bhavik Mehta, Kim Morrison, Oliver Nash, and Adam Topaz.


## Design principles

1. **Normalize disclosure.** The schema succeeds when people fill it in honestly, including the uncomfortable parts. Inspired by [Model Cards](https://arxiv.org/abs/1810.03993) (Mitchell et al.) and [Datasheets for Datasets](https://arxiv.org/abs/1803.09010) (Gebru et al.), which succeeded not because of their specific fields but because they established disclosure as a professional norm.

2. **Required fields, honest answers.** Every field should be filled in, even if the answer is empty or "unknown." This is the NeurIPS reproducibility checklist principle: you must answer each question, even if the answer is "no" or "N/A."

3. **Composable over monolithic.** Review is a list of passes. Models is a list with roles. This lets people describe what actually happened rather than forcing a single summary.

4. **System-agnostic.** Works for Lean, Coq, Isabelle, Agda, or anything else. System-specific details belong in the build manifest, not here.


## Analogous standards

| Standard | Domain | Key insight borrowed |
|---|---|---|
| Model Cards | ML models | Structured disclosure as professional norm |
| Datasheets for Datasets | ML datasets | Provenance and motivation sections |
| CITATION.cff / CodeMeta | Software | Lightweight YAML/JSON with extensibility |
| NeurIPS reproducibility checklist | Research | Mandatory self-reporting, even when the answer is "no" |
| FAIR principles | Research data | Findable, Accessible, Interoperable, Reusable as design tests |
| W&B / MLflow experiment tracking | ML experiments | "What model" without "what cost" is useless |


## The schema

```yaml
# formalization.yaml v0.1
schema_version: "0.1"

# ── WHAT ──────────────────────────────────────────────
artifact:
  name: ""
  url: ""
  description: ""
  date: ""
  authors: []
  license: ""
  organization: ""        # or "independent"
  funding: []             # grants, sponsors, or organizations that funded the work
  contribution_target: "" # mathlib | standalone | blueprint | undecided
  maintenance: ""         # active | best-effort | archival | unknown

# ── FROM WHAT ─────────────────────────────────────────
source:
  title: ""
  authors: []
  id: ""                  # DOI, arXiv ID (with version), ISBN, etc.
  type: ""                # textbook | article | lecture-notes | monograph
  license: ""             # open | CC-BY | publisher-restricted | unknown
  author_contacted: false
  prior_formalization: "" # URL/citation of earlier work built upon, or "none"
  size_bytes: 0           # PDF-to-markdown, raw byte count

# ── WITH WHAT ─────────────────────────────────────────
toolchain:
  system: ""              # lean4 | coq | isabelle | agda | ...
  system_version: ""
  dependencies: []        # libraries, pinned versions/commits
  build_manifest_url: ""

# ── HOW (MACHINE) ────────────────────────────────────
automation:
  method: ""              # manual | copilot | agent | autonomous
  framework: ""           # custom | repoprover | numina-lean-agent | n/a
  models:
    - name: ""
      role: ""            # proof-search | statement-generation | repair | translation

# ── HOW MUCH ──────────────────────────────────────────
cost:
  wall_time: ""
  compute_time: ""
  person_hours: ""        # human time invested, or "unknown"
  api_spend: ""           # or "unknown" or "n/a"
  hardware: ""            # "API-only" | "8xH100" | "M1 Max laptop"
  includes_failures: true

# ── HOW FAITHFUL ──────────────────────────────────────
fidelity:
  sorry_count: 0
  sorry_in_definitions: 0
  sorry_details: ""        # origin and nature of remaining sorries
  axiom_count: 0
  axiom_details: ""
  builds_clean: true
  builds_clean_date: ""   # ISO 8601 — toolchains break things

  human_review:            # list of review passes; empty if none
    - depth: ""            # endorsed | validated | reconstructed
      coverage: ""         # sampled | definitions-only | complete
      expertise:
        math: false
        formal: false
      independent: false
      url: ""

  machine_review:
    performed: false
    tools: []              # linter names, LLM review agents, comparator, etc.
    methodology: ""        # linting | semantic-comparison | adversarial | re-formalized
    coverage: ""           # sampled | definitions-only | complete
    url: ""

  source_mapping:
    method: ""             # blueprint | inline-comments | mapping-doc | none
    url: ""

  known_divergences: ""

# ── SELF-ASSESSMENT ──────────────────────────────────
self_assessment:
  source_detail_level: ""   # terse | standard | detailed | exhaustive
  math_sophistication: ""   # undergrad | early-grad | advanced-grad | research
  dependency_distance: ""   # near | moderate | far
  formalization_quality: "" # sketch | draft | polished | publication-ready

# ── COMMUNITY ────────────────────────────────────────
community:
  related_projects: []
  upstream_prs: []
  reviews: []

# ── ACKNOWLEDGEMENTS ─────────────────────────────────
acknowledgements: ""

notes: ""
```


## Field-by-field guide


### artifact — What is this project?

- **name**: Human-readable project name. E.g. "FormalFrontier-EtingofRepresentationTheory".
- **url**: Repository URL.
- **description**: One-line summary of what is formalized.
- **date**: ISO 8601 date of initial release or current version.
- **authors**: List of people who did the formalization work (not the source authors).
- **license**: License of the formalization code.
- **organization**: The group or team behind this. Use "independent" for solo work.
- **funding**: List of grants, sponsors, or organizations that funded the work. Use `[]` if self-funded or unfunded.
- **contribution_target**: Where is this heading? "mathlib" if you intend to upstream, "standalone" if it lives on its own, "blueprint" if it's a blueprint-driven project, "undecided" if you don't know yet.
- **maintenance**: Will this be kept up to date? Be honest. "archival" is a perfectly respectable answer — it means "this was a one-time effort and will not track upstream changes."


### source — What mathematical text is being formalized?

- **title**: Title of the source work.
- **authors**: Authors of the source work.
- **id**: A stable identifier. DOI, arXiv ID (include the version, e.g. "2301.12345v3"), or ISBN. This, combined with the identifier, pins the exact source.
- **type**: What kind of document. Affects expectations — formalizing a terse research article is very different from formalizing a detailed textbook.
- **license**: License of the source material. Relevant for redistribution of extracted content (e.g. markdown conversions in alignment data).
- **author_contacted**: Did you reach out to the author(s) of the source material? A boolean. The point is not to require consent but to encourage communication.
- **prior_formalization**: If this builds on someone else's earlier formalization or blueprint, link it here. "none" if starting from scratch. This is about intellectual lineage and avoiding duplicated effort.
- **size_bytes**: Convert the source PDF to markdown and count bytes. A rough but comparable measure of how much material is being formalized. Enables cross-project comparisons.


### toolchain — What proof assistant environment?

- **system**: Which proof assistant. E.g. "lean4", "coq", "isabelle".
- **system_version**: Pinned version. E.g. "leanprover/lean4:v4.16.0".
- **dependencies**: List of libraries with pinned versions or commit hashes. E.g. `["mathlib4@abc1234", "aesop@def5678"]`. This is what makes the formalization reproducible.
- **build_manifest_url**: Link to the build file — lakefile.lean, \_CoqProject, etc. System-specific by nature, but the field name is generic.


### automation — How was AI involved?

- **method**: The human/machine division of labor.
  - *manual*: Human writes everything, no AI involved.
  - *copilot*: Human drives, AI suggests (autocomplete, tactic suggestions, Copilot-style assistance).
  - *agent*: AI drives, human steers, approves, or repairs.
  - *autonomous*: AI produces, human evaluates the output only.
- **framework**: What orchestration system ran the pipeline. "custom" for bespoke scripts, "n/a" for manual work.
- **models**: List of AI models used, each with a name and role. A pipeline might use one model for translating natural language to formal statements and another for proof search. Just listing model names without roles loses important information.


### cost — What resources did this consume?

- **wall_time**: Total elapsed time. E.g. "\~4 hours" or "3 weeks".
- **compute_time**: GPU-hours or CPU-hours if relevant.
- **person_hours**: Human time invested. Critical for understanding the true cost of "autonomous" methods that still require significant human debugging. Use "unknown" if you didn't track it.
- **api_spend**: Dollar cost of API calls. "unknown" is acceptable. "n/a" for manual or local-only work.
- **hardware**: What ran the computation. "API-only" if everything went through cloud APIs, or describe the hardware for local work.
- **includes_failures**: Does the reported cost include dead-end runs, failed attempts, and abandoned approaches? This is a critical honesty flag. Survivorship bias in cost reporting is already a problem in ML; don't import it into formalization.


### fidelity — How trustworthy is the output?

**Mechanical facts:**

- **sorry_count**: Remaining sorrys (or equivalent) in the project.
- **sorry_in_definitions**: sorrys specifically in definitions. Must be 0 for any serious quality claim — a wrong definition with a correct proof of the wrong thing is worse than a sorry.
- **sorry_details**: Origin and nature of remaining sorries. A sorry inserted by a tool like comparator for alignment testing is very different from a genuine gap. E.g. "12 comparator-inserted alignment probes, 3 genuine gaps in Section 4."
- **axiom_count**: Non-standard axioms beyond the proof assistant's foundations.
- **axiom_details**: What axioms and why. E.g. "classical choice used for Zorn's lemma application" or "assumed Riemann hypothesis."
- **builds_clean**: Does the project build without errors?
- **builds_clean_date**: When was this last verified? Toolchains and dependencies evolve — a project that built clean six months ago may not build today.

**Human review:**

A list of review passes. Each pass records:

- **depth**: How deeply did the reviewer engage with the formal code?
  - *endorsed*: Accepted based on summary, LLM output, or trust — didn't read the code.
  - *validated*: Directly read and validated the formal code.
  - *reconstructed*: Independently re-derived the formalization and compared.
- **coverage**: What was reviewed?
  - *sampled*: Spot-checked selected parts.
  - *definitions-only*: Reviewed all definitions but not proofs.
  - *complete*: Reviewed everything.
- **expertise.math**: Does the reviewer have domain expertise in the relevant mathematics?
- **expertise.formal**: Does the reviewer have expertise in the proof assistant used?
- **independent**: Does the reviewer have no relationship to the formalization authors?

Multiple passes are common and encouraged. E.g. "a domain mathematician validated the definitions, and a Lean expert endorsed the proof structure" is two entries. No review is an empty list — which is a perfectly honest answer.

- **url**: Link to review notes, PR discussion, or assessment document.

**Machine review:**

- **performed**: Was any automated review conducted?
- **tools**: List of tools used. E.g. `["mathlib-linter", "leanprover/comparator", "gpt-4-review-agent"]`.
- **methodology**: What kind of checking?
  - *linting*: Style and convention checks.
  - *semantic-comparison*: Automated comparison of formal statements against natural language source.
  - *adversarial*: Automated attempts to find counterexamples or break proofs.
  - *re-formalized*: Independent machine re-formalization for comparison.
- **coverage**: Same scale as human review.
- **url**: Link to review output or logs.

**Source mapping:**

- **method**: How is the correspondence between source text and formal code tracked?
  - *blueprint*: A blueprint document (e.g. using leanblueprint).
  - *inline-comments*: Comments in the formal code referencing source locations.
  - *mapping-doc*: A separate document mapping source items to formal names.
  - *none*: No systematic mapping exists.
- **url**: Link to the mapping artifact if external.

- **known_divergences**: Free text describing where the formalization intentionally or unintentionally diverges from the source. E.g. "universe polymorphism forced a stronger hypothesis in Theorem 3.2" or "simplified to finite-dimensional case only."


### self_assessment — Subjective characterization

These axes help consumers quickly gauge what kind of project this is.

- **source_detail_level**: How detailed is the source text?
  - *terse*: Minimal proofs, many steps left to the reader.
  - *standard*: Normal level of detail for the genre.
  - *detailed*: Unusually thorough exposition.
  - *exhaustive*: Every step spelled out.
- **math_sophistication**: What level of mathematics?
  - *undergrad*: Undergraduate-level material.
  - *early-grad*: First-year graduate level.
  - *advanced-grad*: Advanced graduate / early research level.
  - *research*: Current research frontier.
- **dependency_distance**: How much new material vs. near-existing library content?
  - *near*: Most definitions and results are close to what's already in the library.
  - *moderate*: Significant new material but building on existing foundations.
  - *far*: Mostly new territory requiring substantial new development.
- **formalization_quality**: Overall quality of the formal code.
  - *sketch*: Proof sketches, many sorries, exploratory.
  - *draft*: Mostly complete but rough around the edges.
  - *polished*: Clean, well-documented, follows library conventions.
  - *publication-ready*: Ready for upstream contribution or archival.


### community — Coordination with others

- **related_projects**: URLs of other formalization efforts covering overlapping material. Checking this before starting avoids duplicated work.
- **upstream_prs**: List of PR numbers for contributions to the parent library (e.g. Mathlib PR numbers).
- **reviews**: Links to external reviews, assessments, or discussions of this project.


### acknowledgements

Free-form text acknowledging individuals, projects, or organizations whose work this formalization depends on or benefited from.


### notes

Free-form text for anything not captured above.


## How to use this


### Adding to your project

1. Copy `formalization.yaml` to the root of your repository.
2. Fill in every field. Use "unknown", "n/a", "none", `false`, `0`, or `[]` where appropriate — the point is that every field has a value.
3. Update it when things change (especially fidelity fields after reviews, and `builds_clean_date` periodically).


### Naming

The file should be called `formalization.yaml` and live at the repository root, next to your build manifest.


### Validation

A JSON Schema for programmatic validation is planned. In the meantime, the file is valid YAML — any YAML linter will catch syntax errors.


### Multiple sources

If a project formalizes multiple sources, use a list under `source`:

```yaml
source:
  - title: "Paper A"
    authors: ["..."]
    id: "..."
    # ...
  - title: "Paper B"
    authors: ["..."]
    id: "..."
    # ...
```


### Evolving the schema

The `schema_version` field allows tooling to handle schema evolution. Bump the version when fields are added, removed, or renamed.
