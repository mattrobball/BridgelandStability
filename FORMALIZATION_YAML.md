# formalization.yaml — A Metadata Standard for Autoformalization


## Why this exists

As AI-assisted formalization scales, the community needs a shared way to report what was done, how it was done, and how much to trust the result. Without this, we get a landscape of repos with opaque provenance — some carefully human-reviewed, others autonomously generated with no semantic checking, and no way to tell which is which from the outside.

formalization.yaml is a self-reporting metadata file that lives in the root of a formalization project. Its purpose is not gatekeeping — it is transparency. The mere existence of `author_endorsement: "not-contacted"` or `sorry_in_definitions: 3` makes gaps visible without shaming anyone.


## Acknowledgements

This schema was developed in collaboration with Kevin Buzzard, Johan Commelin, Fabian Glöckle, Bhavik Mehta, Kim Morrison, Oliver Nash, and Adam Topaz.


## Design principles

1. **Normalize disclosure.** The schema succeeds when people fill it in honestly, including the uncomfortable parts. Inspired by [Model Cards](https://arxiv.org/abs/1810.03993) (Mitchell et al.) and [Datasheets for Datasets](https://arxiv.org/abs/1803.09010) (Gebru et al.), which succeeded not because of their specific fields but because they established disclosure as a professional norm.

2. **Required fields, honest answers.** Every field should be filled in, even if the answer is empty or "unknown." This is the NeurIPS reproducibility checklist principle: you must answer each question, even if the answer is "no" or "N/A."

3. **Composable over monolithic.** Automation is a list of methods. Models is a list with roles. This lets people describe what actually happened rather than forcing a single summary.

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

The common format is maintained by the
[mathlib-initiative formalization.yaml project](https://github.com/mathlib-initiative/formalization.yaml).
Palomar adds required provenance, repository-role, responsible-maintainer, and
classification fields. The complete current example is the
[Palomar template](https://github.com/PalomarRegistry/PalomarTemplate/blob/main/formalization.yaml).

```yaml
version: "v0.4"

# ── WHAT ──────────────────────────────────────────────
project:
  name: ""
  url: ""
  date: ""
  authors: []
  license: ""
  responsible_maintainers: []
  organization: ""        # or "independent"
  funding: []             # grants, sponsors, or organizations that funded the work
  contribution_target: "" # mathlib | standalone | blueprint | undecided
  maintenance: ""         # active | best-effort | archival | unknown

repository:
  role: ""                # substantive-development | thin-wrapper
  # substantive_formalization:
  #   id: "owner/repository"
  #   revision: "0000000000000000000000000000000000000000"

classification:
  arxiv: []               # one or two arXiv subject identifiers
  msc2020: []             # one to eight MSC 2020 identifiers

# ── FROM WHAT ─────────────────────────────────────────
sources:
  - title: ""
    authors: []
    id: ""                # DOI, arXiv ID (with version), ISBN, etc.
    type: ""              # paper | book | web discussion | folklore | original-proof | other
    location: ""
    relationship: ""      # formalizes | adapts | independently-proves | background | other
    license: ""           # open | CC-BY | publisher-restricted | unknown
    author_endorsement: ""  # participated | endorsed | no-response | not-contacted | declined | n/a
    prior_formalization: "" # URL/citation of earlier work built upon, or "none"
    size_bytes: 0         # PDF-to-markdown, raw byte count

related_formalizations: []

# ── WITH WHAT ─────────────────────────────────────────
toolchain:
  system: ""              # lean4 | coq | isabelle | agda | ...
  system_version: ""
  dependencies: []        # libraries, pinned versions/commits
  build_manifest_url: ""

# ── PROJECT STATUS ────────────────────────────────────
status:
  scope: ""
  sorry_count: 0
  sorry_in_definitions: 0
  axioms: []
  main_results:
    - declaration: ""
      file: ""
      sorry_count: 0
      axioms: []
      comparator_config: ""
      literature_dependencies: []

# ── HOW (MACHINE) ────────────────────────────────────
automation:
  methods:
    - method: ""          # manual | copilot | agent | autonomous | other
      models: []
      framework: ""       # custom | repoprover | numina-lean-agent | n/a
      tool_setup: ""
      cost:
        wall_time: ""
        compute_time: ""
        person_hours: ""  # human time invested, or "unknown"
        spend_usd: ""     # or "unknown" or "n/a"
        hardware: ""      # "API-only" | "8xH100" | "M1 Max laptop"
        includes_failures: true
      prompting_notes: ""
  spend_usd: ""
  notes: ""

# ── HOW FAITHFUL ──────────────────────────────────────
fidelity:
  divergences: ""
  source_mapping:
    method: ""            # blueprint | inline-comments | mapping-doc | none
    url: ""

# ── REVIEW ────────────────────────────────────────────
review:
  status: ""              # unchecked | agent-reviewed | self-assessed | peer-reviewed | author-verified
  reviewers: []
  notes: ""

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


### project — What is this project?

- **name**: Human-readable project name. E.g. "FormalFrontier-EtingofRepresentationTheory".
- **url**: Repository URL.
- **date**: ISO 8601 date of initial release or current version.
- **authors**: List of people who did the formalization work (not the source authors).
- **license**: License of the formalization code.
- **responsible_maintainers**: People responsible for the submitted formalization. In v0.4 this is a list of names; Palomar requires it to be nonempty.
- **organization**: The group or team behind this. Use "independent" for solo work.
- **funding**: List of grants, sponsors, or organizations that funded the work. Use `[]` if self-funded or unfunded.
- **contribution_target**: Where is this heading? "mathlib" if you intend to upstream, "standalone" if it lives on its own, "blueprint" if it's a blueprint-driven project, "undecided" if you don't know yet.
- **maintenance**: Will this be kept up to date? Be honest. "archival" is a perfectly respectable answer — it means "this was a one-time effort and will not track upstream changes."


### repository — Where is the substantive formalization?

- **role**: Use `substantive-development` when this repository contains the formalization. Use `thin-wrapper` only when it exposes a formalization in another repository to Comparator.
- **substantive_formalization**: Required for a thin wrapper. Give the underlying repository and exact 40-character lowercase revision.


### classification — What mathematics is this?

- **arxiv**: One or two official arXiv subject identifiers.
- **msc2020**: One to eight five-character MSC 2020 identifiers.

Classify the mathematical result, not its use of Lean or AI.


### sources — What mathematical text is being formalized?

- **title**: Title of the source work.
- **authors**: Authors of the source work.
- **id**: A stable identifier. DOI, arXiv ID (include the version, e.g. "2301.12345v3"), or ISBN. This, combined with the identifier, pins the exact source.
- **type**: What kind of document. Affects expectations — formalizing a terse research article is very different from formalizing a detailed textbook.
- **location**: Stable URL or bibliographic location.
- **relationship**: How the result uses the source: `formalizes`, `adapts`, `independently-proves`, `background`, or `other`.
- **license**: License of the source material. Relevant for redistribution of extracted content (e.g. markdown conversions in alignment data).
- **author_endorsement**: Source-author involvement or response: `participated`, `endorsed`, `no-response`, `not-contacted`, `declined`, or `n/a`.
- **related_formalizations**: Record earlier or parallel formalizations separately, with a stable identifier, relationship, and optional note.
- **size_bytes**: Convert the source PDF to markdown and count bytes. A rough but comparable measure of how much material is being formalized. Enables cross-project comparisons.

Palomar requires a nonempty `sources` list. For a result first presented by the formalization, use `type: original-proof` and `relationship: other`. Otherwise at least one source must use `formalizes`, `adapts`, or `independently-proves`.

Previous formalizations may also be listed under `related_formalizations`, with a stable identifier, relationship, and optional note.


### toolchain — What proof assistant environment?

- **system**: Which proof assistant. E.g. "lean4", "coq", "isabelle".
- **system_version**: Pinned version. E.g. "leanprover/lean4:v4.16.0".
- **dependencies**: List of libraries with pinned versions or commit hashes. E.g. `["mathlib4@abc1234", "aesop@def5678"]`. This is what makes the formalization reproducible.
- **build_manifest_url**: Link to the build file — lakefile.lean, \_CoqProject, etc. System-specific by nature, but the field name is generic.


### status — What is complete?

- **scope**: What is and is not formalized, including changed hypotheses, generalizations, restrictions, and omitted material.
- **sorry_count**: Remaining genuine sorries (or equivalent) in the proof development. Do not count the deliberate placeholder in a Comparator challenge.
- **sorry_in_definitions**: Genuine sorries specifically in definitions. Must be 0 for any serious quality claim — a wrong definition with a correct proof of the wrong thing is worse than a sorry.
- **axioms**: All axioms used, including standard axioms such as `Quot.sound`.
- **main_results**: The declarations proving the main results, their files, genuine sorry counts, axioms, Comparator configurations, and literature dependencies.

A literature dependency is a result the formalization relies on but does not prove. The paper being formalized is not automatically a literature dependency.

Projects may keep additional mechanical facts such as `builds_clean` and `builds_clean_date`. The latter records when the build was last verified; toolchains and dependencies evolve, and a project that built clean six months ago may not build today.


### automation — How was AI involved?

`methods` is a list with one entry for each distinct phase, run, or tool.

- **method**: The human/machine division of labor.
  - *manual*: Human writes everything, no AI involved.
  - *copilot*: Human drives, AI suggests (autocomplete, tactic suggestions, Copilot-style assistance).
  - *agent*: AI drives, human steers, approves, or repairs.
  - *autonomous*: AI produces, human evaluates the output only.
- **framework**: What orchestration system ran the pipeline. "custom" for bespoke scripts, "n/a" for manual work.
- **models**: List of AI models used, each with a name and role. A pipeline might use one model for translating natural language to formal statements and another for proof search. Just listing model names without roles loses important information.
- **tool_setup**: Tools, harnesses, plugins, orchestration, and customizations used.
- **prompting_notes**: Free-form notes or examples about the prompts or task specifications used.


### cost — What resources did this consume?

Cost fields live within each automation method; `automation.spend_usd` records the total across the project.

- **wall_time**: Total elapsed time. E.g. "\~4 hours" or "3 weeks".
- **compute_time**: GPU-hours or CPU-hours if relevant.
- **person_hours**: Human time invested. Critical for understanding the true cost of "autonomous" methods that still require significant human debugging. Use "unknown" if you didn't track it.
- **spend_usd**: Dollar cost of API calls. "unknown" is acceptable. "n/a" for manual or local-only work.
- **hardware**: What ran the computation. "API-only" if everything went through cloud APIs, or describe the hardware for local work.
- **includes_failures**: Does the reported cost include dead-end runs, failed attempts, and abandoned approaches? This is a critical honesty flag. Survivorship bias in cost reporting is already a problem in ML; don't import it into formalization.


### fidelity — How faithfully does the output track its source?

- **divergences**: Free text describing where the formalization intentionally or unintentionally diverges from the source. E.g. "universe polymorphism forced a stronger hypothesis in Theorem 3.2" or "simplified to finite-dimensional case only."

**Source mapping:**

- **method**: How is the correspondence between source text and formal code tracked?
  - *blueprint*: A blueprint document (e.g. using leanblueprint).
  - *inline-comments*: Comments in the formal code referencing source locations.
  - *mapping-doc*: A separate document mapping source items to formal names.
  - *none*: No systematic mapping exists.
- **url**: Link to the mapping artifact if external.


### review — How was it reviewed?

- **status**: Review completed before submission. Typical values are `unchecked`, `agent-reviewed`, `self-assessed`, `peer-reviewed`, and `author-verified`.
- **reviewers**: People who performed the review.
- **notes**: More details on the review process.

No review is `status: unchecked` — which is a perfectly honest answer. Only report reviewers and review work that actually occurred.


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
3. Update it when things change (especially status fields after reviews, and `builds_clean_date` periodically).


### Naming

The file should be called `formalization.yaml` and live at the repository root, next to your build manifest.


### Validation

Validate the file against the current JSON Schema:

```bash
check-jsonschema --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json formalization.yaml
```

Palomar additionally checks provenance, repository role, responsible maintainers, and mathematical classifications, and rejects duplicate YAML keys.


### Multiple sources

If a project formalizes multiple sources, add multiple entries under `sources`:

```yaml
sources:
  - title: "Paper A"
    authors: ["..."]
    id: "..."
    relationship: "formalizes"
    # ...
  - title: "Paper B"
    authors: ["..."]
    id: "..."
    relationship: "background"
    # ...
```


### Evolving the schema

The `version` field allows tooling to handle schema evolution. Schema maintainers update it when fields are added, removed, or renamed.
