---
name: verso
description: "Build, edit, debug, and extend Verso documentation sites for Lean 4 projects. Use when working with Verso markup, site generation, styling, or any Verso-related task."
---

# Verso Documentation Skill

Comprehensive reference for the Verso documentation system for Lean 4.

---

## 0. CRITICAL WARNING: NEVER PARSE LEAN WITH REGEX OR PYTHON

**Do not attempt to parse, analyze, or extract information from `.lean` files
using Python, regex, sed, awk, or any tool other than Lean itself.**

Lean's syntax is context-dependent, macro-extensible, and has custom operators,
notation, and elaboration rules that make it fundamentally impossible to parse
correctly with regex or traditional parsers. Examples of what will go wrong:

- Notation declarations change the grammar at elaborate-time
- `macro` and `syntax` extend the parser dynamically
- String interpolation, doc comments, and attribute syntax have complex nesting
- Indentation-sensitive syntax (e.g., `by` blocks, `where` clauses)
- Unicode operators and custom infixes

**Instead:** Use Lean's own environment APIs (`importModules`, `env.find?`,
`findDocString?`, `ppExpr`, `Expr.getUsedConstants`, `DeclarationRanges`),
SubVerso's extraction tools (`subverso-extract-mod`), or Lake facets
(`:highlighted`, `:docs`) to extract structured data. Write a `lean_exe` or
`lean_lib` that walks the environment and emits JSON — then post-process the
JSON with Python.

The only safe thing to do with `.lean` files in Python is copy them verbatim
or inject well-known comment markers (like `-- ANCHOR:`) at known line numbers
obtained from Lean's own APIs.

---

## 1. WHAT VERSO IS

Verso is a documentation authoring system for Lean 4, developed by the Lean
team. It provides a markup language (similar to but NOT Markdown), an
elaboration pipeline that can embed and check Lean code, and multi-format
output (HTML multi-page, HTML single-page, TeX). SubVerso is a companion
library providing syntax highlighting with hover info.

### Genres

| Genre | Import | Purpose |
|-------|--------|---------|
| `Manual` | `VersoManual` | Books, reference manuals, multi-page sites |
| `Blog` | `VersoBlog` | Websites and blogs |
| `Tutorial` | `VersoTutorial` | Interactive tutorials |
| `Literate` | `VersoLiterate` | Literate programming (docstrings rendered as text) |

The Manual genre is the most common. The Lean Reference Manual, Sutherland-NT,
and most formalization exposition sites use it.

### Literate mode (alternative)

Used by Tao's Analysis project. Configured via `literate.toml`, built with
`lake build :literateHtml`. Renders docstrings as running text automatically.
No hand-authored markup needed.

---

## 2. PROJECT SETUP

### Minimal lakefile.toml

```toml
name = "MyDocs"
version = "0.1.0"

[[require]]
name = "verso"
git = "https://github.com/leanprover/verso"
rev = "v4.29.0"       # match your lean-toolchain

[[require]]
name = "MyProject"
path = "/path/to/project"   # or git = "..."

[[lean_lib]]
name = "Docs"

[[lean_exe]]
name = "generate-docs"
root = "Main"
```

### Minimal Main.lean

```lean
import VersoManual
import Docs.Root

open Verso.Genre Manual

def main := manualMain (%doc Docs.Root)
```

### Minimal Root.lean

```lean
import VersoManual

open Verso.Genre Manual

#doc (Manual) "My Documentation" =>

Welcome to the documentation.
```

### Build and serve

```bash
lake update                   # first time only
lake exe cache get || true    # fetch caches
lake build generate-docs      # compile executable
lake exe generate-docs        # render to _out/html-multi/

# Serve locally (file:// won't work — hover JSON fetch needs HTTP)
python3 -m http.server 8000 --directory _out/html-multi/
```

### CLI flags for manualMain

`--output DIR`, `--depth N`, `--draft`, `--verbose`, `--with-tex`,
`--without-tex`, `--with-html-single`, `--without-html-single`,
`--with-html-multi`, `--without-html-multi`, `--with-word-count FILE`.

---

## 3. MARKUP SYNTAX

### Text and paragraphs

Plain text on consecutive lines forms a paragraph. Blank lines separate paragraphs.

### Emphasis and bold

```
_emphasized text_     ← italic (underscores)
*bold text*           ← bold (asterisks)
```

**CRITICAL:** Unlike Markdown, `*` = **bold** and `_` = _emphasis_ in Verso.
This is the opposite of most Markdown flavors.

### Links

```
[Link text](https://example.com)     ← inline link
[Link text][ref-id]                  ← reference link

[ref-id]: https://example.com        ← reference definition
```

### Images

```
![Alt text](image.png)
```

### Math

```
$`\sum_{i=0}^{n} i`        ← inline math (dollar + backtick)
$$`\sum_{i=0}^{n} i`       ← display math (double dollar + backtick)
```

**NOT** `$...$` like LaTeX. The backtick after `$` is mandatory. KaTeX is
used for rendering (enabled by default).

### Inline code

```
The term `main` is...       ← backtick code span
`` `quotedName ``            ← double backticks for content with backticks
```

### Code blocks

````
```
plain code block (no processing)
```

```lean
def x := 5                  ← elaborated Lean code with hover info
#check x
```

```lean (name := ex1)
#eval 2 + 2                 ← named block, output capturable
```

```leanOutput ex1
4                            ← validates expected output
```

```signature
def List.map (f : α → β) (xs : List α) : List β
```                          ← signature only, checked against env

```anchor MyAnchor (module := MyModule) (project := "path")
-- external code with pre-computed highlighting
```
````

### Headers

```
# Top Level
## Second Level
### Third Level
```

Headers **must be well-nested**: the first header uses `#`, each subsequent
header adds at most one more `#` than the previous. Skipping levels
(e.g., `#` then `###`) is an error.

**CRITICAL:** `#` headings trigger **page splitting** by default. See
Section 7 for how to control this.

### Lists

```
* Unordered item (also - or +)
  * Nested item

1. Ordered item
2) Alternative ordered indicator

: Term
  Definition (description list)
```

### Blockquotes

```
> Quoted text
  continues here
```

### Directives (block-level wrappers)

```
:::directiveName arg1 (named := "value")
Content blocks here
:::

::::outerDirective
:::innerDirective
Nested content
:::
::::
```

### Roles (inline extensions)

```
{roleName "arg"}`inline content`
{roleName "arg"}[multiple words of content]
```

### Footnotes

```
Text with a footnote[^note-id].

[^note-id]: The footnote content.
```

---

## 4. SPECIAL CHARACTERS AND ESCAPING

These characters are **special** in Verso inline text:

| Char | Meaning | Escape |
|------|---------|--------|
| `_`  | Emphasis (italic) | `\_` |
| `*`  | Strong (bold) | `\*` |
| `[`  | Link start | `\[` |
| `]`  | Link end | `\]` |
| `{`  | Directive/role start | `\{` |
| `}`  | Directive/role end | `\}` |
| `` ` `` | Code span | `` \` `` |
| `\`  | Escape character | `\\` |
| `$`  | Math (when followed by `` ` ``) | `\$` |
| `!`  | Image (when followed by `[`) | `\!` |

**Lesson learned:** Unescaped `{` in prose text is interpreted as a Verso
directive and will cause a build error. Unescaped `_` triggers emphasis
parsing. When programmatically generating Verso content from external
text (e.g., JSON prose databases), you MUST sanitize all special characters.

### Sanitization strategy for external prose

When converting external text (e.g., LaTeX-style prose) to Verso:

1. Split on `$...$` math boundaries first
2. Math spans: convert `$...$` → `$`...`` (Verso syntax)
3. Non-math spans: escape or replace `_`, `*`, `[`, `]`, `{`, `}`
4. Preserve backtick code spans (`` `...` ``) intact — Verso uses these too
5. Display math `$$...$$` → `$$`...``

---

## 5. COMMANDS, ROLES, AND DIRECTIVES

### Block commands

| Command | Usage | Purpose |
|---------|-------|---------|
| `{docstring Name}` | `{docstring List.map}` | Render declaration signature with hover |
| `{include N Module}` | `{include 0 Docs.Chapter1}` | Include sub-document at level N |
| `{theIndex}` | `{theIndex}` | Render accumulated index |
| `{licenseInfo}` | `{licenseInfo}` | Render license info |
| `{optionDocs opt}` | `{optionDocs pp.deepTerms.threshold}` | Option documentation |

### Roles (inline)

| Role | Usage | Purpose |
|------|-------|---------|
| `lean` | `` {lean}`2 + f 4` `` | Inline Lean term with hover |
| `leanCommand` | `` {leanCommand}`#check Nat` `` | Inline Lean command |
| `name` | `` {name}`List.map` `` | Link to named constant |
| `ref` | `{ref "tag"}[link text]` | Cross-reference to tagged section |
| `deftech` | `{deftech}_stability condition_` | Define technical term |
| `tech` | `{tech}[stability condition]` | Reference technical term |
| `margin` | `{margin}[Side note text]` | Marginal note |
| `draft` | `` {draft}`draft-only text` `` | Draft-only content |
| `index` | `{index}[term]` | Add index entry |
| `citep` | `{citep someRef}[]` | Parenthetical citation |
| `citet` | `{citet someRef}[]` | Textual citation |

### Directives (block)

| Directive | Purpose |
|-----------|---------|
| `:::paragraph` | Logical paragraph grouping |
| `:::table (header := true)` | Table from nested lists |
| `:::draft` | Draft-only block |
| `:::tactic "name"` | Tactic documentation |

### Code block types

| Name | Purpose |
|------|---------|
| `` ```lean `` | Elaborate Lean commands (full highlighting + hover) |
| `` ```leanTerm `` | Elaborate Lean term |
| `` ```leanOutput `` | Validate expected output from named block |
| `` ```signature `` | Type signature display (checked against env) |
| `` ```anchor `` | External pre-highlighted code by anchor name |

---

## 6. `{docstring}` IN DEPTH

### What it does

`{docstring Fully.Qualified.Name}` looks up a declaration in the Lean
environment and renders:
- Kind badge (theorem, def, structure, class, instance)
- Full type signature with SubVerso hover info
- Structure fields, constructor, extends info (for structures/classes)

### Requirements

1. The module containing the declaration must be **imported**
2. `import VersoManual` must be present
3. `open Verso.Genre Manual` must be present
4. `set_option verso.docstring.allowMissing true` — prevents build failure
   when a declaration has no docstring (RECOMMENDED for auto-generated docs)

### Parameters

| Parameter | Type | Purpose |
|-----------|------|---------|
| `allowMissing` | `Bool` | Warn instead of error on missing docstrings |
| `hideFields` | `Bool` | Hide structure/class fields |
| `hideStructureConstructor` | `Bool` | Hide the constructor |
| `label` | `String` | Custom label |

### Key behaviors

- Build cost is **cheap** — just environment lookups, no re-elaboration
- Shows signature only, **not** declaration body. For bodies, use `` ```anchor ``
- Creates a **duplicate TOC entry** with the full qualified name alongside
  the heading entry. Fix with CSS:
  ```css
  #toc .split-toc li:has(> a > code) { display: none; }
  ```

---

## 7. PAGE STRUCTURE AND SPLITTING

### `#doc (Manual)` declaration

```lean
#doc (Manual) "Page Title" =>
```

Creates a `Part Manual` value. The title becomes the page heading and
sidebar entry. Reference from another file with `%doc ModuleName`.

### Metadata blocks (`%%%`)

Must come immediately after `#doc` or a `#` heading, before content:

```
#doc (Manual) "Title" =>
%%%
htmlSplit := .never
tag := "my-section"
shortTitle := "Short"
file := "custom-filename"
number := false
draft := true
authors := ["Author"]
htmlToc := true
%%%
```

| Field | Type | Default | Purpose |
|-------|------|---------|---------|
| `htmlSplit` | `HtmlSplitMode` | `.default` | Page splitting control |
| `tag` | `Option Tag` | `none` | Cross-reference tag |
| `shortTitle` | `Option String` | `none` | Shorter title for TOC |
| `shortContextTitle` | `Option String` | `none` | Even shorter, for breadcrumbs |
| `file` | `Option String` | `none` | Custom HTML filename |
| `number` | `Bool` | `true` | Numbered section |
| `draft` | `Bool` | `false` | Draft-only section |
| `htmlToc` | `Bool` | `true` | Show sub-page list |
| `authors` | `List String` | `[]` | Author list |

### HtmlSplitMode

```lean
inductive HtmlSplitMode where
  | default   -- follow the global htmlDepth setting
  | never     -- this part and ALL children stay on one page
```

### Global depth

`htmlDepth` in `Config` (default: 2) controls how many heading levels deep
the document splits into separate pages. Override per-part with
`htmlSplit := .never`.

### PAGE SPLITTING LESSONS (hard-won)

1. **`#` headings cause page splits** at the configured depth. If a page
   should not split, set `htmlSplit := .never` in the `%%%` block.

2. **Root/landing pages should NOT use `htmlSplit := .never`** — it inlines
   ALL sub-content onto one huge page.

3. **Root/landing pages should NOT use `#` or `##` headings** for intro
   sections — they will cause unwanted page splits (or build errors in some
   contexts). Use bold text (`*Section Label*`) and style it via CSS instead.

4. **Leaf pages** (pages with actual content, no sub-parts) should use
   `htmlSplit := .never` so their `#` headings don't split into tiny pages.

5. **Chapter/group pages** that only contain `{include}` directives should
   NOT set `htmlSplit` — let the default splitting apply so sub-pages render
   as separate pages.

### `{include}` directive

```
{include 0 Docs.Chapter1}
```

- `{include N ModuleName}` — includes the module's `#doc` as a sub-part
- `N` controls heading demotion: `0` = keep original level, `1` = demote by one, etc.
- The module must contain a `#doc (Manual)` declaration and be imported

---

## 8. CROSS-REFERENCES

### Tag-based

Assign a tag:
```
# My Section
%%%
tag := "my-section"
%%%
```

Reference it:
```
See {ref "my-section"}[the section on this topic].
```

### Name-based (link to Lean constant)

```
The function {name}`List.map` transforms lists.
```

### Technical terms (glossary)

```
A {deftech}_stability condition_ is...        ← defines the term
Later, {tech}[stability condition] means...    ← links back
```

Parameters: `(key := "alternate key")`, `(remote := "...")`.

### Remote cross-references

```
{ref "section" (remote := "otherProject")}[link]
```

Requires `remoteConfigFile` in Config.

---

## 9. CONFIGURATION

### Config structure

```lean
structure Config extends HtmlConfig, TeXConfig, OutputConfig where
  extraFiles : List (System.FilePath × String) := []
  maxTraversals : Nat := 20
  remoteConfigFile : Option System.FilePath := none

structure OutputConfig where
  destination : System.FilePath := "_out"
  emitTeX : Bool := false
  emitHtmlSingle : EmitHtml := .no
  emitHtmlMulti : EmitHtml := .immediately
  draft : Bool := false
  verbose : Bool := false

structure HtmlConfig extends HtmlAssets where
  htmlDepth := 2
  extraHead : Array Output.Html := #[]
  extraContents : Array Output.Html := #[]
  logo : Option String := none
  logoLink : Option String := none
  sourceLink : Option String := none
  issueLink : Option String := none
  sectionTocDepth : Option Nat := some 1
  rootTocDepth : Option Nat := some 1

structure HtmlAssets where
  extraCss : HashSet CSS := {}
  extraJs : HashSet JS := {}
  extraJsFiles : HashSet JsFile := {}
  extraCssFiles : HashSet CssFile := {}
```

### Passing config to manualMain

```lean
def config : Config where
  htmlDepth := 2
  emitTeX := false

def main := manualMain (%doc Docs.Root) (config := { config with })
```

### Output structure

```
_out/
  html-multi/          ← multi-page HTML (default)
    index.html
    Chapter1/
      index.html
    -verso-search/     ← search index
  html-single/         ← single-page HTML (if enabled)
  tex/                 ← TeX output (if enabled)
```

---

## 10. SUBVERSO

SubVerso provides code highlighting with hover info for Verso documents.

### Anchor system

In source files:
```lean
-- ANCHOR: myExample
def foo := 42
-- ANCHOR_END: myExample
```

In Verso docs:
````
```anchor myExample (module := MyModule) (project := "path")
def foo := 42
```
````

Parameters: `(module := ModuleName)`, `(project := "path")`,
`+showProofStates`, `+defSite`.

### Proof state extraction

```lean
-- ^ PROOF_STATE: stepName
```

### What SubVerso produces in HTML

- Clickable identifiers linking to definitions
- Hover tooltips showing types and docs
- Toggleable proof states for tactic proofs
- Syntax-highlighted code with semantic token types

### Module extraction CLI

```bash
subverso-extract-mod MODNAME OUT.json
```

Produces JSON with full `Highlighted` data. Expensive — re-elaborates the
entire module.

---

## 11. HTML POST-PROCESSING PATTERNS

Verso's HTML output often needs post-processing for polished sites. Common
patterns discovered through production use:

### DOM surgery on `{docstring}` output

Verso wraps docstring content in `<div class="namedocs">` with a `<div class="text">`
child. Source docstrings appear as `<p>` tags before the first `<h1>` (Constructor/
Extends/Fields). If you provide your own prose outside the block, you may want
to strip these duplicate `<p>` tags.

### Navigation link rewriting

Multi-module chapter pages often render as empty TOC stubs. To create a polished
navigation experience:

1. **Detect stubs:** Pages with `<ol class="section-toc">` but no
   `<div class="namedocs">` are empty stubs
2. **Rewrite prev/next:** `<a rel="next">` pointing to a stub should skip to
   the stub's first child. `<a rel="prev">` should skip to the page before
   the stub.
3. **Rewrite TOC links:** Sidebar links pointing to stubs should redirect
   to the first child.
4. **Add JS redirect:** Inject `window.location.replace(firstChild)` on stub
   pages for direct URL access.

**Key insight:** Verso uses `<base href="...">` pointing to site root, so all
hrefs are site-root-relative. This simplifies programmatic link rewriting.

### CSS variable overrides

Verso exposes CSS custom properties you can override:

```css
:root {
  --verso-text-font-family: 'Source Serif 4', Georgia, serif;
  --verso-structure-font-family: 'Source Serif 4', Georgia, serif;
  --verso-code-font-family: 'Fira Code', monospace;
  --verso-toc-background-color: #faf8f4;
}
```

### Heading text extraction

Verso wraps heading text in anchor/span elements. In BeautifulSoup:
- `h1.string` returns `None` — use `h1.get_text(strip=True)` instead

---

## 12. DEBUGGING CHECKLIST

### Build fails

- [ ] All imported modules exist and compile
- [ ] `set_option verso.docstring.allowMissing true` on pages with `{docstring}`
- [ ] No unescaped special characters in prose (`_`, `*`, `[`, `]`, `{`, `}`)
- [ ] `{docstring Name}` uses fully qualified name
- [ ] Math uses `$`...`` not `$...$`
- [ ] Headers are well-nested (first is `#`, each adds at most one `#`)
- [ ] `%%%` metadata block is immediately after `#doc`/heading, before content

### Pages not splitting correctly

- [ ] `htmlSplit := .never` on pages that should NOT split
- [ ] Root page has NO heading-level markers for intro sections
- [ ] Check `htmlDepth` setting (default 2)

### Missing hover info

- [ ] `import VersoManual` is present
- [ ] Source module is imported (`import MyProject.Module`)
- [ ] `open Verso.Genre Manual` is present
- [ ] Serving over HTTP (not file://)

### Performance

- [ ] `{docstring}` is cheap (~seconds) — just env lookup
- [ ] `` ```lean `` is expensive — re-elaborates code
- [ ] `` ```anchor `` is medium — uses pre-computed JSON
- [ ] Large numbers of `{include}` may need `set_option maxHeartbeats`

---

## 13. COMPLETE SYNTAX QUICK REFERENCE

```
#doc (Manual) "Title" =>           Document declaration
%%% key := value %%%               Metadata block (after #doc or # heading)
{docstring Qualified.Name}         Declaration signature with hover
{include N ModuleName}             Include sub-document at level N
{name}`Qualified.Name`             Link to constant with highlighting
{ref "tag"}[link text]             Cross-reference to tagged section
{lean}`expr`                       Inline Lean term with hover
{deftech}_term_                    Define glossary term
{tech}[term]                       Reference glossary term
{margin}[note]                     Marginal note
{index}[entry]                     Index entry
$`math`                            Inline math (KaTeX)
$$`math`                           Display math (KaTeX)
*bold*                             Bold text
_emphasis_                         Italic text
[text](url)                        Link
![alt](path)                       Image
# Heading                          Section heading (triggers page split!)
:::directive (args)                Block directive start
:::                                Block directive end
```

---

## 14. EXAMPLE PROJECTS FOR REFERENCE

| Project | Approach | URL |
|---------|----------|-----|
| Lean Reference Manual | Manual genre, hand-authored | github.com/leanprover/reference-manual |
| Sutherland-NT | Manual genre + Mathlib | github.com/FormalFrontier/Sutherland-NumberTheory-verso |
| Tao Analysis | Literate mode | github.com/teorth/analysis |
| PhysLean Notes | Literate mode | notes.physlean.com |
| Verso User Guide | Manual genre (self-documenting) | verso.lean-lang.org/doc/latest/ |
