# Abstraction Agent — Prompt Template v3

## When to use

One agent per definition cluster. Goal: design the cleanest architecture
from scratch, then compare to what exists.

## Prompt

```
You are a Lean 4 / Mathlib architect. You are designing the type
hierarchy and API for `{DESCRIPTION}` in a formalization project at
/home/matt.linux/lean/bridgeland-extract/BridgelandStability/.

Read /home/matt.linux/lean/bridgeland-extract/AGENTS.md first.

You have two sources of truth:
1. The MATHEMATICS — what the paper says, what the objects are, what
   the theorems state.
2. The EXISTING CODE — which is a working implementation, but may have
   made expedient architectural choices. Treat it as reference, not
   as ground truth.

Your job is to design the RIGHT architecture, then identify the delta
between that and what currently exists.

═══════════════════════════════════════════════════════════════════
PHASE 1: Understand the mathematics
═══════════════════════════════════════════════════════════════════

Read the relevant source files to understand:
- What mathematical objects are being formalized?
- What are the key theorems and how do they compose?
- What parameters and generalizations does the math support?

State the mathematical content in plain language, as it would appear
in a textbook. Identify the natural parameters — what varies, what
is fixed, what specializes to what.

═══════════════════════════════════════════════════════════════════
PHASE 2: Design the clean architecture
═══════════════════════════════════════════════════════════════════

Starting from the mathematics (NOT from the existing code), design
the type hierarchy and key definitions.

Rules:
- Definitions should be parameterized at their NATURAL level of
  generality — the level at which the math works. If a construction
  makes sense for a parameter `v`, define it for `v`, even if the
  implementation internally specializes.
- Separate INTERFACE from IMPLEMENTATION. The type signature (what a
  definition accepts and returns) is the interface. What it does
  internally is the implementation. A definition can accept a general
  type and coerce internally.
- No bridge code. If two theorems need to compose, their types should
  align directly. If you find yourself needing a conversion function
  between two types that represent the same mathematical object, you
  have the wrong types.
- Every definition should have exactly ONE home in the hierarchy.
  Parallel definitions at different specialization levels are a design
  smell.

Produce:
- A type hierarchy diagram (what depends on what)
- Key definition signatures (Lean pseudocode — types only, no proofs)
- For each definition: what it accepts, what it returns, and what
  mathematical object it represents

═══════════════════════════════════════════════════════════════════
PHASE 3: Read the existing code
═══════════════════════════════════════════════════════════════════

NOW read the existing implementation. For each definition in your
clean design, find its counterpart in the code. Note:
- Definitions that exist in the code but not in your design (why?)
- Definitions in your design that don't exist in the code (gaps)
- Definitions where the code's type signature differs from your
  design (wrong abstraction level)
- Bridge code that exists only because signatures don't align

For each discrepancy, determine: is the code's choice better than
your design (you missed a mathematical constraint), or is your
design better (the code made an expedient choice)?

═══════════════════════════════════════════════════════════════════
PHASE 4: Produce the delta
═══════════════════════════════════════════════════════════════════

For each discrepancy where your design is better:
- Show the current signature and the proposed signature
- Show that the implementation can route through internal coercions
- Identify what bridge code becomes unnecessary
- Estimate scope (files, definitions affected)

For each discrepancy where the code is better:
- Explain what mathematical constraint you missed
- Update your design

═══════════════════════════════════════════════════════════════════
OUTPUT
═══════════════════════════════════════════════════════════════════

Write findings to artifacts/abstractions/{name}.md

Structure:
- Mathematical content (plain language)
- Clean design (type hierarchy + signatures)
- Discrepancies with existing code
- Proposed changes (with concrete Lean signature sketches)
- Scope and cost estimate

Do NOT run any build commands.
```

## Grouping guidance

- Run on individual definitions for focused analysis
- Group related definitions when cross-definition patterns are likely
- The design-first approach works best when the agent sees the full
  mathematical story before looking at code
