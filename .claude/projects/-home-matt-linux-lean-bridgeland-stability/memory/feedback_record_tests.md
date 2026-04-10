---
name: Record tests in existing test libraries
description: Always add tests to existing test files/libraries rather than ad-hoc scripts — tests are important
type: feedback
---

When writing tests, add them to the existing test library (e.g. Test/ directory in lean-informal). Don't create throwaway test scripts. Tests are important and should be recorded properly.

**Why:** The user values tests and wants them preserved in the project's test infrastructure.

**How to apply:** Look for existing test files/directories and add new tests there. Match the existing test style.
