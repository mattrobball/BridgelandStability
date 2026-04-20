/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
module

public meta import Informal
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# External paper-reference bindings

Paper statements from Bridgeland (2007) whose formalization already lives
upstream (mathlib, or another project) are tagged here with the
`#informal_external` command instead of attaching `@[informal]` directly —
the attribute can only decorate local declarations.

Each entry teaches the comparison-dashboard extractor that a given paper
reference is already formalized and points it at the upstream definition so
the dashboard can surface it without a placeholder row.
-/

@[expose] public section

#informal_external "Definition 3.1"
  := CategoryTheory.Triangulated.TStructure complete

end
