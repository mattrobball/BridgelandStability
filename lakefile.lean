import Lake

open Lake DSL

package BridgelandStability where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "efe911a4cad7ab54c187dabca7f8ee633f099be9"

@[default_target]
lean_lib BridgelandStability where
  srcDir := "."
