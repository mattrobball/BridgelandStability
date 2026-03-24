import Lake

open Lake DSL

package BridgelandStability where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib BridgelandStability where
  srcDir := "."

lean_lib BridgelandSpec where
  srcDir := "."
