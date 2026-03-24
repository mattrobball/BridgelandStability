import Lake

open Lake DSL

package BridgelandStability where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require LeanArchitect from git
  "https://github.com/mattrobball/LeanArchitect" @ "e8c18617df9210f176e6fada714ab1e907e2cf93"
require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls" @ "master"
require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib BridgelandStability where
  srcDir := "."

lean_lib BridgelandSpec where
  srcDir := "."

lean_lib BridgelandBlueprint where
  srcDir := "."
