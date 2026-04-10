import BridgelandStability.Spec

open Lean in
#eval! show MetaM Unit from do
  let env ← getEnv
  let target := `CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent
  let some ci := env.find? target | return
  let deps := Informal.computeDepHashes env target ci
  for (n, _) in deps.qsort (Name.lt ·.1 ·.1) do
    IO.println (toString n)
