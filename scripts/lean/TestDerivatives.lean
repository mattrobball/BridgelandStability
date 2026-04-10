/-
Test: derivative resolution starting from real declarations.
Walks the dependency graph of BridgelandStability.Spec's theorem,
collecting constants from types (always) and values (skip for theorems).
Reports how each constant is classified and whether derivatives resolve.
-/
import BridgelandStability.Spec

open Lean

/-- One-level used constants, proof-irrelevant: skip theorem values. -/
def usedConstsPI (env : Environment) (ci : ConstantInfo) : NameSet :=
  ci.type.getUsedConstantsAsSet ++ match ci with
  | .thmInfo _    => {}
  | .defnInfo v   => v.value.getUsedConstantsAsSet
  | .opaqueInfo v => v.value.getUsedConstantsAsSet
  | .inductInfo v => .ofList v.ctors
  | .ctorInfo v   => ({} : NameSet).insert v.name
  | .recInfo v    => .ofList v.all
  | .axiomInfo _  => {}
  | .quotInfo _   => {}

def isProjectLocal (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!.getRoot == `BridgelandStability
  | none => false

def isCaughtStructural (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => true
  | _ =>
    isAuxRecursor env name
    || isNoConfusion env name
    || (env.getProjectionFnInfo? name).isSome

/-- Resolve a name to its user-facing parent.
    Strips _private wrapper, then for derivatives uses getPrefix. -/
def resolveToUser (env : Environment) (name : Name) : Name :=
  let n := (privateToUserName? name).getD name
  -- If after unwrapping private, the name itself exists as a user decl, keep it
  if !n.isInternalDetail && !isCaughtStructural env n then n
  else
    -- Try getPrefix
    let p := n.getPrefix
    if !p.isAnonymous && (env.find? p).isSome then p
    else n  -- can't resolve further

structure WalkStats where
  visited : Nat := 0
  projectLocal : Nat := 0
  projectLocalUserFacing : Nat := 0
  projectLocalDerivative : Nat := 0
  derivativeResolved : Nat := 0
  derivativeUnresolved : Nat := 0
  proofsSkipped : Nat := 0
  deriving Repr

/-- Walk the dependency graph from a starting declaration.
    Collects used constants proof-irrelevantly, filters to project-local,
    classifies each as user-facing vs derivative, checks resolution. -/
def walkDeps (env : Environment) (startName : Name) : IO WalkStats := do
  let mut visited : NameSet := {}
  let mut frontier : Array Name := #[startName]
  let mut stats : WalkStats := {}
  let mut unresolvedLog : Array String := #[]

  while !frontier.isEmpty do
    let mut next : Array Name := #[]
    for name in frontier do
      if visited.contains name then continue
      visited := visited.insert name
      stats := { stats with visited := stats.visited + 1 }

      let some ci := env.find? name | continue

      -- Get used constants (proof-irrelevant)
      let used := usedConstsPI env ci
      let isProof := match ci with | .thmInfo _ => true | _ => false
      if isProof && name != startName then
        stats := { stats with proofsSkipped := stats.proofsSkipped + 1 }

      for c in used.toArray do
        if visited.contains c then continue
        unless isProjectLocal env c do continue

        stats := { stats with projectLocal := stats.projectLocal + 1 }

        let structural := isCaughtStructural env c
        let intDetail := c.isInternalDetail
        let isDerivative := structural || intDetail

        if isDerivative then
          stats := { stats with projectLocalDerivative := stats.projectLocalDerivative + 1 }
          let resolved := resolveToUser env c
          if resolved != c && (env.find? resolved).isSome then
            stats := { stats with derivativeResolved := stats.derivativeResolved + 1 }
          else
            stats := { stats with derivativeUnresolved := stats.derivativeUnresolved + 1 }
            unresolvedLog := unresolvedLog.push s!"  {c} → resolved to {resolved}"
        else
          stats := { stats with projectLocalUserFacing := stats.projectLocalUserFacing + 1 }

        -- Continue traversal through this constant
        next := next.push c

    frontier := next

  IO.println s!"\n  Walk stats:"
  IO.println s!"    Constants visited: {stats.visited}"
  IO.println s!"    Project-local refs encountered: {stats.projectLocal}"
  IO.println s!"      User-facing: {stats.projectLocalUserFacing}"
  IO.println s!"      Derivative: {stats.projectLocalDerivative}"
  IO.println s!"        Resolved: {stats.derivativeResolved}"
  IO.println s!"        Unresolved: {stats.derivativeUnresolved}"
  IO.println s!"    Proofs skipped (type-only): {stats.proofsSkipped}"

  if !unresolvedLog.isEmpty then
    IO.println s!"\n  UNRESOLVED DERIVATIVES:"
    for msg in unresolvedLog do
      IO.println msg

  return stats

#eval! show MetaM Unit from do
  let env ← getEnv
  let target := `CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent

  IO.println s!"=== Dependency walk from {target} ==="
  let some ci := env.find? target | IO.println "NOT FOUND"; return
  IO.println s!"Kind: {match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other"}"

  -- Show what's directly in the type
  let typeConsts := ci.type.getUsedConstantsAsSet
  let localTypeConsts := typeConsts.toArray.filter (isProjectLocal env ·)
  IO.println s!"\nDirect type constants ({typeConsts.size} total, {localTypeConsts.size} project-local):"
  for c in localTypeConsts.qsort Name.lt do
    let deriv := isCaughtStructural env c || c.isInternalDetail
    let kind := match env.find? c with
      | some (.defnInfo _) => "def" | some (.thmInfo _) => "thm"
      | some (.inductInfo _) => "induct" | some (.ctorInfo _) => "ctor"
      | some (.recInfo _) => "rec" | some (.axiomInfo _) => "axiom"
      | _ => "?"
    let tag := if deriv then s!" [derivative → {resolveToUser env c}]" else ""
    IO.println s!"  {c}: {kind}{tag}"

  -- Walk full dependency graph
  let stats ← walkDeps env target

  if stats.derivativeUnresolved == 0 then
    IO.println s!"\nPASS"
  else
    IO.println s!"\nFAIL: {stats.derivativeUnresolved} unresolved derivatives"

  -- Compare: what does the OLD logic (current Informal.computeDepHashes) produce?
  IO.println s!"\n=== COMPARISON: old logic (Informal.computeDepHashes) ==="
  let oldDeps := Informal.computeDepHashes env target ci
  IO.println s!"Old dep count: {oldDeps.size}"
  let oldNames := oldDeps.map (·.1)
  for (n, h) in oldDeps.qsort (Name.lt ·.1 ·.1) do
    IO.println s!"  {n}: {h}"

  -- Compare: what does the NEW walk produce (user-facing names only)?
  IO.println s!"\n=== COMPARISON: new walk (resolved user-facing deps) ==="
  let mut newVisited : NameSet := {}
  let mut newFrontier : Array Name := #[target]
  let mut newDeps : NameSet := {}
  while !newFrontier.isEmpty do
    let mut next : Array Name := #[]
    for name in newFrontier do
      if newVisited.contains name then continue
      newVisited := newVisited.insert name
      let some ci := env.find? name | continue
      let used := usedConstsPI env ci
      for c in used.toArray do
        if newVisited.contains c then continue
        unless isProjectLocal env c do continue
        let resolved := resolveToUser env c
        if resolved != target then
          newDeps := newDeps.insert resolved
        next := next.push c
    newFrontier := next
  IO.println s!"New dep count: {newDeps.size}"
  for n in newDeps.toArray.qsort Name.lt do
    IO.println s!"  {n}"

  -- Diff
  let oldSet : NameSet := oldNames.foldl (·.insert ·) {}
  let onlyOld := oldSet.toArray.filter (!newDeps.contains ·)
  let onlyNew := newDeps.toArray.filter (!oldSet.contains ·)
  IO.println s!"\n=== DIFF ==="
  IO.println s!"In old but not new ({onlyOld.size}):"
  for n in onlyOld.qsort Name.lt do IO.println s!"  - {n}"
  IO.println s!"In new but not old ({onlyNew.size}):"
  for n in onlyNew.qsort Name.lt do IO.println s!"  + {n}"
