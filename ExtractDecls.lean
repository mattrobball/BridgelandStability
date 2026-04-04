/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
import BridgelandStability
import Informal

/-!
# Declaration extraction

Walks the compiled `BridgelandStability` environment and emits a JSON array of
all user-facing declarations with metadata, `@[informal]` paper references,
docstrings, and a content hash for staleness detection.

Usage: `lake build extractDecls` then the JSON is written at elaboration time.
Alternatively: `lake exe extractDecls [output.json]` for explicit output path.
-/

open Lean Meta

namespace ExtractDecls

/-- Classification of declaration kinds. -/
inductive DeclKind where
  | «theorem» | «def» | «structure» | «class» | «abbrev»
  | «instance» | «inductive» | «axiom» | «opaque»
  deriving BEq, Repr

instance : ToString DeclKind where
  toString
    | .theorem => "theorem"
    | .def => "def"
    | .structure => "structure"
    | .class => "class"
    | .abbrev => "abbrev"
    | .instance => "instance"
    | .inductive => "inductive"
    | .axiom => "axiom"
    | .opaque => "opaque"

/-- JSON output entry. -/
structure DeclEntry where
  declName : String
  declKind : String
  moduleName : String
  docstring : Option String := none
  contentHash : UInt64 := 0
  paperRef : Option String := none
  paperComment : Option String := none
  sourceFile : Option String := none
  startLine : Option Nat := none
  endLine : Option Nat := none
  deriving Inhabited

instance : ToJson DeclEntry where
  toJson e := Json.mkObj [
    ("declName", Json.str e.declName),
    ("declKind", Json.str e.declKind),
    ("moduleName", Json.str e.moduleName),
    ("docstring", match e.docstring with | some d => Json.str d | none => Json.null),
    ("contentHash", Json.num (Lean.JsonNumber.fromNat e.contentHash.toNat)),
    ("paperRef", match e.paperRef with | some r => Json.str r | none => Json.null),
    ("paperComment", match e.paperComment with | some c => Json.str c | none => Json.null),
    ("sourceFile", match e.sourceFile with | some s => Json.str s | none => Json.null),
    ("startLine", match e.startLine with | some n => Json.num (.fromNat n) | none => Json.null),
    ("endLine", match e.endLine with | some n => Json.num (.fromNat n) | none => Json.null)
  ]

private def isAuxComponent (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_"

/-- Check if any component of a name is auto-generated.
    Adapted from lean-exposition `LeanExposition/Site.lean`. -/
private partial def isInternalName : Name → Bool
  | .anonymous => false
  | .num p _ => isInternalName p
  | .str p s =>
      isAuxComponent s
      || s ∈ ["brecOn", "below", "casesOn", "noConfusion", "noConfusionType",
              "recOn", "rec", "ind", "mk", "sizeOf_spec", "inject", "injEq",
              "ctorIdx", "ext_iff", "congr_simp"]
      || (s.startsWith "eq_" && (s.drop 3).toString.all Char.isDigit)
      || isInternalName p

/-- Should this declaration be exposed?
    Adapted from lean-exposition `LeanExposition/Site.lean:shouldExpose`. -/
def shouldExpose (env : Environment) (name : Name) (ci : ConstantInfo) : Bool :=
  if env.getProjectionFnInfo? name |>.isSome then false
  else if isInternalName name || name.isInternal || name.isImplementationDetail then false
  else if isAuxRecursor env name || isNoConfusion env name then false
  else match ci with
    | .ctorInfo _ | .recInfo _ | .quotInfo _ => false
    | _ => true

/-- Classify a constant into a `DeclKind`. -/
def classifyDecl (env : Environment) (name : Name) (ci : ConstantInfo) : CoreM DeclKind := do
  match ci with
  | .thmInfo _ =>
    if (← isInstance name) then return .instance else return .theorem
  | .inductInfo _ =>
    if isStructure env name then
      if isClass env name then return .class else return .structure
    else return .inductive
  | .defnInfo _ =>
    if isStructure env name then
      if isClass env name then return .class else return .structure
    else if (← isInstance name) then return .instance
    else if (← isReducible name) then return .abbrev
    else return .def
  | .axiomInfo _ => return .axiom
  | .opaqueInfo _ => return .opaque
  | .ctorInfo _ => return .def
  | .recInfo _ => return .def
  | .quotInfo _ => return .def

/-- Is this a proof-irrelevant declaration (type only matters for hash)? -/
def isProofIrrelevant (ci : ConstantInfo) (kind : DeclKind) : Bool :=
  match kind with
  | .theorem => true
  | .instance => match ci with | .thmInfo _ => true | _ => false
  | .def | .structure | .class | .abbrev | .inductive | .axiom | .opaque => false

/-- Compute a content hash for staleness detection.
    Hashes the type for all declarations, plus body/fields for data-carrying ones. -/
def computeContentHash (env : Environment) (name : Name) (ci : ConstantInfo)
    (kind : DeclKind) : MetaM UInt64 := do
  let typePP ← ppExpr ci.type
  let typeStr := toString typePP
  if isProofIrrelevant ci kind then
    return typeStr.hash
  else
    let mut combined := typeStr
    match ci with
    | .defnInfo di => combined := combined ++ " := " ++ toString (← ppExpr di.value)
    | .opaqueInfo oi => combined := combined ++ " := " ++ toString (← ppExpr oi.value)
    | _ => pure ()
    if let some sinfo := getStructureInfo? env name then
      for field in sinfo.fieldNames do
        if let some projInfo := env.find? (name ++ field) then
          let fTypePP ← ppExpr projInfo.type
          combined := combined ++ s!" field {field} : {fTypePP}"
    if let .inductInfo ii := ci then
      for ctorName in ii.ctors do
        if let some ctorInfo := env.find? ctorName then
          let cTypePP ← ppExpr ctorInfo.type
          combined := combined ++ s!" ctor {ctorName} : {cTypePP}"
    return combined.hash

/-- Resolve the module name for a declaration. -/
def getModuleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none => "unknown"

/-- Walk the environment and collect all user-facing declarations. -/
def collectDecls : CoreM (Array DeclEntry) := do
  let env ← getEnv
  let informalEntries := Informal.getEntries env
  let informalMap : Std.HashMap Name Informal.Entry :=
    informalEntries.foldl (init := {}) fun m e => m.insert e.declName e
  let rootPrefix := `BridgelandStability
  let mut result : Array DeclEntry := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    unless rootPrefix.isPrefixOf modName do continue
    let modData := env.header.moduleData[i]!
    for j in [:modData.constNames.size] do
      let name := modData.constNames[j]!
      let some ci := env.find? name | continue
      unless shouldExpose env name ci do continue
      let kind ← classifyDecl env name ci
      let hash ← computeContentHash env name ci kind |>.run'
      let doc ← findDocString? env name
      let informal? := informalMap[name]?
      let range? ← findDeclarationRanges? name
      let sourceFile := modName.toString.replace "." "/" ++ ".lean"
      let entry : DeclEntry := {
        declName := name.toString
        declKind := toString kind
        moduleName := getModuleName env name
        docstring := doc
        contentHash := hash
        paperRef := informal?.map (·.paperRef)
        paperComment := informal?.bind fun e =>
          if e.comment.isEmpty then none else some e.comment
        sourceFile := some sourceFile
        startLine := range?.map (·.range.pos.line + 1)
        endLine := range?.map (·.range.endPos.line + 1)
      }
      result := result.push entry
  return result.qsort fun a b =>
    if a.moduleName == b.moduleName then a.declName < b.declName
    else a.moduleName < b.moduleName

end ExtractDecls

open ExtractDecls Lean Elab Command in
/-- Export declarations to a JSON file. Runs at elaboration time. -/
elab "#extract_decls" path:str : command => do
  let entries ← liftCoreM collectDecls
  let json := Lean.toJson entries
  IO.FS.writeFile path.getString json.pretty
  logInfo m!"Extracted {entries.size} declarations to {path.getString}"

-- Write extracted.json at elaboration time (lake build extractDecls triggers this)
#extract_decls "extracted.json"

def main : IO UInt32 := do
  IO.eprintln "extracted.json was written at build time by #extract_decls"
  return 0
