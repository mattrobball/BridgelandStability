import VersoManual
import SubVerso.Compat
import SubVerso.Highlighting
import Verso.Code.External

open Lean
open Verso Doc Elab ArgParse Genre.Manual
open Verso.Code.External
open ExternalCode
open SubVerso.Highlighting

namespace ComparatorManualSupport

/-- True when the keyword name identifies a declaration-value construct
    (`where` or `|` at the declaration level). -/
private def isDeclValueKeyword (name : Name) : Bool :=
  match name with
  | .str _ "whereStructInst" => true
  | .str _ "declValEqns"     => true
  | _ => false

/-- Walk the Highlighted tree and find the character offset where the
    declaration body begins. Matches:
    1. Keyword tokens named `whereStructInst` or `declValEqns`
    2. Unknown tokens with content `:=` at bracket depth 0
    Returns the character count of the signature prefix. -/
private def findDeclBodyOffset (hl : Highlighted) : Option Nat :=
  -- depth tracks bracket nesting: only `:=` at depth 0 is the declaration body
  let rec go (hl : Highlighted) (offset depth : Nat) : Option Nat × Nat × Nat :=
    match hl with
    | .token tok =>
        let len := tok.content.length
        -- Check for keyword-identified declaration values (where, |)
        let foundKeyword := match tok.kind with
          | .keyword (some name) _ _ => isDeclValueKeyword name
          | _ => false
        if foundKeyword then (some offset, offset + len, depth)
        else
          -- Check for `:=` at bracket depth 0 (unknown kind in SubVerso)
          let foundAssign := depth == 0 && tok.content == ":="
          if foundAssign then (some offset, offset + len, depth)
          else
            -- Track bracket depth
            let depth := match tok.content with
              | "(" | "{" | "[" | "⦃" | "⟨" => depth + 1
              | ")" | "}" | "]" | "⦄" | "⟩" => depth - 1
              | _ => depth
            (none, offset + len, depth)
    | .text s => (none, offset + s.length, depth)
    | .unparsed s => (none, offset + s.length, depth)
    | .point _ _ => (none, offset, depth)
    | .span _ inner => go inner offset depth
    | .tactics _ _ _ inner => go inner offset depth
    | .seq hs =>
        let rec loop (items : List Highlighted) (offset depth : Nat) : Option Nat × Nat × Nat :=
          match items with
          | [] => (none, offset, depth)
          | h :: t =>
              let (result, offset', depth') := go h offset depth
              match result with
              | some _ => (result, offset', depth')
              | none   => loop t offset' depth'
        loop hs.toList offset depth
  (go hl 0 0).1

private def takeExact (remaining : Nat) (hl : Highlighted) : Highlighted × Nat :=
  match hl with
  | .point kind info =>
      (.point kind info, remaining)
  | .text s =>
      if remaining >= s.length then
        (.text s, remaining - s.length)
      else
        (.text (SubVerso.Compat.String.take s remaining), 0)
  | .token tok =>
      if remaining >= tok.content.length then
        (.token tok, remaining - tok.content.length)
      else
        (.text (SubVerso.Compat.String.take tok.content remaining), 0)
  | .unparsed s =>
      if remaining >= s.length then
        (.unparsed s, remaining - s.length)
      else
        (.text (SubVerso.Compat.String.take s remaining), 0)
  | .span info inner =>
      let (inner', remaining') := takeExact remaining inner
      (if inner'.isEmpty then .empty else .span info inner', remaining')
  | .tactics info startPos endPos inner =>
      let (inner', remaining') := takeExact remaining inner
      (if inner'.isEmpty then .empty else .tactics info startPos endPos inner', remaining')
  | .seq hs =>
      let rec loop (remaining : Nat) (todo : List Highlighted) (acc : Highlighted) : Highlighted × Nat :=
        match todo with
        | [] => (acc, remaining)
        | h :: t =>
            let (h', remaining') := takeExact remaining h
            let acc := acc ++ h'
            if remaining' == 0 then
              (acc, 0)
            else
              loop remaining' t acc
      loop remaining hs.toList .empty

-- Custom block that renders its child inside a collapsed <details> element.
def Block.collapsibleProof : Genre.Manual.Block where
  name := `ComparatorManualSupport.Block.collapsibleProof

open Verso.Output Html in
@[block_extension Block.collapsibleProof]
def collapsibleProof.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [
    -- Warm academic theme from the exposition site
    ":root { --site-ink: #193428; --site-muted: #5a655f; --site-warm: #fbf7ef; --site-card: #fffdf8; --site-accent: #a14d2a; --site-border: #d8cdbd; --verso-structure-color: #154734; --verso-toc-background-color: #f4efe5; --verso-selected-color: #f0dcc8; --verso-text-font-family: 'Iowan Old Style', 'Palatino Linotype', 'Book Antiqua', serif; --verso-structure-font-family: 'Avenir Next Condensed', 'Gill Sans', sans-serif; --verso-code-font-family: 'Iosevka Term', 'JetBrains Mono', monospace; }",
    "body { color: var(--site-ink); }",
    -- Code block styling
    ".hl.lean.block { background: #faf4e8; border: 1px solid #eadfcf; border-radius: 10px; padding: 0.85rem 1rem; box-shadow: inset 0 1px 0 rgba(255,255,255,0.7); }",
    -- Collapsible proof styling
    "details.collapsible-proof > summary { cursor: pointer; color: var(--site-muted, #666); font-style: italic; margin: 0.3em 0; user-select: none; font-family: var(--verso-structure-font-family, sans-serif); font-size: 0.88rem; }",
    "details.collapsible-proof > summary:hover { color: var(--site-accent, #a14d2a); }",
    -- Section heading accents
    "main section > h2, main section > h3, main section > h4 { border-left: 4px solid var(--verso-structure-color, #154734); padding-left: 0.6rem; }",
    ".decl-anchor { height: 0; margin: 0; padding: 0; }"]
  toHtml := some fun _goI goB _id _data blocks => do
    let inner ← blocks.mapM (goB ·)
    pure {{ <details class="collapsible-proof"><summary>"Show proof"</summary>{{inner}}</details> }}

-- Invisible anchor block that registers a constant in the docstring domain
-- for cross-reference linking. Renders only an empty anchor div.
def Block.declAnchor (declName : String) : Genre.Manual.Block where
  name := `ComparatorManualSupport.Block.declAnchor
  data := Lean.toJson declName

open Verso.Output Html in
@[block_extension Block.declAnchor]
def declAnchor.descr : BlockDescr where
  traverse id info _ := do
    let some declName := info.getStr? |>.toOption | pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path declName
    modify fun st => st.saveDomainObject Verso.Genre.Manual.docstringDomain declName id
    pure none
  toTeX := none
  toHtml := some fun _goI _goB id _info _blocks => open Verso.Output Html Verso.Doc.Html in do
    let xref ← HtmlT.state
    let idAttr := xref.htmlId id
    pure {{ <div class="decl-anchor" {{idAttr}}></div> }}

private abbrev ManualDocBlock := Verso.Doc.Block Verso.Genre.Manual

def wrapDeclAnchor (declName : String) : ManualDocBlock :=
  .other (Block.declAnchor declName) #[]

private def stringTail (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

private def dropExact (n : Nat) (hl : Highlighted) : Highlighted :=
  let rec go (remaining : Nat) (hl : Highlighted) : Highlighted × Nat :=
    match hl with
    | .point _ _ => (.empty, remaining)
    | .text s =>
        if remaining >= s.length then (.empty, remaining - s.length)
        else (.text (stringTail s remaining), 0)
    | .token tok =>
        if remaining >= tok.content.length then (.empty, remaining - tok.content.length)
        else (.token { tok with content := stringTail tok.content remaining }, 0)
    | .unparsed s =>
        if remaining >= s.length then (.empty, remaining - s.length)
        else (.unparsed (stringTail s remaining), 0)
    | .span info inner =>
        let (inner', remaining') := go remaining inner
        (if inner'.isEmpty then .empty else .span info inner', remaining')
    | .tactics info startPos endPos inner =>
        let (inner', remaining') := go remaining inner
        (if inner'.isEmpty then .empty else .tactics info startPos endPos inner', remaining')
    | .seq hs =>
        let rec loop (remaining : Nat) (todo : List Highlighted) : Highlighted × Nat :=
          match todo with
          | [] => (.empty, remaining)
          | h :: t =>
              if remaining == 0 then (.seq (h :: t).toArray, 0)
              else
                let (tail, remaining') := go remaining h
                if remaining' == 0 then
                  -- h spans the boundary; include its tail + rest
                  if tail.isEmpty then (.seq t.toArray, 0)
                  else (.seq (tail :: t).toArray, 0)
                else
                  loop remaining' t
        loop remaining hs.toList
  (go n hl).1

-- Dependency graph block: renders a D3 force-directed graph from embedded JSON data.
def Block.dependencyGraph (graphJson : String) : Genre.Manual.Block where
  name := `ComparatorManualSupport.Block.dependencyGraph
  data := Lean.Json.str graphJson

open Verso.Output Html in
@[block_extension Block.dependencyGraph]
def dependencyGraph.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  extraJs := ["document.addEventListener('DOMContentLoaded',function(){var el=document.getElementById('graph-data');if(!el)return;var data=JSON.parse(el.textContent);var root=document.getElementById('graph-root');if(!root)return;var w=root.clientWidth,h=600;var svg=document.createElementNS('http://www.w3.org/2000/svg','svg');svg.setAttribute('width','100%');svg.setAttribute('height',h);svg.setAttribute('viewBox','0 0 '+w+' '+h);root.appendChild(svg);var nodeMap={};data.nodes.forEach(function(n){nodeMap[n.id]=n;});var groups=Array.from(new Set(data.nodes.map(function(n){return n.groupKey})));var colors=['#3d6b59','#b96d2d','#7a4e7a','#2f5f87','#8a3b3b','#5f6f2e','#9a5b8f','#6b5041'];function groupColor(g){return colors[groups.indexOf(g)%colors.length]}var sim=d3.forceSimulation(data.nodes).force('link',d3.forceLink(data.edges).id(function(d){return d.id}).distance(80).strength(0.2)).force('charge',d3.forceManyBody().strength(-210)).force('center',d3.forceCenter(w/2,h/2)).force('collide',d3.forceCollide(22));var g=document.createElementNS('http://www.w3.org/2000/svg','g');svg.appendChild(g);var linkG=document.createElementNS('http://www.w3.org/2000/svg','g');g.appendChild(linkG);var nodeG=document.createElementNS('http://www.w3.org/2000/svg','g');g.appendChild(nodeG);data.edges.forEach(function(e){var line=document.createElementNS('http://www.w3.org/2000/svg','line');line.setAttribute('stroke','#b8b0a4');line.setAttribute('stroke-opacity','0.6');line.setAttribute('stroke-width','1.2');line._data=e;linkG.appendChild(line)});data.nodes.forEach(function(n){var ng=document.createElementNS('http://www.w3.org/2000/svg','g');ng.setAttribute('cursor','pointer');var c=document.createElementNS('http://www.w3.org/2000/svg','circle');c.setAttribute('r','10');c.setAttribute('fill',groupColor(n.groupKey));c.setAttribute('stroke','#1f6b4b');c.setAttribute('stroke-width','2');ng.appendChild(c);var t=document.createElementNS('http://www.w3.org/2000/svg','text');t.setAttribute('dx','14');t.setAttribute('dy','4');t.setAttribute('font-size','11');t.setAttribute('fill','#333');t.textContent=n.label;ng.appendChild(t);ng._data=n;ng.addEventListener('click',function(){if(n.href)window.location.href=n.href});nodeG.appendChild(ng)});sim.on('tick',function(){linkG.childNodes.forEach(function(l){l.setAttribute('x1',l._data.source.x);l.setAttribute('y1',l._data.source.y);l.setAttribute('x2',l._data.target.x);l.setAttribute('y2',l._data.target.y)});nodeG.childNodes.forEach(function(ng){var d=ng._data;ng.setAttribute('transform','translate('+d.x+','+d.y+')')})});var zoom=d3.zoom().scaleExtent([0.25,4]).on('zoom',function(e){g.setAttribute('transform',e.transform)});d3.select(svg).call(zoom)})"]
  extraCss := ["#graph-root { background: var(--site-card, #fffdf8); border: 1px solid var(--site-border, #d8cdbd); border-radius: 14px; min-height: 620px; padding: 1rem; margin: 1rem 0; } #graph-root svg { display: block; }"]
  toHtml := some fun _goI _goB _id info _blocks => open Output.Html in do
    let graphJson := info.getStr? |>.toOption |>.getD "{}"
    pure {{ <div id="graph-root"><script id="graph-data" type="application/json">{{graphJson}}</script><script src="https://d3js.org/d3.v7.min.js"></script></div> }}

def wrapCollapsible (body : ManualDocBlock) : ManualDocBlock :=
  .other Block.collapsibleProof #[body]

def wrapDependencyGraph (graphJson : String) : ManualDocBlock :=
  .other (Block.dependencyGraph graphJson) #[]

/-- Embed an interactive dependency graph. The code block body is the JSON data. -/
@[code_block_expander graphEmbed]
public meta def graphEmbed : CodeBlockExpander
  | _args, code => do
    let json := code.getString
    pure #[← ``(wrapDependencyGraph $(quote json))]

/-- Register a declaration name as a cross-reference anchor. Renders nothing. -/
@[code_block_expander declAnchorEmbed]
public meta def declAnchorEmbed : CodeBlockExpander
  | _args, code => do
    let declName := code.getString.trim
    pure #[← ``(wrapDeclAnchor $(quote declName))]

/-- Render an anchored external Lean block with the proof body inside
    a collapsed `<details>` element. The signature is always visible. -/
@[code_block_expander collapsibleModule]
public meta def collapsibleModule : CodeBlockExpander
  | args, _code => withTraceNode `Elab.Verso (fun _ => pure m!"collapsibleModule") <| do
    let cfg@{ module := moduleName, project, anchor?, showProofStates := _, defSite := _ } ← parseThe CodeContext args
    withAnchored project moduleName anchor? fun hl => do
      match findDeclBodyOffset hl with
      | some offset =>
          let headHl := (takeExact offset hl).1
          let bodyHl := dropExact offset hl
          let headBlock ← ``(leanBlock $(quote headHl) $(quote cfg.toCodeConfig))
          let bodyBlock ← ``(leanBlock $(quote bodyHl) $(quote cfg.toCodeConfig))
          pure #[headBlock, ← ``(wrapCollapsible $bodyBlock)]
      | none =>
          pure #[← ``(leanBlock $(quote hl) $(quote cfg.toCodeConfig))]

end ComparatorManualSupport