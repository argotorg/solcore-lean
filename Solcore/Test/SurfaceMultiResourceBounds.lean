import Solcore.Surface.Multi.StructureNodeVisitUnits

/-! Executable regressions for the M2c resource-bound primitives. -/

set_option autoImplicit false

namespace Tests

open Solcore.Workspace
open Solcore.Surface.Multi

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def expectSourceId : IO SourceId := do
  match CanonicalSourcePath.parse "ResourceBounds.solc" with
  | some path => pure { library := .main, path }
  | none => throw (IO.userError "the resource-bound test path is invalid")

private def expectPathSegment (text : String) : IO PathSegment := do
  match PathSegment.parse text with
  | some segment => pure segment
  | none => throw (IO.userError s!"invalid resource-bound path segment: {text}")

private def spanAt (source : SourceId)
    (startByte endByte : Nat) : SourceSpan := {
  source
  startByte
  endByte
}

private def locatedAt {alpha : Type} (source : SourceId)
    (startByte endByte : Nat) (payload : alpha) : Located alpha := {
  span := spanAt source startByte endByte
  payload
}

private def visit (ordinal : Nat)
    (carrier : AstCarrier) : StructureNodeVisitUnit := {
  ordinal
  carrier
}

/-- Check the executable node-visit trace, including the payload-only
`ImportMode` carrier fixed by the resource contract. -/
def testMultiResourceBounds : IO Unit := do
  let source ← expectSourceId
  let component ← expectPathSegment "core"

  let emptyModule : ParsedModuleV1 :=
    locatedAt source 0 0 { source, items := [] }
  let emptyTrace := [
    visit 0 (.located .parsedModule),
    visit 1 (.payload .parsedModule)
  ]
  assertTrue (decide (structureNodeVisitTrace emptyModule = emptyTrace))
    "the empty-module structural visit trace changed"
  assertTrue (structureNodeVisitUnits emptyModule == 2)
    "the empty module must contain exactly two AST carriers"
  assertTrue
    (structureNodeVisitUnits emptyModule ≤
      structureBound (astNodeMeasure emptyModule))
    "the empty-module node visits exceeded the structural bound"

  let pathComponent : PathComponent :=
    locatedAt source 7 11 component
  let moduleReference : ModuleReference :=
    locatedAt source 7 11 (.relative { head := pathComponent, tail := [] })
  let declaration : ImportDecl :=
    locatedAt source 0 12 {
      moduleRef := moduleReference
      mode := .module none
    }
  let item : TopItem :=
    locatedAt source 0 12 (.importDecl declaration)
  let importModule : ParsedModuleV1 :=
    locatedAt source 0 12 { source, items := [item] }
  let importTrace := [
    visit 0 (.located .parsedModule),
    visit 1 (.payload .parsedModule),
    visit 2 (.located .topItem),
    visit 3 (.payload .topItem),
    visit 4 (.located .importDecl),
    visit 5 (.payload .importDecl),
    visit 6 (.located .moduleReference),
    visit 7 (.payload .moduleReference),
    visit 8 (.located .pathComponent),
    visit 9 (.payload .pathComponent),
    visit 10 (.payload .importMode)
  ]
  assertTrue (decide (structureNodeVisitTrace importModule = importTrace))
    "the import structural visit trace or carrier order changed"
  assertTrue
    (structureNodeVisitUnits importModule == astNodeMeasure importModule)
    "the executable node-visit count diverged from the AST measure"
  assertTrue (parseBound 0 < parseBound 1)
    "the parser bound must grow when one terminal is added"

end Tests
