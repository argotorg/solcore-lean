import Solcore.Surface.Multi.StructureDiagnosticInsertionUnits
import Solcore.Surface.Multi.StructureCanonicalDedupComparisonUnits
import Solcore.Surface.Multi.StructureCanonicalOrderingComparisonUnits
import Solcore.Surface.Multi.StructureDuplicateComparisonUnits
import Solcore.Surface.Multi.StructureLeastSpanComparisonUnits
import Solcore.Surface.Multi.StructureResourceAccounting
import Solcore.Surface.Multi.StructureResourceBound
import Solcore.Surface.Multi.ParserScheduleTrace

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

private def expectIdentifier (text : String) : IO Identifier := do
  match Identifier.parse text with
  | some identifier => pure identifier
  | none => throw (IO.userError s!"invalid resource-bound identifier: {text}")

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
  assertTrue (structureResourceLedger emptyModule == {
      nodeVisits := 2
      diagnosticInsertions := 0
      duplicateComparisons := 0
      canonicalDedupComparisons := 0
      canonicalOrderingComparisons := 0
      leastSpanComparisons := 0
    })
    "the empty-module structural resource ledger changed"
  assertTrue (structureActualUnits emptyModule == 2)
    "the empty-module structural resource total changed"
  assertTrue
    (structureActualUnits emptyModule ≤
      structureBound (astNodeMeasure emptyModule))
    "the empty module exceeded the complete structural resource bound"

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
  let parserCapacity := parserScheduleCapacity 4
  assertTrue (parserCapacity.total == parseBound 4)
    "the parser schedule capacity diverged from the fixed parser bound"
  assertTrue (parserCapacity.fixedUnits == 1)
    "the parser schedule must retain its one fixed startup unit"
  let noTokens : List Solcore.Surface.Multi.Token := []
  let firstKind : FastMemoKindIndex := ⟨0, by decide⟩
  let firstBoundaryAddress : FastBoundarySlotAddress noTokens := {
    kind := firstKind
    boundary := Boundary.start noTokens
    slot := ⟨0, by decide⟩
  }
  let firstMemoAddress : FastMemoSlotAddress noTokens := {
    kind := firstKind
    start := Boundary.start noTokens
    finish := Boundary.start noTokens
    slot := ⟨0, by decide⟩
  }
  let fixedAddress : FastParserUnitAddress noTokens := .fixed .startup
  let boundaryAddress : FastParserUnitAddress noTokens :=
    .boundarySlot firstBoundaryAddress
  let memoAddress : FastParserUnitAddress noTokens :=
    .memoSlot firstMemoAddress
  assertTrue
    (FastMemoKindIndex.kind firstKind == .rule .module)
    "the first fast memo-kind index must select the module rule"
  assertTrue (firstBoundaryAddress.rank.val == 0)
    "the first boundary-local schedule address must have rank zero"
  assertTrue (firstMemoAddress.rank.val == 0)
    "the first span-local schedule address must have rank zero"
  assertTrue (fixedAddress.rank.val == 0)
    "the fixed startup address must begin the total address space"
  assertTrue (boundaryAddress.rank.val == 1)
    "the first boundary-local address must follow the startup address"
  assertTrue
    (fastParserUnitAddressCapacity noTokens == parseBound 1)
    "the empty-token address universe must equal the one-terminal bound"
  let chargedCounter :=
    (((FastParserCounter.zero noTokens).charge fixedAddress).charge
      boundaryAddress).charge memoAddress
  assertTrue (chargedCounter.ledger == {
      fixedUnits := 1
      boundarySlotUnits := 1
      memoSlotUnits := 1
    })
    "typed schedule charges must update their three ledger components"
  assertTrue (chargedCounter.actualUnits == 3)
    "three typed schedule charges must record exactly three units"
  let addressCapacity := fastParserScheduleAddressCapacity noTokens
  assertTrue
    (decide (chargedCounter.ledger.fixedUnits ≤ addressCapacity.fixedUnits) &&
      decide (chargedCounter.ledger.boundarySlotUnits ≤
        addressCapacity.boundarySlotUnits) &&
      decide (chargedCounter.ledger.memoSlotUnits ≤
        addressCapacity.memoSlotUnits))
    "the three-address regression counter must fit the empty-token schedule"
  let emptyScheduleTrace := FastParserScheduleTrace.empty noTokens
  assertTrue (emptyScheduleTrace.actualUnits == 0)
    "the fresh schedule trace must contain no charged addresses"
  match emptyScheduleTrace.charge? fixedAddress with
  | none =>
      throw (IO.userError "the fresh fixed address was rejected")
  | some fixedTrace =>
      assertTrue (fixedTrace.actualUnits == 1)
        "the first fixed-address charge must add exactly one unit"
      assertTrue ((fixedTrace.charge? fixedAddress).isNone)
        "the fixed-address duplicate charge was accepted"
      match fixedTrace.charge? boundaryAddress with
      | none =>
          throw (IO.userError "the fresh boundary address was rejected")
      | some boundaryTrace =>
          assertTrue (boundaryTrace.actualUnits == 2)
            "the first boundary-address charge must add exactly one unit"
          assertTrue ((boundaryTrace.charge? boundaryAddress).isNone)
            "the boundary-address duplicate charge was accepted"
          match boundaryTrace.charge? memoAddress with
          | none =>
              throw (IO.userError "the fresh memo address was rejected")
          | some memoTrace =>
              assertTrue (memoTrace.ledger == {
                  fixedUnits := 1
                  boundarySlotUnits := 1
                  memoSlotUnits := 1
                })
                "the trace ledger must count one address in every component"
              assertTrue (memoTrace.actualUnits == 3)
                "three fresh trace charges must record exactly three units"
              assertTrue ((memoTrace.charge? memoAddress).isNone)
                "the memo-address duplicate charge was accepted"

  let emptySelection : ImportSelection :=
    locatedAt source 12 14 { entries := [] }
  let emptyHiding : HidingClause :=
    locatedAt source 15 17 { names := [] }
  let invalidDeclaration : ImportDecl :=
    locatedAt source 0 17 {
      moduleRef := moduleReference
      mode := .items emptySelection (some emptyHiding)
    }
  let invalidItem : TopItem :=
    locatedAt source 0 17 (.importDecl invalidDeclaration)
  let invalidModule : ParsedModuleV1 :=
    locatedAt source 0 17 { source, items := [invalidItem] }
  assertTrue (structureDiagnosticInsertionUnits invalidModule == 2)
    "the two empty import clauses must produce two charged insertions"
  assertTrue
    ((Structure.diagnostics invalidModule).length ≤
      structureDiagnosticInsertionUnits invalidModule)
    "canonicalization created an uncharged structural diagnostic"

  let duplicateName ← expectIdentifier "item"
  let firstName : IdentifierOccurrence :=
    locatedAt source 12 16 duplicateName
  let secondName : IdentifierOccurrence :=
    locatedAt source 18 22 duplicateName
  let firstEntry : ImportSelectorEntry :=
    locatedAt source 12 16 (.named firstName none)
  let secondEntry : ImportSelectorEntry :=
    locatedAt source 18 22 (.named secondName none)
  let duplicateSelection : ImportSelection :=
    locatedAt source 11 23 { entries := [firstEntry, secondEntry] }
  let duplicateDeclaration : ImportDecl :=
    locatedAt source 0 23 {
      moduleRef := moduleReference
      mode := .items duplicateSelection none
    }
  let duplicateItem : TopItem :=
    locatedAt source 0 23 (.importDecl duplicateDeclaration)
  let duplicateModule : ParsedModuleV1 :=
    locatedAt source 0 23 { source, items := [duplicateItem] }
  assertTrue
    (Structure.structureDuplicateComparisonUnits duplicateModule == 2)
    "two duplicate-name scans must perform two key comparisons"
  assertTrue
    (Structure.structureCanonicalDedupComparisonUnits duplicateModule == 1)
    "two distinct diagnostic candidates must perform one dedup comparison"
  assertTrue
    (Structure.structureCanonicalOrderingComparisonUnits duplicateModule == 1)
    "sorting two canonical diagnostics must perform one ordering comparison"
  assertTrue
    (structureActualUnits duplicateModule ==
      structureNodeVisitUnits duplicateModule + 6)
    "the duplicate-module resource ledger did not sum all charged units"
  assertTrue
    (structureActualUnits duplicateModule ≤
      structureBound (astNodeMeasure duplicateModule))
    "the duplicate module exceeded the complete structural resource bound"

  let firstWildcardMarker : Marker :=
    locatedAt source 12 13 .wildcard
  let secondWildcardMarker : Marker :=
    locatedAt source 24 25 .wildcard
  let firstWildcard : ImportSelectorEntry :=
    locatedAt source 12 13 (.wildcard firstWildcardMarker)
  let secondWildcard : ImportSelectorEntry :=
    locatedAt source 24 25 (.wildcard secondWildcardMarker)
  let mixedSelection : ImportSelection :=
    locatedAt source 11 26 {
      entries := [firstWildcard, firstEntry, secondWildcard]
    }
  let mixedDeclaration : ImportDecl :=
    locatedAt source 0 26 {
      moduleRef := moduleReference
      mode := .items mixedSelection none
    }
  let mixedItem : TopItem :=
    locatedAt source 0 26 (.importDecl mixedDeclaration)
  let mixedModule : ParsedModuleV1 :=
    locatedAt source 0 26 { source, items := [mixedItem] }
  assertTrue (Structure.structureLeastSpanComparisonUnits mixedModule == 1)
    "two wildcard spans must perform one least-span comparison"
  assertTrue
    ((structureResourceLedger mixedModule).leastSpanComparisons == 1)
    "the mixed-wildcard comparison was not exposed by the resource ledger"
  assertTrue
    (structureActualUnits mixedModule ==
      (structureResourceLedger mixedModule).total)
    "the public structural total diverged from its resource ledger"
  assertTrue
    (structureActualUnits mixedModule ≤
      structureBound (astNodeMeasure mixedModule))
    "the mixed-wildcard module exceeded the structural resource bound"

end Tests
