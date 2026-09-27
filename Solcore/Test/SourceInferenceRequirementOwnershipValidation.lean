import Solcore.Frontend.SourceInference

/-!
Focused executable coverage for the final typed-source requirement-ownership
boundary.

The synthetic source exercises every primary attachment category while also
retaining secondary mirrors.  Requirement ownership is intentionally
order-insensitive because pattern obligations can be allocated before nodes
whose entries precede the enclosing match node in the final source table.
-/

set_option autoImplicit false

namespace Tests.SourceInferenceRequirementOwnershipValidation

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_inference_requirement_ownership_validation", by decide⟩],
    by decide⟩⟩

private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩

private def sourceId : Syntax.SourceId := {
  origin := .main
  path := "source_inference_requirement_ownership_validation.solc"
}

private def span : Syntax.SourceSpan := {
  source := sourceId
  startByte := 0
  endByte := 1
}

private def localId (index : Nat) : Resolved.LocalId :=
  ⟨owner, index⟩

private def occurrence (index : Nat) : OccurrenceId :=
  ⟨owner, index⟩

private def expressionId (index : Nat) : ExpressionId :=
  ⟨occurrence index⟩

private def statementId (index : Nat) : StatementId :=
  ⟨occurrence index⟩

private def requirementId (index : Nat) : RequirementId := ⟨index⟩

private def expressionRequirement := requirementId 0
private def patternRequirement := requirementId 1
private def directAssignmentRequirement := requirementId 2
private def forInitializerRequirement := requirementId 3
private def forPostRequirement := requirementId 4

private def schemeTemplateMirror := requirementId 100
private def indirectArgumentMirror := requirementId 101

private def predicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate .word

private def requirement (id : RequirementId) : Requirement := {
  id
  predicate
}

private def ledger (ids : List RequirementId) : List Requirement :=
  ids.map requirement

private def inputBinder : TypedBinder := {
  id := localId 0
  name := "input"
  scheme := .mono .word
  schemeRequirements := [{
    templateRequirement := schemeTemplateMirror
    predicate
  }]
  span := some span
}

private def assignment (owned : RequirementId) : AssignmentResolution := {
  target := {
    root := inputBinder.id
    projections := []
    type := .word
  }
  requirements := [owned]
}

private def expressionNode (index : Nat) (form : ExpressionForm)
    (requirements : List RequirementId := [])
    (coercions : List CoercionStep := []) : ExpressionNode := {
  id := expressionId index
  span
  type := .word
  form
  requirements
  coercions
}

private def statementNode (index : Nat) (form : StatementForm) :
    StatementNode := {
  id := statementId index
  span
  type := .unit
  form
}

private def integerResolution (owned : RequirementId) :
    IntegerLiteralResolution := {
  rawValue := 0
  targetType := .word
  requirement := owned
}

private def integerPattern (owned : RequirementId) : TypedMatchPattern := {
  source := .integerLiteral span {
    span
    value := .decimal "0"
  }
  type := .word
  resolution := .integerLiteral (.decimal "0") (integerResolution owned)
  requirements := [owned]
}

private def mixedSource : TypedSource := {
  owner
  inputs := [inputBinder]
  roots := []
  nodes := [
    .expression (expressionNode 0
      (.integerLiteral (.decimal "0")
        (integerResolution expressionRequirement))
      [expressionRequirement]
      [{
        requirement := expressionRequirement
        source := .word
        target := .word
      }]),
    .expression (expressionNode 1 (.call
      (expressionId 0) [] (.indirect {
        argumentCount := 0
        argumentTypeBeforeCoercion := .unit
        argumentTypeAfterCoercion := .unit
        argumentCoercions := [{
          requirement := indirectArgumentMirror
          source := .unit
          target := .unit
        }]
      }))),
    .statement (statementNode 2 (.matchWith {
      scrutinee := expressionId 0
      hiddenScrutinee := localId 1
      cases := [{
        span
        pattern := integerPattern patternRequirement
        body := []
      }]
      defaultBody := none
      requirements := [patternRequirement]
    })),
    .statement (statementNode 3 (.assignValue
      (assignment directAssignmentRequirement) .add (expressionId 0))),
    .statement (statementNode 4 (.forLoop
      [.assignBitNot (assignment forInitializerRequirement)]
      (expressionId 0)
      [.assignValue (assignment forPostRequirement) .subtract
        (expressionId 0)]
      []))
  ]
}

private def expectedPrimary : List RequirementId := [
  expressionRequirement,
  patternRequirement,
  directAssignmentRequirement,
  forInitializerRequirement,
  forPostRequirement
]

private def validate (source : TypedSource) (rows : List Requirement) :
    Except Error Unit :=
  Detail.validateSourceRequirementOwnership source rows

private def expectAccepted (label : String) (source : TypedSource)
    (rows : List Requirement) : IO Unit := do
  match validate source rows with
  | .ok () => pure ()
  | .error error => throw (IO.userError
      s!"{label}: valid requirement ownership produced {reprStr error}")

private def expectError (label : String) (source : TypedSource)
    (rows : List Requirement) (expected : Error) : IO Unit := do
  match validate source rows with
  | .error actual =>
      assertTrue (decide (actual = expected))
        s!"{label}: expected {reprStr expected}, got {reprStr actual}"
  | .ok () => throw (IO.userError
      s!"{label}: malformed requirement ownership passed validation")

private def changeExpressionRequirements (source : TypedSource)
    (selected : ExpressionId) (requirements : List RequirementId) :
    TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = selected then
          .expression { node with requirements }
        else
          .expression node
    | .statement node => .statement node
}

private def testCanonicalInventoryAndMirrors : IO Unit := do
  assertTrue (mixedSource.primaryRequirementIds == expectedPrimary)
    "canonical primary inventory omitted or reordered an attachment category"
  assertTrue (!mixedSource.primaryRequirementIds.contains schemeTemplateMirror &&
      !mixedSource.primaryRequirementIds.contains indirectArgumentMirror)
    "a local-scheme or indirect-coercion mirror became a primary attachment"
  expectAccepted "canonical mixed source" mixedSource (ledger expectedPrimary)

private def testPermutedLedgerAccepted : IO Unit :=
  expectAccepted "permuted solver ledger" mixedSource
    (ledger expectedPrimary.reverse)

private def testDuplicatePrimaryRejected : IO Unit := do
  let duplicate := changeExpressionRequirements mixedSource (expressionId 0)
    [expressionRequirement, expressionRequirement]
  expectError "duplicate primary attachment" duplicate
    (ledger expectedPrimary)
    (.duplicatePrimaryRequirement expressionRequirement)

private def testDuplicateLedgerRejected : IO Unit :=
  expectError "duplicate solver row" mixedSource
    (ledger (expectedPrimary ++ [patternRequirement]))
    (.duplicateRequirementLedgerRow patternRequirement)

private def testMissingLedgerRowRejected : IO Unit :=
  expectError "missing solver row" mixedSource
    (ledger [
      expressionRequirement,
      directAssignmentRequirement,
      forInitializerRequirement,
      forPostRequirement
    ])
    (.missingRequirementLedgerRow patternRequirement)

private def testUnattachedLedgerRowRejected : IO Unit :=
  expectError "mirror-only solver row" mixedSource
    (ledger (expectedPrimary ++ [indirectArgumentMirror]))
    (.unattachedRequirementLedgerRow indirectArgumentMirror)

private def defaultedPatternBodyRequirement := requirementId 200
private def defaultedPatternRequirement := requirementId 201

/-- A defaulted integer pattern is allocated before its arm is inferred, while
the arm's expression node precedes the enclosing match node in the final node
table.  The two inventories therefore agree by permutation, not equality. -/
private def defaultedPatternOrderSource : TypedSource := {
  owner
  inputs := []
  roots := []
  nodes := [
    .expression (expressionNode 10 (.literal (.decimal "1"))
      [defaultedPatternBodyRequirement]),
    .statement (statementNode 11 (.matchWith {
      scrutinee := expressionId 10
      hiddenScrutinee := localId 10
      cases := [{
        span
        pattern := integerPattern defaultedPatternRequirement
        body := []
      }]
      defaultBody := none
      requirements := [defaultedPatternRequirement]
    }))
  ]
}

private def testDefaultedPatternAllocationOrder : IO Unit := do
  assertTrue (defaultedPatternOrderSource.primaryRequirementIds == [
      defaultedPatternBodyRequirement,
      defaultedPatternRequirement
    ])
    "defaulted-pattern fixture lost final node-table ownership order"
  expectAccepted "defaulted pattern allocation order"
    defaultedPatternOrderSource
    (ledger [defaultedPatternRequirement, defaultedPatternBodyRequirement])

private def finalizeRequirement := requirementId 300

private def finalizeExpression : ExpressionNode :=
  expressionNode 20 (.literal (.decimal "2")) [finalizeRequirement]

private def finalizeState : State := {
  State.initial owner with
  nextOccurrence := 21
  nodes := [.expression finalizeExpression]
  nextRequirement := 301
  requirements := []
}

private def finalizeContext : Context := {
  environment := { modules := [], declarations := [] }
  signatures := {
    functions := []
    implRules := []
    traits := []
    implementations := []
  }
  scope := {
    currentModule := ownerModule
    genericOwner := owner
    genericParameters := []
  }
}

/-- Finalization must reject an unattested primary attachment before trait
solving, even when the occurrence forest and all earlier metadata are valid. -/
private def testFinalizeRejectsMissingLedgerRow : IO Unit := do
  match Detail.finalize finalizeContext .word finalizeState
      [.expression finalizeExpression.id] with
  | .error (.missingRequirementLedgerRow actual) =>
      assertTrue (actual == finalizeRequirement)
        "finalize lost the exact primary requirement missing from its ledger"
  | .error error => throw (IO.userError
      s!"finalize produced the wrong ownership diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError
      "finalize accepted a primary requirement without a raw ledger row")

def testSourceInferenceRequirementOwnershipValidation : IO Unit := do
  testCanonicalInventoryAndMirrors
  testPermutedLedgerAccepted
  testDuplicatePrimaryRejected
  testDuplicateLedgerRejected
  testMissingLedgerRowRejected
  testUnattachedLedgerRowRejected
  testDefaultedPatternAllocationOrder
  testFinalizeRejectsMissingLedgerRow

end Tests.SourceInferenceRequirementOwnershipValidation
