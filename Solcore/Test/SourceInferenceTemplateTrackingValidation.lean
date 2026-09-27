import Solcore.Frontend.SourceInference

/-!
Focused executable coverage for qualified local-scheme template tracking.

The synthetic source covers initialized statement lets, initialized lets in
both `for` header positions, multiple scheme requirements on one binder, and
the deliberate exclusion of uninitialized lets.  Classification is checked as
an order-insensitive exact inventory, while raw-ledger coverage remains an
independent requirement.
-/

set_option autoImplicit false

namespace Tests.SourceInferenceTemplateTrackingValidation

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_inference_template_tracking_validation", by decide⟩],
    by decide⟩⟩

private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩

private def sourceId : Syntax.SourceId := {
  origin := .main
  path := "source_inference_template_tracking_validation.solc"
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

private def statementTemplateA := requirementId 0
private def statementTemplateB := requirementId 1
private def forInitializerTemplateA := requirementId 2
private def forInitializerTemplateB := requirementId 3
private def forPostTemplate := requirementId 4
private def excludedUninitializedTemplate := requirementId 90
private def unownedTemplate := requirementId 91

private def predicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate .word

private def schemeRequirement (id : RequirementId) : LocalSchemeRequirement := {
  templateRequirement := id
  predicate
}

private def requirement (id : RequirementId) : Requirement := {
  id
  predicate
}

private def ledger (ids : List RequirementId) : List Requirement :=
  ids.map requirement

private def binder (index : Nat) (name : String)
    (templates : List RequirementId) : TypedBinder := {
  id := localId index
  name
  scheme := .mono .word
  schemeRequirements := templates.map schemeRequirement
  span := some span
}

private def statementNode (index : Nat) (form : StatementForm) :
    StatementNode := {
  id := statementId index
  span
  type := .unit
  form
}

private def templateSource
    (statementTemplates : List RequirementId :=
      [statementTemplateA, statementTemplateB]) : TypedSource := {
  owner
  inputs := []
  roots := []
  nodes := [
    .statement (statementNode 0 (.letDecl
      (binder 0 "statementInitialized" statementTemplates)
      (some (expressionId 100)))),
    .statement (statementNode 1 (.letDecl
      (binder 1 "statementUninitialized" [excludedUninitializedTemplate])
      none)),
    .statement (statementNode 2 (.forLoop
      [
        .letDecl
          (binder 2 "forInitializer"
            [forInitializerTemplateA, forInitializerTemplateB])
          (some (expressionId 101)),
        .letDecl
          (binder 3 "forInitializerUninitialized"
            [excludedUninitializedTemplate])
          none
      ]
      (expressionId 102)
      [
        .letDecl (binder 4 "forPost" [forPostTemplate])
          (some (expressionId 103))
      ]
      []))
  ]
}

private def expectedTemplates : List RequirementId := [
  statementTemplateA,
  statementTemplateB,
  forInitializerTemplateA,
  forInitializerTemplateB,
  forPostTemplate
]

private def trackingState (classified raw : List RequirementId) : State := {
  State.initial owner with
  localSchemeAssumptions := classified
  requirements := ledger raw
}

private def validate (source : TypedSource) (state : State) :
    Except Error Unit :=
  Detail.validateSourceTemplateTracking source state

private def expectAccepted (label : String) (source : TypedSource)
    (state : State) : IO Unit := do
  match validate source state with
  | .ok () => pure ()
  | .error error => throw (IO.userError
      s!"{label}: valid template tracking produced {reprStr error}")

private def expectError (label : String) (source : TypedSource)
    (state : State) (expected : Error) : IO Unit := do
  match validate source state with
  | .error actual =>
      assertTrue (decide (actual = expected))
        s!"{label}: expected {reprStr expected}, got {reprStr actual}"
  | .ok () => throw (IO.userError
      s!"{label}: malformed template tracking passed validation")

private def testCanonicalInventoryAndValidState : IO Unit := do
  let source := templateSource
  assertTrue (source.localSchemeTemplateIds == expectedTemplates)
    "canonical template inventory omitted or reordered a let category"
  assertTrue (!source.localSchemeTemplateIds.contains
      excludedUninitializedTemplate)
    "an uninitialized statement or for-header let contributed a template"
  expectAccepted "canonical source classification" source
    (trackingState expectedTemplates expectedTemplates)

private def testPermutedClassificationAccepted : IO Unit :=
  expectAccepted "permuted state classification" templateSource
    (trackingState expectedTemplates.reverse expectedTemplates)

private def testDuplicateTemplateRejected : IO Unit :=
  expectError "duplicate source template"
    (templateSource [statementTemplateA, statementTemplateA])
    (trackingState expectedTemplates expectedTemplates)
    (.duplicateLocalSchemeTemplate statementTemplateA)

private def testDuplicateAssumptionRejected : IO Unit :=
  expectError "duplicate classified assumption" templateSource
    (trackingState (expectedTemplates ++ [statementTemplateA])
      expectedTemplates)
    (.duplicateLocalSchemeAssumption statementTemplateA)

private def testMissingAssumptionRejected : IO Unit :=
  expectError "missing classified assumption" templateSource
    (trackingState [
      statementTemplateA,
      forInitializerTemplateA,
      forInitializerTemplateB,
      forPostTemplate
    ] expectedTemplates)
    (.missingLocalSchemeAssumption statementTemplateB)

private def testUnownedAssumptionRejected : IO Unit :=
  expectError "unowned classified assumption" templateSource
    (trackingState (expectedTemplates ++ [unownedTemplate])
      (expectedTemplates ++ [unownedTemplate]))
    (.unownedLocalSchemeAssumption unownedTemplate)

private def testMissingRawRequirementRejected : IO Unit :=
  expectError "classified assumption without a raw row" templateSource
    (trackingState expectedTemplates [
      statementTemplateA,
      forInitializerTemplateA,
      forInitializerTemplateB,
      forPostTemplate
    ])
    (.missingLocalSchemeRequirement statementTemplateB)

private def finalizeTemplate := requirementId 200

private def finalizeExpression : ExpressionNode := {
  id := expressionId 20
  span
  type := .word
  form := .literal (.decimal "0")
  requirements := [finalizeTemplate]
}

private def finalizeBinder : TypedBinder :=
  binder 20 "finalizeLocal" [finalizeTemplate]

private def finalizeStatement : StatementNode :=
  statementNode 21 (.letDecl finalizeBinder (some finalizeExpression.id))

private def finalizeRoots : List NodeId :=
  [.statement finalizeStatement.id]

private def finalizeState : State := {
  State.initial owner with
  nextLocal := 21
  nextOccurrence := 22
  nodes := [
    .expression finalizeExpression,
    .statement finalizeStatement
  ]
  nextRequirement := 201
  requirements := ledger [finalizeTemplate]
  localSchemeAssumptions := []
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

/-! Finalization must reject malformed template classification before trait
solving once the occurrence forest and declaration-local identities are valid. -/
private def testFinalizeRejectsTemplateMismatch : IO Unit := do
  let source := finalizeState.toTypedSource finalizeRoots
  match Detail.validateSourceGraph source with
  | .error error => throw (IO.userError
      s!"finalize fixture is not graph-valid: {reprStr error}")
  | .ok () => pure ()
  match Detail.validateSourceLocalIdentities source with
  | .error error => throw (IO.userError
      s!"finalize fixture has invalid local identities: {reprStr error}")
  | .ok () => pure ()
  match Detail.finalize finalizeContext .unit finalizeState finalizeRoots with
  | .error (.missingLocalSchemeAssumption actual) =>
      assertTrue (actual == finalizeTemplate)
        "finalize lost the exact unclassified source template"
  | .error error => throw (IO.userError
      s!"finalize produced the wrong template diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError
      "finalize accepted an unclassified qualified-local template")

def testSourceInferenceTemplateTrackingValidation : IO Unit := do
  testCanonicalInventoryAndValidState
  testPermutedClassificationAccepted
  testDuplicateTemplateRejected
  testDuplicateAssumptionRejected
  testMissingAssumptionRejected
  testUnownedAssumptionRejected
  testMissingRawRequirementRejected
  testFinalizeRejectsTemplateMismatch

end Tests.SourceInferenceTemplateTrackingValidation
