import Solcore.Frontend.SourceInference.Internal.ExpressionProperties
import Solcore.Frontend.SourceInference
import Solcore.Frontend.SourceInference.Internal.NodeGraph
import Solcore.Frontend.ProgramInterfaces

/-!
# Source inference tests

Typed IR inference, inference validation, requirement identity, path extensions and the phase 7 language
forms. They stay apart from the typed runtime tests, whose imports bring a second `checkLoadedProgram`.
-/

section
-- leanmerge: from Solcore.Test.SourceInferenceEmptyMatchGuard
/-! Regression: nominal exhaustiveness must not accept an empty arm list by
vacuous quantification over an empty constructor catalog. -/

set_option autoImplicit false

namespace Tests.SourceInferenceEmptyMatchGuard

open Solcore.Frontend Solcore.Frontend.SourceInference Solcore.TypeSystem

example (context : Context) (state : State) (scrutineeType : Ty) :
    Detail.exhaustsNominalConstructors context state scrutineeType [] = false := by
  rfl

end Tests.SourceInferenceEmptyMatchGuard
end

section
-- leanmerge: from Solcore.Test.SourceInferenceLocalIdentityValidation
/-!
Focused executable coverage for the final typed-source local-identity boundary.

The synthetic source deliberately exercises every binder category consumed by
the canonical `TypedSource.definedLocalIds` inventory.  The node graph itself is
irrelevant here: this file isolates declaration ownership and uniqueness from
the separate occurrence-graph validator.
-/

set_option autoImplicit false

namespace Tests.SourceInferenceLocalIdentityValidation

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_inference_local_identity_validation", by decide⟩],
    by decide⟩⟩

private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩

private def foreignOwner : Resolved.DeclarationId :=
  { owner with declarationIndex := 1 }

private def sourceId : Syntax.SourceId := {
  origin := .main
  path := "source_inference_local_identity_validation.solc"
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

private def binder (id : Resolved.LocalId) (name : String) : TypedBinder := {
  id
  name
  scheme := .mono .word
  span := some span
}

private def expressionNode (index : Nat) (form : ExpressionForm) :
    ExpressionNode := {
  id := expressionId index
  span
  type := .word
  form
}

private def statementNode (index : Nat) (form : StatementForm) :
    StatementNode := {
  id := statementId index
  span
  type := .unit
  form
}

private def inputBinder := binder (localId 0) "input"
private def lambdaBinder := binder (localId 1) "lambdaParameter"
private def letBinder := binder (localId 2) "local"
private def hiddenScrutinee := localId 3
private def rootPatternBinder := binder (localId 4) "rootPattern"
private def nestedPatternBinder := binder (localId 5) "nestedPattern"
private def forInitializerBinder := binder (localId 6) "initializer"
private def forPostBinder := binder (localId 7) "post"

private def rootBinderPattern : TypedMatchPattern := {
  source := .binder span rootPatternBinder.name
  type := .word
  resolution := .binder rootPatternBinder
}

/-- A tuple-root pattern whose nested child introduces a binder. -/
private def nestedBinderPattern : TypedMatchPattern := {
  source := .tuple span 1
  type := .word
  resolution := .tuple [.binder nestedPatternBinder]
}

private def localIdentitySource (selectedLambdaBinder : TypedBinder) :
    TypedSource := {
  owner
  inputs := [inputBinder]
  roots := [
    .expression (expressionId 0),
    .statement (statementId 1),
    .statement (statementId 3),
    .statement (statementId 5)
  ]
  nodes := [
    .expression (expressionNode 0
      (.lambda [selectedLambdaBinder] .unit [])),
    .statement (statementNode 1 (.letDecl letBinder none)),
    .expression (expressionNode 2 (.literal (.decimal "0"))),
    .statement (statementNode 3 (.matchWith {
      scrutinee := expressionId 2
      hiddenScrutinee
      cases := [
        { span, pattern := rootBinderPattern, body := [] },
        { span, pattern := nestedBinderPattern, body := [] }
      ]
      defaultBody := none
    })),
    .expression (expressionNode 4 (.literal (.decimal "1"))),
    .statement (statementNode 5 (.forLoop
      [.letDecl forInitializerBinder none]
      (expressionId 4)
      [.letDecl forPostBinder none]
      []))
  ]
}

private def expectedLocalIds : List Resolved.LocalId :=
  [
    inputBinder.id,
    lambdaBinder.id,
    letBinder.id,
    hiddenScrutinee,
    rootPatternBinder.id,
    nestedPatternBinder.id,
    forInitializerBinder.id,
    forPostBinder.id
  ]

private def testCanonicalInventoryAndValidSource : IO Unit := do
  let source := localIdentitySource lambdaBinder
  assertTrue (source.definedLocalIds == expectedLocalIds)
    "the canonical local-ID inventory omitted or reordered a binder category"
  match Detail.validateSourceLocalIdentities source with
  | .ok () => pure ()
  | .error error => throw (IO.userError
      s!"a unique declaration-owned local inventory produced {reprStr error}")

private def testDuplicateRejected : IO Unit := do
  let duplicate := { lambdaBinder with id := inputBinder.id }
  match Detail.validateSourceLocalIdentities (localIdentitySource duplicate) with
  | .error (.duplicateLocalIdentity id) =>
      assertTrue (id == inputBinder.id)
        "duplicate validation lost the exact shared input/lambda identity"
  | .error error => throw (IO.userError
      s!"a duplicate input/lambda identity produced {reprStr error}")
  | .ok () => throw (IO.userError
      "a duplicate input/lambda identity passed validation")

private def testForeignOwnerRejected : IO Unit := do
  let foreignId : Resolved.LocalId := ⟨foreignOwner, lambdaBinder.id.binderIndex⟩
  let foreign := { lambdaBinder with id := foreignId }
  match Detail.validateSourceLocalIdentities (localIdentitySource foreign) with
  | .error (.localIdentityOwnerMismatch expected actual) =>
      assertTrue (expected == owner && actual == foreignId)
        "owner validation lost the exact expected or foreign local identity"
  | .error error => throw (IO.userError
      s!"a foreign-owner lambda identity produced {reprStr error}")
  | .ok () => throw (IO.userError
      "a foreign-owner lambda identity passed validation")

def testSourceInferenceLocalIdentityValidation : IO Unit := do
  testCanonicalInventoryAndValidSource
  testDuplicateRejected
  testForeignOwnerRejected

end Tests.SourceInferenceLocalIdentityValidation
end

section
-- leanmerge: from Solcore.Test.SourceInferenceRequirementOwnershipValidation
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
end

section
-- leanmerge: from Solcore.Test.SourceInferenceTemplateScopeValidation
/-!
Focused executable coverage for qualified local-scheme template scope
validation.

The synthetic source retains one initialized `let` and one template row.  The
negative fixtures independently tamper the row predicate, remove its primary
attachment, or move that attachment to a separate source root outside the
initializer subtree.
-/

set_option autoImplicit false

namespace Tests.SourceInferenceTemplateScopeValidation

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_inference_template_scope_validation", by decide⟩],
    by decide⟩⟩

private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩

private def sourceId : Syntax.SourceId := {
  origin := .main
  path := "source_inference_template_scope_validation.solc"
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

private def templateId : RequirementId := ⟨0⟩

private def templatePredicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate .word

private def wrongPredicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate .bool

private def templateRequirement : LocalSchemeRequirement := {
  templateRequirement := templateId
  predicate := templatePredicate
}

private def templateBinder : TypedBinder := {
  id := localId 0
  name := "template"
  scheme := .mono .word
  schemeRequirements := [templateRequirement]
  span := some span
}

private def expressionNode (index : Nat)
    (requirements : List RequirementId) : ExpressionNode := {
  id := expressionId index
  span
  type := .word
  form := .literal (.decimal "0")
  requirements
}

private def initializer := expressionNode 0 [templateId]

private def letStatement : StatementNode := {
  id := statementId 1
  span
  type := .unit
  form := .letDecl templateBinder (some initializer.id)
}

private def validSource : TypedSource := {
  owner
  inputs := []
  roots := [.statement letStatement.id]
  nodes := [
    .expression initializer,
    .statement letStatement
  ]
}

private def validationState (source : TypedSource)
    (predicate : ProgramPredicate := templatePredicate) : State := {
  State.initial owner with
  nextLocal := 1
  nextOccurrence := 3
  nodes := source.nodes
  nextRequirement := 1
  requirements := [{ id := templateId, predicate }]
  localSchemeAssumptions := [templateId]
}

private def validate (source : TypedSource) (state : State) :
    Except Error Unit :=
  Detail.validateSourceTemplateScopes source state

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

private def expectAccepted (label : String) (source : TypedSource)
    (state : State) : IO Unit := do
  match validate source state with
  | .ok () => pure ()
  | .error error => throw (IO.userError
      s!"{label}: valid template scope produced {reprStr error}")

private def expectError (label : String) (source : TypedSource)
    (state : State) (expected : Error) : IO Unit := do
  match validate source state with
  | .error actual =>
      assertTrue (decide (actual = expected))
        s!"{label}: expected {reprStr expected}, got {reprStr actual}"
  | .ok () => throw (IO.userError
      s!"{label}: malformed template scope passed validation")

private def testInitializedLetAccepted : IO Unit :=
  expectAccepted "initialized let" validSource (validationState validSource)

private def groupedInitializer : ExpressionNode := {
  expressionNode 2 [] with
  form := .group initializer.id
}

private def groupedLetStatement : StatementNode := {
  letStatement with
  form := .letDecl templateBinder (some groupedInitializer.id)
}

private def descendantScopeSource : TypedSource := {
  validSource with
  roots := [.statement groupedLetStatement.id]
  nodes := [
    .expression initializer,
    .expression groupedInitializer,
    .statement groupedLetStatement
  ]
}

private def testInitializerDescendantAccepted : IO Unit := do
  assertTrue
    ((Detail.sourceSubtreeNodeIds descendantScopeSource
      (.expression groupedInitializer.id)).contains
        (.expression initializer.id))
    "initializer subtree traversal lost a requirement-bearing descendant"
  expectAccepted "initializer descendant" descendantScopeSource
    (validationState descendantScopeSource)

private def testPredicateMismatchRejected : IO Unit :=
  expectError "template predicate mismatch" validSource
    (validationState validSource wrongPredicate)
    (.localSchemeTemplatePredicateMismatch templateId templatePredicate
      wrongPredicate)

private def missingPrimarySource : TypedSource := {
  validSource with
  nodes := [
    .expression (expressionNode 0 []),
    .statement letStatement
  ]
}

private def testMissingPrimaryRejected : IO Unit :=
  expectError "missing primary template attachment" missingPrimarySource
    (validationState missingPrimarySource)
    (.missingLocalSchemePrimaryRequirement templateId)

private def outsideInitializer := expressionNode 2 [templateId]

private def outsideScopeSource : TypedSource := {
  validSource with
  roots := [
    .statement letStatement.id,
    .expression outsideInitializer.id
  ]
  nodes := [
    .expression (expressionNode 0 []),
    .statement letStatement,
    .expression outsideInitializer
  ]
}

private def testOutsideInitializerRejected : IO Unit :=
  expectError "template attachment outside initializer" outsideScopeSource
    (validationState outsideScopeSource)
    (.localSchemeTemplateOutOfScope templateId
      (.expression initializer.id) (.expression outsideInitializer.id))

/-- The complete finalization path runs scope validation after constructing the
final substituted source and before requirement solving. -/
private def testFinalizeIntegration : IO Unit := do
  match Detail.finalize finalizeContext .unit
      (validationState validSource) validSource.roots with
  | .ok _ => pure ()
  | .error error => throw (IO.userError
      s!"valid template scope failed finalization: {reprStr error}")
  match Detail.finalize finalizeContext .unit
      (validationState validSource wrongPredicate) validSource.roots with
  | .error (.localSchemeTemplatePredicateMismatch id expected actual) =>
      assertTrue (id == templateId && expected == templatePredicate &&
          actual == wrongPredicate)
        "finalize lost the exact template predicate mismatch"
  | .error error => throw (IO.userError
      s!"finalize produced the wrong scope diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError
      "finalize accepted a mismatched local-scheme template predicate")

def testSourceInferenceTemplateScopeValidation : IO Unit := do
  testInitializedLetAccepted
  testInitializerDescendantAccepted
  testPredicateMismatchRejected
  testMissingPrimaryRejected
  testOutsideInitializerRejected
  testFinalizeIntegration

end Tests.SourceInferenceTemplateScopeValidation
end

section
-- leanmerge: from Solcore.Test.SourceInferenceTemplateTrackingValidation
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
end

section
-- leanmerge: from Solcore.Test.SourceNodeGraphAutomation
set_option autoImplicit false

namespace Tests.SourceNodeGraphAutomation

open Solcore.Frontend.SourceInference

private def StateTail := Nat × State
private def NestedStateTail := Bool × StateTail

example (pair : NestedStateTail) : ∃ _ : State, True := by
  occurrence_split_state_pairs
  rename_i flag count state
  exact ⟨state, trivial⟩

example (pair : State × Nat) : pair.2 = pair.2 := by
  occurrence_split_state_pairs
  guard_hyp pair : State × Nat
  rfl

private def LeftEquations (a b c : Nat) := a = b ∧ (True ∧ b = c)
private def RightEquations (c d : Nat) := (True ∨ False) ∧ c = d

example (a b c d : Nat)
    (equations : LeftEquations a b c ∧ RightEquations c d) :
    a = b ∧ b = c ∧ c = d := by
  occurrence_split_conjunctions
  exact ⟨by assumption, by assumption, by assumption⟩

example (_ignored : True ∧ (True ∨ False)) : True := by
  occurrence_split_conjunctions
  trivial

end Tests.SourceNodeGraphAutomation
end

section
-- leanmerge: from Solcore.Test.SourcePathExtensions
/-! Canonical Rust source paths retain exact provenance and share module names with legacy paths. -/
set_option autoImplicit false
namespace Tests.SourcePathExtensions
open Solcore Solcore.Frontend

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def parse (text : String) : IO Workspace.CanonicalSourcePath :=
  match Workspace.CanonicalSourcePath.parse text with
  | some path => pure path
  | none => throw (IO.userError s!"source path rejected: {text}")

private def source : String := "function main() returns (word) { return 7; }"

private def raw (entry : String) (sources : List Workspace.RawSourceFile) : Workspace.RawWorkspace :=
  {entry, mainSources := sources, externalLibraries := []}

def run : IO Unit := do
  for stem in ["main", "nested/Module_1", "function"] do
    let canonical ← parse (stem ++ ".sol")
    let legacy ← parse (stem ++ ".solc")
    require (canonical.extension == .sol && legacy.extension == .solc)
      "source path parser lost its exact extension"
    require (canonical.render == stem ++ ".sol" && legacy.render == stem ++ ".solc")
      "source path renderer changed its original spelling"
    require (canonical.modulePath == legacy.modulePath && canonical != legacy)
      "source and module identity no longer distinguish suffix spelling"
    let canonicalId : Workspace.SourceId := {library := .main, path := canonical}
    let legacyId : Workspace.SourceId := {library := .main, path := legacy}
    require (canonicalId.toModuleId == legacyId.toModuleId)
      "source extensions created distinct module identities"
    require ((syntaxSourceIdOfWorkspaceSource canonicalId).path == stem ++ ".sol")
      "parser-boundary provenance rewrote a canonical source path"
  for suffix in ["sol", "solc"] do
    let path := "main." ++ suffix
    match loadProgram (raw path [{path, content := source}]) with
    | .error errors => throw (IO.userError s!"source loading failed: {reprStr errors}")
    | .ok loaded =>
      require (loaded.sources.map (·.source.path) == [path])
        "loaded program lost source suffix provenance"
      require (loaded.environment.modules.length == 1) "source loading lost its module"
  match loadProgram (raw "main.sol" [
      {path := "main.sol", content := source}, {path := "main.solc", content := source}]) with
  | .error [.environment (.duplicateModule _)] => pure ()
  | result => throw (IO.userError s!"mixed suffix module collision was not rejected: {reprStr result}")
  match loadProgram (raw "main.sol" [{path := "main.solc", content := source}]) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "entry matching silently substituted the legacy source path")
  for path in [".sol", "a/.sol", "a.SOL", "a.sol.sol", "a.solc.sol", "a.sol.solc", "../a.sol", "a//b.sol"] do
    require (Workspace.CanonicalSourcePath.parse path).isNone s!"malformed canonical path accepted: {path}"

end Tests.SourcePathExtensions
end

section
-- leanmerge: from Solcore.Test.SourcePhase7Inference
/-!
Focused source-inference regressions for the phase-7 language forms.

These tests deliberately exercise the raw-workspace entry point.  They
therefore cover parsing, whole-program signature construction, name/type
resolution, and body inference together instead of manufacturing typed IR.
-/

set_option autoImplicit false

namespace Tests.SourcePhase7Inference

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def check (label content : String) :
    IO (List CheckedFunction) := do
  match loadAndCheckProgram (workspace content) with
  | .ok functions => pure functions
  | .error errors => throw (IO.userError
      s!"{label} failed source inference: {reprStr errors}")

private def expectInferenceError (label content : String)
    (accept : Error → Bool) : IO Unit := do
  match loadAndCheckProgram (workspace content) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure => accept failure.error
        | _ => false) s!"{label} reported the wrong error: {reprStr errors}"
  | .ok _ => throw (IO.userError s!"{label} was unexpectedly accepted")

private def checkedNamed (functions : List CheckedFunction)
    (environment : ProgramEnvironment) (name : String) : IO CheckedFunction :=
  match functions.find? fun function =>
      (environment.declaration? function.declaration).any fun declaration =>
        declaration.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def checkedProgram (label content : String) :
    IO (ProgramEnvironment × List CheckedFunction) := do
  let loaded ← match loadProgram (workspace content) with
    | .ok loaded => pure loaded
    | .error errors => throw (IO.userError
        s!"{label} failed loading: {reprStr errors}")
  let functions ← match checkLoadedProgram loaded with
    | .ok functions => pure functions
    | .error errors => throw (IO.userError
        s!"{label} failed source inference: {reprStr errors}")
  pure (loaded.environment, functions)

private def hasConstructorExpression (function : CheckedFunction) : Bool :=
  function.typedBody.nodes.any fun
    | .expression { form := .constructor .., .. } => true
    | _ => false

private def hasConstructorPattern (function : CheckedFunction) : Bool :=
  function.typedBody.nodes.any fun
    | .statement { form := .matchWith resolution, .. } =>
        resolution.cases.any fun arm => match arm.pattern.resolution with
          | .constructor .. => true
          | _ => false
    | _ => false

private def testConstructors : IO Unit := do
  let source := String.intercalate "\n" [
    "enum Box<T> { Empty, Wrap(T) }",
    "function qualified(value: Word) returns (Box<Word>) {",
    "  return Box.Wrap(value);",
    "}",
    "function contextual(value: Word) returns (Box<Word>) {",
    "  return .Wrap(value);",
    "}"
  ]
  let (environment, functions) ← checkedProgram "constructor forms" source
  let qualified ← checkedNamed functions environment "qualified"
  let contextual ← checkedNamed functions environment "contextual"
  assertTrue (hasConstructorExpression qualified)
    "qualified generic constructor did not produce a constructor node"
  assertTrue (hasConstructorExpression contextual)
    "contextual constructor did not produce a constructor node"

  expectInferenceError "constructor arity"
    (String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "function bad() returns (Box<Word>) { return Box.Wrap(); }"
    ]) fun error => error matches .constructorArityMismatch _ 1 0
  expectInferenceError "unknown contextual constructor"
    (String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "function bad(value: Word) returns (Box<Word>) {",
      "  return .Missing(value);",
      "}"
    ]) fun error => error == .unknownConstructor [] "Missing"
  expectInferenceError "unknown qualified constructor"
    (String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "function bad(value: Word) returns (Box<Word>) {",
      "  return Box.Missing(value);",
      "}"
    ]) fun error => error == .unknownConstructor ["Box"] "Missing"
  expectInferenceError "contextual constructor without an expected type"
    (String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "function bad() { .Wrap(1); return; }"
    ]) fun error => error == .constructorNeedsExpectedType "Wrap"

private def testConstructorPatterns : IO Unit := do
  let source := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "function nested(tree: Tree<Word>) returns (Word) {",
    "  match (tree) {",
    "    case .Pair(.Leaf(left), .Leaf(right)) { return left; }",
    "    default { return 0; }",
    "  }",
    "}"
  ]
  let (environment, functions) ← checkedProgram "nested patterns" source
  let nested ← checkedNamed functions environment "nested"
  assertTrue (hasConstructorPattern nested)
    "nested constructor/binder pattern did not produce constructor metadata"

  expectInferenceError "duplicate pattern binder"
    (String.intercalate "\n" [
      "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
      "function bad(tree: Tree<Word>) returns (Word) {",
      "  match (tree) {",
      "    case .Pair(.Leaf(value), .Leaf(value)) { return value; }",
      "    default { return 0; }",
      "  }",
      "}"
    ]) fun error => error == .duplicatePatternBinder "value"

private def testMultipleScrutinees : IO Unit := do
  let functions ← check "multiple scrutinees" (String.intercalate "\n" [
    "function select(left: Word, right: Bool) returns (Word) {",
    "  match (left, right) {",
    "    case (value, flag) { return flag ? value : 0; }",
    "    default { return 1; }",
    "  }",
    "}"
  ])
  assertTrue (functions.length == 1)
    "multiple-scrutinee tuple pattern lost its checked function"

private def testAssignments : IO Unit := do
  let functions ← check "assignments" (String.intercalate "\n" [
    "function update() returns (Word) {",
    "  let local: Word = 0;",
    "  local = 1;",
    "  let table: mapping(Word => Word);",
    "  table[local] = 2;",
    "  return table[local];",
    "}"
  ])
  let function ← match functions with
    | [function] => pure function
    | _ => throw (IO.userError "assignment fixture lost its checked function")
  let assignments := function.typedBody.nodes.filter fun
    | .statement { form := .assignValue .., .. } => true
    | _ => false
  let indexes := function.typedBody.nodes.filter fun
    | .expression { form := .index .., .. } => true
    | _ => false
  assertTrue (decide (assignments.length = 2) && !indexes.isEmpty)
    "local or mapping-index assignment did not survive in typed source"

private def testLoopsAndControl : IO Unit := do
  let functions ← check "loops and control" (String.intercalate "\n" [
    "function loops(flag: Bool) returns (Word) {",
    "  let total: Word = 0;",
    "  while (flag) { total += 1; break; }",
    "  for (let i: Word = 0; i < 2; i += 1) {",
    "    if (i == 0) { continue; } else { break; }",
    "  }",
    "  return total;",
    "}"
  ])
  let function ← match functions with
    | [function] => pure function
    | _ => throw (IO.userError "loop fixture lost its checked function")
  let hasWhile := function.typedBody.nodes.any fun
    | .statement { form := .whileLoop .., .. } => true
    | _ => false
  let hasFor := function.typedBody.nodes.any fun
    | .statement { form := .forLoop .., .. } => true
    | _ => false
  let hasBreak := function.typedBody.nodes.any fun
    | .statement { form := .breakStmt, .. } => true
    | _ => false
  let hasContinue := function.typedBody.nodes.any fun
    | .statement { form := .continueStmt, .. } => true
    | _ => false
  assertTrue (hasWhile && hasFor && hasBreak && hasContinue)
    "for/while or nested break/continue did not survive in typed source"

  for (kind, statement) in [("break", "break;"), ("continue", "continue;")] do
    expectInferenceError s!"loop-external {kind}"
      ("function bad() { " ++ statement ++ " return; }") fun error =>
        error == .controlOutsideLoop kind

  expectInferenceError "lambda cannot break its enclosing loop"
    (String.intercalate "\n" [
      "function bad(flag: Bool) {",
      "  while (flag) {",
      "    let escape = lam() { break; };",
      "    break;",
      "  }",
      "}"
    ]) fun error => error == .controlOutsideLoop "break"

private def testNonterminalMatch : IO Unit := do
  let functions ← check "nonterminal match" (String.intercalate "\n" [
    "function route(tag: Word) returns (Word) {",
    "  let result: Word = 0;",
    "  match (tag) {",
    "    case 0 { result = 1; }",
    "    default { result = 2; }",
    "  }",
    "  return result;",
    "}"
  ])
  assertTrue (functions.length == 1)
    "a nonterminal exhaustive match did not check"

/-- Exercise every phase-7 source-inference form before runtime lowering. -/
def testSourcePhase7Inference : IO Unit := do
  testConstructors
  testConstructorPatterns
  testMultipleScrutinees
  testAssignments
  testLoopsAndControl
  testNonterminalMatch
  IO.println "phase-7 source inference GREEN"

end Tests.SourcePhase7Inference
end

section
-- leanmerge: from Solcore.Test.SourceRequirementIdentity
/-! Stable function-local identities for solved source obligations. -/

set_option autoImplicit false

namespace Tests.SourceRequirementIdentity

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private structure Fixture where
  environment : ProgramEnvironment
  checked : List SourceInference.CheckedFunction

private def check (content : String) : IO Fixture := do
  match loadProgram (workspace content) with
  | .error errors =>
      throw (IO.userError s!"requirement identity loading failed: {reprStr errors}")
  | .ok loaded =>
      match SourceInference.checkLoadedProgram loaded with
      | .error errors =>
          throw (IO.userError
            s!"requirement identity checking failed: {reprStr errors}")
      | .ok checked => pure { environment := loaded.environment, checked }

private def checkedNamed (fixture : Fixture) (name : String) :
    IO SourceInference.CheckedFunction :=
  match fixture.checked.find? fun function =>
      match fixture.environment.declaration? function.declaration with
      | some declaration => declaration.name == some name
      | none => false with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def namedType (environment : ProgramEnvironment) (name : String) :
    IO TypeSystem.Ty :=
  match environment.typesNamed name with
  | [declaration] => pure (.nominal declaration.id)
  | declarations =>
      throw (IO.userError
        s!"expected one type `{name}`, found {declarations.length}")

private def namedTrait (environment : ProgramEnvironment) (name : String) :
    IO Resolved.DeclarationId :=
  match environment.traitsNamed name with
  | [declaration] => pure declaration.id
  | declarations =>
      throw (IO.userError
        s!"expected one trait `{name}`, found {declarations.length}")

private def predicate (trait : Resolved.DeclarationId) (subject : TypeSystem.Ty)
    (arguments : List TypeSystem.Ty := []) : ProgramPredicate := {
  trait
  subject
  arguments
}

private def evidenceHasGoal (expected : ProgramPredicate) :
    SourceInference.PredicateEvidence → Bool
  | .assumption actual => decide (actual = expected)
  | .implementation (.byImpl goal _ _) => decide (goal = expected)

private def aligned (function : SourceInference.CheckedFunction)
    (expected : List ProgramPredicate) : Bool :=
  let solved := function.solvedRequirements
  decide (solved.map (·.id.index) = List.range solved.length) &&
    decide (solved.map (·.predicate) = expected) &&
    decide (function.predicates = expected) &&
    function.evidence == solved.map (·.evidence) &&
    solved.all fun requirement =>
      evidenceHasGoal requirement.predicate requirement.evidence &&
        decide (requirement.evidence.goal = requirement.predicate)

private def testAssumptionAndImplementationKeepPathIds : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum C { Only }",
    "impl Coerce<B, C> {}",
    "function accept(value: C) returns (C) { return value; }",
    "function convert(value: A) returns (C) where A: Coerce<B> {",
    "  return accept(value);",
    "}"
  ])
  let convert ← checkedNamed fixture "convert"
  let a ← namedType fixture.environment "A"
  let b ← namedType fixture.environment "B"
  let c ← namedType fixture.environment "C"
  let coerce ← namedTrait fixture.environment "Coerce"
  let first := predicate coerce a [b]
  let second := predicate coerce b [c]
  assertTrue (aligned convert [first, second])
    "multi-step coercion requirements lost contiguous path identities"
  match convert.solvedRequirements with
  | [{ evidence := .assumption _ , .. },
      { evidence := .implementation _, .. }] => pure ()
  | _ => throw (IO.userError
      "assumption and implementation evidence changed requirement order")

private def testCandidateForkCommitsOnlySelectedIds : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Ready<T> {}",
    "trait Coerce<From, To> {}",
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "enum Box { Only }",
    "enum Flag { Only }",
    "enum Token { Only }",
    "impl Ready<Word> {}",
    "impl Coerce<Word, Box> {}",
    "impl Eq<Token> {",
    "  function eq(left: Token, right: Token) returns (Bool) { return true; }",
    "}",
    "function choose(value: Box) returns (Bool) { return true; }",
    "function choose(value: Flag) returns (Bool) { return true; }",
    "function choose<T>(value: T) returns (Bool) where T: Ready {",
    "  return true;",
    "}",
    "function run(value: Word, token: Token) returns (Bool) {",
    "  choose(value);",
    "  return token == token;",
    "}"
  ])
  let run ← checkedNamed fixture "run"
  let token ← namedType fixture.environment "Token"
  let ready ← namedTrait fixture.environment "Ready"
  let equality ← namedTrait fixture.environment "Eq"
  assertTrue (aligned run [predicate ready .word, predicate equality token])
    "failed or higher-cost candidates consumed committed requirement identities"

private def testIntegerLiteralOwnsImmediateRequirementId : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "function compute(value: Word) returns (Word) { return value + 1; }"
  ])
  let compute ← checkedNamed fixture "compute"
  let integer := ProgramSignatures.builtinIntPredicate TypeSystem.Ty.word
  assertTrue (aligned compute [integer])
    "integer literal did not retain its inference-time builtin Int requirement ID"
  match compute.typedBody.nodes.filterMap fun
      | .expression node => match node.form with
          | .integerLiteral _ resolution => some (node, resolution)
          | _ => none
      | .statement _ => none with
  | [(node, resolution)] =>
      assertTrue (decide (resolution.requirement = ⟨0⟩ ∧
          node.requirements = [resolution.requirement]))
        "integer literal requirement was allocated twice or attached late"
  | literals => throw (IO.userError
      s!"expected one integer carrier, found {literals.length}")

private def testRepeatedPredicatesKeepDistinctIds : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "enum Token { Only }",
    "impl Eq<Token> {",
    "  function eq(left: Token, right: Token) returns (Bool) { return true; }",
    "}",
    "function compareTwice(token: Token) returns (Bool) {",
    "  token == token;",
    "  return token == token;",
    "}"
  ])
  let compareTwice ← checkedNamed fixture "compareTwice"
  let token ← namedType fixture.environment "Token"
  let equality ← namedTrait fixture.environment "Eq"
  let equalityOnToken := predicate equality token
  assertTrue (aligned compareTwice [equalityOnToken, equalityOnToken])
    "repeated identical predicates were merged or shared a requirement identity"

/-- Exercise identity order across coercion paths, transactional overload
selection, and immediate integer-literal requirement allocation. -/
def testSourceRequirementIdentity : IO Unit := do
  testAssumptionAndImplementationKeepPathIds
  testCandidateForkCommitsOnlySelectedIds
  testIntegerLiteralOwnsImmediateRequirementId
  testRepeatedPredicatesKeepDistinctIds

end Tests.SourceRequirementIdentity
end

section
-- leanmerge: from Solcore.Test.SourceTypedIRInference
/-!
End-to-end coverage for the occurrence-addressed typed source produced by
source inference.  The fixture deliberately combines lexical shadowing,
generic overload selection, rejected overload candidates, a two-edge coercion
path, an operator obligation, and an explicit builtin-Int literal carrier.
-/

set_option autoImplicit false

namespace Tests.SourceTypedIRInference

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private structure Fixture where
  environment : ProgramEnvironment
  checked : List CheckedFunction

private def check (content : String) : IO Fixture := do
  match loadProgram (workspace content) with
  | .error errors =>
      throw (IO.userError s!"typed IR loading failed: {reprStr errors}")
  | .ok loaded =>
      match SourceInference.checkLoadedProgram loaded with
      | .error errors =>
          throw (IO.userError s!"typed IR checking failed: {reprStr errors}")
      | .ok checked => pure { environment := loaded.environment, checked }

private def checkedNamed (fixture : Fixture) (name : String) :
    IO CheckedFunction :=
  match fixture.checked.find? fun function =>
      match fixture.environment.declaration? function.declaration with
      | some declaration => declaration.name == some name
      | none => false with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def namedType (environment : ProgramEnvironment) (name : String) :
    IO TypeSystem.Ty :=
  match environment.typesNamed name with
  | [declaration] => pure (.nominal declaration.id)
  | declarations =>
      throw (IO.userError
        s!"expected one type `{name}`, found {declarations.length}")

private def namedTrait (environment : ProgramEnvironment) (name : String) :
    IO Resolved.DeclarationId :=
  match environment.traitsNamed name with
  | [declaration] => pure declaration.id
  | declarations =>
      throw (IO.userError
        s!"expected one trait `{name}`, found {declarations.length}")

private def namedFunctionWhere (environment : ProgramEnvironment) (name : String)
    (accept : ProgramDeclaration → Bool) : IO Resolved.DeclarationId :=
  match (environment.valuesNamed name).filter accept with
  | [declaration] => pure declaration.id
  | declarations =>
      throw (IO.userError
        s!"expected one selected declaration `{name}`, found {declarations.length}")

private def predicate (trait : Resolved.DeclarationId) (subject : TypeSystem.Ty)
    (arguments : List TypeSystem.Ty := []) : ProgramPredicate := {
  trait
  subject
  arguments
}

private def expressionNodes (source : TypedSource) : List ExpressionNode :=
  source.nodes.filterMap fun
    | .expression node => some node
    | .statement _ => none

private def statementNodes (source : TypedSource) : List StatementNode :=
  source.nodes.filterMap fun
    | .expression _ => none
    | .statement node => some node

private def rootResolves (source : TypedSource) : NodeId → Bool
  | .expression id =>
      match source.lookupExpression? id with
      | some node => node.id == id
      | none => false
  | .statement id =>
      match source.lookupStatement? id with
      | some node => node.id == id
      | none => false

private def findSolved (function : CheckedFunction)
    (goal : ProgramPredicate) : IO SolvedRequirement :=
  match function.solvedRequirements.filter fun solved => solved.predicate == goal with
  | [solved] => pure solved
  | solved =>
      throw (IO.userError
        s!"expected one solved requirement for {reprStr goal}, found {solved.length}")

private def findCall (source : TypedSource)
    (declaration : Resolved.DeclarationId) : IO ExpressionNode :=
  match (expressionNodes source).filter fun node =>
      match node.form with
      | .call _ _ (.declaration instantiation) =>
          instantiation.declaration == declaration
      | _ => false with
  | [node] => pure node
  | nodes =>
      throw (IO.userError
        s!"expected one call of declaration {reprStr declaration}, found {nodes.length}")

private def testIdentityAndLookup (function : CheckedFunction) : IO Unit := do
  let source := function.typedBody
  let occurrences := source.nodes.map Node.occurrenceId
  let rootOccurrences := source.roots.map NodeId.occurrenceId
  assertTrue (decide (source.owner = function.declaration))
    "typed body owner differs from its checked declaration"
  assertTrue (!source.roots.isEmpty && source.roots.all (rootResolves source))
    "a typed body root does not resolve through its category-safe lookup"
  assertTrue (occurrences.length == occurrences.eraseDups.length)
    "typed source reused an occurrence identity"
  assertTrue (rootOccurrences.length == rootOccurrences.eraseDups.length)
    "typed source repeated a root identity"
  assertTrue (source.nodes.all fun node =>
      decide (node.occurrenceId.owner = source.owner))
    "a typed source node belongs to a different declaration"
  assertTrue (source.roots.all fun root =>
      decide (root.occurrenceId.owner = source.owner))
    "a typed source root belongs to a different declaration"
  assertTrue (source.nodes.all fun node =>
      match node with
      | .expression expression =>
          decide (source.lookupExpression? expression.id = some expression)
      | .statement statement =>
          decide (source.lookupStatement? statement.id = some statement))
    "a typed source node could not be recovered by its stable ID"

private def shadowedBinder (source : TypedSource) (input : TypedBinder) :
    IO TypedBinder := do
  match (statementNodes source).filterMap fun node =>
      match node.form with
      | .letDecl binder (some initializer) =>
          if binder.name == "item" then some (binder, initializer) else none
      | _ => none with
  | [(binder, initializer)] =>
      assertTrue (binder.id != input.id)
        "shadowing reused the input binder identity"
      match source.lookupExpression? initializer with
      | some { form := .reference "item" (.local resolved), .. } =>
          assertTrue (resolved == input.id)
            "the shadowing initializer did not resolve to the outer input"
      | _ => throw (IO.userError
          "the shadowing initializer lost its typed local reference")
      pure binder
  | bindings => throw (IO.userError
      s!"expected one shadowing item binding, found {bindings.length}")

private def testTypedInferenceFacts (fixture : Fixture)
    (run : CheckedFunction) : IO Unit := do
  let source := run.typedBody
  let word := TypeSystem.Ty.word
  let mid ← namedType fixture.environment "Mid"
  let box ← namedType fixture.environment "Box"
  let ready ← namedTrait fixture.environment "Ready"
  let coerce ← namedTrait fixture.environment "Coerce"
  let addition ← namedTrait fixture.environment "Add"
  let integer := ProgramSignatures.builtinIntPredicate word
  let genericChoose ← namedFunctionWhere fixture.environment "choose" fun declaration =>
    !declaration.genericParameters.isEmpty
  let accept ← namedFunctionWhere fixture.environment "accept" fun _ => true
  let input ← match source.inputs.find? fun binder => binder.name == "item" with
    | some input => pure input
    | none => throw (IO.userError "run lost its item input binder")
  let boxInput ← match source.inputs.find? fun binder => binder.name == "box" with
    | some input => pure input
    | none => throw (IO.userError "run lost its box input binder")
  assertTrue (source.inputs.length == 2 &&
      decide (input.scheme = .mono word) &&
      decide (boxInput.scheme = .mono box))
    "run's input binder lost its name or type"
  let inner ← shadowedBinder source input

  match source.roots with
  | [.statement blockId, .statement useOuterId, .statement returnId] =>
      match source.lookupStatement? blockId,
          source.lookupStatement? useOuterId,
          source.lookupStatement? returnId with
      | some { form := .block nested, .. },
          some { form := .expression outerReference true, .. },
          some { form := .returnStmt (some _), .. } =>
          assertTrue (nested.length == 4 && nested.all fun id =>
              !(source.roots.contains (.statement id)))
            "nested block statements leaked into the top-level root list"
          match source.lookupExpression? outerReference with
          | some { form := .reference "item" (.local binder), .. } =>
              assertTrue (binder == input.id)
                "block scope restoration did not recover the outer item binder"
          | _ => throw (IO.userError
              "post-block item use lost its typed outer reference")
      | _, _, _ => throw (IO.userError
          "typed statement roots lost block/expression/return source order")
  | roots => throw (IO.userError
      s!"expected three ordered top-level statement roots, found {roots.length}")

  let integerSolved ← findSolved run integer
  let readySolved ← findSolved run (predicate ready word)
  let firstCoercion ← findSolved run (predicate coerce word [mid])
  let secondCoercion ← findSolved run (predicate coerce mid [box])
  let addSolved ← findSolved run (predicate addition box)
  assertTrue (decide (run.predicates = [
      integer,
      predicate ready word,
      predicate coerce word [mid],
      predicate coerce mid [box],
      predicate addition box
    ]))
    "speculative overload requirements leaked or committed requirements reordered"

  let chooseCall ← findCall source genericChoose
  match chooseCall.form with
  | .call callee [argument] (.declaration selected) =>
      assertTrue (decide (selected.declaration = genericChoose ∧
          selected.parameterSubstitution =
            [(⟨genericChoose, 0⟩, word)] ∧
          selected.type = .function word .bool ∧
          selected.predicates = [predicate ready word] ∧
          chooseCall.requirements = [readySolved.id] ∧
          chooseCall.coercions = []))
        "generic overload selection lost its closed instantiation or requirement"
      match source.lookupExpression? callee with
      | some { form := .reference "choose" (.declaration reference), .. } =>
          assertTrue (decide (reference = selected))
            "the semantic choose reference disagrees with its call resolution"
      | _ => throw (IO.userError
          "the chosen overload has no matching semantic callee reference")
      match source.lookupExpression? argument with
      | some { form := .reference "item" (.local binder), requirements, coercions, .. } =>
          assertTrue (binder == inner.id && requirements.isEmpty && coercions.isEmpty)
            "a rejected choose overload leaked coercions or requirements"
      | _ => throw (IO.userError
          "the chosen generic argument lost its shadowed local resolution")
  | _ => throw (IO.userError "the chosen generic call changed shape")

  let acceptCall ← findCall source accept
  match acceptCall.form with
  | .call _ [argument] (.declaration selected) =>
      assertTrue (selected.declaration == accept)
        "accept call retained the wrong declaration"
      match source.lookupExpression? argument with
      | some node =>
          match node.form with
          | .reference "item" (.local binder) =>
              assertTrue (decide (binder = inner.id ∧
                  node.rawType = word ∧ node.type = box ∧
                  node.hasValidCoercionPath ∧
                  node.requirements = [firstCoercion.id, secondCoercion.id] ∧
                  node.coercions = [
                    { requirement := firstCoercion.id, source := word, target := mid },
                    { requirement := secondCoercion.id, source := mid, target := box }
                  ]))
                "accept argument lost its exact Word -> Mid -> Box coercion path"
          | _ => throw (IO.userError
              "accept argument lost its shadowed local resolution")
      | none => throw (IO.userError "accept argument is absent from typed source")
  | _ => throw (IO.userError "accept call changed shape")

  match (expressionNodes source).filter fun node =>
      match node.form with
      | .binary _ .add _ => true
      | _ => false with
  | [node] =>
      assertTrue (decide (node.type = box ∧
          node.requirements = [addSolved.id]))
        "Box addition lost its Add<Box> requirement"
  | nodes => throw (IO.userError
      s!"expected one addition node, found {nodes.length}")

  match (expressionNodes source).filter fun node =>
      node.requirements.contains integerSolved.id with
  | [{ form := .integerLiteral (.decimal "1") resolution,
        type, requirements, .. }] =>
      assertTrue (decide (type = word ∧
          resolution.rawValue = 1 ∧
          resolution.targetType = word ∧
          resolution.requirement = integerSolved.id ∧
          resolution.predicate = integer ∧
          requirements = [integerSolved.id]))
        "the Word literal lost its exact builtin Int carrier"
  | nodes => throw (IO.userError
      s!"expected one Int<Word> literal owner, found {nodes.length}")

  let attached := source.primaryRequirementIds
  let solvedIds := run.solvedRequirements.map (·.id)
  assertTrue (attached.length == attached.eraseDups.length)
    "one requirement identity is owned by multiple primary source nodes"
  assertTrue (decide (attached.length = solvedIds.length) &&
      attached.all solvedIds.contains && solvedIds.all attached.contains)
    "typed expression requirement ownership and solved requirements diverged"

private def testIndirectArgumentBundleCoercion : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function apply(f: function(Box) returns (Word), value: Word) returns (Word) {",
    "  return f(value);",
    "}"
  ])
  let apply ← checkedNamed fixture "apply"
  let box ← namedType fixture.environment "Box"
  let coerce ← namedTrait fixture.environment "Coerce"
  let solved ← findSolved apply (predicate coerce .word [box])
  match (expressionNodes apply.typedBody).filter fun node =>
      match node.form with
      | .call _ _ (.indirect _) => true
      | _ => false with
  | [{ type, form := .call _ [_] (.indirect metadata), requirements,
        coercions, .. }] =>
      assertTrue (decide (type = .word ∧ requirements = [solved.id] ∧
          coercions = [] ∧
          metadata.argumentTypeBeforeCoercion = .word ∧
          metadata.argumentTypeAfterCoercion = box ∧
          metadata.argumentCoercions = [{
            requirement := solved.id
            source := .word
            target := box
          }] ∧ metadata.hasValidArgumentCoercionPath))
        "an indirect argument-bundle coercion leaked into the call output path"
  | calls => throw (IO.userError
      s!"expected one indirect call with bundle metadata, found {calls.length}")

/-- Check that the real source-inference traversal produces a complete,
occurrence-addressed semantic carrier without leaking speculative candidates. -/
def testSourceTypedIRInference : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Ready<T> {}",
    "trait Coerce<From, To> {}",
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "enum Mid { Only }",
    "enum Box { Only }",
    "enum Flag { Only }",
    "impl Ready<Word> {}",
    "impl Coerce<Word, Mid> {}",
    "impl Coerce<Mid, Box> {}",
    "impl Add<Box> {",
    "  function add(left: Box, right: Box) returns (Box) { return left; }",
    "}",
    "function choose(value: Box) returns (Bool) { return true; }",
    "function choose(value: Flag) returns (Bool) { return true; }",
    "function choose<T>(value: T) returns (Bool) where T: Ready {",
    "  return true;",
    "}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function run(item: Word, box: Box) returns (Box) {",
    "  {",
    "    let item = item;",
    "    let one: Word = 1;",
    "    choose(item);",
    "    accept(item);",
    "  }",
    "  item;",
    "  return box + box;",
    "}"
  ])
  let run ← checkedNamed fixture "run"
  testIdentityAndLookup run
  testTypedInferenceFacts fixture run
  testIndirectArgumentBundleCoercion

end Tests.SourceTypedIRInference
end
