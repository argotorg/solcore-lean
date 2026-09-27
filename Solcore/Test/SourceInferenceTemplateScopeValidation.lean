import Solcore.Frontend.SourceInference

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
