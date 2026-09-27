import Solcore.Frontend.SourceInference

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
