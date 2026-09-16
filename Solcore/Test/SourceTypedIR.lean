import Solcore.Frontend.SourceInference.Types
import Solcore.Frontend.SourceInference.TypedIRProperties

/-! Executable coverage for the additive occurrence-addressed typed IR carrier. -/

set_option autoImplicit false

namespace Tests.SourceTypedIR

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_typed_ir", by decide⟩], by decide⟩⟩

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨ownerModule, index⟩

private def owner := declaration 0
private def trait := declaration 1

private def sourceId : Syntax.SourceId := {
  origin := .main
  path := "source_typed_ir.solc"
}

private def span : Syntax.SourceSpan := {
  source := sourceId
  startByte := 0
  endByte := 1
}

private def expressionId : ExpressionId :=
  ⟨⟨owner, 0⟩⟩

private def requirementId : RequirementId := ⟨4⟩
private def variable0 : TypeSystem.Ty := .variable ⟨0⟩
private def variable1 : TypeSystem.Ty := .variable ⟨1⟩

private def instantiation : DeclarationInstantiation := {
  declaration := declaration 2
  parameterSubstitution := [(⟨declaration 2, 0⟩, variable0)]
  type := variable0
  predicates := [{ trait, subject := variable0, arguments := [] }]
}

private def expression : ExpressionNode := {
  id := expressionId
  span
  type := variable0
  form := .reference "chosen" (.declaration instantiation)
  requirements := [requirementId]
  coercions := [{
    requirement := requirementId
    source := variable0
    target := variable1
  }]
}

private def source : TypedSource := {
  owner
  inputs := [{
    id := { owner, binderIndex := 0 }
    name := "input"
    scheme := { quantified := [⟨0⟩], body := .product variable0 variable1 }
    span := some span
  }]
  roots := [.expression expressionId]
  nodes := [.expression expression]
}

private def testFinalSubstitutionPreservesIdentity : IO Unit := do
  let substitution : TypeSystem.Substitution :=
    [(⟨0⟩, .word), (⟨1⟩, .bool)]
  let closed := source.applySubstitution substitution
  assertTrue (decide (closed.owner = owner ∧ closed.roots = source.roots ∧
      closed.nodes.map Node.id = source.nodes.map Node.id))
    "final substitution changed typed-source identities"
  match closed.inputs with
  | [input] =>
      assertTrue (decide (input.scheme.body = .product variable0 .bool))
        "final substitution entered a quantified binder or missed a free type"
  | _ => throw (IO.userError "typed-source inputs changed shape")
  match closed.lookupExpression? expressionId with
  | none => throw (IO.userError "typed expression lookup lost its node")
  | some node =>
      assertTrue (decide (node.type = .word ∧
          node.requirements = [requirementId] ∧
          node.coercions = [{
            requirement := requirementId
            source := .word
            target := .bool
          }]))
        "typed expression type/coercion closure changed"
      match node.form with
      | .reference "chosen" (.declaration selected) =>
          assertTrue (decide (selected.type = .word ∧
              selected.parameterSubstitution =
                [(⟨declaration 2, 0⟩, .word)] ∧
              selected.predicates = [{
                trait, subject := .word, arguments := []
              }]))
            "selected declaration instantiation was not closed consistently"
      | _ => throw (IO.userError "typed reference resolution changed shape")
  assertTrue (decide (closed.lookupStatement? ⟨⟨owner, 0⟩⟩ = none))
    "category-safe lookup reinterpreted an expression as a statement"

private def testInferenceStateScaffolding : IO Unit := do
  let locals : TypeSystem.Environment :=
    [("first", .mono .word), ("second", .mono .bool)]
  let initial := State.initial owner locals
  let outer := initial.lexicalScope
  assertTrue (decide (initial.owner = owner ∧ initial.nextLocal = 2 ∧
      initial.inputs.map (·.id) = [⟨owner, 0⟩, ⟨owner, 1⟩] ∧
      initial.localBinders = initial.inputs))
    "initial inference binders were not assigned stable declaration-local IDs"
  let (nested, state) := initial.allocateBinder "first" (.mono .word) (some span)
  let (expressionId, state) := state.allocateExpressionId
  let (statementId, state) := state.allocateStatementId
  assertTrue (decide (nested.id = ⟨owner, 2⟩ ∧
      state.lookupBinder? "first" = some nested ∧
      expressionId.occurrence = ⟨owner, 0⟩ ∧
      statementId.occurrence = ⟨owner, 1⟩))
    "inference-state allocators did not use independent stable ID streams"
  let expressionNode : ExpressionNode := {
    id := expressionId
    span
    type := .word
    form := .proxy .word
  }
  let statementNode : StatementNode := {
    id := statementId
    span
    type := .word
    form := .expression expressionId false
  }
  let state := state.recordNode (.expression expressionNode)
    |>.recordNode (.statement statementNode)
    |>.modifyExpressionNode expressionId fun node => {
        node with
        id := ⟨⟨owner, 99⟩⟩
        type := .bool
      }
  let state := state.restoreLexicalScope outer
  let typed := state.toTypedSource
    [.expression expressionId, .statement statementId]
  assertTrue (decide (state.locals = locals ∧
      state.localBinders = initial.localBinders ∧
      state.lookupBinder? "first" = initial.inputs.head? ∧
      state.nextLocal = 3 ∧ state.nextOccurrence = 2 ∧
      typed.owner = owner ∧ typed.inputs = initial.inputs ∧
      typed.nodes.length = 2))
    "lexical restoration rewound semantic state or changed typed inputs"
  match typed.lookupExpression? expressionId with
  | some node =>
      assertTrue (decide (node.id = expressionId ∧ node.type = .bool))
        "typed-node modification changed its stable identity"
  | none => throw (IO.userError "recorded expression was absent from typed source")
  match typed.lookupStatement? statementId with
  | some node =>
      assertTrue (decide (node.id = statementId ∧
          node.form = .expression expressionId false))
        "recorded statement changed while modifying an expression"
  | none => throw (IO.userError "recorded statement was absent from typed source")

def testSourceTypedIR : IO Unit := do
  testFinalSubstitutionPreservesIdentity
  testInferenceStateScaffolding

end Tests.SourceTypedIR
