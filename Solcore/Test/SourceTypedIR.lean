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
private def methodRequirement0 : RequirementId := ⟨5⟩
private def methodRequirement1 : RequirementId := ⟨6⟩
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
  type := variable1
  form := .reference "chosen" (.declaration instantiation)
  requirements := [requirementId, methodRequirement0, methodRequirement1]
  coercions := [{
    requirement := requirementId
    methodRequirements := [methodRequirement0, methodRequirement1]
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
      assertTrue (decide (node.rawType = .word ∧ node.type = .bool ∧
          node.hasValidCoercionPath ∧
          node.requirements =
            [requirementId, methodRequirement0, methodRequirement1] ∧
          node.coercions = [{
            requirement := requirementId
            methodRequirements := [methodRequirement0, methodRequirement1]
            source := .word
            target := .bool
          }]))
        "typed expression type/coercion closure changed"
      match node.coercions with
      | [step] =>
          assertTrue (decide (step.requirements =
              [requirementId, methodRequirement0, methodRequirement1]))
            "coercion obligations lost primary-first declaration order"
      | _ => throw (IO.userError "typed coercion path changed shape")
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
  let indirect := CallResolution.indirect {
    argumentTypeBeforeCoercion := variable0
    argumentTypeAfterCoercion := variable1
    argumentCoercions := [{
      requirement := requirementId
      methodRequirements := [methodRequirement0, methodRequirement1]
      source := variable0
      target := variable1
    }]
  }
  match indirect.applySubstitution substitution with
  | .indirect metadata =>
      assertTrue (decide (metadata.argumentTypeBeforeCoercion = .word ∧
          metadata.argumentTypeAfterCoercion = .bool ∧
          metadata.argumentCoercions = [{
            requirement := requirementId
            methodRequirements := [methodRequirement0, methodRequirement1]
            source := .word
            target := .bool
          }] ∧ metadata.hasValidArgumentCoercionPath))
        "final substitution did not close indirect argument coercion metadata"
  | .declaration _ => throw (IO.userError
      "final substitution changed an indirect call into a declaration call")

private def testCoercionPathValidation : IO Unit := do
  let secondRequirement : RequirementId := ⟨5⟩
  let disconnected : ExpressionNode := {
    expression with
    type := .unit
    coercions := [
      { requirement := requirementId, source := .word, target := .bool },
      { requirement := secondRequirement, source := .word, target := .unit }
    ]
  }
  assertTrue (!disconnected.hasValidCoercionPath)
    "a disconnected expression coercion path was accepted"
  let wrongTarget : ExpressionNode := {
    expression with
    type := .unit
    coercions := [{
      requirement := requirementId
      source := .word
      target := .bool
    }]
  }
  assertTrue (!wrongTarget.hasValidCoercionPath)
    "an expression coercion path ending before node.type was accepted"
  let exact : ExpressionNode := {
    expression with
    type := .unit
    coercions := []
  }
  assertTrue (decide (exact.rawType = .unit ∧ exact.hasValidCoercionPath))
    "an uncoerced expression did not use its stored type as its raw type"

private def testIntegerLiteralFlexibleSubstitution : IO Unit := do
  let resolution : IntegerLiteralResolution := {
    rawValue := 42
    targetType := variable0
    requirement := requirementId
  }
  let substitution : TypeSystem.Substitution := [(⟨0⟩, .word)]
  match (ExpressionForm.integerLiteral (.decimal "42") resolution)
      |>.applySubstitution substitution with
  | .integerLiteral source closed =>
      assertTrue (decide (source = .decimal "42" ∧
          closed.rawValue = 42 ∧
          closed.targetType = .word ∧
          closed.requirement = requirementId ∧
          closed.predicate = ProgramSignatures.builtinIntPredicate .word))
        "flexible substitution changed integer literal provenance or missed its target"
  | _ => throw (IO.userError
      "flexible substitution changed the integer-literal expression form")

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
  testCoercionPathValidation
  testIntegerLiteralFlexibleSubstitution
  testInferenceStateScaffolding

end Tests.SourceTypedIR
