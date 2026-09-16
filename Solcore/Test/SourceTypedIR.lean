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

def testSourceTypedIR : IO Unit := do
  testFinalSubstitutionPreservesIdentity

end Tests.SourceTypedIR
