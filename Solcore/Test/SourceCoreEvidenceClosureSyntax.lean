import Solcore.Test.SourceCoreEvidenceClosureMetadata
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original


section Factory
variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {firstParameter secondParameter : TypeSystem.TypeParameterId} {firstType secondType : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait)

theorem FactoryShape.body_shape :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.typedBody true [shape.statement.id] :=
  .returnValue [] shape.statementFound shape.statementForm

theorem FactoryShape.body_syntax
    (unique : NodeOccurrencesUnique function.typedBody)
    {approved : ExpressionId → Prop} (leaf : approved shape.call.value.node.id)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType function.typedBody {returnType := firstType} context
      [shape.statement.id] final facts) :
    GenericImperativeMatch.Syntax function.typedBody approved context
      (.statements true [shape.statement.id]) firstType := by
  obtain ⟨_, _, _, returned, _⟩ := head_tail typed
  have original := form_at unique shape.statementFound returned
  rw [shape.statementForm] at original
  cases original with
  | returnValue expression =>
    exact .body (.returnValue [] shape.statementFound shape.statementForm
      shape.statementType shape.call.value.found shape.call.value.type
      (by simpa only [shape.call.value.type] using expression) leaf)
end Factory
end Tests.SourceCoreEvidenceClosure
