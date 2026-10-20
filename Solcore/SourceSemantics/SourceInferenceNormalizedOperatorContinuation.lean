import Solcore.SourceSemantics.SourceInferenceNormalizedRecordingContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedOperatorIssuance

/-! Actual operator outputs are either closed builtin types or the actual
resolved operand. Their predicates use the same final substitution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceRequirementFormation

set_option maxHeartbeats 800000 in
private theorem unary_result_shape
    {context : SourceInference.Context} {operator : Syntax.UnaryOp}
    {operand : Ty} {expected : Option Ty} {literals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : inferUnaryOperator context operator operand expected literals state = .ok result) :
    result.type = .bool ∨ result.type = .word ∨ result.type = result.state.resolve operand := by
  unfold inferUnaryOperator at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals simp_all [State.resolve]
  all_goals cases operator <;> simp_all

set_option maxHeartbeats 800000 in
private theorem binary_result_shape
    {context : SourceInference.Context} {operator : Syntax.BinaryOp}
    {left right : Ty} {expected : Option Ty} {literals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : inferBinaryOperator context operator left right expected literals state = .ok result) :
    result.type = .bool ∨ result.type = .word ∨ result.type = result.state.resolve left := by
  unfold inferBinaryOperator at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals simp_all [State.resolve]
  all_goals cases operator <;> simp_all [binaryBuiltinType]

theorem inferUnaryOperator_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {operator : Syntax.UnaryOp}
    {operand : Ty} {expected : Option Ty} {literals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (operandFormed : TypeAdmissible semantic (outer.apply operand))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferUnaryOperator context operator operand expected literals state = .ok result) :
    TypeAdmissible semantic (outer.apply result.type) ∧
      NormalizedStateFormation semantic outer result.state := by
  refine ⟨?_, formed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_inferUnaryOperator_lexicalScope accepted))
    (inferUnaryOperator_normalized_issuance formation.catalog formation.signatures operandFormed continuation accepted)⟩
  rcases unary_result_shape accepted with closed | closed | resolved
  · rw [closed]; exact .bool formation.scope.binders
  · rw [closed]; exact .word formation.scope.binders
  · rw [resolved]
    exact (continuation operand).symm ▸ operandFormed

theorem inferBinaryOperator_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {operator : Syntax.BinaryOp}
    {left right : Ty} {expected : Option Ty} {literals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (leftFormed : TypeAdmissible semantic (outer.apply left))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferBinaryOperator context operator left right expected literals state = .ok result) :
    TypeAdmissible semantic (outer.apply result.type) ∧
      NormalizedStateFormation semantic outer result.state := by
  refine ⟨?_, formed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_inferBinaryOperator_lexicalScope accepted))
    (inferBinaryOperator_normalized_issuance formation.catalog formation.signatures leftFormed continuation accepted)⟩
  rcases binary_result_shape accepted with closed | closed | resolved
  · rw [closed]; exact .bool formation.scope.binders
  · rw [closed]; exact .word formation.scope.binders
  · rw [resolved]
    exact (continuation left).symm ▸ leftFormed

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
