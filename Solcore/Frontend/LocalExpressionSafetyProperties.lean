import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Core.Safety

/-! Direct source-level existence and type/store preservation for the local
Boolean/Word-complement/conditional fragment. Identity order and positional environment typing
remain explicit; no closedness or general resolved-evaluation existence theorem is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- An independently typed source expression evaluates in a matching typed
environment, returning a value of its assigned type and the unchanged store. -/
theorem LocalExpressionHasType.evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) :
    ∃ value, LocalExpressionEvaluates table environment store source value store ∧
      Core.ValueHasType value type := by
  induction typing with
  | identifier named found =>
      obtain ⟨index, indexed, atType⟩ := found.indexed
      obtain ⟨value, atValue, valueTyped⟩ := environmentTyped.lookup atType
      have envIndex := sameIds ▸ indexed
      exact ⟨value, .identifier named
        (Resolved.LocalScope.lookup_of_indexed envIndex atValue), valueTyped⟩
  | group _ ih =>
      obtain ⟨value, evaluation, valueTyped⟩ := ih
      exact ⟨value, .group evaluation, valueTyped⟩
  | logicalNot _ ih =>
      obtain ⟨value, evaluation, valueTyped⟩ := ih
      obtain ⟨decision, rfl⟩ := valueTyped.bool_shape
      exact ⟨.bool (!decision), .logicalNot evaluation, .bool⟩
  | bitNot _ ih =>
      obtain ⟨value, evaluation, valueTyped⟩ := ih
      cases valueTyped with
      | word => exact ⟨_, .bitNot evaluation, .word⟩
  | logicalAnd _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨decision, rfl⟩ := leftTyped.bool_shape
      cases decision with
      | false => exact ⟨.bool false, .andFalse leftEvaluation, .bool⟩
      | true =>
          obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
          exact ⟨rightValue, .andTrue leftEvaluation rightEvaluation, rightTyped⟩
  | logicalOr _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨decision, rfl⟩ := leftTyped.bool_shape
      cases decision with
      | false =>
          obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
          exact ⟨rightValue, .orFalse leftEvaluation rightEvaluation, rightTyped⟩
      | true => exact ⟨.bool true, .orTrue leftEvaluation, .bool⟩
  | conditional _ _ _ conditionIH thenIH elseIH =>
      obtain ⟨conditionValue, conditionEvaluation, conditionTyped⟩ := conditionIH
      obtain ⟨decision, rfl⟩ := conditionTyped.bool_shape
      cases decision with
      | false =>
          obtain ⟨value, evaluation, valueTyped⟩ := elseIH
          exact ⟨value, .ifFalse conditionEvaluation evaluation, valueTyped⟩
      | true =>
          obtain ⟨value, evaluation, valueTyped⟩ := thenIH
          exact ⟨value, .ifTrue conditionEvaluation evaluation, valueTyped⟩

/-- Every independent evaluation agrees with the typed result and exact store
endpoint, including open expressions and repeated caller-supplied identities. -/
theorem LocalExpressionEvaluates.preserves_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty} {value : Core.Value}
    {initialStore finalStore : Core.Store}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore)
    (typing : LocalExpressionHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, valueTyped⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, storeEq⟩ := evaluation.deterministic evaluated
  exact ⟨valueTyped, storeEq⟩

end Solcore.Frontend
