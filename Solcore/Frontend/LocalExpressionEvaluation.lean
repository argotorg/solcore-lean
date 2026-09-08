import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Resolved.EvaluationProperties

/-! Independent canonical evaluation for the local conditional/negation fragment.
Evaluation requires only the selected branch, not whole-expression resolution.
Both stores are explicit even though every constructor is store-preserving. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalExpressionEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop where
  | identifier {store : Core.Store} {span : Syntax.SourceSpan} {name : Syntax.Identifier}
      {id : Resolved.LocalId} {value : Core.Value}
      (named : LocalNameTable.Lookup table name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      LocalExpressionEvaluates table environment store
        { span, value := .identifier name } value store
  | group {initialStore finalStore : Core.Store} {span : Syntax.SourceSpan}
      {inner : Syntax.Expr} {value : Core.Value}
      (child : LocalExpressionEvaluates table environment initialStore inner value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .group inner } value finalStore
  | logicalNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Bool}
      (child : LocalExpressionEvaluates table environment initialStore operand (.bool value) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand } (.bool (!value)) finalStore
  | ifTrue {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment initialStore
        condition (.bool true) middleStore)
      (branchEvaluation : LocalExpressionEvaluates table environment middleStore
        thenBranch value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .conditional condition question thenBranch colon elseBranch } value finalStore
  | ifFalse {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment initialStore
        condition (.bool false) middleStore)
      (branchEvaluation : LocalExpressionEvaluates table environment middleStore
        elseBranch value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .conditional condition question thenBranch colon elseBranch } value finalStore

theorem LocalExpressionEvaluates.store_eq {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore) :
    finalStore = initialStore := by
  induction evaluation with
  | identifier => rfl
  | group _ ih | logicalNot _ ih => exact ih
  | ifTrue _ _ conditionIH branchIH | ifFalse _ _ conditionIH branchIH =>
      exact branchIH.trans conditionIH

/-- No whole-resolution or typing premise is needed for source determinism. -/
theorem LocalExpressionEvaluates.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (leftEvaluation : LocalExpressionEvaluates table environment initialStore source left leftStore)
    (rightEvaluation : LocalExpressionEvaluates table environment initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction leftEvaluation generalizing right rightStore with
  | identifier named found =>
      cases rightEvaluation with
      | identifier otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound, rfl⟩
  | group _ ih =>
      cases rightEvaluation with
      | group child => exact ih child
  | logicalNot _ ih =>
      cases rightEvaluation with
      | logicalNot child =>
          obtain ⟨same, storeEq⟩ := ih child
          cases same
          exact ⟨rfl, storeEq⟩
  | ifTrue _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue condition branch =>
          obtain ⟨_, rfl⟩ := conditionIH condition
          exact branchIH branch
      | ifFalse condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible
  | ifFalse _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifFalse condition branch =>
          obtain ⟨_, rfl⟩ := conditionIH condition
          exact branchIH branch
      | ifTrue condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible

end Solcore.Frontend
