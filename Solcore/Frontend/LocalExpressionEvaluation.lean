import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.WordLiteralProperties
import Solcore.Resolved.EvaluationProperties

/-! Independent canonical evaluation for the local conditional/operator fragment.
Evaluation requires only the selected branch, not whole-expression resolution.
Short-circuit forms forward any selected right value at this raw boundary;
source typing separately requires both operands to be Boolean. Both stores are
explicit even though every constructor is store-preserving. Strict Word literals
return their independently denoted value without consulting caller tables. -/

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
  | wordLiteral {store : Core.Store} {span : Syntax.SourceSpan}
      {literal : Syntax.CoreLiteral} {word : Core.Word}
      (meaning : WordLiteralDenotes literal word) :
      LocalExpressionEvaluates table environment store
        { span, value := .literal literal } (.word word) store
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
  | bitNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Core.Word}
      (child : LocalExpressionEvaluates table environment initialStore operand (.word value) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand } (.word value.bitNot) finalStore
  | andTrue {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.bool true) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right } value finalStore
  | andFalse {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.bool false) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right } (.bool false) finalStore
  | orTrue {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.bool true) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right } (.bool true) finalStore
  | orFalse {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.bool false) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right } value finalStore
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
  | wordLiteral => rfl
  | group _ ih | logicalNot _ ih | bitNot _ ih | andFalse _ ih | orTrue _ ih => exact ih
  | ifTrue _ _ conditionIH branchIH | ifFalse _ _ conditionIH branchIH =>
      exact branchIH.trans conditionIH
  | andTrue _ _ leftIH rightIH | orFalse _ _ leftIH rightIH =>
      exact rightIH.trans leftIH

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
  | wordLiteral meaning =>
      cases rightEvaluation with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact ⟨rfl, rfl⟩
  | group _ ih =>
      cases rightEvaluation with
      | group child => exact ih child
  | logicalNot _ ih =>
      cases rightEvaluation with
      | logicalNot child =>
          obtain ⟨same, storeEq⟩ := ih child
          cases same
          exact ⟨rfl, storeEq⟩
  | bitNot _ ih =>
      cases rightEvaluation with
      | bitNot child =>
          obtain ⟨same, storeEq⟩ := ih child
          cases same
          exact ⟨rfl, storeEq⟩
  | andTrue _ _ leftIH rightIH =>
      cases rightEvaluation with
      | andTrue leftChild rightChild =>
          obtain ⟨_, rfl⟩ := leftIH leftChild
          exact rightIH rightChild
      | andFalse leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | andFalse _ leftIH =>
      cases rightEvaluation with
      | andFalse leftChild => exact leftIH leftChild
      | andTrue leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orTrue _ leftIH =>
      cases rightEvaluation with
      | orTrue leftChild => exact leftIH leftChild
      | orFalse leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orFalse _ _ leftIH rightIH =>
      cases rightEvaluation with
      | orFalse leftChild rightChild =>
          obtain ⟨_, rfl⟩ := leftIH leftChild
          exact rightIH rightChild
      | orTrue leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
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
