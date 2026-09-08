import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.WordLiteralProperties
import Solcore.Resolved.EvaluationProperties

/-! Independent canonical evaluation for the local conditional/operator fragment.
Evaluation requires only the selected branch, not whole-expression resolution.
Short-circuit forms forward any selected right value at this raw boundary;
source typing separately requires both operands to be Boolean. Word arithmetic,
bitwise operations, unsigned comparisons, and Word equality/inequality evaluate both operands left to right.
Both stores are explicit even though every constructor is store-preserving. Strict Word literals
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
  | add {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .add⟩ right }
        (.word (leftValue.add rightValue)) finalStore
  | subtract {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .subtract⟩ right }
        (.word (leftValue.sub rightValue)) finalStore
  | multiply {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .multiply⟩ right }
        (.word (leftValue.mul rightValue)) finalStore
  | bitAnd {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right }
        (.word (leftValue.bitAnd rightValue)) finalStore
  | bitOr {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right }
        (.word (leftValue.bitOr rightValue)) finalStore
  | bitXor {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right }
        (.word (leftValue.bitXor rightValue)) finalStore
  | greater {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .greater⟩ right }
        (.bool (decide (leftValue > rightValue))) finalStore
  | less {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .less⟩ right }
        (.bool (decide (leftValue < rightValue))) finalStore
  | equal {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .equal⟩ right }
        (.bool (leftValue == rightValue)) finalStore
  | notEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right }
        (.bool (!(leftValue == rightValue))) finalStore
  | lessEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .lessEqual⟩ right }
        (.bool (!(decide (leftValue > rightValue)))) finalStore
  | greaterEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .greaterEqual⟩ right }
        (.bool (!(decide (leftValue < rightValue)))) finalStore
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
  | add _ _ leftIH rightIH | bitAnd _ _ leftIH rightIH | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH
  | subtract _ _ leftIH rightIH | multiply _ _ leftIH rightIH | greater _ _ leftIH rightIH
  | less _ _ leftIH rightIH
  | equal _ _ leftIH rightIH
  | notEqual _ _ leftIH rightIH
  | lessEqual _ _ leftIH rightIH
  | greaterEqual _ _ leftIH rightIH
  | andTrue _ _ leftIH rightIH | orFalse _ _ leftIH rightIH =>
      exact rightIH.trans leftIH

end Solcore.Frontend
