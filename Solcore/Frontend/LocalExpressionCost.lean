import Solcore.Frontend.LocalExpressionEvaluation

/-! Independent successful source evaluation indexed by Core transition count.
Costs do not measure frontend traversal, lookup, decoding, gas, or elapsed time.
Unselected branches carry no premise; strict Word operands retain their order
and both store endpoints. This relation does not assume execution or erasure. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalExpressionEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop where
  | identifier {store : Core.Store} {span : Syntax.SourceSpan} {name : Syntax.Identifier}
      {id : Resolved.LocalId} {value : Core.Value}
      (named : LocalNameTable.Lookup table name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      LocalExpressionEvaluatesWithCost table environment store
        { span, value := .identifier name } value store 1
  | wordLiteral {store : Core.Store} {span : Syntax.SourceSpan}
      {literal : Syntax.CoreLiteral} {word : Core.Word}
      (meaning : WordLiteralDenotes literal word) :
      LocalExpressionEvaluatesWithCost table environment store
        { span, value := .literal literal } (.word word) store 1
  | group {initialStore finalStore : Core.Store} {span : Syntax.SourceSpan}
      {inner : Syntax.Expr} {value : Core.Value} {childCost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment
        initialStore inner value finalStore childCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .group inner } value finalStore childCost
  | logicalNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Bool} {childCost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment
        initialStore operand (.bool value) finalStore childCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand }
        (.bool (!value)) finalStore (childCost + 2)
  | bitNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Core.Word} {childCost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment
        initialStore operand (.word value) finalStore childCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand }
        (.word value.bitNot) finalStore (childCost + 2)
  | add {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .add⟩ right }
        (.word (leftValue.add rightValue)) finalStore (leftCost + rightCost + 3)
  | subtract {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .subtract⟩ right }
        (.word (leftValue.sub rightValue)) finalStore (leftCost + rightCost + 3)
  | multiply {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .multiply⟩ right }
        (.word (leftValue.mul rightValue)) finalStore (leftCost + rightCost + 3)
  | bitAnd {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right }
        (.word (leftValue.bitAnd rightValue)) finalStore (leftCost + rightCost + 3)
  | bitOr {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right }
        (.word (leftValue.bitOr rightValue)) finalStore (leftCost + rightCost + 3)
  | bitXor {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right }
        (.word (leftValue.bitXor rightValue)) finalStore (leftCost + rightCost + 3)
  | greater {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .greater⟩ right }
        (.bool (decide (leftValue > rightValue))) finalStore (leftCost + rightCost + 3)
  | equal {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .equal⟩ right }
        (.bool (leftValue == rightValue)) finalStore (leftCost + rightCost + 3)
  | notEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right }
        (.bool (!(leftValue == rightValue))) finalStore (leftCost + rightCost + 5)
  | lessEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .lessEqual⟩ right }
        (.bool (!(decide (leftValue > rightValue)))) finalStore (leftCost + rightCost + 5)
  | andTrue {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.bool true) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right value finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right }
        value finalStore (leftCost + rightCost + 2)
  | andFalse {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {leftCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.bool false) finalStore leftCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right }
        (.bool false) finalStore (leftCost + 3)
  | orTrue {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {leftCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.bool true) finalStore leftCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right }
        (.bool true) finalStore (leftCost + 3)
  | orFalse {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.bool false) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right value finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right }
        value finalStore (leftCost + rightCost + 2)
  | ifTrue {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment initialStore
        condition (.bool true) middleStore conditionCost)
      (branchEvaluation : LocalExpressionEvaluatesWithCost table environment middleStore
        thenBranch value finalStore branchCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .conditional condition question thenBranch colon elseBranch }
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment initialStore
        condition (.bool false) middleStore conditionCost)
      (branchEvaluation : LocalExpressionEvaluatesWithCost table environment middleStore
        elseBranch value finalStore branchCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .conditional condition question thenBranch colon elseBranch }
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend
