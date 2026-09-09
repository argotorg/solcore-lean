import Solcore.Frontend.RecursiveLocalComputationCost

/-! Original calls retain actual bodies and captures. Strict binary children
thread their real stores left to right before applying the actual operator.
Conditionals evaluate the actual Bool guard and selected branch only.
Fixed lazy operators require an actual Bool left child; a selected right child
retains its actual value, while skipping evaluates one internal Bool literal.
Unary operations use the actual child payload and preserve its final store.
Fixed negated comparisons evaluate both actual Words before comparison and negation.
Ordered comparisons retain both original Words before swapping their saved positions.
Tuples retain arbitrary actual components in original order, with right-associated tails.
Grouping preserves the exact value, stores and cost of its child. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RecursiveLocalComputationEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
      (child : LocalExpressionEvaluates table environment initialStore source value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore source value finalStore
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : RecursiveLocalComputationEvaluates table environment initialStore inner value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore ⟨span, .group inner⟩ value finalStore
  | application {initialStore argumentStore bodyStore finalStore : Core.Store}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty} {body : Core.Expr}
      {captured : Core.Environment} {argumentValue result : Core.Value}
      (functionEvaluation : RecursiveLocalComputationEvaluates table environment initialStore
        callee (.closure parameterType resultType body captured) argumentStore)
      (argumentEvaluation : RecursiveLocalComputationEvaluates table environment argumentStore
        argument argumentValue bodyStore)
      (bodyEvaluation : Core.Evaluates (argumentValue :: captured) bodyStore body result finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore

  | pair {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Value}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left leftValue middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right rightValue finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩ (.pair leftValue rightValue) finalStore
  | many {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {headValue tailValue : Core.Value}
      (headEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore first headValue middleStore)
      (tailEvaluation : RecursiveLocalComputationEvaluates table environment middleStore
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailValue finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
        (.pair headValue tailValue) finalStore

  | binary {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {leftValue rightValue result : Core.Value}
      (operator : DirectWordBinary sourceOp op)
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left leftValue middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right rightValue finalStore)
      (applied : op.apply leftValue rightValue = some result) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ result finalStore

  | ifTrue {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value}
      (conditionEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore condition (.bool true) middleStore)
      (branchEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore thenBranch value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore
  | ifFalse {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value}
      (conditionEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore condition (.bool false) middleStore)
      (branchEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore elseBranch value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore

  | logicalNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Bool}
      (child : RecursiveLocalComputationEvaluates table environment
        initialStore operand (.bool value) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ (.bool (!value)) finalStore
  | bitNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Core.Word}
      (child : RecursiveLocalComputationEvaluates table environment
        initialStore operand (.word value) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ (.word value.bitNot) finalStore

  | andTrue {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.bool true) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore
  | andFalse {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.bool false) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ (.bool false) finalStore
  | orTrue {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.bool true) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ (.bool true) finalStore
  | orFalse {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.bool false) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore

  | notEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.word leftValue) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right (.word rightValue) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .notEqual⟩ right⟩
        (.bool (!(leftValue == rightValue))) finalStore
  | lessEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.word leftValue) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right (.word rightValue) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .lessEqual⟩ right⟩
        (.bool (!(decide (leftValue > rightValue)))) finalStore

  | less {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.word leftValue) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right (.word rightValue) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .less⟩ right⟩
        (.bool (decide (leftValue < rightValue))) finalStore
  | greaterEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.word leftValue) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right (.word rightValue) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .greaterEqual⟩ right⟩
        (.bool (!(decide (leftValue < rightValue)))) finalStore

end Solcore.Frontend
