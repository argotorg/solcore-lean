import Solcore.Frontend.LocalExpressionCost
import Solcore.Core.Machine
import Solcore.Frontend.DirectWordBinary

/-! Original calls retain actual bodies and captures. Strict binary children
thread their real stores left to right before applying the actual operator.
Conditionals evaluate the actual Bool guard and selected branch only.
Fixed lazy operators require an actual Bool left child; a selected right child
retains its actual value, while skipping evaluates one internal Bool literal.
Unary operations use the actual child payload and preserve its final store.
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

inductive RecursiveLocalComputationEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr}
      {value : Core.Value} {cost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : RecursiveLocalComputationEvaluatesWithCost table environment initialStore inner value finalStore cost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .group inner⟩ value finalStore cost
  | application {initialStore argumentStore bodyStore finalStore : Core.Store}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty} {body : Core.Expr}
      {captured : Core.Environment} {argumentValue result : Core.Value}
      {functionCost argumentCost bodyCost : Nat}
      (functionEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        callee (.closure parameterType resultType body captured) argumentStore functionCost)
      (argumentEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment argumentStore
        argument argumentValue bodyStore argumentCost)
      (bodyPath : Core.Steps bodyCost
        (Core.State.initial body (argumentValue :: captured) bodyStore)
        (Core.State.final result finalStore)) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore
        (functionCost + argumentCost + bodyCost + 3)

  | binary {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {leftValue rightValue result : Core.Value}
      {leftCost rightCost : Nat}
      (operator : DirectWordBinary sourceOp op)
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left leftValue middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right rightValue finalStore rightCost)
      (applied : op.apply leftValue rightValue = some result) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ result finalStore (leftCost + rightCost + 3)

  | ifTrue {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore thenBranch value finalStore branchCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore
        (conditionCost + branchCost + 2)
  | ifFalse {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore elseBranch value finalStore branchCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore
        (conditionCost + branchCost + 2)

  | logicalNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Bool} {childCost : Nat}
      (child : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore operand (.bool value) finalStore childCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ (.bool (!value)) finalStore (childCost + 2)
  | bitNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Core.Word} {childCost : Nat}
      (child : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore operand (.word value) finalStore childCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ (.word value.bitNot) finalStore (childCost + 2)

  | andTrue {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      {leftCost rightCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.bool true) middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right value finalStore rightCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore (leftCost + rightCost + 2)
  | andFalse {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.bool false) finalStore leftCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ (.bool false) finalStore (leftCost + 3)
  | orTrue {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.bool true) finalStore leftCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ (.bool true) finalStore (leftCost + 3)
  | orFalse {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      {leftCost rightCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.bool false) middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right value finalStore rightCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore (leftCost + rightCost + 2)

end Solcore.Frontend
