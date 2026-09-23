import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalReference
import Solcore.Frontend.WordLiteral
import Solcore.Resolved.Eval

/-! Independent canonical evaluation for the local conditional/operator fragment.
Evaluation requires only the selected branch, not whole-expression resolution.
Short-circuit forms forward any selected right value at this raw boundary;
source typing separately requires both operands to be Boolean. Word arithmetic,
bitwise operations, unsigned comparisons, Word equality/inequality and tuple elements
evaluate left to right. Tuples retain arbitrary actual components in right-associated
pairs; an empty tuple denotes unit without any lookup.
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
  | unit {store : Core.Store} {span tupleSpan : Syntax.SourceSpan} :
      LocalExpressionEvaluates table environment store
        { span, value := .tuple ⟨tupleSpan, []⟩ } .unit store
  | pair {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Value}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left leftValue middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right rightValue finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .tuple ⟨tupleSpan, [left, right]⟩ } (.pair leftValue rightValue) finalStore
  | many {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {headValue tailValue : Core.Value}
      (headEvaluation : LocalExpressionEvaluates table environment initialStore first headValue middleStore)
      (tailEvaluation : LocalExpressionEvaluates table environment middleStore
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailValue finalStore) :
      LocalExpressionEvaluates table environment initialStore
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ (.pair headValue tailValue) finalStore
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
  | divide {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .divide⟩ right }
        (.word (leftValue.udiv rightValue)) finalStore
  | modulo {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .modulo⟩ right }
        (.word (leftValue.umod rightValue)) finalStore
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
  | unit => rfl
  | group _ ih | logicalNot _ ih | bitNot _ ih | andFalse _ ih | orTrue _ ih => exact ih
  | ifTrue _ _ conditionIH branchIH | ifFalse _ _ conditionIH branchIH =>
      exact branchIH.trans conditionIH
  | pair _ _ leftIH rightIH
  | many _ _ leftIH rightIH
  | add _ _ leftIH rightIH | bitAnd _ _ leftIH rightIH | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH
  | subtract _ _ leftIH rightIH | multiply _ _ leftIH rightIH | greater _ _ leftIH rightIH
  | divide _ _ leftIH rightIH | modulo _ _ leftIH rightIH
  | less _ _ leftIH rightIH
  | equal _ _ leftIH rightIH
  | notEqual _ _ leftIH rightIH
  | lessEqual _ _ leftIH rightIH
  | greaterEqual _ _ leftIH rightIH
  | andTrue _ _ leftIH rightIH | orFalse _ _ leftIH rightIH =>
      exact rightIH.trans leftIH

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionEvaluation`
-/

/-! Determinism for independent source evaluation. The historical import path
continues to expose the evaluation rules and unchanged store law. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- No whole-resolution or typing premise is needed for source determinism. -/
theorem LocalExpressionEvaluates.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (leftEvaluation : LocalExpressionEvaluates table environment initialStore source left leftStore)
    (rightEvaluation : LocalExpressionEvaluates table environment initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction leftEvaluation generalizing right rightStore with
  | unit => cases rightEvaluation; exact ⟨rfl, rfl⟩
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
  | pair _ _ leftIH rightIH =>
      cases rightEvaluation with
      | pair leftChild rightChild =>
          obtain ⟨rfl, rfl⟩ := leftIH leftChild
          obtain ⟨rfl, storeEq⟩ := rightIH rightChild
          exact ⟨rfl, storeEq⟩
  | many _ _ headIH tailIH =>
      cases rightEvaluation with
      | many headChild tailChild =>
          obtain ⟨rfl, rfl⟩ := headIH headChild
          obtain ⟨rfl, storeEq⟩ := tailIH tailChild
          exact ⟨rfl, storeEq⟩
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
  | add _ _ leftIH rightIH =>
      cases rightEvaluation with
      | add leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | subtract _ _ leftIH rightIH =>
      cases rightEvaluation with
      | subtract leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | multiply _ _ leftIH rightIH =>
      cases rightEvaluation with
      | multiply leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | divide _ _ leftIH rightIH =>
      cases rightEvaluation with
      | divide leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | modulo _ _ leftIH rightIH =>
      cases rightEvaluation with
      | modulo leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | bitAnd _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitAnd leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | bitOr _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitOr leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | bitXor _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitXor leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | greater _ _ leftIH rightIH =>
      cases rightEvaluation with
      | greater leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | less _ _ leftIH rightIH =>
      cases rightEvaluation with
      | less leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | equal _ _ leftIH rightIH =>
      cases rightEvaluation with
      | equal leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | notEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | notEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | lessEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | lessEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | greaterEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | greaterEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
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

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionEvaluationProperties`
-/

/-! Exact canonical-to-resolved evaluation correspondence. Whole structural
resolution is explicit: a skipped branch can otherwise prevent elaboration. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ResolvesLocalExpression.preserves_evaluation {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore) :
    Resolved.Evaluates environment initialStore resolved value finalStore := by
  induction resolution generalizing initialStore finalStore value with
  | unit => cases evaluation; exact .unit
  | identifier named =>
      cases evaluation with
      | identifier otherNamed found =>
          cases named.id_unique otherNamed
          exact .var found
  | wordLiteral meaning =>
      cases evaluation with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact .word
  | group _ ih =>
      cases evaluation with
      | group child => exact ih child
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pair leftChild rightChild => exact .pair (leftIH leftChild) (rightIH rightChild)
  | many _ _ headIH tailIH =>
      cases evaluation with
      | many headChild tailChild => exact .pair (headIH headChild) (tailIH tailChild)
  | logicalNot _ ih =>
      cases evaluation with
      | logicalNot child => exact .unary (ih child) rfl
  | bitNot _ ih =>
      cases evaluation with
      | bitNot child => exact .unary (ih child) rfl
  | add _ _ leftIH rightIH =>
      cases evaluation with
      | add leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | subtract _ _ leftIH rightIH =>
      cases evaluation with
      | subtract leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | multiply _ _ leftIH rightIH =>
      cases evaluation with
      | multiply leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | divide _ _ leftIH rightIH =>
      cases evaluation with
      | divide leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | modulo _ _ leftIH rightIH =>
      cases evaluation with
      | modulo leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | bitAnd _ _ leftIH rightIH =>
      cases evaluation with
      | bitAnd leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | bitOr _ _ leftIH rightIH =>
      cases evaluation with
      | bitOr leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | bitXor _ _ leftIH rightIH =>
      cases evaluation with
      | bitXor leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | greater _ _ leftIH rightIH =>
      cases evaluation with
      | greater leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | less _ _ leftIH rightIH =>
      cases evaluation with
      | less leftChild rightChild => exact .wordLt (leftIH leftChild) (rightIH rightChild)
  | equal _ _ leftIH rightIH =>
      cases evaluation with
      | equal leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | notEqual _ _ leftIH rightIH =>
      cases evaluation with
      | notEqual leftChild rightChild => exact .unary (.binary (leftIH leftChild) (rightIH rightChild) rfl) rfl
  | lessEqual _ _ leftIH rightIH =>
      cases evaluation with
      | lessEqual leftChild rightChild => exact .unary (.binary (leftIH leftChild) (rightIH rightChild) rfl) rfl
  | greaterEqual _ _ leftIH rightIH =>
      cases evaluation with
      | greaterEqual leftChild rightChild => exact .unary (.wordLt (leftIH leftChild) (rightIH rightChild)) rfl
  | logicalAnd _ _ leftIH rightIH =>
      cases evaluation with
      | andTrue leftChild rightChild => exact .ifTrue (leftIH leftChild) (rightIH rightChild)
      | andFalse leftChild => exact .ifFalse (leftIH leftChild) .bool
  | logicalOr _ _ leftIH rightIH =>
      cases evaluation with
      | orTrue leftChild => exact .ifTrue (leftIH leftChild) .bool
      | orFalse leftChild rightChild => exact .ifFalse (leftIH leftChild) (rightIH rightChild)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch => exact .ifTrue (conditionIH condition) (thenIH branch)
      | ifFalse condition branch => exact .ifFalse (conditionIH condition) (elseIH branch)

theorem ResolvesLocalExpression.reflects_evaluation {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value}
    (evaluation : Resolved.Evaluates environment initialStore resolved value finalStore) :
    LocalExpressionEvaluates table environment initialStore source value finalStore := by
  induction resolution generalizing initialStore finalStore value with
  | unit => cases evaluation; exact .unit
  | identifier named =>
      cases evaluation with
      | var found => exact .identifier named found
  | wordLiteral meaning =>
      cases evaluation with
      | word => exact .wordLiteral meaning
  | group _ ih => exact .group (ih evaluation)
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pair leftChild rightChild => exact .pair (leftIH leftChild) (rightIH rightChild)
  | many _ _ headIH tailIH =>
      cases evaluation with
      | pair headChild tailChild => exact .many (headIH headChild) (tailIH tailChild)
  | logicalNot _ ih =>
      cases evaluation with
      | @unary _ _ _ _ _ operandValue _ child applied =>
          cases operandValue <;> simp only [Core.UnaryOp.apply, reduceCtorEq] at applied
          case bool decision =>
            cases applied
            exact .logicalNot (ih child)
  | bitNot _ ih =>
      cases evaluation with
      | @unary _ _ _ _ _ operandValue _ child applied =>
          cases operandValue <;> simp only [Core.UnaryOp.apply, reduceCtorEq] at applied
          case word value =>
            cases applied
            exact .bitNot (ih child)
  | add _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .add (leftIH leftChild) (rightIH rightChild)
  | subtract _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .subtract (leftIH leftChild) (rightIH rightChild)
  | multiply _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .multiply (leftIH leftChild) (rightIH rightChild)
  | divide _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .divide (leftIH leftChild) (rightIH rightChild)
  | modulo _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .modulo (leftIH leftChild) (rightIH rightChild)
  | bitAnd _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .bitAnd (leftIH leftChild) (rightIH rightChild)
  | bitOr _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .bitOr (leftIH leftChild) (rightIH rightChild)
  | bitXor _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .bitXor (leftIH leftChild) (rightIH rightChild)
  | greater _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .greater (leftIH leftChild) (rightIH rightChild)
  | less _ _ leftIH rightIH =>
      cases evaluation with
      | wordLt leftChild rightChild => exact .less (leftIH leftChild) (rightIH rightChild)
  | equal _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .equal (leftIH leftChild) (rightIH rightChild)
  | notEqual _ _ leftIH rightIH =>
      cases evaluation with
      | unary equality negated =>
          cases equality with
          | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
              cases leftValue <;> cases rightValue <;>
                simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
              case word.word leftWord rightWord =>
                cases applied
                cases negated
                exact .notEqual (leftIH leftChild) (rightIH rightChild)
  | lessEqual _ _ leftIH rightIH =>
      cases evaluation with
      | unary comparison negated =>
          cases comparison with
          | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
              cases leftValue <;> cases rightValue <;>
                simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
              case word.word leftWord rightWord =>
                cases applied
                cases negated
                exact .lessEqual (leftIH leftChild) (rightIH rightChild)
  | greaterEqual _ _ leftIH rightIH =>
      cases evaluation with
      | unary comparison negated =>
          cases comparison with
          | wordLt leftChild rightChild =>
              cases negated
              exact .greaterEqual (leftIH leftChild) (rightIH rightChild)
  | logicalAnd _ _ leftIH rightIH =>
      cases evaluation with
      | ifTrue leftChild rightChild => exact .andTrue (leftIH leftChild) (rightIH rightChild)
      | ifFalse leftChild constant =>
          cases constant
          exact .andFalse (leftIH leftChild)
  | logicalOr _ _ leftIH rightIH =>
      cases evaluation with
      | ifTrue leftChild constant =>
          cases constant
          exact .orTrue (leftIH leftChild)
      | ifFalse leftChild rightChild => exact .orFalse (leftIH leftChild) (rightIH rightChild)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch => exact .ifTrue (conditionIH condition) (thenIH branch)
      | ifFalse condition branch => exact .ifFalse (conditionIH condition) (elseIH branch)

theorem ResolvesLocalExpression.evaluates_iff {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      Resolved.Evaluates environment initialStore resolved value finalStore :=
  ⟨resolution.preserves_evaluation, resolution.reflects_evaluation⟩

/-- Exact Core correspondence for an explicitly resolved and lowered expression.
The lowering scope is the runtime identity order, not merely its length. -/
theorem ResolvesLocalExpression.core_evaluates_iff {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {core : Core.Expr}
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore :=
  resolution.evaluates_iff.trans lowered.evaluates_iff

end Solcore.Frontend
