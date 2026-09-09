import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalExpressionResolutionProperties
import Solcore.Resolved.TypingProperties

/-! Independent source typing constructs its exact resolved expression and type.
Kept separate so the established typing-properties import remains within its size limit. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalExpressionHasType.resolves {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType table context source type) :
    ∃ resolved, ResolvesLocalExpression table source resolved ∧ Resolved.HasType context resolved type := by
  induction typing with
  | unit => exact ⟨.unit, .unit, .unit⟩
  | identifier named found => exact ⟨_, .identifier named, .var found⟩
  | wordLiteral meaning => exact ⟨_, .wordLiteral meaning, .word⟩
  | group _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := ih
      exact ⟨resolved, .group resolution, typed⟩
  | pair _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .pair leftResolved rightResolved, .pair leftTyped rightTyped⟩
  | many _ _ headIH tailIH =>
      obtain ⟨head, headResolved, headTyped⟩ := headIH
      obtain ⟨tail, tailResolved, tailTyped⟩ := tailIH
      exact ⟨_, .many headResolved tailResolved, .pair headTyped tailTyped⟩
  | logicalNot _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := ih
      exact ⟨_, .logicalNot resolution, .unary typed⟩
  | bitNot _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := ih
      exact ⟨_, .bitNot resolution, .unary typed⟩
  | add _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .add leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | subtract _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .subtract leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | multiply _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .multiply leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | divide _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .divide leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | modulo _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .modulo leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | greater _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .greater leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | equal _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .equal leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | notEqual _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .notEqual leftResolved rightResolved, .unary (.binary leftTyped rightTyped)⟩
  | lessEqual _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .lessEqual leftResolved rightResolved, .unary (.binary leftTyped rightTyped)⟩
  | less _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .less leftResolved rightResolved, .wordLt leftTyped rightTyped⟩
  | greaterEqual _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .greaterEqual leftResolved rightResolved, .unary (.wordLt leftTyped rightTyped)⟩
  | bitAnd _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .bitAnd leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | bitOr _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .bitOr leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | bitXor _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .bitXor leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | logicalAnd _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .logicalAnd leftResolved rightResolved, .ifE leftTyped rightTyped .bool⟩
  | logicalOr _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .logicalOr leftResolved rightResolved, .ifE leftTyped .bool rightTyped⟩
  | conditional _ _ _ conditionIH thenIH elseIH =>
      obtain ⟨condition, conditionResolved, conditionTyped⟩ := conditionIH
      obtain ⟨thenBranch, thenResolved, thenTyped⟩ := thenIH
      obtain ⟨elseBranch, elseResolved, elseTyped⟩ := elseIH
      exact ⟨_, .conditional conditionResolved thenResolved elseResolved,
        .ifE conditionTyped thenTyped elseTyped⟩

end Solcore.Frontend
