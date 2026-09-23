import Solcore.Syntax.Parser.Expression.Atom
import Solcore.Syntax.Parser.Expression.PostfixTailFuelTotalityProperties

/-! Fuel-aware totality for complete postfix expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem expressionPostfix_ordinary_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (atomValid : (expressionAtom nested block).ValidFor (fun _ _ => True))
    (atomWindow : Parser.PreservesTokenWindow
      (expressionAtom nested block))
    (atomStrict : ∀ {input next : State} {value : Expr},
      expressionAtom nested block input = .ok value next →
        input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      expressionPostfix nested block input = .ok expression next) ∨
    (∃ failure next,
      expressionPostfix nested block input = .reject failure next) := by
  rcases expressionAtom_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree input inputValid adequate with
    ⟨base, next, atomResult⟩ | ⟨failure, rejected, atomResult⟩
  · have atomReply := atomValid input inputValid
    rw [atomResult] at atomReply
    have atomShape := atomWindow input
    rw [atomResult] at atomShape
    have nextAdequate : next.remainingCount < nestedFuel + 1 :=
      remainingCount_lt_of_cursor_le atomShape.2
        (Nat.le_of_lt (atomStrict atomResult)) adequate
    rcases postfixTail_production_ordinary nested block nestedFuel
        nestedContract base next atomReply.2.1 nextAdequate with
      ⟨expression, final, tailResult⟩ |
      ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨expression, final, by
        simp only [expressionPostfix, atomResult]
        exact tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [expressionPostfix, atomResult]
        exact tailResult⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [expressionPostfix, atomResult]⟩

theorem expressionPostfix_ne_invariant_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (atomValid : (expressionAtom nested block).ValidFor (fun _ _ => True))
    (atomWindow : Parser.PreservesTokenWindow
      (expressionAtom nested block))
    (atomStrict : ∀ {input next : State} {value : Expr},
      expressionAtom nested block input = .ok value next →
        input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    expressionPostfix nested block input ≠ .invariant error := by
  intro failed
  rcases expressionPostfix_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree atomValid atomWindow atomStrict input
      inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
