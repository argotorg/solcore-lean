import Solcore.Syntax.Parser.Expression.AtomDelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.Expression.AtomRecoveryTotalityProperties
import Solcore.Syntax.Parser.Expression.AtomTupleTotalityProperties

/-! Fuel-aware totality for expression-atom dispatch and recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem expressionAtomCore_ordinary_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      expressionAtomCore nested block input = .ok expression next) ∨
    (∃ failure next,
      expressionAtomCore nested block input = .reject failure next) := by
  unfold expressionAtomCore
  split
  · exact literalExpression_invariantFreeOnValid input inputValid
  · split
    · exact identifierExpression_invariantFreeOnValid input inputValid
    · split
      · exact dotConstructor_ordinary_of_elementFuel nested nestedFuel
          nestedContract input inputValid adequate
      · split
        · exact proxyExpression_invariantFreeOnValid input inputValid
        · split
          · exact parenthesized_ordinary_of_elementFuel nested nestedFuel
              nestedContract input inputValid adequate
          · split
            · exact arrayLiteral_ordinary_of_elementFuel nested nestedFuel
                nestedContract input inputValid adequate
            · split
              · exact lambdaFree input inputValid
              · exact Parser.rejectAt_invariantFreeOnValid
                  { head := .expression, tail := [] } .expression
                    input inputValid

theorem expressionAtomCore_ne_invariant_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    expressionAtomCore nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtomCore_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Recovery adds no invariant after an ordinary atom-core rejection. -/
theorem expressionAtom_ordinary_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      expressionAtom nested block input = .ok expression next) ∨
    (∃ failure next,
      expressionAtom nested block input = .reject failure next) := by
  rcases expressionAtomCore_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree input inputValid adequate with
    ⟨value, next, coreResult⟩ | ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [expressionAtom, coreResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : isAtomBoundary rewound
    · exact Or.inr ⟨failure, rewound, by
        simp only [expressionAtom, coreResult, rewound, boundary, ↓reduceIte]⟩
    · have boundaryFalse : isAtomBoundary rewound = false := by
        cases found : isAtomBoundary rewound with
        | false => rfl
        | true => exact False.elim (boundary found)
      rcases recoverAtom_ordinary
          (rewound.emit failure.toDiagnostic) with
        ⟨recovered, final, recoveryResult⟩ |
        ⟨recoveryFailure, rejected, recoveryResult⟩
      · exact Or.inl ⟨recovered, final, by
          simp only [expressionAtom, coreResult, rewound, boundaryFalse,
            Bool.false_eq_true, ↓reduceIte, recoveryResult]⟩
      · exact Or.inr ⟨recoveryFailure, rejected, by
          simp only [expressionAtom, coreResult, rewound, boundaryFalse,
            Bool.false_eq_true, ↓reduceIte, recoveryResult]⟩

theorem expressionAtom_ne_invariant_of_elementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (lambdaFree : Parser.InvariantFreeOnValid (lambdaExpression block))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    expressionAtom nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtom_ordinary_of_elementFuel nested block nestedFuel
      nestedContract lambdaFree input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
