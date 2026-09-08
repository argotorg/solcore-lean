import Solcore.Syntax.Parser.ExpressionAtomUnrestrictedFuelTotalityProperties

/-! Both expression and block children may have only bounded ordinary
execution. A real lam marker pays one unit before its concrete parameter and
return parsers. This layer adds no child success/rejection frame or validity
premise and does not construct an atom success-progress/end-index contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar ExpressionAtomDispatchTraceInternals

/-- Only the block contract's bounded ordinary field is used here. Concrete
prefix parsers transfer its budget without constraining the body result State. -/
theorem lambdaExpression_ordinary_of_unrestrictedBodyFuel
    (block : Parser Block) (bodyFuel : Nat)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (adequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output, lambdaExpression block input = .ok value output) ∨
    (∃ failure rejected, lambdaExpression block input = .reject failure rejected) := by
  rcases keyword_ordinary .lamKw .expression input with
    ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
  · have markerBudget := keyword_remainingCount_lt_of_success .lamKw .expression markerResult adequate
    rcases lambdaParameters_ordinary_unrestricted afterMarker with
      ⟨parameters, afterParameters, parameterResult⟩ | ⟨failure, rejected, parameterResult⟩
    · have parameterFrame := lambdaParameters_success_context parameterResult
      have parameterCursor := delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
        lambdaParameter .parameter .expression afterMarker parameters afterParameters parameterResult
      have parameterBudget := remainingCount_lt_of_endIndex_eq
        (congrArg TokenWindow.endIndex parameterFrame.2) parameterCursor markerBudget
      rcases optionalLambdaReturnType_ordinary_unrestricted afterParameters with
        ⟨returnType, afterReturn, returnResult⟩ | ⟨failure, rejected, returnResult⟩
      · have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
        have returnCursor := optionalLambdaReturnType_cursorMonotoneOnSuccess
          afterParameters returnType afterReturn returnResult
        have returnBudget := remainingCount_lt_of_endIndex_eq
          (congrArg TokenWindow.endIndex returnFrame.2) returnCursor parameterBudget
        rcases bodyContract.ordinary afterReturn returnBudget with
          ⟨body, output, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
        · exact .inl ⟨{
            span := SourceSpan.cover marker.span body.span
            value := .lambda marker.span parameters returnType body
          }, output, by simp only [lambdaExpression, bind, markerResult, parameterResult, returnResult, bodyResult, pure]⟩
        · exact .inr ⟨failure, rejected, by
            simp only [lambdaExpression, bind, markerResult, parameterResult, returnResult, bodyResult]⟩
      · exact .inr ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult, parameterResult, returnResult]⟩
    · exact .inr ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult, parameterResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult]⟩

theorem lambdaExpression_ne_invariant_of_unrestrictedBodyFuel
    (block : Parser Block) (bodyFuel : Nat)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (adequate : input.remainingCount < bodyFuel + 1) (error : ParserInvariantError) :
    lambdaExpression block input ≠ .invariant error := by
  intro failed
  rcases lambdaExpression_ordinary_of_unrestrictedBodyFuel block bodyFuel bodyContract input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

/-- Outside the selected lambda branch the body parser is unused, so all
seven remaining branches reuse the established expression-child fuel proof. -/
theorem expressionAtomCore_ordinary_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output, expressionAtomCore nested block input = .ok value output) ∨
    (∃ failure rejected, expressionAtomCore nested block input = .reject failure rejected) := by
  let unusedBody : Parser Block := fun state => rejectAt state { head := .expression, tail := [] } .expression
  have unusedOrdinary : Parser.Ordinary unusedBody := fun state => .inr ⟨_, state, rfl⟩
  have otherBranches := expressionAtomCore_ordinary_of_unrestrictedElementFuel nested unusedBody
    nestedFuel nestedContract unusedOrdinary input nestedAdequate
  rw [expressionAtomCore_eq_selected_raw] at otherBranches ⊢
  cases chosen : selectedBranch input with
  | lambda => exact lambdaExpression_ordinary_of_unrestrictedBodyFuel block bodyFuel bodyContract input bodyAdequate
  | literal | name | dotConstructor | proxy | parenthesized | array | final =>
      simpa only [chosen, rawParser] using otherBranches

theorem expressionAtomCore_ne_invariant_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) (error : ParserInvariantError) :
    expressionAtomCore nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtomCore_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

/-- Recovery is ordinary on every failed replacement carrier, independently
of both original budgets and without a rejection end-index frame. -/
theorem expressionAtom_ordinary_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output, expressionAtom nested block input = .ok value output) ∨
    (∃ failure rejected, expressionAtom nested block input = .reject failure rejected) := by
  rcases expressionAtomCore_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · exact .inl ⟨value, output, by simp only [expressionAtom, result]⟩
  · simp only [expressionAtom, result]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverAtom_ordinary _

theorem expressionAtom_ne_invariant_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) (error : ParserInvariantError) :
    expressionAtom nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtom_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
