import Solcore.Syntax.Parser.CoreExpressionDotConstructorArgumentsOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionNameOutcomeSoundnessProperties

/-! Executable ordinary outcomes for the guarded leading-dot constructor. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable leading-dot success retains its exact dot, Boolean-first
name, optional arguments, constructed AST, span, and final remainder. -/
theorem dotConstructor_success_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State} {expression : Expr}
    (result : dotConstructor nested input = .ok expression output) :
    DeclarativeGrammar.DotConstructorOrdinaryParses nestedOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold dotConstructor at result
  cases dotResult : symbol .dot .expression input with
  | invariant error => simp [bind, dotResult] at result
  | reject failure rejected => simp [bind, dotResult] at result
  | ok dot afterDot =>
      simp only [bind, dotResult] at result
      cases nameResult : expressionName afterDot with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalDotConstructorArguments nested
              afterName with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult, pure] at result
              cases result
              exact .parsed dot.span
                (symbol_success_exactTokenParses .dot .expression dotResult)
                (expressionName_success_sound nameResult)
                (optionalDotConstructorArguments_success_ordinary_sound
                  nested nestedOrdinary nestedSuccessSound nestedShape
                    argumentsResult)

/-- Under the atom dispatcher's positive dot guard, executable constructor
rejection occurs exactly at the name or optional-argument stage. -/
theorem dotConstructor_reject_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (dotPresent : isSymbol input .dot = true)
    (result : dotConstructor nested input = .reject failure rejected) :
    DeclarativeGrammar.DotConstructorRejects nestedOrdinary nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .dot .expression dotPresent with
    ⟨dot, dotResult⟩
  unfold dotConstructor at result
  simp only [bind, dotResult] at result
  cases nameResult : expressionName { input with cursor := input.cursor + 1 }
      with
  | invariant error => simp [nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [nameResult] at result
      cases result
      exact .nameRejected dot.span
        (symbol_success_exactTokenParses .dot .expression dotResult)
        (expressionName_reject_ordinary_sound nameResult)
  | ok name afterName =>
      simp only [nameResult] at result
      cases argumentsResult : optionalDotConstructorArguments nested afterName
          with
      | invariant error => simp [argumentsResult] at result
      | ok arguments afterArguments =>
          simp [argumentsResult, pure] at result
      | reject argumentsFailure argumentsRejected =>
          simp only [argumentsResult] at result
          cases result
          exact .argumentsRejected dot.span
            (symbol_success_exactTokenParses .dot .expression dotResult)
            (expressionName_success_sound nameResult)
            (optionalDotConstructorArguments_reject_ordinary_sound nested
              nestedOrdinary nestedRejects nestedSuccessSound nestedRejectSound
                argumentsResult)

/-- Package unconditional success with rejection under the dispatcher's
positive dot guard. -/
theorem dotConstructor_guardedOrdinaryOutcome_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    (∀ {input output : State} {expression : Expr},
      dotConstructor nested input = .ok expression output →
        DeclarativeGrammar.DotConstructorOrdinaryParses nestedOrdinary
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isSymbol input .dot = true →
        dotConstructor nested input = .reject failure rejected →
          DeclarativeGrammar.DotConstructorRejects nestedOrdinary
            nestedRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨dotConstructor_success_ordinary_sound nested nestedOrdinary
      nestedSuccessSound nestedShape,
    dotConstructor_reject_ordinary_sound nested nestedOrdinary nestedRejects
      nestedSuccessSound nestedRejectSound⟩

/-- Lift deterministic nested outcomes to the guarded leading-dot branch. -/
theorem dotConstructor_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.DotConstructorOrdinaryParses nestedOrdinary)
      (DeclarativeGrammar.DotConstructorRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.dotConstructorDeterministicOutcomeSpec nestedOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
