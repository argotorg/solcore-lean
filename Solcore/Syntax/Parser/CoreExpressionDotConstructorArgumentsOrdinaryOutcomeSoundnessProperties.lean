import Solcore.Syntax.DeclarativeCoreExpressionDotConstructorOutcomeProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Executable ordinary outcomes for optional leading-dot arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every optional-argument success takes exactly the absent branch or the
committed allow-empty, no-trailing parenthesized branch. -/
theorem optionalDotConstructorArguments_success_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State}
    {arguments : Option (DelimitedList Expr)}
    (result : optionalDotConstructorArguments nested input =
      .ok arguments output) :
    DeclarativeGrammar.OptionalDotConstructorArgumentsOrdinaryParses
      nestedOrdinary input.declarativeRemainder arguments
        output.declarativeRemainder := by
  unfold optionalDotConstructorArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases argumentsResult :
        delimitedNoTrailing .leftParen .rightParen true nested .expression
          .expression input with
    | invariant error => simp [argumentsResult] at result
    | reject failure rejected => simp [argumentsResult] at result
    | ok values afterArguments =>
        simp only [argumentsResult, pure] at result
        cases result
        exact .present
          (delimitedNoTrailing_allowEmpty_success_sound .leftParen
            .rightParen nested nestedOrdinary .expression .expression
              nestedSuccessSound nestedShape argumentsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

/-- Every optional-argument rejection occurs only after a positive opening
guard and carries the exact delimited-list rejection trace. -/
theorem optionalDotConstructorArguments_reject_ordinary_sound
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
    (result : optionalDotConstructorArguments nested input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalDotConstructorArgumentsRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalDotConstructorArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases argumentsResult :
        delimitedNoTrailing .leftParen .rightParen true nested .expression
          .expression input with
    | invariant error => simp [argumentsResult] at result
    | ok values afterArguments => simp [argumentsResult, pure] at result
    | reject argumentsFailure argumentsRejected =>
        simp only [argumentsResult] at result
        cases result
        rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression present
          with ⟨opening, openingResult⟩
        exact .present opening.span
          (symbol_success_exactTokenParses .leftParen .expression
            openingResult).1
          (delimitedNoTrailing_reject_sound .leftParen .rightParen true
            nested nestedOrdinary nestedRejects .expression .expression
              nestedSuccessSound nestedRejectSound argumentsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package the executable optional-argument ordinary outcome. -/
theorem optionalDotConstructorArguments_ordinaryOutcome_sound
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
    (∀ {input output : State}
      {arguments : Option (DelimitedList Expr)},
      optionalDotConstructorArguments nested input = .ok arguments output →
        DeclarativeGrammar.OptionalDotConstructorArgumentsOrdinaryParses
          nestedOrdinary input.declarativeRemainder arguments
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalDotConstructorArguments nested input =
        .reject failure rejected →
        DeclarativeGrammar.OptionalDotConstructorArgumentsRejects
          nestedOrdinary nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨optionalDotConstructorArguments_success_ordinary_sound nested
      nestedOrdinary nestedSuccessSound nestedShape,
    optionalDotConstructorArguments_reject_ordinary_sound nested
      nestedOrdinary nestedRejects nestedSuccessSound nestedRejectSound⟩

/-- Lift a deterministic nested outcome to optional arguments. -/
theorem optionalDotConstructorArguments_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalDotConstructorArgumentsOrdinaryParses
        nestedOrdinary)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsRejects
        nestedOrdinary nestedRejects) :=
  DeclarativeGrammar.optionalDotConstructorArgumentsDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
