import Solcore.Syntax.DeclarativeCoreArrayLiteralOutcomeProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Executable ordinary outcomes for guarded Core array literals. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable array-literal success retains its exact brackets,
source-order elements, covering span, AST, and output remainder. -/
theorem arrayLiteral_success_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State} {expression : Expr}
    (result : arrayLiteral nested input = .ok expression output) :
    DeclarativeGrammar.ArrayLiteralExpressionOrdinaryParses nestedOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold arrayLiteral at result
  cases valuesResult :
      delimitedNoTrailing .leftBracket .rightBracket true nested .expression
        .expression input with
  | invariant error => simp [bind, valuesResult] at result
  | reject failure rejected => simp [bind, valuesResult] at result
  | ok values afterValues =>
      simp only [bind, valuesResult, pure] at result
      cases result
      exact .parsed
        (delimitedNoTrailing_allowEmpty_success_sound .leftBracket
          .rightBracket nested nestedOrdinary .expression .expression
            nestedSuccessSound nestedShape valuesResult)

/-- Under the dispatcher's positive `[` guard, every executable rejection is
the exact allow-empty, no-trailing delimiter rejection. -/
theorem arrayLiteral_reject_ordinary_sound
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
    (openingPresent : isSymbol input .leftBracket = true)
    (result : arrayLiteral nested input = .reject failure rejected) :
    DeclarativeGrammar.ArrayLiteralExpressionRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold arrayLiteral at result
  cases valuesResult :
      delimitedNoTrailing .leftBracket .rightBracket true nested .expression
        .expression input with
  | invariant error => simp [bind, valuesResult] at result
  | ok values afterValues => simp [bind, valuesResult, pure] at result
  | reject valuesFailure valuesRejected =>
      simp only [bind, valuesResult] at result
      cases result
      rcases symbol_eq_ok_of_isSymbol_eq_true .leftBracket .expression
          openingPresent with ⟨opening, openingResult⟩
      exact .present opening.span
        (symbol_success_exactTokenParses .leftBracket .expression
          openingResult).1
        (delimitedNoTrailing_reject_sound .leftBracket .rightBracket true
          nested nestedOrdinary nestedRejects .expression .expression
            nestedSuccessSound nestedRejectSound valuesResult)

/-- Package executable array success and guarded rejection. -/
theorem arrayLiteral_guardedOrdinaryOutcome_sound
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
      arrayLiteral nested input = .ok expression output →
        DeclarativeGrammar.ArrayLiteralExpressionOrdinaryParses
          nestedOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isSymbol input .leftBracket = true →
        arrayLiteral nested input = .reject failure rejected →
          DeclarativeGrammar.ArrayLiteralExpressionRejects nestedOrdinary
            nestedRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨arrayLiteral_success_ordinary_sound nested nestedOrdinary
      nestedSuccessSound nestedShape,
    arrayLiteral_reject_ordinary_sound nested nestedOrdinary nestedRejects
      nestedSuccessSound nestedRejectSound⟩

/-- Lift a deterministic nested expression outcome to arrays. -/
theorem arrayLiteral_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ArrayLiteralExpressionOrdinaryParses
        nestedOrdinary)
      (DeclarativeGrammar.ArrayLiteralExpressionRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.arrayLiteralExpressionDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
