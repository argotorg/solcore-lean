import Solcore.Syntax.DeclarativeCoreExpressionPostfixOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionPostfixSoundnessProperties

/-!
Unconditional ordinary-success bridges for maximal Core postfix parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable postfix-tail success follows the exact prioritized,
maximal ordinary suffix grammar, independently of diagnostics. -/
theorem postfixTail_success_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {value : Expr},
      nested input = .ok value output →
        nestedOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    ∀ fuel base input expression output,
      postfixTail nested block fuel base input = .ok expression output →
        DeclarativeGrammar.PostfixTailOrdinaryParses nestedOrdinary
          input.declarativeRemainder base expression
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro base input expression output result
      simp [postfixTail] at result
  | succ fuel inductionHypothesis =>
      intro base input expression output result
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at result
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject failure rejected => simp [openingResult] at result
        | ok opening afterOpening =>
            simp only [openingResult] at result
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at result
            | reject failure rejected => simp [indexResult] at result
            | ok index afterIndex =>
                simp only [indexResult] at result
                cases closingResult : symbol .rightBracket .expression
                    afterIndex with
                | invariant error => simp [closingResult] at result
                | reject failure rejected => simp [closingResult] at result
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    exact .index opening.span closing.span
                      (symbol_success_exactTokenParses .leftBracket
                        .expression openingResult)
                      (nestedSuccessSound indexResult)
                      (symbol_success_exactTokenParses .rightBracket
                        .expression closingResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span closing.span
                        value := .index base
                          (SourceSpan.cover opening.span closing.span) index
                      } afterClosing expression output result)
      · simp only [indexed, Bool.false_eq_true, if_false] at result
        have indexedFalse : isSymbol input .leftBracket = false := by
          simp_all
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false
          .leftBracket indexedFalse
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at result
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              exact .call indexAbsent
                (delimitedNoTrailing_allowEmpty_success_sound
                  .leftParen .rightParen nested nestedOrdinary .expression
                    .expression nestedSuccessSound nestedShape argumentsResult)
                (inductionHypothesis {
                  span := SourceSpan.cover base.span arguments.span
                  value := .call base arguments
                } afterArguments expression output result)
        · simp only [called, Bool.false_eq_true, if_false] at result
          have calledFalse : isSymbol input .leftParen = false := by
            simp_all
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false
            .leftParen calledFalse
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at result
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject failure rejected => simp [dotResult] at result
            | ok dot afterDot =>
                simp only [dotResult] at result
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at result
                | reject failure rejected => simp [nameResult] at result
                | ok name afterName =>
                    simp only [nameResult] at result
                    exact .field dot.span indexAbsent callAbsent
                      (symbol_success_exactTokenParses .dot .expression
                        dotResult)
                      (identifier_success_sound .expression nameResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span name.span
                        value := .field base dot.span name
                      } afterName expression output result)
          · simp only [field] at result
            cases result
            have fieldFalse : isSymbol input .dot = false := by
              simp_all
            exact .done ⟨indexAbsent, callAbsent,
              symbolAbsentAt_of_isSymbol_eq_false .dot fieldFalse⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- Every executable complete postfix success consists of one supplied
ordinary atom followed by its exact maximal ordinary suffix sequence. -/
theorem expressionPostfix_success_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomOrdinary nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomSuccessSound : ∀ {input output : State} {value : Expr},
      expressionAtom nested block input = .ok value output →
        atomOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (nestedSuccessSound : ∀ {input output : State} {value : Expr},
      nested input = .ok value output →
        nestedOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State} {expression : Expr}
    (result : expressionPostfix nested block input = .ok expression output) :
    DeclarativeGrammar.ExpressionPostfixOrdinaryParses atomOrdinary
      nestedOrdinary input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base afterAtom =>
      simp only [atomResult] at result
      exact ⟨base, afterAtom.declarativeRemainder,
        atomSuccessSound atomResult,
        ExpressionAtomInternals.postfixTail_success_ordinary_sound
          nested block nestedOrdinary nestedSuccessSound nestedShape
            (afterAtom.remainingCount + 1) base afterAtom expression output
              result⟩

end Solcore.Syntax.Parser
