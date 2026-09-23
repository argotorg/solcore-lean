import Solcore.Syntax.DeclarativeCoreExpressionPostfixOutcomeProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-!
Exact executable rejection bridges for maximal Core postfix expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable postfix-tail rejection follows the exact selected suffix
branch and subordinate ordinary outcome. -/
theorem postfixTail_reject_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
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
    ∀ fuel base input failure rejected,
      postfixTail nested block fuel base input = .reject failure rejected →
      DeclarativeGrammar.PostfixTailRejects nestedOrdinary nestedRejects
        input.declarativeRemainder base rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro base input failure rejected result
      simp [postfixTail] at result
  | succ fuel inductionHypothesis =>
      intro base input failure rejected result
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at result
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject openingFailure openingRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .leftBracket .expression
                indexed with ⟨opening, parsed⟩
            rw [parsed] at openingResult
            contradiction
        | ok opening afterOpening =>
            simp only [openingResult] at result
            have openingParsed := symbol_success_exactTokenParses .leftBracket
              .expression openingResult
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at result
            | reject indexFailure indexRejected =>
                simp only [indexResult] at result
                cases result
                exact .indexNestedRejected opening.span openingParsed
                  (nestedRejectSound indexResult)
            | ok index afterIndex =>
                simp only [indexResult] at result
                have indexParsed := nestedSuccessSound indexResult
                cases closingResult : symbol .rightBracket .expression
                    afterIndex with
                | invariant error => simp [closingResult] at result
                | reject closingFailure closingRejected =>
                    have rejectedEq := symbol_reject_state_eq .rightBracket
                      .expression closingResult
                    subst rejectedEq
                    simp only [closingResult] at result
                    cases result
                    exact .indexClosingMissing opening.span openingParsed
                      indexParsed
                      (symbol_reject_tokenKindAbsentAt .rightBracket
                        .expression closingResult)
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    exact .indexLaterRejected opening.span closing.span
                      openingParsed indexParsed
                      (symbol_success_exactTokenParses .rightBracket
                        .expression closingResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span closing.span
                        value := .index base
                          (SourceSpan.cover opening.span closing.span) index
                      } afterClosing failure rejected result)
      · have indexedFalse : isSymbol input .leftBracket = false :=
          Bool.eq_false_iff.mpr indexed
        simp only [indexedFalse, Bool.false_eq_true, if_false] at result
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftBracket
          indexedFalse
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at result
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject argumentsFailure argumentsRejected =>
              simp only [argumentsResult] at result
              cases result
              rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression
                  called with ⟨opening, openingResult⟩
              exact .callArgumentsRejected opening.span indexAbsent
                (symbol_success_exactTokenParses .leftParen .expression
                  openingResult).1
                (delimitedNoTrailing_reject_sound .leftParen .rightParen true
                  nested nestedOrdinary nestedRejects .expression .expression
                    nestedSuccessSound nestedRejectSound argumentsResult)
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              exact .callLaterRejected indexAbsent
                (delimitedNoTrailing_allowEmpty_success_sound .leftParen
                  .rightParen nested nestedOrdinary .expression .expression
                    nestedSuccessSound nestedShape argumentsResult)
                (inductionHypothesis {
                  span := SourceSpan.cover base.span arguments.span
                  value := .call base arguments
                } afterArguments failure rejected result)
        · have calledFalse : isSymbol input .leftParen = false :=
            Bool.eq_false_iff.mpr called
          simp only [calledFalse, Bool.false_eq_true, if_false] at result
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftParen
            calledFalse
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at result
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject dotFailure dotRejected =>
                rcases symbol_eq_ok_of_isSymbol_eq_true .dot .expression field
                  with ⟨dot, parsed⟩
                rw [parsed] at dotResult
                contradiction
            | ok dot afterDot =>
                simp only [dotResult] at result
                have dotParsed := symbol_success_exactTokenParses .dot
                  .expression dotResult
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at result
                | reject nameFailure nameRejected =>
                    simp only [nameResult] at result
                    cases result
                    exact .fieldNameRejected dot.span indexAbsent callAbsent
                      dotParsed (identifier_reject_sound .expression nameResult)
                | ok name afterName =>
                    simp only [nameResult] at result
                    exact .fieldLaterRejected dot.span indexAbsent callAbsent
                      dotParsed (identifier_success_sound .expression
                        nameResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span name.span
                        value := .field base dot.span name
                      } afterName failure rejected result)
          · have fieldFalse : isSymbol input .dot = false :=
              Bool.eq_false_iff.mpr field
            simp [fieldFalse] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- Every executable complete-postfix rejection is either atom rejection or
an exact rejection after ordinary atom success. -/
theorem expressionPostfix_reject_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomOrdinary nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomRejects nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (atomSuccessSound : ∀ {input output : State} {expression : Expr},
      expressionAtom nested block input = .ok expression output →
        atomOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (atomRejectSound : ∀ {input rejected : State} {failure : Failure},
      expressionAtom nested block input = .reject failure rejected →
        atomRejects input.declarativeRemainder rejected.declarativeRemainder)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input rejected : State} {failure : Failure}
    (result : expressionPostfix nested block input =
      .reject failure rejected) :
    DeclarativeGrammar.ExpressionPostfixRejects atomOrdinary nestedOrdinary
      atomRejects nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject atomFailure atomRejected =>
      simp only [atomResult] at result
      cases result
      exact .atomRejected (atomRejectSound atomResult)
  | ok base afterAtom =>
      simp only [atomResult] at result
      exact .tailRejected (atomSuccessSound atomResult)
        (ExpressionAtomInternals.postfixTail_reject_ordinary_sound nested block
          nestedOrdinary nestedRejects nestedSuccessSound nestedRejectSound
            nestedShape (afterAtom.remainingCount + 1) base afterAtom failure
              rejected result)

end Solcore.Syntax.Parser
