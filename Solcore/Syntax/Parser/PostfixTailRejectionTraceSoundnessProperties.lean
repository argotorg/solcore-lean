import Solcore.Syntax.DeclarativePostfixTailRejectionTraceGrammar
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingRejectionTraceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceContextProperties
import Solcore.Syntax.Parser.IdentifierTraceProperties
import Solcore.Syntax.Parser.PragmaItemsContextProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Every ordinary postfix-tail rejection retains the exact first report and
ordered child/name events. The selected opening symbols are silent and cannot
reject. Successful child context is explicit; no child rejection frame,
progress, totality, validity, or fuel-adequacy premise is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem postfixTail_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block) :
    ∀ fuel base input failure rejected,
      postfixTail nested block fuel base input = .reject failure rejected →
      ∃ trace, PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
        input.declarativeRemainder base rejected.declarativeRemainder failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro base input failure rejected result; simp [postfixTail] at result
  | succ fuel ih =>
      intro base input failure rejected result
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .leftBracket .expression indexed with
          ⟨opening, openingResult⟩
        have openingParsed := symbol_success_exactTokenParses .leftBracket .expression openingResult
        simp only [indexed, if_true, openingResult] at result
        cases indexResult : nested { input with cursor := input.cursor + 1 } with
        | invariant error => simp [indexResult] at result
        | reject actual next =>
            simp only [indexResult] at result
            cases result
            rcases rejectSound indexResult with ⟨trace, rejection, events⟩
            exact ⟨trace, .indexNestedRejected opening.span openingParsed rejection, events⟩
        | ok index next =>
            simp only [indexResult] at result
            rcases successSound indexResult with ⟨indexEvents, indexParsed, indexEq⟩
            have frame := contextFrame indexResult
            cases closingResult : symbol .rightBracket .expression next with
            | invariant error => simp [closingResult] at result
            | reject actual afterClosing =>
                simp only [closingResult] at result
                cases result
                have same := symbol_reject_state_eq .rightBracket .expression closingResult
                subst rejected
                have reported := (symbol_reject_reports_iff .rightBracket .expression).mpr
                  ⟨failure, closingResult, rfl⟩
                refine ⟨indexEvents, .indexClosingMissing opening.span openingParsed indexParsed reported.1 ?_, indexEq⟩
                simpa only [frame.1, frame.2] using reported.2
            | ok closing afterClosing =>
                simp only [closingResult] at result
                have closingParsed := symbol_success_exactTokenParses .rightBracket .expression closingResult
                have closingShape := (symbol_ok_tokenAt .rightBracket .expression closingResult).2
                rcases ih (postfixIndexTraceValue base index opening.span closing.span)
                    afterClosing failure rejected result with ⟨tailEvents, tail, tailEq⟩
                refine ⟨indexEvents ++ tailEvents,
                  .indexLaterRejected opening.span closing.span openingParsed indexParsed closingParsed ?_, ?_⟩
                · simpa only [closingShape, frame.1, frame.2] using tail
                · have closingEvents : afterClosing.diagnostics = next.diagnostics := by rw [closingShape]; rfl
                  rw [tailEq, closingEvents, indexEq]
                  exact List.append_assoc _ _ _
      · have indexedFalse := Bool.eq_false_iff.mpr indexed
        simp only [indexedFalse, Bool.false_eq_true, if_false] at result
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftBracket indexedFalse
        by_cases called : isSymbol input .leftParen = true
        · simp only [called, if_true] at result
          cases argumentsResult : delimitedNoTrailing .leftParen .rightParen true nested
              .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject actual next =>
              simp only [argumentsResult] at result
              cases result
              rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression called with
                ⟨opening, openingResult⟩
              rcases delimitedNoTrailing_reject_trace_sound successSound rejectSound contextFrame
                  .leftParen .rightParen true .expression .expression argumentsResult with
                ⟨trace, rejection, events⟩
              exact ⟨trace, .callArgumentsRejected opening.span indexAbsent
                (symbol_success_exactTokenParses .leftParen .expression openingResult).1 rejection, events⟩
          | ok arguments next =>
              simp only [argumentsResult] at result
              rcases delimitedNoTrailing_success_trace_sound successSound contextFrame
                  .leftParen .rightParen true .expression .expression argumentsResult with
                ⟨argumentEvents, argumentsParsed, argumentsEq⟩
              have frame := delimitedNoTrailing_success_context contextFrame
                .leftParen .rightParen true .expression .expression argumentsResult
              rcases ih (postfixCallTraceValue base arguments) next failure rejected result with
                ⟨tailEvents, tail, tailEq⟩
              refine ⟨argumentEvents ++ tailEvents, .callLaterRejected indexAbsent argumentsParsed ?_, ?_⟩
              · simpa only [frame.1, frame.2] using tail
              · rw [tailEq, argumentsEq]; exact List.append_assoc _ _ _
        · have calledFalse := Bool.eq_false_iff.mpr called
          simp only [calledFalse, Bool.false_eq_true, if_false] at result
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftParen calledFalse
          by_cases field : isSymbol input .dot = true
          · rcases symbol_eq_ok_of_isSymbol_eq_true .dot .expression field with ⟨dot, dotResult⟩
            have dotParsed := symbol_success_exactTokenParses .dot .expression dotResult
            simp only [field, if_true, dotResult] at result
            cases nameResult : identifier .expression { input with cursor := input.cursor + 1 } with
            | invariant error => simp [nameResult] at result
            | reject actual next =>
                simp only [nameResult] at result
                cases result
                have same := identifier_reject_state_eq .expression nameResult
                subst rejected
                have reported := (identifier_reject_reports_iff .expression).mpr ⟨failure, nameResult, rfl⟩
                exact ⟨[], .fieldNameRejected dot.span indexAbsent callAbsent dotParsed reported.1 reported.2,
                  by simp only [List.append_nil]; rfl⟩
            | ok name next =>
                simp only [nameResult] at result
                rcases identifier_success_trace_sound .expression nameResult with ⟨nameEvents, nameParsed, nameEq⟩
                have frame := identifier_success_context_eq .expression nameResult
                rcases ih (postfixFieldTraceValue base dot.span name) next failure rejected result with
                  ⟨tailEvents, tail, tailEq⟩
                refine ⟨nameEvents ++ tailEvents,
                  .fieldLaterRejected dot.span indexAbsent callAbsent dotParsed nameParsed ?_, ?_⟩
                · simpa only [frame.1, frame.2] using tail
                · rw [tailEq, nameEq]; exact List.append_assoc _ _ _
          · have fieldFalse := Bool.eq_false_iff.mpr field
            simp [fieldFalse] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals
