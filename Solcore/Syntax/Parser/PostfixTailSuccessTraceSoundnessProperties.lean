import Solcore.Syntax.DeclarativePostfixTailTraceGrammar
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceContextProperties
import Solcore.Syntax.Parser.IdentifierTraceProperties
import Solcore.Syntax.Parser.PragmaItemsContextProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Every successful actual postfix tail retains the exact maximal suffix AST
and ordered nested/name events. Soundness holds for every fuel without a child
progress or ordinary contract; only successful source/full-window context is used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}

theorem postfixTail_trace_success_sound
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block) :
    ∀ fuel base input value output,
      postfixTail nested block fuel base input = .ok value output →
      ∃ trace, PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
        input.declarativeRemainder base value output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro base input value output result; simp [postfixTail] at result
  | succ fuel ih =>
      intro base input value output result
      unfold postfixTail at result
      split at result
      · cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject failure rejected => simp [openingResult] at result
        | ok opening afterOpening =>
            simp only [openingResult] at result
            have openingParsed := symbol_success_exactTokenParses .leftBracket .expression openingResult
            have openingShape := (symbol_ok_tokenAt .leftBracket .expression openingResult).2
            subst afterOpening
            cases indexResult : nested { input with cursor := input.cursor + 1 } with
            | invariant error => simp [indexResult] at result
            | reject failure rejected => simp [indexResult] at result
            | ok index afterIndex =>
                simp only [indexResult] at result
                rcases successSound indexResult with ⟨indexTrace, indexParsed, indexEvents⟩
                have frame := contextFrame indexResult
                cases closingResult : symbol .rightBracket .expression afterIndex with
                | invariant error => simp [closingResult] at result
                | reject failure rejected => simp [closingResult] at result
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    have closingParsed := symbol_success_exactTokenParses .rightBracket .expression closingResult
                    have closingShape := (symbol_ok_tokenAt .rightBracket .expression closingResult).2
                    rcases ih (postfixIndexTraceValue base index opening.span closing.span) afterClosing value output result with
                      ⟨tailTrace, tailParsed, tailEvents⟩
                    refine ⟨indexTrace ++ tailTrace, .index opening.span closing.span openingParsed indexParsed closingParsed ?_, ?_⟩
                    · simpa only [closingShape, frame.1, frame.2] using tailParsed
                    · rw [tailEvents, closingShape]
                      change afterIndex.diagnostics ++ tailTrace = _
                      rw [indexEvents]
                      exact List.append_assoc _ _ _
      · rename_i indexFalse
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftBracket (Bool.eq_false_iff.mpr indexFalse)
        split at result
        · cases argumentsResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              rcases delimitedNoTrailing_success_trace_sound successSound contextFrame
                  .leftParen .rightParen true .expression .expression argumentsResult with
                ⟨argumentTrace, argumentsParsed, argumentEvents⟩
              have frame := delimitedNoTrailing_success_context contextFrame
                .leftParen .rightParen true .expression .expression argumentsResult
              rcases ih (postfixCallTraceValue base arguments) afterArguments value output result with
                ⟨tailTrace, tailParsed, tailEvents⟩
              refine ⟨argumentTrace ++ tailTrace, .call indexAbsent argumentsParsed ?_, ?_⟩
              · simpa only [frame.1, frame.2] using tailParsed
              · rw [tailEvents, argumentEvents]; exact List.append_assoc _ _ _
        · rename_i callFalse
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftParen (Bool.eq_false_iff.mpr callFalse)
          split at result
          · cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject failure rejected => simp [dotResult] at result
            | ok dot afterDot =>
                simp only [dotResult] at result
                have dotParsed := symbol_success_exactTokenParses .dot .expression dotResult
                have dotShape := (symbol_ok_tokenAt .dot .expression dotResult).2
                subst afterDot
                cases nameResult : identifier .expression { input with cursor := input.cursor + 1 } with
                | invariant error => simp [nameResult] at result
                | reject failure rejected => simp [nameResult] at result
                | ok name afterName =>
                    simp only [nameResult] at result
                    rcases identifier_success_trace_sound .expression nameResult with ⟨nameTrace, nameParsed, nameEvents⟩
                    have frame := identifier_success_context_eq .expression nameResult
                    rcases ih (postfixFieldTraceValue base dot.span name) afterName value output result with
                      ⟨tailTrace, tailParsed, tailEvents⟩
                    refine ⟨nameTrace ++ tailTrace, .field dot.span indexAbsent callAbsent dotParsed nameParsed ?_, ?_⟩
                    · simpa only [frame.1, frame.2] using tailParsed
                    · rw [tailEvents, nameEvents]; exact List.append_assoc _ _ _
          · rename_i fieldFalse
            cases result
            exact ⟨[], .done ⟨indexAbsent, callAbsent,
              symbolAbsentAt_of_isSymbol_eq_false .dot (Bool.eq_false_iff.mpr fieldFalse)⟩, (List.append_nil _).symm⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
