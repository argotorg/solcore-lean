import Solcore.Syntax.Parser.TupleClosingTraceProperties

/-! Successful actual parentheses reflect complete appended diagnostic traces.
Tail suffixes exclude the existing reverse prefix, which is used only for AST
assembly at the final closing token. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem tupleTail_success_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) :
    ∀ fuel elementsRev input value output,
      tupleTail nested opening fuel elementsRev input = .ok value output →
      ∃ suffix closingSpan trace,
        value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
          input.declarativeRemainder suffix closingSpan output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input value output result; simp [tupleTail] at result
  | succ fuel ih =>
      intro elementsRev input value output result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          have commaParsed := symbol_success_exactTokenParses .comma .expression commaResult
          have commaState := (symbol_ok_tokenAt .comma .expression commaResult).2
          subst afterComma
          simp only [commaResult] at result
          split at result
          · rcases closeTuple_success_trace_sound opening elementsRev result with
              ⟨closingSpan, closingParsed, valueEq, stateEq⟩
            refine ⟨[], closingSpan, [], by simpa only [List.append_nil] using valueEq,
              .trailing comma.span closingSpan commaParsed closingParsed, ?_⟩
            rw [stateEq]; simp only [State.diagnostics, List.append_nil]
          · rename_i noClose
            have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen (Bool.eq_false_iff.mpr noClose)
            cases childResult : nested { input with cursor := input.cursor + 1 } with
            | invariant error => simp [childResult] at result
            | reject failure rejected => simp [childResult] at result
            | ok child next =>
                simp only [childResult] at result
                split at result
                · rename_i progress
                  rcases successSound childResult with ⟨headEvents, childParsed, childEq⟩
                  split at result
                  · have frame := contextFrame childResult
                    rcases ih (child :: elementsRev) next value output result with
                      ⟨suffix, closingSpan, tailEvents, valueEq, tailParsed, tailEq⟩
                    refine ⟨child :: suffix, closingSpan, headEvents ++ tailEvents, ?_,
                      .next comma.span closingSpan commaParsed closingAbsent childParsed progress ?_, ?_⟩
                    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valueEq
                    · simpa only [frame.1, frame.2] using tailParsed
                    · rw [tailEq, childEq]; exact List.append_assoc _ _ _
                  · rename_i noComma
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma (Bool.eq_false_iff.mpr noComma)
                    rcases closeTuple_success_trace_sound opening (child :: elementsRev) result with
                      ⟨closingSpan, closingParsed, valueEq, stateEq⟩
                    refine ⟨[child], closingSpan, headEvents, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent childParsed progress commaAbsent closingParsed, ?_⟩
                    · simpa only [List.reverse_cons] using valueEq
                    · rw [stateEq]; exact childEq
                · contradiction

theorem parenthesized_trace_success_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceSuccessSound (parenthesized nested)
      (DeclarativeGrammar.ParenthesizedExpressionTraceParses elementTrace) := by
  intro input output value result
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      have openingParsed := symbol_success_exactTokenParses .leftParen .expression openingResult
      have openingState := (symbol_ok_tokenAt .leftParen .expression openingResult).2
      subst afterOpening
      simp only [openingResult] at result
      split at result
      · rcases closeTuple_success_trace_sound opening [] result with ⟨closingSpan, closingParsed, valueEq, stateEq⟩
        refine ⟨[], ?_, ?_⟩
        · rw [valueEq]; exact .empty opening.span closingSpan openingParsed closingParsed
        · rw [stateEq]; simp only [State.diagnostics, List.append_nil]
      · rename_i noClose
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen (Bool.eq_false_iff.mpr noClose)
        cases childResult : nested { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject failure rejected => simp [childResult] at result
        | ok first next =>
            simp only [childResult] at result
            split at result
            · contradiction
            · rename_i noStall
              have progress : input.cursor + 1 < next.cursor := Nat.lt_of_not_ge noStall
              rcases successSound childResult with ⟨headEvents, childParsed, childEq⟩
              split at result
              · have frame := contextFrame childResult
                rcases tupleTail_success_trace_sound successSound contextFrame opening
                    (next.remainingCount + 1) [first] next value output result with
                  ⟨suffix, closingSpan, tailEvents, valueEq, tailParsed, tailEq⟩
                have valueShape : value = DeclarativeGrammar.closeParenthesizedExpression
                    opening.span closingSpan (first :: suffix) := by simpa using valueEq
                refine ⟨headEvents ++ tailEvents, ?_, ?_⟩
                · rw [valueShape]
                  exact .tuple opening.span closingSpan openingParsed closingAbsent childParsed progress
                    (by simpa only [frame.1, frame.2] using tailParsed)
                · rw [tailEq, childEq]; exact List.append_assoc _ _ _
              · rename_i noComma
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma (Bool.eq_false_iff.mpr noComma)
                rcases closeTuple_success_trace_sound opening [first] result with
                  ⟨closingSpan, closingParsed, valueEq, stateEq⟩
                refine ⟨headEvents, ?_, ?_⟩
                · rw [valueEq]
                  exact .group opening.span closingSpan openingParsed closingAbsent childParsed progress commaAbsent closingParsed
                · rw [stateEq]; exact childEq

end Solcore.Syntax.Parser.ExpressionAtomInternals
