import Solcore.Syntax.DeclarativeParenthesizedTraceDisjointnessProperties
import Solcore.Syntax.Parser.ParenthesizedRejectionTraceCorrespondenceProperties

/-! Public consumers of the raw, not dispatcher-selected, boundaries. These
exact-token laws quantify arbitrary parsers, states, and prior diagnostics;
there is no lexical or concrete nested-expression completeness claim. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParenthesizedRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.Parser.DelimitedTraceInternals


theorem unselected_tail_reports_comma_without_calling_child
    (nested : Parser Expr) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} {failure : Failure}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .comma))
    (reported : DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      { head := .symbol .comma, tail := [] } .expression input.declarativeRemainder failure.toDiagnostic) :
    tupleTail nested opening (fuel + 1) elementsRev input = .reject failure input := by
  rcases (symbol_reject_reports_iff .comma .expression).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [tupleTail, result]

theorem unselected_parenthesized_reports_opening_without_calling_child
    (nested : Parser Expr) {input : State} {failure : Failure}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .leftParen))
    (reported : DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      { head := .symbol .leftParen, tail := [] } .expression input.declarativeRemainder failure.toDiagnostic) :
    parenthesized nested input = .reject failure input := by
  rcases (symbol_reject_reports_iff .leftParen .expression).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parenthesized, result]

theorem closing_rejection_preserves_every_state_field
    (opening : Token) (elementsRev : List Expr) {input : State} {failure : Failure}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .rightParen))
    (reported : DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      { head := .symbol .rightParen, tail := [] } .expression input.declarativeRemainder failure.toDiagnostic) :
    closeTuple opening elementsRev input = .reject failure input := by
  rcases (closeTuple_reject_reports_iff opening elementsRev).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  exact result

/-- Even a trailing comma with one prior element closes a group, not a tuple.
The child parser is completely arbitrary and is bypassed at the right paren. -/
theorem trailing_comma_single_element_is_group_without_child
    (nested : Parser Expr) (opening : Token) (only : Expr) (fuel : Nat)
    {input : State} {afterComma after : DeclarativeGrammar.Remainder} (commaSpan closingSpan : SourceSpan)
    (comma : DeclarativeGrammar.ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (closing : DeclarativeGrammar.ExactTokenParses (.symbol .rightParen) afterComma closingSpan after) :
    tupleTail nested opening (fuel + 1) [only] input =
      .ok { span := SourceSpan.cover opening.span closingSpan, value := .group only }
        { input with cursor := input.cursor + 1 + 1 } ∧
      ({ input with cursor := input.cursor + 1 + 1 } : State).declarativeRemainder = after := by
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
  rcases comma with ⟨_, rfl⟩
  have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .expression
    (input := { input with cursor := input.cursor + 1 }) closing
  have selected := symbol_present .rightParen (input := { input with cursor := input.cursor + 1 }) closing
  exact ⟨by simp only [tupleTail, commaResult, selected, if_true, closeTuple_eq_of_symbol, closingResult]
            rfl, closing.2.symm⟩

/-- After a successful child, a non-comma goes directly to a right-paren
failure; no generic comma-or-closing report and no extra event is introduced. -/
theorem first_child_events_survive_right_paren_only_failure
    (nested : Parser Expr) {input next : State} {afterOpening : DeclarativeGrammar.Remainder}
    (openingSpan : SourceSpan) (value : Expr) (failure : Failure) (events : List ParseDiagnostic)
    (opening : DeclarativeGrammar.ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (notEmpty : DeclarativeGrammar.TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
    (child : nested { input with cursor := input.cursor + 1 } = .ok value next)
    (progress : input.cursor + 1 < next.cursor)
    (childEvents : next.diagnostics = input.diagnostics ++ events)
    (noComma : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex next.cursor (.symbol .comma))
    (noClosing : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex next.cursor (.symbol .rightParen))
    (reported : DeclarativeGrammar.RejectAtReports next.file.id next.window.endByte
      { head := .symbol .rightParen, tail := [] } .expression next.declarativeRemainder failure.toDiagnostic) :
    parenthesized nested input = .reject failure next ∧ next.diagnostics = input.diagnostics ++ events := by
  have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
  rcases opening with ⟨_, rfl⟩
  have closingResult := closing_rejection_preserves_every_state_field
    { span := openingSpan, value := .symbol .leftParen } [value] noClosing reported
  have moved : ¬ next.cursor ≤ input.cursor + 1 := by omega
  exact ⟨by simp only [parenthesized, openingResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) notEmpty, Bool.false_eq_true, if_false,
              child, moved, symbol_absent .comma noComma, closingResult], childEvents⟩

end Solcore.Test.SyntaxParenthesizedRejectionTraceProperties
