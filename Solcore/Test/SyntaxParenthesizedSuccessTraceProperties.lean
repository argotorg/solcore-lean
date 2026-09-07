import Solcore.Syntax.Parser.TupleClosingTraceProperties

/-! Boundary consumers for the bespoke parenthesized parser. Immediate empty
and trailing closes bypass any child, preserve all prior events, and interpret
an already-read singleton as a group even after a comma. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParenthesizedSuccessTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

theorem empty_parentheses_bypass_any_child (nested : Parser Expr)
    {input : State} {openingSpan closingSpan : SourceSpan} {afterOpening after : Remainder}
    (opening : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (closing : ExactTokenParses (.symbol .rightParen) afterOpening closingSpan after) :
    parenthesized nested input = .ok
      (closeParenthesizedExpression openingSpan closingSpan [])
      { input with cursor := input.cursor + 2 } := by
  have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
  rcases opening with ⟨_, rfl⟩
  have present := DelimitedTraceInternals.symbol_present .rightParen
    (input := { input with cursor := input.cursor + 1 }) closing
  have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .expression
    (input := { input with cursor := input.cursor + 1 }) closing
  simp only [parenthesized, openingResult, present, if_true, closeTuple_eq_of_symbol, closingResult,
    List.reverse_nil]

/-- Closing is silent even with an arbitrary accumulated reverse prefix; the
prefix is restored in forward order exactly once and never diagnosed again. -/
theorem trailing_close_bypasses_any_child (nested : Parser Expr) (opening : Token)
    (elementsRev : List Expr) (fuel : Nat) {input : State}
    {commaSpan closingSpan : SourceSpan} {afterComma after : Remainder}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (closing : ExactTokenParses (.symbol .rightParen) afterComma closingSpan after) :
    tupleTail nested opening (fuel + 1) elementsRev input = .ok
      (closeParenthesizedExpression opening.span closingSpan elementsRev.reverse)
      { input with cursor := input.cursor + 2 } := by
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
  rcases comma with ⟨_, rfl⟩
  have present := DelimitedTraceInternals.symbol_present .rightParen
    (input := { input with cursor := input.cursor + 1 }) closing
  have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .expression
    (input := { input with cursor := input.cursor + 1 }) closing
  simp only [tupleTail, commaResult, present, if_true, closeTuple_eq_of_symbol, closingResult]

theorem two_element_prefix_closes_as_forward_tuple (nested : Parser Expr) (opening : Token)
    (first second : Expr) (fuel : Nat) {input : State}
    {commaSpan closingSpan : SourceSpan} {afterComma after : Remainder}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (closing : ExactTokenParses (.symbol .rightParen) afterComma closingSpan after) :
    tupleTail nested opening (fuel + 1) [second, first] input = .ok
      { span := SourceSpan.cover opening.span closingSpan
        value := .tuple { span := SourceSpan.cover opening.span closingSpan, elements := [first, second] } }
      { input with cursor := input.cursor + 2 } :=
  trailing_close_bypasses_any_child nested opening [second, first] fuel comma closing

end Solcore.Test.SyntaxParenthesizedSuccessTraceProperties
