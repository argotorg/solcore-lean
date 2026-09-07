import Solcore.Syntax.Parser.DelimitedTrailingTraceContextProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceProtectionProperties

/-! The trailing guard bypasses every possible child behavior. A comma-valued
closing delimiter still obeys comma-first priority and consumes two tokens. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.DelimitedTraceInternals

theorem trailing_close_bypasses_any_child {α : Type} (element : Parser α)
    (opening : Token) (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (fuel : Nat) (elementsRev : List α) {input : State}
    {afterComma after : Remainder} {commaSpan closingSpan : SourceSpan}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (finish : ExactTokenParses (.symbol closing) afterComma closingSpan after) :
    afterDelimitedElement element closing true context phase opening (fuel + 1) elementsRev input =
      .ok { span := SourceSpan.cover opening.span closingSpan, elements := elementsRev.reverse }
        { input with cursor := input.cursor + 2 } := by
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma context comma
  have commaPresent := symbol_present .comma comma
  rcases comma with ⟨_, rfl⟩
  have finishResult := symbol_eq_ok_of_exactTokenParses closing context
    (input := { input with cursor := input.cursor + 1 }) finish
  simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.true_and,
    symbol_present closing (input := { input with cursor := input.cursor + 1 }) finish,
    closeDelimited, finishResult]

theorem comma_closing_consumes_two_commas {α : Type} (element : Parser α)
    (opening : Token) (context : ParseContext) (phase : ParserPhase)
    (fuel : Nat) (elementsRev : List α) {input : State}
    {afterComma after : Remainder} {commaSpan closingSpan : SourceSpan}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (finish : ExactTokenParses (.symbol .comma) afterComma closingSpan after) :
    afterDelimitedElement element .comma true context phase opening (fuel + 1) elementsRev input =
      .ok { span := SourceSpan.cover opening.span closingSpan, elements := elementsRev.reverse }
        { input with cursor := input.cursor + 2 } :=
  trailing_close_bypasses_any_child element opening .comma context phase fuel elementsRev comma finish

theorem empty_list_bypasses_any_child {α : Type} (element : Parser α)
    (opening closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    {input : State} {afterOpening after : Remainder} {openingSpan closingSpan : SourceSpan}
    (marker : ExactTokenParses (.symbol opening) input.declarativeRemainder openingSpan afterOpening)
    (finish : ExactTokenParses (.symbol closing) afterOpening closingSpan after) :
    delimited opening closing true element context phase input =
      .ok { span := SourceSpan.cover openingSpan closingSpan, elements := [] }
        { input with cursor := input.cursor + 2 } := by
  have markerResult := symbol_eq_ok_of_exactTokenParses opening context marker
  rcases marker with ⟨_, rfl⟩
  have finishResult := symbol_eq_ok_of_exactTokenParses closing context
    (input := { input with cursor := input.cursor + 1 }) finish
  simp only [delimited, delimitedWithPolicy, markerResult, Bool.true_and,
    symbol_present closing (input := { input with cursor := input.cursor + 1 }) finish,
    if_true, closeDelimited, finishResult, List.reverse_nil]

/-- A single comma selects the child when the following token is not the
comma-valued closing delimiter; the child's exact failure and state escape. -/
theorem single_comma_invokes_child {α : Type} (element : Parser α)
    (opening : Token) (context : ParseContext) (phase : ParserPhase)
    (fuel : Nat) (elementsRev : List α) {input rejected : State} {failure : Failure}
    {afterComma : Remainder} {commaSpan : SourceSpan}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (absent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .comma))
    (child : element { input with cursor := input.cursor + 1 } = .reject failure rejected) :
    afterDelimitedElement element .comma true context phase opening (fuel + 1) elementsRev input =
      .reject failure rejected := by
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma context comma
  have commaPresent := symbol_present .comma comma
  rcases comma with ⟨_, rfl⟩
  simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.true_and,
    symbol_absent .comma (input := { input with cursor := input.cursor + 1 }) absent,
    Bool.false_eq_true, if_false, child]

end Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties
