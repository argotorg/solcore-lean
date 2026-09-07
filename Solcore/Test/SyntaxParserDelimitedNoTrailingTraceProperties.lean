import Solcore.Syntax.Parser.DelimitedNoTrailingTraceContextProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceExactnessProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties

/-! Boundary consumers for actual generic delimited parsers. All states may
already carry arbitrary diagnostics; no lexer or general-expression claim. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedNoTrailingTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @NoTrailingDelimitedListTraceParses.ordinary
example := @NoTrailingDelimitedListTraceParses.result_unique
example := @afterDelimitedElement_noTrailing_production_trace_success_iff
example := @delimitedNoTrailing_success_context

/-- The immediate empty branch precedes child execution, even when closing is comma. -/
theorem empty_comma_close_bypasses_any_child {α : Type} (child : Parser α)
    (context : ParseContext) (phase : ParserPhase) {input : State}
    {openingSpan closingSpan : SourceSpan} {afterOpening after : Remainder}
    (marker : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (finish : ExactTokenParses (.symbol .comma) afterOpening closingSpan after) :
    delimitedNoTrailing .leftParen .comma true child context phase input = .ok {
      span := SourceSpan.cover openingSpan closingSpan
      elements := [] } { input with cursor := input.cursor + 2 } := by
  have markerResult := symbol_eq_ok_of_exactTokenParses .leftParen context marker
  rcases marker with ⟨_, rfl⟩
  have present := DelimitedTraceInternals.symbol_present .comma
    (input := { input with cursor := input.cursor + 1 }) finish
  have result := symbol_eq_ok_of_exactTokenParses .comma context
    (input := { input with cursor := input.cursor + 1 }) finish
  simp only [delimitedNoTrailing, delimitedWithPolicy, markerResult, Bool.true_and,
    present, if_true, closeDelimited, result, List.reverse_nil]

/-- Once a first value has been read, a comma is never interpreted as closing. -/
theorem comma_closing_never_completes_a_tail {α : Type} {child : Parser α}
    {childTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    (sound : ParserTraceSuccessSound child childTrace) (frame : ParserSuccessContext child)
    (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (prefixRev : List α) (input output : State) (values : DelimitedList α) :
    afterDelimitedElement child .comma false context phase opening fuel prefixRev input ≠
      .ok values output := by
  intro result
  rcases afterDelimitedElement_noTrailing_success_trace_sound sound frame .comma context phase
      opening fuel prefixRev input values output result with ⟨_, _, _, _, parsed, _⟩
  exact parsed.closing_ne_comma rfl

private def symbolTrace (symbolValue : Symbol) (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (token : Token) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  ExactTokenParses (.symbol symbolValue) input token.span output ∧
    token.value = .symbol symbolValue ∧ trace = []

private theorem symbol_complete (symbolValue : Symbol) (context : ParseContext) :
    ParserTraceSuccessComplete (symbol symbolValue context) (symbolTrace symbolValue) := by
  intro input token after trace parsed
  rcases parsed with ⟨parsed, kindEq, rfl⟩
  rcases token with ⟨span, kind⟩
  cases kindEq
  exact ⟨_, symbol_eq_ok_of_exactTokenParses symbolValue context parsed,
    parsed.2.symm, by simp only [State.diagnostics, List.append_nil]⟩

private theorem symbol_context (symbolValue : Symbol) (context : ParseContext) :
    ParserSuccessContext (symbol symbolValue context) := by
  intro input output value result
  rw [(symbol_ok_tokenAt symbolValue context result).2]
  exact ⟨rfl, rfl⟩

/-- With empty disabled, the first closing token can be the child's own value. -/
theorem nonempty_child_can_consume_first_closing
    (context : ParseContext) (phase : ParserPhase) {input : State}
    {openingSpan valueSpan closingSpan : SourceSpan} {afterOpening afterValue after : Remainder}
    (marker : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (value : ExactTokenParses (.symbol .rightParen) afterOpening valueSpan afterValue)
    (finish : ExactTokenParses (.symbol .rightParen) afterValue closingSpan after) :
    ∃ output, delimitedNoTrailing .leftParen .rightParen false (symbol .rightParen context)
      context phase input = .ok {
        span := SourceSpan.cover openingSpan closingSpan
        elements := [{ span := valueSpan, value := .symbol .rightParen }] } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  have commaAbsent : TokenKindAbsentAt afterValue.tokens afterValue.endIndex
      afterValue.cursor (.symbol .comma) := by
    rintro ⟨span, comma⟩
    have tokenEq := comma.token_unique finish.1
    cases tokenEq
  have valueTrace : symbolTrace .rightParen input.file.id input.window.endByte afterOpening
      { span := valueSpan, value := .symbol .rightParen } afterValue [] := ⟨value, rfl, rfl⟩
  have parsed : NoTrailingDelimitedListTraceParses .leftParen .rightParen false
      (symbolTrace .rightParen) input.file.id input.window.endByte input.declarativeRemainder
      { span := SourceSpan.cover openingSpan closingSpan,
        elements := [{ span := valueSpan, value := .symbol .rightParen }] } after [] :=
    .nonempty openingSpan closingSpan marker .disabled valueTrace
      (by rw [value.2]; exact Nat.lt_succ_self _) (.close commaAbsent finish)
  simpa only [List.append_nil] using delimitedNoTrailing_trace_success_complete
    (symbol_complete .rightParen context) (symbol_context .rightParen context)
    .leftParen .rightParen false context phase parsed

private theorem name_trace {source : SourceId} {endByte : Nat}
    {input output : Remainder} {name : Identifier}
    (parsed : IdentifierParses input name output) (hyphen : IdentifierHyphenSpelling name.value) :
    IdentifierExpressionTraceParses source endByte input { span := name.span, value := .identifier name }
      output [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨span, keyword⟩ <;>
      have tokenEq := parsed.1.token_unique keyword <;> cases tokenEq
  exact .parsed (.identifier absent (.parsed parsed (.hyphen hyphen)))

/-- The actual checked-name leaf appends both exact spelling events in written order. -/
theorem checked_name_list_keeps_complete_event_order
    (context : ParseContext) (phase : ParserPhase) {input : State}
    {openingSpan commaSpan closingSpan : SourceSpan} {first second : Identifier}
    {afterOpening afterFirst afterComma afterSecond after : Remainder}
    (marker : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (firstParsed : IdentifierParses afterOpening first afterFirst)
    (firstHyphen : IdentifierHyphenSpelling first.value)
    (comma : ExactTokenParses (.symbol .comma) afterFirst commaSpan afterComma)
    (secondParsed : IdentifierParses afterComma second afterSecond)
    (secondHyphen : IdentifierHyphenSpelling second.value)
    (finish : ExactTokenParses (.symbol .rightParen) afterSecond closingSpan after) :
    ∃ output, delimitedNoTrailing .leftParen .rightParen true identifierExpression context phase input =
      .ok { span := SourceSpan.cover openingSpan closingSpan, elements := [
        { span := first.span, value := .identifier first },
        { span := second.span, value := .identifier second }] } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ [
        { span := first.span, kind := .invalidIdentifierHyphen first.value },
        { span := second.span, kind := .invalidIdentifierHyphen second.value }] := by
  have firstAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex
      afterOpening.cursor (.symbol .rightParen) := by
    rintro ⟨span, token⟩; have tokenEq := firstParsed.1.token_unique token; cases tokenEq
  have commaAbsent : TokenKindAbsentAt afterSecond.tokens afterSecond.endIndex
      afterSecond.cursor (.symbol .comma) := by
    rintro ⟨span, token⟩; have tokenEq := finish.1.token_unique token; cases tokenEq
  apply delimitedNoTrailing_trace_success_complete identifierExpression_trace_success_complete
    identifierExpression_success_context .leftParen .rightParen true context phase
  exact .nonempty openingSpan closingSpan marker (.absent firstAbsent)
    (name_trace firstParsed firstHyphen) (by rw [firstParsed.2.2.2]; exact Nat.lt_succ_self _)
    (.next commaSpan comma (name_trace secondParsed secondHyphen)
      (by rw [secondParsed.2.2.2]; exact Nat.lt_succ_self _) (.close commaAbsent finish))

end Solcore.Test.SyntaxParserDelimitedNoTrailingTraceProperties
