import Solcore.Syntax.Parser.DotConstructorSuccessTraceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.DeclarativeDotConstructorTraceProtectionProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Concrete wrappers with arbitrary prior diagnostics: absent/empty argument
branches bypass any child, and real checked-name arguments retain exact order. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxDotConstructorSuccessTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @DotConstructorTraceParses.ordinary
example := @DotConstructorTraceParses.result_unique
example := @dotConstructor_trace_success_iff

theorem missing_parenthesis_keeps_entire_state (nested : Parser Expr) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .leftParen)) :
    optionalDotConstructorArguments nested input = .ok none input :=
  optionalDotConstructorArguments_eq_none_of_absent nested absent

/-- No-argument constructors need no child contract, and use the name's span as endpoint. -/
theorem no_arguments_bypasses_any_child (nested : Parser Expr)
    {input : State} {dotSpan : SourceSpan} {name : Identifier} {afterDot afterName : Remainder}
    {nameEvents : List ParseDiagnostic}
    (dot : ExactTokenParses (.symbol .dot) input.declarativeRemainder dotSpan afterDot)
    (nameParsed : ExpressionNameTraceParses input.file.id input.window.endByte
      afterDot name afterName nameEvents)
    (absent : TokenKindAbsentAt afterName.tokens afterName.endIndex afterName.cursor (.symbol .leftParen)) :
    dotConstructor nested input = .ok {
      span := SourceSpan.cover dotSpan name.span
      value := .dotConstructor dotSpan name none } { input with
        cursor := input.cursor + 2
        diagnosticsRev := nameEvents.reverse ++ input.diagnosticsRev } := by
  have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dot
  rcases dot with ⟨_, rfl⟩
  have nameResult := expressionName_eq_ok_of_trace
    (input := { input with cursor := input.cursor + 1 }) nameParsed
  have absentNext : TokenKindAbsentAt input.tokens input.window.endIndex
      (input.cursor + 2) (.symbol .leftParen) := by
    simpa only [nameParsed.output_eq, State.declarativeRemainder] using absent
  have argsResult := optionalDotConstructorArguments_eq_none_of_absent nested
    (input := { input with
      cursor := input.cursor + 2
      diagnosticsRev := nameEvents.reverse ++ input.diagnosticsRev }) absentNext
  exact dotConstructor_success_iff_components.mpr
    ⟨_, _, name, _, none, dotResult, nameResult, argsResult, rfl⟩

/-- Boolean-first names remain identifier-shaped in the constructor AST and emit nothing. -/
theorem boolean_constructor_without_arguments_is_silent (nested : Parser Expr)
    {input : State} {dotSpan nameSpan : SourceSpan} {afterDot afterName : Remainder}
    (dot : ExactTokenParses (.symbol .dot) input.declarativeRemainder dotSpan afterDot)
    (name : ExactTokenParses (.keyword .trueKw) afterDot nameSpan afterName)
    (absent : TokenKindAbsentAt afterName.tokens afterName.endIndex afterName.cursor (.symbol .leftParen)) :
    dotConstructor nested input = .ok {
      span := SourceSpan.cover dotSpan nameSpan
      value := .dotConstructor dotSpan { span := nameSpan, value := "true" } none }
      { input with cursor := input.cursor + 2 } := by
  have parsed : ExpressionNameTraceParses input.file.id input.window.endByte afterDot
      { span := nameSpan, value := "true" } afterName [] := by
    rcases name with ⟨token, rfl⟩
    exact .boolean ⟨.trueKeyword token, rfl⟩
  simpa only [List.reverse_nil, List.nil_append] using
    no_arguments_bypasses_any_child nested dot parsed absent

/-- Empty written parentheses are some empty list, never the absent-argument case. -/
theorem empty_arguments_bypasses_any_child (nested : Parser Expr)
    {input : State} {openingSpan closingSpan : SourceSpan} {afterOpening after : Remainder}
    (opening : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (closing : ExactTokenParses (.symbol .rightParen) afterOpening closingSpan after) :
    optionalDotConstructorArguments nested input = .ok
      (some { span := SourceSpan.cover openingSpan closingSpan, elements := [] })
      { input with cursor := input.cursor + 2 } := by
  rw [optionalDotConstructorArguments_eq_of_present nested opening.1]
  have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
  rcases opening with ⟨_, rfl⟩
  have closingPresent := DelimitedTraceInternals.symbol_present .rightParen
    (input := { input with cursor := input.cursor + 1 }) closing
  have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .expression
    (input := { input with cursor := input.cursor + 1 }) closing
  simp only [delimitedNoTrailing, delimitedWithPolicy, openingResult, Bool.true_and,
    closingPresent, if_true, closeDelimited, closingResult, List.reverse_nil]

private theorem checked_name_trace {source : SourceId} {endByte : Nat}
    {input output : Remainder} {name : Identifier}
    (parsed : IdentifierParses input name output) (hyphen : IdentifierHyphenSpelling name.value) :
    ExpressionNameTraceParses source endByte input name output
      [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨span, keyword⟩ <;>
      have tokenEq := parsed.1.token_unique keyword <;> cases tokenEq
  exact .identifier absent (.parsed parsed (.hyphen hyphen))

/-- Real constructor/name arguments contribute three separate events. The
outer dot, name, and written-parenthesis spans remain separately observable. -/
theorem checked_constructor_and_arguments_keep_event_order
    {input : State} {dotSpan openingSpan commaSpan closingSpan : SourceSpan}
    {name first second : Identifier}
    {afterDot afterName afterOpening afterFirst afterComma afterSecond after : Remainder}
    (dot : ExactTokenParses (.symbol .dot) input.declarativeRemainder dotSpan afterDot)
    (nameParsed : IdentifierParses afterDot name afterName)
    (nameHyphen : IdentifierHyphenSpelling name.value)
    (opening : ExactTokenParses (.symbol .leftParen) afterName openingSpan afterOpening)
    (firstParsed : IdentifierParses afterOpening first afterFirst)
    (firstHyphen : IdentifierHyphenSpelling first.value)
    (comma : ExactTokenParses (.symbol .comma) afterFirst commaSpan afterComma)
    (secondParsed : IdentifierParses afterComma second afterSecond)
    (secondHyphen : IdentifierHyphenSpelling second.value)
    (closing : ExactTokenParses (.symbol .rightParen) afterSecond closingSpan after) :
    ∃ output, dotConstructor identifierExpression input = .ok {
        span := SourceSpan.cover dotSpan (SourceSpan.cover openingSpan closingSpan)
        value := .dotConstructor dotSpan name (some {
          span := SourceSpan.cover openingSpan closingSpan
          elements := [{ span := first.span, value := .identifier first },
            { span := second.span, value := .identifier second }] }) } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ [
        { span := name.span, kind := .invalidIdentifierHyphen name.value },
        { span := first.span, kind := .invalidIdentifierHyphen first.value },
        { span := second.span, kind := .invalidIdentifierHyphen second.value }] := by
  have firstAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex
      afterOpening.cursor (.symbol .rightParen) := by
    rintro ⟨span, token⟩; have impossible := firstParsed.1.token_unique token; cases impossible
  have commaAbsent : TokenKindAbsentAt afterSecond.tokens afterSecond.endIndex
      afterSecond.cursor (.symbol .comma) := by
    rintro ⟨span, token⟩; have impossible := closing.1.token_unique token; cases impossible
  apply dotConstructor_trace_success_complete identifierExpression_trace_success_complete
    identifierExpression_success_context
  exact .parsed dotSpan dot (checked_name_trace nameParsed nameHyphen) (.present
    (.nonempty openingSpan closingSpan opening (.absent firstAbsent)
      (IdentifierExpressionTraceParses.parsed (checked_name_trace firstParsed firstHyphen))
      (by rw [firstParsed.2.2.2]; exact Nat.lt_succ_self _)
      (.next commaSpan comma (IdentifierExpressionTraceParses.parsed (checked_name_trace secondParsed secondHyphen))
        (by rw [secondParsed.2.2.2]; exact Nat.lt_succ_self _) (.close commaAbsent closing))))

theorem checked_constructor_filter_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input output : Remainder} {value : Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses IdentifierExpressionTraceParses source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun child => child.cascadeFilters _ _))

end Solcore.Test.SyntaxDotConstructorSuccessTraceProperties
