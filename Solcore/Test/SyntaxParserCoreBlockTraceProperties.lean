import Solcore.Syntax.Parser.CoreBlockTraceCompletenessProperties

/-! Conditional raw-block execution consumers. Existing reverse prefixes are
checked once at closing; only fresh statements contribute statement events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → Remainder → Statement →
    Remainder → List ParseDiagnostic → Prop}

example := @coreBlockItems_success_trace_sound
example := @coreBlock_success_trace_sound
example := @coreBlockItems_trace_success_complete
example := @coreBlockItems_production_trace_success_complete
example := @coreBlock_trace_success_complete

/-- Both directions expose their statement assumptions, and incoming diagnostic
events remain unrestricted. This is not a concrete Core-statement trace claim. -/
theorem exact_success_under_statement_contracts
    (sound : StatementTraceSuccessSound statement statementTrace)
    (complete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {body : Block} {after : Remainder} {trace : List ParseDiagnostic} :
    CoreBlockTraceParses statementTrace policy.declarative input.file.id input.window.endByte
      input.declarativeRemainder body after trace ↔
    ∃ output, coreBlock statement policy input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  coreBlock_trace_success_iff sound complete contextFrame policy

/-- Successful empty blocks preserve all prior events under both tail policies. -/
theorem empty_block_retains_prior_events
    (complete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {afterOpening after : Remainder} {openingSpan closingSpan : SourceSpan}
    (opening : ExactTokenParses (.symbol .leftBrace)
      input.declarativeRemainder openingSpan afterOpening)
    (closing : ExactTokenParses (.symbol .rightBrace) afterOpening closingSpan after) :
    ∃ output, coreBlock statement policy input = .ok {
        span := SourceSpan.cover openingSpan closingSpan, value := []
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    coreBlock_trace_success_complete complete contextFrame policy
      (.parsed openingSpan closingSpan opening (.close closingSpan closing) .nil)

/-- Two accumulated statements are reversed back into source order, then one
fresh statement is appended. Its duplicate events precede the three distinct
tail-check events; accumulated statements contribute no replayed parse events. -/
theorem reverse_prefix_is_checked_once_after_fresh_events
    (complete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (opening : Token)
    {input : State} {beforeClose after : Remainder} {closingSpan : SourceSpan}
    (first second fresh : Statement) (event : ParseDiagnostic)
    (inside : input.cursor < input.window.endIndex)
    (notClosing : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.symbol .rightBrace))
    (freshParsed : statementTrace input.file.id input.window.endByte
      input.declarativeRemainder fresh beforeClose [event, event])
    (progress : input.cursor < beforeClose.cursor)
    (closing : ExactTokenParses (.symbol .rightBrace) beforeClose closingSpan after)
    (firstMissing : ¬ CoreBlockStatementTerminated first)
    (secondMissing : ¬ CoreBlockStatementTerminated second)
    (freshMissing : ¬ CoreBlockStatementTerminated fresh) :
    ∃ output, coreBlockItems statement opening .require
        (input.remainingCount + 1) [second, first] input = .ok {
          span := SourceSpan.cover opening.span closingSpan, value := [first, second, fresh]
        } output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ [event, event,
        { span := first.span, kind := .constraintViolation .expressionRequiresSemicolon },
        { span := second.span, kind := .constraintViolation .expressionRequiresSemicolon },
        { span := fresh.span, kind := .constraintViolation .expressionRequiresSemicolon }] := by
  have items : CoreBlockItemsTraceParses statementTrace input.file.id input.window.endByte
      input.declarativeRemainder [fresh] closingSpan after [event, event] :=
    .next inside notClosing freshParsed progress (.close closingSpan closing)
  have validated : CoreBlockTailsDiagnosticTrace .require
      ([second, first].reverse ++ [fresh]) [
        { span := first.span, kind := .constraintViolation .expressionRequiresSemicolon },
        { span := second.span, kind := .constraintViolation .expressionRequiresSemicolon },
        { span := fresh.span, kind := .constraintViolation .expressionRequiresSemicolon }] :=
    .cons (.missing firstMissing) (.cons (.missing secondMissing) (.lastRequired (.missing freshMissing)))
  exact coreBlockItems_production_trace_success_complete complete contextFrame
    opening .require [second, first] items validated

/-- The allow policy exempts only the fresh final expression's tail report.
The previous expression still reports after the fresh statement's own event. -/
theorem allow_preserves_prior_tail_error_after_fresh_event
    (complete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (opening : Token)
    {input : State} {beforeClose after : Remainder} {closingSpan : SourceSpan}
    (earlier fresh : Statement) (event : ParseDiagnostic)
    (inside : input.cursor < input.window.endIndex)
    (notClosing : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.symbol .rightBrace))
    (freshParsed : statementTrace input.file.id input.window.endByte
      input.declarativeRemainder fresh beforeClose [event])
    (progress : input.cursor < beforeClose.cursor)
    (closing : ExactTokenParses (.symbol .rightBrace) beforeClose closingSpan after)
    (earlierMissing : ¬ CoreBlockStatementTerminated earlier) :
    ∃ output, coreBlockItems statement opening .allow
        (input.remainingCount + 1) [earlier] input = .ok {
          span := SourceSpan.cover opening.span closingSpan, value := [earlier, fresh]
        } output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ [event,
        { span := earlier.span, kind := .constraintViolation .expressionRequiresSemicolon }] :=
  coreBlockItems_production_trace_success_complete complete contextFrame opening .allow [earlier]
    (.next inside notClosing freshParsed progress (.close closingSpan closing))
    (.cons (.missing earlierMissing) .lastAllowed)

end Solcore.Test.SyntaxParserCoreBlockTraceProperties
