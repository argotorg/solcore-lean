import Solcore.Syntax.DeclarativePostfixTailRejectionTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceOutcomeProperties
import Solcore.Syntax.DeclarativeIdentifierTraceProperties

/-! Fixed-base postfix success functionality follows from independent child
functionality. No child carrier, progress, parser, or existence law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem NoTrailingDelimitedListTraceParses.opening_present
    {α : Type} {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    {opening closing : Symbol} {allowEmpty : Bool} {input output : Remainder}
    {values : DelimitedList α} {events : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      source endByte input values output events) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol opening } := by
  cases parsed with
  | empty span _ _ token _ | nonempty span _ token _ _ _ _ => exact ⟨span, token.1⟩

private theorem absent_conflicts_exact {kind : TokenKind} {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False := absent ⟨span, parsed.1⟩

private theorem absent_conflicts_token {kind : TokenKind} {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

theorem PostfixTailTraceParses.result_unique
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input afterLeft afterRight : Remainder} {base left right : Syntax.Expr}
    {leftEvents rightEvents : List ParseDiagnostic}
    (leftParsed : PostfixTailTraceParses nestedTrace source endByte input base left afterLeft leftEvents)
    (rightParsed : PostfixTailTraceParses nestedTrace source endByte input base right afterRight rightEvents) :
    left = right ∧ afterLeft = afterRight ∧ leftEvents = rightEvents := by
  have arguments := noTrailingDelimitedListTraceExactOutcomeSpec .leftParen .rightParen true .expression nested
  induction leftParsed generalizing right afterRight rightEvents <;> cases rightParsed <;>
    grind (ematch := 20) [PostfixSuffixAbsentAt, absent_conflicts_exact, absent_conflicts_token,
      ExactTokenParses.result_unique, nested.successResultUnique,
      NoTrailingDelimitedListTraceParses.opening_present,
      arguments.successResultUnique, IdentifierTraceParses.result_unique]

end Solcore.Syntax.DeclarativeGrammar
