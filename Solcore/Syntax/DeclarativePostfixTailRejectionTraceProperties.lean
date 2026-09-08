import Solcore.Syntax.DeclarativePostfixTailTraceProperties

/-! Exact postfix failures and success/rejection disjointness use independent
nested outcome laws only. Earlier events are retained in order; no existence,
recursive parser closure, progress, or carrier law follows from this bundle. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem absent_conflicts_exact {kind : TokenKind} {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False := absent ⟨span, parsed.1⟩

private theorem absent_conflicts_token {kind : TokenKind} {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem identifier_absent_conflicts_trace {input output : Remainder}
    {name : Syntax.Identifier} {events : List ParseDiagnostic}
    (absent : IdentifierAbsentAt input) (parsed : IdentifierTraceParses input name output events) : False := by
  cases parsed with
  | parsed ordinary _ => exact absent ⟨name.span, name.value, ordinary.1⟩

/-- Rejection functionality is independent even of the accumulated base AST. -/
theorem PostfixTailTraceRejects.result_unique
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftBase rightBase : Syntax.Expr}
    {leftReport rightReport : ParseDiagnostic} {leftEvents rightEvents : List ParseDiagnostic}
    (left : PostfixTailTraceRejects nestedTrace nestedRejects source endByte
      input leftBase afterLeft leftReport leftEvents)
    (right : PostfixTailTraceRejects nestedTrace nestedRejects source endByte
      input rightBase afterRight rightReport rightEvents) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftEvents = rightEvents := by
  have arguments := noTrailingDelimitedListTraceExactOutcomeSpec .leftParen .rightParen true .expression nested
  induction left generalizing rightBase afterRight rightReport rightEvents <;> cases right <;>
    grind (ematch := 20) [absent_conflicts_exact, absent_conflicts_token,
      identifier_absent_conflicts_trace, ExactTokenParses.result_unique,
      nested.successResultUnique, nested.rejectResultUnique, nested.successRejectDisjoint,
      NoTrailingDelimitedListTraceParses.opening_present, arguments.successResultUnique,
      arguments.rejectResultUnique, arguments.successRejectDisjoint,
      IdentifierTraceParses.result_unique, RejectAtReports.diagnostic_unique]

/-- The rejected base need not equal the successful base: selection and child
outcomes already exclude every success at this same starting remainder. -/
theorem PostfixTailTraceRejects.disjoint_success
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input rejected : Remainder} {base : Syntax.Expr} {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (rejection : PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report events) :
    ¬ ∃ otherBase value after trace, PostfixTailTraceParses nestedTrace source endByte input otherBase value after trace := by
  have arguments := noTrailingDelimitedListTraceExactOutcomeSpec .leftParen .rightParen true .expression nested
  induction rejection <;> rintro ⟨otherBase, value, after, trace, parsed⟩ <;> cases parsed <;>
    grind (ematch := 20) [PostfixSuffixAbsentAt, absent_conflicts_exact, absent_conflicts_token,
      identifier_absent_conflicts_trace, ExactTokenParses.result_unique,
      nested.successResultUnique, nested.successRejectDisjoint,
      NoTrailingDelimitedListTraceParses.opening_present, arguments.successResultUnique,
      arguments.successRejectDisjoint, IdentifierTraceParses.result_unique]

theorem postfixTailTraceExactOutcomeSpec
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte) (base : Syntax.Expr) :
    TraceExactOutcomeSpec
      (fun source endByte input value after trace => PostfixTailTraceParses nestedTrace source endByte input base value after trace)
      (fun source endByte input after report trace => PostfixTailTraceRejects nestedTrace nestedRejects source endByte
        input base after report trace) source endByte where
  successResultUnique := PostfixTailTraceParses.result_unique nested
  rejectResultUnique := PostfixTailTraceRejects.result_unique nested
  successRejectDisjoint := by
    intro input rejected report trace rejection
    rintro ⟨value, after, events, parsed⟩
    exact rejection.disjoint_success nested ⟨base, value, after, events, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
