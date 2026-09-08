import Solcore.Syntax.DeclarativeExpressionUnaryTraceGrammar
import Solcore.Syntax.DeclarativeCoreExpressionOperatorExactnessProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Maximal unary-prefix determinism and independent postfix exactness fix
the complete wrapped AST, remainder, ordered events, and terminal report.
The joint bundle states only uniqueness/disjointness, never existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {postfixTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ExpressionUnaryTraceParses.result_unique
    (outcomes : TraceExactOutcomeSpec postfixTrace postfixRejects source endByte)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionUnaryTraceParses postfixTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionUnaryTraceParses postfixTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftPrefix leftPostfix =>
      cases rightParsed with
      | parsed rightPrefix rightPostfix =>
          rcases leftPrefix.result_unique rightPrefix with ⟨rfl, rfl⟩
          rcases outcomes.successResultUnique leftPostfix rightPostfix with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionUnaryTraceRejects.result_unique
    (outcomes : TraceExactOutcomeSpec postfixTrace postfixRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ExpressionUnaryTraceRejects postfixRejects source endByte input afterLeft leftReport leftTrace)
    (right : ExpressionUnaryTraceRejects postfixRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | postfixRejected leftPrefix leftPostfix =>
      cases right with
      | postfixRejected rightPrefix rightPostfix =>
          have same := leftPrefix.output_unique rightPrefix
          cases same
          exact outcomes.rejectResultUnique leftPostfix rightPostfix

theorem ExpressionUnaryTraceRejects.disjoint_success
    (outcomes : TraceExactOutcomeSpec postfixTrace postfixRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionUnaryTraceRejects postfixRejects source endByte input rejected report trace) :
    ¬ ∃ value after events, ExpressionUnaryTraceParses postfixTrace source endByte input value after events := by
  rintro ⟨value, after, events, parsed⟩
  cases rejection with
  | postfixRejected rejectedPrefix rejectedPostfix =>
      cases parsed with
      | parsed parsedPrefix parsedPostfix =>
          have same := rejectedPrefix.output_unique parsedPrefix
          cases same
          exact outcomes.successRejectDisjoint rejectedPostfix ⟨_, _, _, parsedPostfix⟩

theorem expressionUnaryTraceExactOutcomeSpec
    (outcomes : TraceExactOutcomeSpec postfixTrace postfixRejects source endByte) :
    TraceExactOutcomeSpec (ExpressionUnaryTraceParses postfixTrace)
      (ExpressionUnaryTraceRejects postfixRejects) source endByte where
  successResultUnique := ExpressionUnaryTraceParses.result_unique outcomes
  rejectResultUnique := ExpressionUnaryTraceRejects.result_unique outcomes
  successRejectDisjoint := ExpressionUnaryTraceRejects.disjoint_success outcomes

end Solcore.Syntax.DeclarativeGrammar
