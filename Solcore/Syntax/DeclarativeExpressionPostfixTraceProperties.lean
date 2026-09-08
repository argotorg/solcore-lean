import Solcore.Syntax.DeclarativeExpressionPostfixTraceGrammar
import Solcore.Syntax.DeclarativePostfixTailRejectionTraceProperties

/-! Exact independent atom and nested outcomes determine the complete postfix
AST, endpoint, first terminal report, and ordered event sequence. This joint
bundle states uniqueness and disjointness, not existence or parser totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {atomTrace nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ExpressionPostfixTraceParses.result_unique
    (atoms : TraceExactOutcomeSpec atomTrace atomRejects source endByte)
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftEvents rightEvents : List ParseDiagnostic}
    (leftParsed : ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input left afterLeft leftEvents)
    (rightParsed : ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input right afterRight rightEvents) :
    left = right ∧ afterLeft = afterRight ∧ leftEvents = rightEvents := by
  cases leftParsed with
  | parsed leftAtom leftTail =>
      cases rightParsed with
      | parsed rightAtom rightTail =>
          rcases atoms.successResultUnique leftAtom rightAtom with ⟨rfl, rfl, rfl⟩
          rcases leftTail.result_unique nested rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionPostfixTraceRejects.result_unique
    (atoms : TraceExactOutcomeSpec atomTrace atomRejects source endByte)
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftEvents rightEvents : List ParseDiagnostic}
    (left : ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
      input afterLeft leftReport leftEvents)
    (right : ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
      input afterRight rightReport rightEvents) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftEvents = rightEvents := by
  cases left with
  | atomRejected leftAtom =>
      cases right with
      | atomRejected rightAtom => exact atoms.rejectResultUnique leftAtom rightAtom
      | tailRejected rightAtom rightTail => exact False.elim (atoms.successRejectDisjoint leftAtom ⟨_, _, _, rightAtom⟩)
  | tailRejected leftAtom leftTail =>
      cases right with
      | atomRejected rightAtom => exact False.elim (atoms.successRejectDisjoint rightAtom ⟨_, _, _, leftAtom⟩)
      | tailRejected rightAtom rightTail =>
          rcases atoms.successResultUnique leftAtom rightAtom with ⟨rfl, rfl, rfl⟩
          rcases leftTail.result_unique nested rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionPostfixTraceRejects.disjoint_success
    (atoms : TraceExactOutcomeSpec atomTrace atomRejects source endByte)
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects source endByte
      input rejected report trace) :
    ¬ ∃ value after events, ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input value after events := by
  rintro ⟨value, after, events, parsed⟩
  cases parsed with
  | parsed atom tail =>
      cases rejection with
      | atomRejected rejectedAtom => exact atoms.successRejectDisjoint rejectedAtom ⟨_, _, _, atom⟩
      | tailRejected otherAtom rejectedTail =>
          rcases atoms.successResultUnique atom otherAtom with ⟨rfl, rfl, rfl⟩
          exact rejectedTail.disjoint_success nested ⟨_, _, _, _, tail⟩

theorem expressionPostfixTraceExactOutcomeSpec
    (atoms : TraceExactOutcomeSpec atomTrace atomRejects source endByte)
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte) :
    TraceExactOutcomeSpec
      (ExpressionPostfixTraceParses atomTrace nestedTrace)
      (ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects) source endByte where
  successResultUnique := ExpressionPostfixTraceParses.result_unique atoms nested
  rejectResultUnique := ExpressionPostfixTraceRejects.result_unique atoms nested
  successRejectDisjoint := ExpressionPostfixTraceRejects.disjoint_success atoms nested

end Solcore.Syntax.DeclarativeGrammar
