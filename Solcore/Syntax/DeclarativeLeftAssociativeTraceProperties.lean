import Solcore.Syntax.DeclarativeLeftAssociativeTraceGrammar
import Solcore.Syntax.DeclarativeCoreExpressionOperatorExactnessProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Independent operand exactness fixes every maximal left-associated trace.
Successful AST uniqueness is at a fixed accumulated base, while rejection
uniqueness and disjointness hold even across different bases. Neither fuel,
progress, window preservation, nor outcome existence is introduced. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte precedence : Nat}

theorem LeftAssociativeTailTraceParses.result_unique
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input afterLeft afterRight : Remainder} {base left right : Syntax.Expr}
    {leftEvents rightEvents : List ParseDiagnostic}
    (leftParsed : LeftAssociativeTailTraceParses operandTrace precedence source endByte input base left afterLeft leftEvents)
    (rightParsed : LeftAssociativeTailTraceParses operandTrace precedence source endByte input base right afterRight rightEvents) :
    left = right ∧ afterLeft = afterRight ∧ leftEvents = rightEvents := by
  induction leftParsed generalizing right afterRight rightEvents with
  | done absent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl, rfl⟩
      | next operatorParsed _ _ => exact False.elim (absent.not_parses operatorParsed)
  | next leftOperator leftOperand leftTail ih =>
      cases rightParsed with
      | done absent => exact False.elim (absent.not_parses leftOperator)
      | next rightOperator rightOperand rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          rcases outcomes.successResultUnique leftOperand rightOperand with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LeftAssociativeTailTraceRejects.result_unique
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftBase rightBase : Syntax.Expr}
    {leftReport rightReport : ParseDiagnostic} {leftEvents rightEvents : List ParseDiagnostic}
    (left : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
      input leftBase afterLeft leftReport leftEvents)
    (right : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
      input rightBase afterRight rightReport rightEvents) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftEvents = rightEvents := by
  induction left generalizing rightBase afterRight rightReport rightEvents with
  | rightRejected leftOperator leftRejected =>
      cases right with
      | rightRejected rightOperator rightRejected =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          exact outcomes.rejectResultUnique leftRejected rightRejected
      | laterRejected rightOperator rightParsed rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          exact False.elim (outcomes.successRejectDisjoint leftRejected ⟨_, _, _, rightParsed⟩)
  | laterRejected leftOperator leftParsed leftTail ih =>
      cases right with
      | rightRejected rightOperator rightRejected =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          exact False.elim (outcomes.successRejectDisjoint rightRejected ⟨_, _, _, leftParsed⟩)
      | laterRejected rightOperator rightParsed rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨rfl, rfl⟩
          rcases outcomes.successResultUnique leftParsed rightParsed with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LeftAssociativeTailTraceRejects.disjoint_success
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input rejected : Remainder} {base : Syntax.Expr} {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (rejection : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
      input base rejected report events) :
    ¬ ∃ otherBase value after trace,
      LeftAssociativeTailTraceParses operandTrace precedence source endByte input otherBase value after trace := by
  induction rejection with
  | rightRejected rejectedOperator rejectedOperand =>
      rintro ⟨otherBase, value, after, trace, parsed⟩
      cases parsed with
      | done absent => exact absent.not_parses rejectedOperator
      | next parsedOperator parsedOperand parsedTail =>
          rcases rejectedOperator.result_unique parsedOperator with ⟨rfl, rfl⟩
          exact outcomes.successRejectDisjoint rejectedOperand ⟨_, _, _, parsedOperand⟩
  | laterRejected rejectedOperator parsedOperand rejectedTail ih =>
      rintro ⟨otherBase, value, after, trace, parsed⟩
      cases parsed with
      | done absent => exact absent.not_parses rejectedOperator
      | next parsedOperator otherOperand parsedTail =>
          rcases rejectedOperator.result_unique parsedOperator with ⟨rfl, rfl⟩
          rcases outcomes.successResultUnique parsedOperand otherOperand with ⟨rfl, rfl, rfl⟩
          exact ih ⟨_, _, _, _, parsedTail⟩

theorem leftAssociativeTailTraceExactOutcomeSpec
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte) (precedence : Nat) (base : Syntax.Expr) :
    TraceExactOutcomeSpec
      (fun source endByte input value after trace =>
        LeftAssociativeTailTraceParses operandTrace precedence source endByte input base value after trace)
      (fun source endByte input after report trace =>
        LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte input base after report trace)
      source endByte where
  successResultUnique := LeftAssociativeTailTraceParses.result_unique outcomes
  rejectResultUnique := LeftAssociativeTailTraceRejects.result_unique outcomes
  successRejectDisjoint := by
    intro input rejected report trace rejection
    rintro ⟨value, after, events, parsed⟩
    exact rejection.disjoint_success outcomes ⟨base, value, after, events, parsed⟩

theorem LeftAssociativeTraceParses.result_unique
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftEvents rightEvents : List ParseDiagnostic}
    (leftParsed : LeftAssociativeTraceParses operandTrace precedence source endByte input left afterLeft leftEvents)
    (rightParsed : LeftAssociativeTraceParses operandTrace precedence source endByte input right afterRight rightEvents) :
    left = right ∧ afterLeft = afterRight ∧ leftEvents = rightEvents := by
  cases leftParsed with
  | parsed leftOperand leftTail =>
      cases rightParsed with
      | parsed rightOperand rightTail =>
          rcases outcomes.successResultUnique leftOperand rightOperand with ⟨rfl, rfl, rfl⟩
          rcases leftTail.result_unique outcomes rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LeftAssociativeTraceRejects.result_unique
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftEvents rightEvents : List ParseDiagnostic}
    (left : LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte
      input afterLeft leftReport leftEvents)
    (right : LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte
      input afterRight rightReport rightEvents) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftEvents = rightEvents := by
  cases left with
  | firstRejected leftRejected =>
      cases right with
      | firstRejected rightRejected => exact outcomes.rejectResultUnique leftRejected rightRejected
      | tailRejected rightParsed rightTail => exact False.elim (outcomes.successRejectDisjoint leftRejected ⟨_, _, _, rightParsed⟩)
  | tailRejected leftParsed leftTail =>
      cases right with
      | firstRejected rightRejected => exact False.elim (outcomes.successRejectDisjoint rightRejected ⟨_, _, _, leftParsed⟩)
      | tailRejected rightParsed rightTail =>
          rcases outcomes.successResultUnique leftParsed rightParsed with ⟨rfl, rfl, rfl⟩
          rcases leftTail.result_unique outcomes rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LeftAssociativeTraceRejects.disjoint_success
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (rejection : LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte input rejected report events) :
    ¬ ∃ value after trace, LeftAssociativeTraceParses operandTrace precedence source endByte input value after trace := by
  rintro ⟨value, after, trace, parsed⟩
  cases parsed with
  | parsed parsedOperand parsedTail =>
      cases rejection with
      | firstRejected rejectedOperand => exact outcomes.successRejectDisjoint rejectedOperand ⟨_, _, _, parsedOperand⟩
      | tailRejected otherOperand rejectedTail =>
          rcases outcomes.successResultUnique parsedOperand otherOperand with ⟨rfl, rfl, rfl⟩
          exact rejectedTail.disjoint_success outcomes ⟨_, _, _, _, parsedTail⟩

theorem leftAssociativeTraceExactOutcomeSpec
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects source endByte) (precedence : Nat) :
    TraceExactOutcomeSpec (LeftAssociativeTraceParses operandTrace precedence)
      (LeftAssociativeTraceRejects operandTrace operandRejects precedence) source endByte where
  successResultUnique := LeftAssociativeTraceParses.result_unique outcomes
  rejectResultUnique := LeftAssociativeTraceRejects.result_unique outcomes
  successRejectDisjoint := LeftAssociativeTraceRejects.disjoint_success outcomes

end Solcore.Syntax.DeclarativeGrammar
