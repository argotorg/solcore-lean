import Solcore.Syntax.DeclarativeExpressionTraceOutcomeSpec

/-! Parser-independent exact diagnostic outcomes for arbitrary result types.
This bundle expresses uniqueness and disjointness, not existence or execution.
Expression laws are reusable without assuming token-carrier preservation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

structure TraceExactOutcomeSpec {α : Type}
    (traceParses : SourceId → Nat → Remainder → α →
      Remainder → List ParseDiagnostic → Prop)
    (traceRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop where
  successResultUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    traceParses source endByte input left afterLeft leftTrace →
    traceParses source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace
  rejectResultUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    traceRejects source endByte input afterLeft leftReport leftTrace →
    traceRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace
  successRejectDisjoint : ∀ {input rejected diagnostic trace},
    traceRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, traceParses source endByte input value output events

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ExpressionTraceExactOutcomeSpec.toTraceExactOutcomeSpec
    (expressions : ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte) :
    TraceExactOutcomeSpec expressionTrace expressionRejects source endByte where
  successResultUnique := expressions.successResultUnique
  rejectResultUnique := expressions.rejectResultUnique
  successRejectDisjoint := expressions.successRejectDisjoint

theorem TraceExactOutcomeSpec.toExpressionTraceExactOutcomeSpec
    (expressions : TraceExactOutcomeSpec expressionTrace expressionRejects source endByte) :
    ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte where
  successResultUnique := expressions.successResultUnique
  rejectResultUnique := expressions.rejectResultUnique
  successRejectDisjoint := expressions.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
