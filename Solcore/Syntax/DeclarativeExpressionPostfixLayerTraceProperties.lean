import Solcore.Syntax.DeclarativeExpressionPostfixTraceProperties
import Solcore.Syntax.DeclarativeExpressionAtomLayerTraceProperties

/-! A selected/recovering atom followed by its maximal postfix tail, leaving
only nested-expression and block relations abstract. This is a one-layer
independent relation, not a recursive least closure or existence theorem. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
  (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
  (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
  (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)

abbrev ExpressionPostfixLayerTraceParses :=
  ExpressionPostfixTraceParses (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects)
    nestedTrace

abbrev ExpressionPostfixLayerTraceRejects :=
  ExpressionPostfixTraceRejects (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects)
    nestedTrace (ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects) nestedRejects

variable {nestedTrace nestedRejects blockTrace blockRejects}

theorem expressionPostfixLayerTraceExactOutcomeSpec {source : SourceId} {endByte : Nat}
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte) :
    TraceExactOutcomeSpec (ExpressionPostfixLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects)
      (ExpressionPostfixLayerTraceRejects nestedTrace nestedRejects blockTrace blockRejects) source endByte :=
  expressionPostfixTraceExactOutcomeSpec (expressionAtomLayerTraceExactOutcomeSpec nested blocks) nested

end Solcore.Syntax.DeclarativeGrammar
