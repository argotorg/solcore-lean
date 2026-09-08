import Solcore.Syntax.DeclarativeExpressionAtomDispatchTraceProperties
import Solcore.Syntax.DeclarativeExpressionAtomTraceProperties

/-! One public atom layer: prioritized raw traces followed by cursor-only
rewind/recovery. Recursive expression and block relations remain explicit;
the joint bundle still expresses only uniqueness and disjointness. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
  (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
  (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
  (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)

abbrev ExpressionAtomLayerTraceParses :=
  ExpressionAtomTraceParses (ExpressionAtomDispatchTraceParses nestedTrace blockTrace)
    (ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects)

abbrev ExpressionAtomLayerTraceRejects :=
  ExpressionAtomTraceRejects (ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects)

variable {nestedTrace nestedRejects blockTrace blockRejects}

theorem expressionAtomLayerTraceExactOutcomeSpec {source : SourceId} {endByte : Nat}
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte) :
    TraceExactOutcomeSpec (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects)
      (ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects) source endByte :=
  expressionAtomTraceExactOutcomeSpec (expressionAtomDispatchTraceExactOutcomeSpec nested blocks)

end Solcore.Syntax.DeclarativeGrammar
