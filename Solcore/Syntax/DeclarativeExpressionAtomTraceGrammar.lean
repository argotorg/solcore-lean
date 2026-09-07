import Solcore.Syntax.DeclarativeExpressionAtomRecoveryTraceGrammar
import Solcore.Syntax.DeclarativeCoreExpressionAtomPublicOutcomeGrammar

/-! Public atom outcomes over arbitrary core traces. Rewind preserves the
failed carrier and end index and restores only the original cursor. Boundary
rejection leaves the original report uncommitted; otherwise it is committed
once before standalone recovery. A recovery failure is a separate terminal
report. Unlike ordinary public atom outcomes, no core carrier law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def expressionAtomTraceRewind (input failed : Remainder) : Remainder :=
  { failed with cursor := input.cursor }

inductive ExpressionAtomTraceParses
    (coreTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | core {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
      (parsed : coreTrace source endByte input value output trace) :
      ExpressionAtomTraceParses coreTrace coreRejects source endByte input value output trace
  | recovered {input failed output : Remainder} {value : Syntax.Expr}
      {coreReport : ParseDiagnostic} {coreTraceEvents recoveryTrace : List ParseDiagnostic}
      (coreRejected : coreRejects source endByte input failed coreReport coreTraceEvents)
      (continues : ¬ ExpressionAtomBoundaryStops (expressionAtomTraceRewind input failed))
      (recovered : ExpressionAtomRecoveryTraceParses source endByte
        (expressionAtomTraceRewind input failed) value output recoveryTrace) :
      ExpressionAtomTraceParses coreTrace coreRejects source endByte input value output
        ((coreTraceEvents ++ [coreReport]) ++ recoveryTrace)

inductive ExpressionAtomTraceRejects
    (coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | boundary {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
      (coreRejected : coreRejects source endByte input failed coreReport coreTrace)
      (stops : ExpressionAtomBoundaryStops (expressionAtomTraceRewind input failed)) :
      ExpressionAtomTraceRejects coreRejects source endByte input
        (expressionAtomTraceRewind input failed) coreReport coreTrace
  | recovery {input failed rejected : Remainder} {coreReport report : ParseDiagnostic}
      {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : coreRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ ExpressionAtomBoundaryStops (expressionAtomTraceRewind input failed))
      (recoveryRejected : ExpressionAtomRecoveryTraceRejects source endByte
        (expressionAtomTraceRewind input failed) rejected report recoveryTrace) :
      ExpressionAtomTraceRejects coreRejects source endByte input rejected report
        ((coreTrace ++ [coreReport]) ++ recoveryTrace)

end Solcore.Syntax.DeclarativeGrammar
