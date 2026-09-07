import Solcore.Syntax.DeclarativeLambdaParameterCoreTraceGrammar
import Solcore.Syntax.DeclarativeLambdaParameterRecoveryTraceGrammar
import Solcore.Syntax.DeclarativeNamedParameterTraceGrammar

/-! Public lambda parameters reuse the exact cursor-only rewind and boundary
policy. Core events survive rewind; only a non-boundary path commits the core
report before lambda recovery. A recovery rejection has its own uncommitted
terminal report, even when its payload equals the already committed report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive LambdaParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | core {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
      (parsed : LambdaParameterCoreTraceParses source endByte input value output trace) :
      LambdaParameterTraceParses source endByte input value output trace
  | recovered {input failed output : Remainder} {value : Syntax.LambdaParameter}
      {coreReport : ParseDiagnostic} {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : LambdaParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ FunctionParameterBoundaryStops (parameterTraceRewind input failed))
      (recovered : LambdaParameterRecoveryTraceParses source endByte
        (parameterTraceRewind input failed) value output recoveryTrace) :
      LambdaParameterTraceParses source endByte input value output ((coreTrace ++ [coreReport]) ++ recoveryTrace)

inductive LambdaParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | boundary {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
      (coreRejected : LambdaParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (stops : FunctionParameterBoundaryStops (parameterTraceRewind input failed)) :
      LambdaParameterTraceRejects source endByte input (parameterTraceRewind input failed) coreReport coreTrace
  | recovery {input failed rejected : Remainder} {coreReport report : ParseDiagnostic}
      {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : LambdaParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ FunctionParameterBoundaryStops (parameterTraceRewind input failed))
      (recoveryRejected : LambdaParameterRecoveryTraceRejects source endByte
        (parameterTraceRewind input failed) rejected report recoveryTrace) :
      LambdaParameterTraceRejects source endByte input rejected report ((coreTrace ++ [coreReport]) ++ recoveryTrace)

end Solcore.Syntax.DeclarativeGrammar
