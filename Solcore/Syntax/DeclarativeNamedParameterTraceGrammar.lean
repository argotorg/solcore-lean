import Solcore.Syntax.DeclarativeNamedParameterCoreTraceGrammar
import Solcore.Syntax.DeclarativeParameterRecoveryTraceGrammar
import Solcore.Syntax.DeclarativeFunctionParameterOutcomeGrammar

/-! Public named-parameter outcomes preserve the failed carrier and end index
while rewinding only its cursor. Boundary rejection commits no terminal report;
otherwise the original report is committed once before standalone recovery.
A later recovery failure is a new, separate uncommitted terminal report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def parameterTraceRewind (input failed : Remainder) : Remainder :=
  { failed with cursor := input.cursor }

inductive NamedParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | core {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (parsed : NamedParameterCoreTraceParses source endByte input value output trace) :
      NamedParameterTraceParses source endByte input value output trace
  | recovered {input failed output : Remainder} {value : Syntax.FunctionParameter}
      {coreReport : ParseDiagnostic} {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : NamedParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ FunctionParameterBoundaryStops (parameterTraceRewind input failed))
      (recovered : FunctionParameterRecoveryTraceParses source endByte
        (parameterTraceRewind input failed) value output recoveryTrace) :
      NamedParameterTraceParses source endByte input value output ((coreTrace ++ [coreReport]) ++ recoveryTrace)

inductive NamedParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | boundary {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
      (coreRejected : NamedParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (stops : FunctionParameterBoundaryStops (parameterTraceRewind input failed)) :
      NamedParameterTraceRejects source endByte input (parameterTraceRewind input failed) coreReport coreTrace
  | recovery {input failed rejected : Remainder} {coreReport report : ParseDiagnostic}
      {coreTrace recoveryTrace : List ParseDiagnostic}
      (coreRejected : NamedParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
      (continues : ¬ FunctionParameterBoundaryStops (parameterTraceRewind input failed))
      (recoveryRejected : FunctionParameterRecoveryTraceRejects source endByte
        (parameterTraceRewind input failed) rejected report recoveryTrace) :
      NamedParameterTraceRejects source endByte input rejected report ((coreTrace ++ [coreReport]) ++ recoveryTrace)

end Solcore.Syntax.DeclarativeGrammar
