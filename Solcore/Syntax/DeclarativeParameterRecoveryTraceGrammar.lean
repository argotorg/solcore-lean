import Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Standalone parameter recovery retains the existing exact scan and emits
one recovered event at its final error-node span. A missing mandatory first
token rejects without events; its terminal report is separate from the trace.
These judgments do not include the caller's earlier failure commitment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def parameterRecoveryTraceEvent (span : SourceSpan) : ParseDiagnostic :=
  { span, kind := .recovered .functionParameter }

def FunctionParameterRecoveryTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : Syntax.FunctionParameter) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  FunctionParameterRecoveryParses input value output ∧ trace = [parameterRecoveryTraceEvent value.span]

def FunctionParameterRecoveryTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  FunctionParameterRecoveryRejects input rejected ∧
    RejectAtReports source endByte { head := .identifier, tail := [] } .parameter input report ∧ trace = []

end Solcore.Syntax.DeclarativeGrammar
