import Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Standalone atom recovery consumes its mandatory first token, then uses the
existing boundary-prioritized scan. Exactly one recovered expression-atom
event is emitted at the error span. Missing backing during a scan is a stop;
an unavailable first token instead rejects with a separate expression report.
Any earlier committed caller report is outside these judgments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def expressionAtomRecoveryTraceEvent (span : SourceSpan) : ParseDiagnostic :=
  { span, kind := .recovered .expressionAtom }

def ExpressionAtomRecoveryTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : Syntax.Expr) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  ExpressionAtomRecoveryParses input value output ∧ trace = [expressionAtomRecoveryTraceEvent value.span]

def ExpressionAtomRecoveryTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  ExpressionAtomRecoveryRejects input rejected ∧
    RejectAtReports source endByte { head := .expression, tail := [] } .expression input report ∧ trace = []

end Solcore.Syntax.DeclarativeGrammar
