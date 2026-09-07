import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Raw proxy-type rejection includes an absent marker and a nested failure.
The terminal report is not appended to the child's ordered event trace. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ProxyTypeTraceRejects
    (typeRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (reported : RejectAtReports source endByte { head := .symbol .at, tail := [] } .typeExpr input report) :
      ProxyTypeTraceRejects typeRejects source endByte input input report []
  | innerRejected {input afterMarker rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.symbol .at) input markerSpan afterMarker)
      (typed : typeRejects source endByte afterMarker rejected report trace) :
      ProxyTypeTraceRejects typeRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
