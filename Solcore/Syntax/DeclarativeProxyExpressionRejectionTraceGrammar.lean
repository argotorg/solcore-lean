import Solcore.Syntax.DeclarativeCoreProxyExpressionOutcomeGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Raw proxy rejection distinguishes a missing marker from a nested type
failure. The exact final report stays separate from the child's ordered events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ProxyExpressionTraceRejects
    (typeRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (reported : RejectAtReports source endByte { head := .symbol .at, tail := [] } .expression input report) :
      ProxyExpressionTraceRejects typeRejects source endByte input input report []
  | typeRejected {input afterMarker rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.symbol .at) input markerSpan afterMarker)
      (typed : typeRejects source endByte afterMarker rejected report trace) :
      ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
