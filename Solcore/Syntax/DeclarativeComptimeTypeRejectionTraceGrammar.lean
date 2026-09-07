import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Raw comptime-type rejection records the first failing stage. Marker and
punctuation are silent; the separate terminal report is never an emitted event. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ComptimeTypeTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.comptime.spelling))
      (reported : RejectAtReports source endByte { head := .contextual .comptime, tail := [] }
        .typeExpr input report) :
      ComptimeTypeTraceRejects elementTrace elementRejects source endByte input input report []
  | openingMissing {input afterMarker : Remainder} {report : ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor (.symbol .less))
      (reported : RejectAtReports source endByte { head := .symbol .less, tail := [] }
        .typeExpr afterMarker report) :
      ComptimeTypeTraceRejects elementTrace elementRejects source endByte input afterMarker report []
  | innerRejected {input afterMarker afterOpening rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan openingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening)
      (typed : elementRejects source endByte afterOpening rejected report trace) :
      ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace
  | closingMissing {input afterMarker afterOpening afterInner : Remainder} {inner : Syntax.TypeExpr}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan openingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening)
      (typed : elementTrace source endByte afterOpening inner afterInner trace)
      (absent : TokenKindAbsentAt afterInner.tokens afterInner.endIndex afterInner.cursor (.symbol .greater))
      (reported : RejectAtReports source endByte { head := .symbol .greater, tail := [] } .typeExpr afterInner report) :
      ComptimeTypeTraceRejects elementTrace elementRejects source endByte input afterInner report trace

end Solcore.Syntax.DeclarativeGrammar
