import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar

/-! Rejection requires an exact present returns marker. Absence is an optional
success, not a raw marker failure; the list's terminal report stays separate. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive FunctionReturnsTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | present {input afterMarker rejected : Remainder} {report : ParseDiagnostic}
      {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.returns.spelling) input markerSpan afterMarker)
      (valuesRejected : TrailingDelimitedListTraceRejects .leftParen .rightParen true .typeExpr
        elementTrace elementRejects source endByte afterMarker rejected report trace) :
      FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
