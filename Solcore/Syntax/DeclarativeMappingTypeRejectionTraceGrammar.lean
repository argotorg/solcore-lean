import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Raw mapping rejection records the first failing stage, including missing
marker/opening cases that a selected dispatcher branch cannot reach. Marker
and punctuation are silent; only completed or rejected children add events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive MappingTypeTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.mapping.spelling))
      (reported : RejectAtReports source endByte { head := .contextual .mapping, tail := [] }
        .typeExpr input report) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input input report []
  | openingMissing {input afterMarker : Remainder} {report : ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor (.symbol .leftParen))
      (reported : RejectAtReports source endByte { head := .symbol .leftParen, tail := [] }
        .typeExpr afterMarker report) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input afterMarker report []
  | keyRejected {input afterMarker afterOpening rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan openingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (key : elementRejects source endByte afterOpening rejected report trace) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace
  | arrowMissing {input afterMarker afterOpening afterKey : Remainder} {key : Syntax.TypeExpr}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan openingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (keyParsed : elementTrace source endByte afterOpening key afterKey trace)
      (absent : TokenKindAbsentAt afterKey.tokens afterKey.endIndex afterKey.cursor (.symbol .fatArrow))
      (reported : RejectAtReports source endByte { head := .symbol .fatArrow, tail := [] } .typeExpr afterKey report) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input afterKey report trace
  | valueRejected {input afterMarker afterOpening afterKey afterArrow rejected : Remainder} {key : Syntax.TypeExpr}
      {report : ParseDiagnostic} {keyEvents valueEvents : List ParseDiagnostic}
      (markerSpan openingSpan arrowSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (keyParsed : elementTrace source endByte afterOpening key afterKey keyEvents)
      (arrow : ExactTokenParses (.symbol .fatArrow) afterKey arrowSpan afterArrow)
      (value : elementRejects source endByte afterArrow rejected report valueEvents) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report (keyEvents ++ valueEvents)
  | closingMissing {input afterMarker afterOpening afterKey afterArrow afterValue : Remainder}
      {key value : Syntax.TypeExpr} {report : ParseDiagnostic} {keyEvents valueEvents : List ParseDiagnostic}
      (markerSpan openingSpan arrowSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (keyParsed : elementTrace source endByte afterOpening key afterKey keyEvents)
      (arrow : ExactTokenParses (.symbol .fatArrow) afterKey arrowSpan afterArrow)
      (valueParsed : elementTrace source endByte afterArrow value afterValue valueEvents)
      (absent : TokenKindAbsentAt afterValue.tokens afterValue.endIndex afterValue.cursor (.symbol .rightParen))
      (reported : RejectAtReports source endByte { head := .symbol .rightParen, tail := [] } .typeExpr afterValue report) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input afterValue report (keyEvents ++ valueEvents)

end Solcore.Syntax.DeclarativeGrammar
