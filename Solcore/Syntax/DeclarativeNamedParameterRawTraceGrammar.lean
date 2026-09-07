import Solcore.Syntax.DeclarativeParameterNameFinishingTraceProperties
import Solcore.Syntax.DeclarativeNamedParameterTailTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Raw ordinary and comptime parameter outcomes, before pair selection or
public recovery. Ordinary names include their spelling-finishing check; names
after a comptime marker receive only checked-identifier events. Every rejection
stops at the first failing stage and retains its separate complete report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OrdinaryNamedParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterName output : Remainder} {name : Syntax.Identifier} {value : Syntax.FunctionParameter}
      {nameEvents tailEvents : List ParseDiagnostic}
      (nameParsed : CheckedParameterNameTraceParses input name afterName nameEvents)
      (tail : NamedParameterTailTraceParses name.span none name name.span source endByte afterName value output tailEvents) :
      OrdinaryNamedParameterTraceParses source endByte input value output (nameEvents ++ tailEvents)

inductive OrdinaryNamedParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | nameRejected {input : Remainder} {report : ParseDiagnostic}
      (absent : IdentifierAbsentAt input)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] } .parameter input report) :
      OrdinaryNamedParameterTraceRejects source endByte input input report []
  | tailRejected {input afterName rejected : Remainder} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic}
      (nameParsed : CheckedParameterNameTraceParses input name afterName nameEvents)
      (tail : NamedParameterTailTraceRejects name.span none name name.span source endByte afterName rejected report tailEvents) :
      OrdinaryNamedParameterTraceRejects source endByte input rejected report (nameEvents ++ tailEvents)

inductive ComptimeNamedParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterName output : Remainder} {name : Syntax.Identifier} {value : Syntax.FunctionParameter}
      {nameEvents tailEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
      (tail : NamedParameterTailTraceParses markerSpan (some markerSpan) name (SourceSpan.cover markerSpan name.span)
        source endByte afterName value output tailEvents) :
      ComptimeNamedParameterTraceParses source endByte input value output (nameEvents ++ tailEvents)

inductive ComptimeNamedParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.identifier ContextualKeyword.comptime.spelling))
      (reported : RejectAtReports source endByte { head := .contextual .comptime, tail := [] } .parameter input report) :
      ComptimeNamedParameterTraceRejects source endByte input input report []
  | nameRejected {input afterMarker : Remainder} {report : ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (absent : IdentifierAbsentAt afterMarker)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] } .parameter afterMarker report) :
      ComptimeNamedParameterTraceRejects source endByte input afterMarker report []
  | tailRejected {input afterMarker afterName rejected : Remainder} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
      (tail : NamedParameterTailTraceRejects markerSpan (some markerSpan) name (SourceSpan.cover markerSpan name.span)
        source endByte afterName rejected report tailEvents) :
      ComptimeNamedParameterTraceRejects source endByte input rejected report (nameEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
