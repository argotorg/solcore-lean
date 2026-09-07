import Solcore.Syntax.DeclarativeParameterNameFinishingTraceProperties
import Solcore.Syntax.DeclarativeLambdaParameterTailTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Raw lambda-parameter outcomes before pair selection or public recovery.
Ordinary names include their parameter-name finishing events. A comptime marker
is silent and its following name receives only identifier checking. Each first
failure retains its complete separate report and all earlier ordered events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OrdinaryLambdaParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterName output : Remainder} {name : Syntax.Identifier} {value : Syntax.LambdaParameter}
      {nameEvents tailEvents : List ParseDiagnostic}
      (nameParsed : CheckedParameterNameTraceParses input name afterName nameEvents)
      (tail : OrdinaryLambdaParameterTailTraceParses name source endByte afterName value output tailEvents) :
      OrdinaryLambdaParameterTraceParses source endByte input value output (nameEvents ++ tailEvents)

inductive OrdinaryLambdaParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | nameRejected {input : Remainder} {report : ParseDiagnostic}
      (absent : IdentifierAbsentAt input)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] } .parameter input report) :
      OrdinaryLambdaParameterTraceRejects source endByte input input report []
  | tailRejected {input afterName rejected : Remainder} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic}
      (nameParsed : CheckedParameterNameTraceParses input name afterName nameEvents)
      (tail : OrdinaryLambdaParameterTailTraceRejects name source endByte afterName rejected report tailEvents) :
      OrdinaryLambdaParameterTraceRejects source endByte input rejected report (nameEvents ++ tailEvents)

inductive ComptimeLambdaParameterTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterName output : Remainder} {name : Syntax.Identifier} {value : Syntax.LambdaParameter}
      {nameEvents tailEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
      (tail : ComptimeLambdaParameterTailTraceParses markerSpan name source endByte afterName value output tailEvents) :
      ComptimeLambdaParameterTraceParses source endByte input value output (nameEvents ++ tailEvents)

inductive ComptimeLambdaParameterTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.identifier ContextualKeyword.comptime.spelling))
      (reported : RejectAtReports source endByte { head := .contextual .comptime, tail := [] } .parameter input report) :
      ComptimeLambdaParameterTraceRejects source endByte input input report []
  | nameRejected {input afterMarker : Remainder} {report : ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (absent : IdentifierAbsentAt afterMarker)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] } .parameter afterMarker report) :
      ComptimeLambdaParameterTraceRejects source endByte input afterMarker report []
  | tailRejected {input afterMarker afterName rejected : Remainder} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
      (tail : ComptimeLambdaParameterTailTraceRejects markerSpan name source endByte afterName rejected report tailEvents) :
      ComptimeLambdaParameterTraceRejects source endByte input rejected report (nameEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
