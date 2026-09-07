import Solcore.Syntax.DeclarativeTypeExprTraceGrammar
import Solcore.Syntax.DeclarativeTypedParameterFinishingTraceGrammar

/-! Independent named-parameter tails use the complete recursive type trace.
Colon absence is an error-valued success with its own constraint event; colon
presence parses the type and then appends only its finishing events. A rejected
type retains its complete trace and separate, uncommitted terminal report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedParameterTailTraceParses
    (start : SourceSpan) (marker : Option SourceSpan) (name : Syntax.Identifier) (errorSpan : SourceSpan)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | typed {input afterColon output : Remainder} {type : Syntax.TypeExpr}
      {typeEvents finishingEvents : List ParseDiagnostic} (colonSpan : SourceSpan)
      (colon : ExactTokenParses (.symbol .colon) input colonSpan afterColon)
      (typeParsed : TypeExprTraceParses source endByte afterColon type output typeEvents)
      (finished : TypedParameterFinishingTrace type finishingEvents) :
      NamedParameterTailTraceParses start marker name errorSpan source endByte input
        (typedParameterTraceValue start marker name type) output (typeEvents ++ finishingEvents)
  | typeMissing {input : Remainder} {events : List ParseDiagnostic}
      (colonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .colon))
      (finished : ErrorParameterFinishingTrace errorSpan .namedParameterRequiresType events) :
      NamedParameterTailTraceParses start marker name errorSpan source endByte input
        (errorParameterTraceValue errorSpan) input events

inductive NamedParameterTailTraceRejects
    (start : SourceSpan) (marker : Option SourceSpan) (name : Syntax.Identifier) (errorSpan : SourceSpan)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | typeRejected {input afterColon rejected : Remainder} {report : ParseDiagnostic}
      {trace : List ParseDiagnostic} (colonSpan : SourceSpan)
      (colon : ExactTokenParses (.symbol .colon) input colonSpan afterColon)
      (typeRejected : TypeExprTraceRejects source endByte afterColon rejected report trace) :
      NamedParameterTailTraceRejects start marker name errorSpan source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
