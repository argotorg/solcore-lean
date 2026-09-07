import Solcore.Syntax.DeclarativeParameterListTraceGrammar
import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceGrammar
import Solcore.Syntax.DeclarativeTypeExprTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Raw lambda expressions retain their marker, complete parameter list,
optional return annotation, and body. Parameter recovery events are committed
before return and body events. Every first failure has a separate terminal
report; these judgments impose no atom-dispatch guard or body frame. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def lambdaExpressionTraceValue (marker : SourceSpan)
    (parameters : Syntax.DelimitedList Syntax.LambdaParameter)
    (returnType : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr := {
  span := SourceSpan.cover marker body.span
  value := .lambda marker parameters returnType body
}

inductive LambdaExpressionTraceParses
    (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterParameters afterReturn output : Remainder}
      {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {returnType : Option Syntax.TypeExpr}
      {body : Syntax.Block} {parameterEvents returnEvents bodyEvents : List ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword .lamKw) input markerSpan afterMarker)
      (parameterList : LambdaParametersTraceParses source endByte afterMarker parameters afterParameters parameterEvents)
      (returnParsed : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses source endByte
        afterParameters returnType afterReturn returnEvents)
      (bodyParsed : blockTrace source endByte afterReturn body output bodyEvents) :
      LambdaExpressionTraceParses blockTrace source endByte input
        (lambdaExpressionTraceValue markerSpan parameters returnType body) output
        ((parameterEvents ++ returnEvents) ++ bodyEvents)

inductive LambdaExpressionTraceRejects
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .lamKw))
      (reported : RejectAtReports source endByte { head := .keyword .lamKw, tail := [] } .expression input report) :
      LambdaExpressionTraceRejects blockRejects source endByte input input report []
  | parametersRejected {input afterMarker rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword .lamKw) input markerSpan afterMarker)
      (parameters : LambdaParametersTraceRejects source endByte afterMarker rejected report trace) :
      LambdaExpressionTraceRejects blockRejects source endByte input rejected report trace
  | returnTypeRejected {input afterMarker afterParameters rejected : Remainder}
      {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {report : ParseDiagnostic}
      {parameterEvents returnEvents : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword .lamKw) input markerSpan afterMarker)
      (parameterList : LambdaParametersTraceParses source endByte afterMarker parameters afterParameters parameterEvents)
      (returnRejected : OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects source endByte
        afterParameters rejected report returnEvents) :
      LambdaExpressionTraceRejects blockRejects source endByte input rejected report (parameterEvents ++ returnEvents)
  | bodyRejected {input afterMarker afterParameters afterReturn rejected : Remainder}
      {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {returnType : Option Syntax.TypeExpr}
      {report : ParseDiagnostic} {parameterEvents returnEvents bodyEvents : List ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword .lamKw) input markerSpan afterMarker)
      (parameterList : LambdaParametersTraceParses source endByte afterMarker parameters afterParameters parameterEvents)
      (returnParsed : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses source endByte
        afterParameters returnType afterReturn returnEvents)
      (bodyRejected : blockRejects source endByte afterReturn rejected report bodyEvents) :
      LambdaExpressionTraceRejects blockRejects source endByte input rejected report
        ((parameterEvents ++ returnEvents) ++ bodyEvents)

end Solcore.Syntax.DeclarativeGrammar
