import Solcore.Syntax.DeclarativeFunctionTypeTraceGrammar
import Solcore.Syntax.DeclarativeFunctionReturnsRejectionTraceGrammar

/-! Raw function rejection stops at the first failing stage. Missing keyword
is a raw failure, not a selected function-type failure. Reports stay separate. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive FunctionTypeTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
      (reported : RejectAtReports source endByte { head := .keyword .functionKw, tail := [] }
        .typeExpr input report) :
      FunctionTypeTraceRejects elementTrace elementRejects source endByte input input report []
  | parametersRejected {input afterKeyword rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic} (keywordSpan : SourceSpan)
      (keywordToken : ExactTokenParses (.keyword .functionKw) input keywordSpan afterKeyword)
      (parametersRejected : TrailingDelimitedListTraceRejects .leftParen .rightParen true .typeExpr
        elementTrace elementRejects source endByte afterKeyword rejected report trace) :
      FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace
  | returnsRejected {input afterKeyword afterParameters rejected : Remainder}
      {parameters : DelimitedList Syntax.TypeExpr} {report : ParseDiagnostic}
      {parameterTrace returnTrace : List ParseDiagnostic} (keywordSpan : SourceSpan)
      (keywordToken : ExactTokenParses (.keyword .functionKw) input keywordSpan afterKeyword)
      (parametersParsed : TrailingDelimitedListTraceParses .leftParen .rightParen true
        elementTrace source endByte afterKeyword parameters afterParameters parameterTrace)
      (returnsRejected : FunctionReturnsTraceRejects elementTrace elementRejects source endByte
        afterParameters rejected report returnTrace) :
      FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report
        (parameterTrace ++ returnTrace)

end Solcore.Syntax.DeclarativeGrammar
