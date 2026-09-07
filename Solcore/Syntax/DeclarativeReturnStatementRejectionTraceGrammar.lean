import Solcore.Syntax.DeclarativeReturnStatementTraceGrammar
import Solcore.Syntax.DeclarativeCoreStatementSimpleOutcomeGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Exact independent rejection traces of optional return values and return
statements. Earlier expression events are separate from the uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Only the non-semicolon branch can reject, through the expression outcome. -/
inductive OptionalReturnValueTraceRejects
    (expressionRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | expressionRejected {input rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (rejectedExpression : expressionRejects source endByte input rejected diagnostic trace) :
      OptionalReturnValueTraceRejects expressionRejects source endByte
        input rejected diagnostic trace

/-- Return rejection records the first failure: keyword, value, or mandatory
semicolon. A semicolon failure retains the successful value's complete trace. -/
inductive ReturnStatementTraceRejects
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (expressionRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerRejected {input : Remainder} {diagnostic : ParseDiagnostic}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .returnKw))
      (reported : RejectAtReports source endByte
        { head := .keyword .returnKw, tail := [] } .statement input diagnostic) :
      ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
        input input diagnostic []
  | valueRejected {input afterMarker rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
      (rejectedValue : OptionalReturnValueTraceRejects expressionRejects source endByte
        afterMarker rejected diagnostic trace) :
      ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
        input rejected diagnostic trace
  | semicolonRejected {input afterMarker afterValue : Remainder} {value : Option Syntax.Expr}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
      (valueParsed : OptionalReturnValueTraceParses expressionTrace source endByte
        afterMarker value afterValue trace)
      (semicolonAbsent : TokenKindAbsentAt afterValue.tokens afterValue.endIndex
        afterValue.cursor (.symbol .semicolon))
      (reported : RejectAtReports source endByte
        { head := .symbol .semicolon, tail := [] } .statement afterValue diagnostic) :
      ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
        input afterValue diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
