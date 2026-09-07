import Solcore.Syntax.DeclarativeCoreStatementSimpleGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent successful return traces. A current semicolon selects no
value without consuming it; otherwise exactly the expression's events survive. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OptionalReturnValueTraceParses
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder} (semicolonSpan : SourceSpan)
      (semicolonCurrent : TokenAt input.tokens input.endIndex input.cursor
        { span := semicolonSpan, value := .symbol .semicolon }) :
      OptionalReturnValueTraceParses expressionTrace source endByte input none input []
  | present {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .semicolon))
      (valueParsed : expressionTrace source endByte input value output trace) :
      OptionalReturnValueTraceParses expressionTrace source endByte input (some value) output trace

inductive ReturnStatementTraceParses
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Statement → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterValue output : Remainder}
      {value : Option Syntax.Expr} {trace : List ParseDiagnostic}
      (markerSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
      (valueParsed : OptionalReturnValueTraceParses expressionTrace source endByte
        afterMarker value afterValue trace)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) afterValue semicolonSpan output) :
      ReturnStatementTraceParses expressionTrace source endByte input {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt value
      } output trace

end Solcore.Syntax.DeclarativeGrammar
