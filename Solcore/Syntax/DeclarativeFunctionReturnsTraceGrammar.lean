import Solcore.Syntax.DeclarativeDelimitedTrailingTraceGrammar

/-! Optional function-type returns preserve the complete parenthesized list.
An absent contextual identifier succeeds without consumption or events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive FunctionReturnsTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option (DelimitedList Syntax.TypeExpr) → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.returns.spelling)) :
      FunctionReturnsTraceParses elementTrace source endByte input none input []
  | present {input afterMarker output : Remainder} {values : DelimitedList Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.returns.spelling) input markerSpan afterMarker)
      (valuesParsed : TrailingDelimitedListTraceParses .leftParen .rightParen true elementTrace
        source endByte afterMarker values output trace) :
      FunctionReturnsTraceParses elementTrace source endByte input (some values) output trace

end Solcore.Syntax.DeclarativeGrammar
