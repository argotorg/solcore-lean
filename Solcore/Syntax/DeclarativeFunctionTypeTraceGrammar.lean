import Solcore.Syntax.DeclarativeFunctionReturnsTraceGrammar

/-! Raw function types retain both trailing-enabled lists and their exact
event order. The keyword is silent; optional returns determine the final span. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def functionTypeTraceValue (keywordSpan : SourceSpan)
    (parameters : DelimitedList Syntax.TypeExpr)
    (returns : Option (DelimitedList Syntax.TypeExpr)) : Syntax.TypeExpr := {
  span := SourceSpan.cover keywordSpan (match returns with
    | some values => values.span
    | none => parameters.span)
  value := .function keywordSpan parameters returns
}

inductive FunctionTypeTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterKeyword afterParameters output : Remainder}
      {parameters : DelimitedList Syntax.TypeExpr} {returns : Option (DelimitedList Syntax.TypeExpr)}
      {parameterTrace returnTrace : List ParseDiagnostic} (keywordSpan : SourceSpan)
      (keywordToken : ExactTokenParses (.keyword .functionKw) input keywordSpan afterKeyword)
      (parametersParsed : TrailingDelimitedListTraceParses .leftParen .rightParen true
        elementTrace source endByte afterKeyword parameters afterParameters parameterTrace)
      (returnsParsed : FunctionReturnsTraceParses elementTrace source endByte
        afterParameters returns output returnTrace) :
      FunctionTypeTraceParses elementTrace source endByte input
        (functionTypeTraceValue keywordSpan parameters returns) output (parameterTrace ++ returnTrace)

end Solcore.Syntax.DeclarativeGrammar
