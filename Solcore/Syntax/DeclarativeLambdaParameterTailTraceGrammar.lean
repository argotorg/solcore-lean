import Solcore.Syntax.DeclarativeNamedParameterTailTraceGrammar

/-! Lambda-tail outcomes before name dispatch or recovery. The retagging is
pure data. A typed branch requires a present colon; without one an ordinary
name is inferred, while a comptime name emits its distinct missing-type event. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def lambdaParameterTraceValue (parameter : Syntax.FunctionParameter) : Syntax.LambdaParameter := {
  span := parameter.span
  value := match parameter.value with
    | .typed marker name type => .typed marker name type
    | .error => .error
}

inductive OrdinaryLambdaParameterTailTraceParses (name : Syntax.Identifier)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | typed {input output : Remainder} {parameter : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .colon })
      (parsed : NamedParameterTailTraceParses name.span none name name.span source endByte
        input parameter output trace) :
      OrdinaryLambdaParameterTailTraceParses name source endByte input (lambdaParameterTraceValue parameter) output trace
  | inferred {input : Remainder}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .colon)) :
      OrdinaryLambdaParameterTailTraceParses name source endByte input { span := name.span, value := .inferred name } input []

abbrev OrdinaryLambdaParameterTailTraceRejects (name : Syntax.Identifier) :=
  NamedParameterTailTraceRejects name.span none name name.span

inductive ComptimeLambdaParameterTailTraceParses (marker : SourceSpan) (name : Syntax.Identifier)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | typed {input output : Remainder} {parameter : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .colon })
      (parsed : NamedParameterTailTraceParses marker (some marker) name (SourceSpan.cover marker name.span)
        source endByte input parameter output trace) :
      ComptimeLambdaParameterTailTraceParses marker name source endByte input (lambdaParameterTraceValue parameter) output trace
  | typeMissing {input : Remainder} {trace : List ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .colon))
      (finished : ErrorParameterFinishingTrace (SourceSpan.cover marker name.span) .comptimeParameterRequiresType trace) :
      ComptimeLambdaParameterTailTraceParses marker name source endByte input
        (lambdaParameterTraceValue (errorParameterTraceValue (SourceSpan.cover marker name.span))) input trace

abbrev ComptimeLambdaParameterTailTraceRejects (marker : SourceSpan) (name : Syntax.Identifier) :=
  NamedParameterTailTraceRejects marker (some marker) name (SourceSpan.cover marker name.span)

end Solcore.Syntax.DeclarativeGrammar
