import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes of function-parameter recovery and the
exact lambda-parameter retagging built on top of it.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Boundary-prioritized stops of the parameter recovery scan. -/
inductive FunctionParameterRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      FunctionParameterRecoveryStops input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      FunctionParameterRecoveryStops input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      FunctionParameterRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      FunctionParameterRecoveryStops input

/-- Exact scan after recovery consumed its mandatory first token. -/
inductive FunctionParameterRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.FunctionParameter → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : FunctionParameterRecoveryStops input) :
      FunctionParameterRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {parameter : Syntax.FunctionParameter}
      (continues : ¬ FunctionParameterRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : FunctionParameterRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } parameter output) :
      FunctionParameterRecoveryScanParses first last input parameter output

/-- Ordinary success of `recoverParameter`, including its mandatory token. -/
inductive FunctionParameterRecoveryParses :
    Remainder → Syntax.FunctionParameter → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {parameter : Syntax.FunctionParameter}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : FunctionParameterRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } parameter output) :
      FunctionParameterRecoveryParses input parameter output

/-- Exact non-consuming rejection when no mandatory first token exists. -/
inductive FunctionParameterRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      FunctionParameterRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      FunctionParameterRecoveryRejects input input

/-- Lambda recovery is the exact span-preserving retag of function recovery. -/
inductive LambdaParameterRecoveryParses :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | recovered {input output : Remainder}
      {parameter : Syntax.FunctionParameter}
      (parsed : FunctionParameterRecoveryParses input parameter output) :
      LambdaParameterRecoveryParses input {
        span := parameter.span
        value := .error
      } output

/-- Lambda recovery propagates the exact function-recovery rejection. -/
abbrev LambdaParameterRecoveryRejects := FunctionParameterRecoveryRejects

end Solcore.Syntax.DeclarativeGrammar
