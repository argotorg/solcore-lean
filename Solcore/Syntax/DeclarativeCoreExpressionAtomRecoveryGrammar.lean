import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes of Core expression-atom recovery.

The outer recovery parser always consumes one token before this scan begins.
The scan then gives boundary detection priority over token consumption and
also records a missing carrier slot inside the active token window.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact stop conditions of the boundary-prioritized atom recovery scan. -/
inductive ExpressionAtomRecoveryStops : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      ExpressionAtomRecoveryStops input input
  | semicolon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .semicolon }) :
      ExpressionAtomRecoveryStops input input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      ExpressionAtomRecoveryStops input input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      ExpressionAtomRecoveryStops input input
  | rightBracket {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBracket }) :
      ExpressionAtomRecoveryStops input input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      ExpressionAtomRecoveryStops input input
  | question {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .question }) :
      ExpressionAtomRecoveryStops input input
  | colon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .colon }) :
      ExpressionAtomRecoveryStops input input
  | fatArrow {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .fatArrow }) :
      ExpressionAtomRecoveryStops input input
  | pipe {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .pipe }) :
      ExpressionAtomRecoveryStops input input
  | elseKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .keyword .elseKw }) :
      ExpressionAtomRecoveryStops input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      ExpressionAtomRecoveryStops input input

/-- Exact scan after recovery has consumed its mandatory first token. -/
inductive ExpressionAtomRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.Expr → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : ExpressionAtomRecoveryStops input input) :
      ExpressionAtomRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {expression : Syntax.Expr}
      (continues : ¬ ExpressionAtomRecoveryStops input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : ExpressionAtomRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } expression output) :
      ExpressionAtomRecoveryScanParses first last input expression output

/-- Ordinary success of `recoverAtom`, including its mandatory first token. -/
inductive ExpressionAtomRecoveryParses :
    Remainder → Syntax.Expr → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {expression : Syntax.Expr}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : ExpressionAtomRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } expression output) :
      ExpressionAtomRecoveryParses input expression output

/-- Exact non-consuming rejection when `recoverAtom` cannot consume first. -/
inductive ExpressionAtomRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      ExpressionAtomRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      ExpressionAtomRecoveryRejects input input

end Solcore.Syntax.DeclarativeGrammar
