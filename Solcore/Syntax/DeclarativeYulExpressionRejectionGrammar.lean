import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent binary rejection grammar for one inline-Yul expression.

The executable recovery layer rejects only at a recovery boundary or when an
active-window cursor has no corresponding array slot.  Every rejection is
non-consuming.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming rejection of one inline-Yul expression layer. -/
inductive YulExpressionRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      YulExpressionRejects input input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .comma
      }) :
      YulExpressionRejects input input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .rightParen
      }) :
      YulExpressionRejects input input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .rightBrace
      }) :
      YulExpressionRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      YulExpressionRejects input input

end Solcore.Syntax.DeclarativeGrammar
