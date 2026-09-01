import Solcore.Syntax.DeclarativeCoreExpressionAtomDispatcherGrammar

/-! Exact selection evidence for the final Core atom rejection branch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every earlier Core atom starter is absent, so the ordered dispatcher
selects its final non-consuming rejection. -/
inductive ExpressionAtomCoreFinalRejects : Remainder → Prop where
  | final {input : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBracket))
      (lambdaAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .lamKw)) :
      ExpressionAtomCoreFinalRejects input

end Solcore.Syntax.DeclarativeGrammar
