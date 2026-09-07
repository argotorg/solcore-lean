import Solcore.Syntax.DeclarativeCoreExpressionAtomDispatcherGrammar

/-! One ordered expression-atom selection, including the final fallback.
Every later branch retains all earlier failed lookaheads. Selection depends
only on the visible token remainder, not on any recursive parsing outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionAtomDispatchBranch where
  | literal | name | dotConstructor | proxy | parenthesized | array | lambda | final
  deriving DecidableEq

inductive ExpressionAtomDispatchSelects (input : Remainder) : ExpressionAtomDispatchBranch → Prop where
  | literal (present : CoreLiteralStartsAt input) :
      ExpressionAtomDispatchSelects input .literal
  | name (literalAbsent : ¬ CoreLiteralStartsAt input)
      (present : ExpressionNameStartsAt input) :
      ExpressionAtomDispatchSelects input .name
  | dotConstructor (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .dot }) :
      ExpressionAtomDispatchSelects input .dotConstructor
  | proxy (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at }) :
      ExpressionAtomDispatchSelects input .proxy
  | parenthesized (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen }) :
      ExpressionAtomDispatchSelects input .parenthesized
  | array (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftBracket }) :
      ExpressionAtomDispatchSelects input .array
  | lambda (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .keyword .lamKw }) :
      ExpressionAtomDispatchSelects input .lambda
  | final (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (lambdaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .lamKw)) :
      ExpressionAtomDispatchSelects input .final

end Solcore.Syntax.DeclarativeGrammar
