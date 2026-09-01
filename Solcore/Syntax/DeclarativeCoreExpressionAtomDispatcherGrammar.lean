import Solcore.Syntax.DeclarativeCoreCollectionAtomGrammar
import Solcore.Syntax.DeclarativeCoreExpressionAtomGrammar
import Solcore.Syntax.DeclarativeCoreLambdaGrammar

/-!
Parser-independent ordered grammar for the seven Core expression-atom
branches.  Starter predicates depend only on the declarative token remainder;
the later constructors retain every earlier failed lookahead.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A Core literal token starts at the current declarative cursor. -/
def CoreLiteralStartsAt (input : Remainder) : Prop :=
  (∃ span spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .decimalLiteral spelling
    }) ∨
  (∃ span spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .hexadecimalLiteral spelling
    }) ∨
  ∃ span spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .stringLiteral spelling
    }

/-- A Boolean builtin or ordinary identifier starts at the current cursor. -/
def ExpressionNameStartsAt (input : Remainder) : Prop :=
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .trueKw
  }) ∨
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .falseKw
  }) ∨
  ∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .identifier spelling
  }

/--
Exact priority grammar of `expressionAtomCore` over supplied recursive
expression and block judgments.
-/
inductive ExpressionAtomCoreParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop)
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | literal {input output : Remainder} {value : Syntax.Expr}
      (parsed : LiteralExpressionParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | identifier {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (parsed : IdentifierExpressionParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | dotConstructor {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (parsed : DotConstructorParses nestedParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | proxy {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (parsed : ProxyExpressionParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | parenthesized {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (parsed : ParenthesizedExpressionParses nestedParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | array {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (parsed : ArrayLiteralExpressionParses nestedParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | lambda {input output : Remainder} {value : Syntax.Expr}
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
      (parsed : LambdaExpressionParses blockParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output

end Solcore.Syntax.DeclarativeGrammar
