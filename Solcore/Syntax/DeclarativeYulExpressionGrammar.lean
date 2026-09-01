import Solcore.Syntax.DeclarativeYulExpressionLeafGrammar

/-!
Parser-independent ordered grammar for one inline-Yul expression layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact successful grammar of a parenthesized inline-Yul call argument list. -/
def YulCallArgumentsParses
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (input : Remainder) (arguments : DelimitedList Syntax.YulExpr)
    (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftParen .rightParen nestedParses input
    arguments output

/-- Parser-independent fallback semantics for transactional call arguments.

The disjointness law makes rejection evidence incompatible with any successful
argument-list derivation, so a fallback cannot also bypass a valid preferred
branch.
-/
structure YulCallArgumentsFallbackSpec
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop) where
  rejects : Remainder → Prop
  disjoint : ∀ input, rejects input →
    ¬ ∃ (arguments : DelimitedList Syntax.YulExpr) (output : Remainder),
      YulCallArgumentsParses nestedParses input arguments output

/-- Exact ordered outcomes of optional transactional Yul call arguments. -/
inductive OptionalYulCallArgumentsParses
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulCallArgumentsFallbackSpec nestedParses) :
    Remainder → Option (DelimitedList Syntax.YulExpr) → Remainder → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalYulCallArgumentsParses nestedParses fallback input none input
  | rewound {input : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (attemptRejected : fallback.rejects input) :
      OptionalYulCallArgumentsParses nestedParses fallback input none input
  | present {input output : Remainder}
      {arguments : DelimitedList Syntax.YulExpr}
      (parsed : YulCallArgumentsParses nestedParses input arguments output) :
      OptionalYulCallArgumentsParses nestedParses fallback input
        (some arguments) output

/-- Inline-Yul literal tokens recognized by the first core-expression guard. -/
def YulLiteralStartsAt (input : Remainder) : Prop :=
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .decimalLiteral spelling
  }) ∨
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .hexadecimalLiteral spelling
  }) ∨
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .stringLiteral spelling
  }) ∨
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .trueKw
  }) ∨
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .falseKw
  }

/-- All token forms recognized by the inline-Yul name guard. -/
def YulNameStartsAt (input : Remainder) : Prop :=
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .identifier spelling
  }) ∨
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .yulIdentifier spelling
  }) ∨
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .symbol .underscore
  }) ∨
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .fallbackKw
  }

/-- Exact named-or-called inline-Yul expression grammar. -/
inductive YulNamedExpressionParses
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulCallArgumentsFallbackSpec nestedParses) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | identifier {input afterName output : Remainder}
      {name : Syntax.YulIdentifier}
      (nameParsed : YulNameParses input name afterName)
      (argumentsParsed : OptionalYulCallArgumentsParses nestedParses fallback
        afterName none output) :
      YulNamedExpressionParses nestedParses fallback input {
        span := name.span
        value := .identifier name
      } output
  | call {input afterName output : Remainder}
      {name : Syntax.YulIdentifier}
      {arguments : DelimitedList Syntax.YulExpr}
      (nameParsed : YulNameParses input name afterName)
      (argumentsParsed : OptionalYulCallArgumentsParses nestedParses fallback
        afterName (some arguments) output) :
      YulNamedExpressionParses nestedParses fallback input {
        span := SourceSpan.cover name.span arguments.span
        value := .call name arguments
      } output

/-- Diagnostic-free literal-before-name grammar of `yulExpressionCore`. -/
inductive YulExpressionCoreParses
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulCallArgumentsFallbackSpec nestedParses) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | literal {input output : Remainder} {literal : Syntax.YulLiteral}
      (parsed : YulLiteralParses input literal output) :
      YulExpressionCoreParses nestedParses fallback input {
        span := literal.span
        value := .literal literal
      } output
  | named {input output : Remainder} {expression : Syntax.YulExpr}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (parsed : YulNamedExpressionParses nestedParses fallback input
        expression output) :
      YulExpressionCoreParses nestedParses fallback input expression output

end Solcore.Syntax.DeclarativeGrammar
