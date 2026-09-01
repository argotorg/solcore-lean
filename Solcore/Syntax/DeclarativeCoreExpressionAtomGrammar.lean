import Solcore.Syntax.DeclarativeCoreLiteralGrammar

/-!
Parser-independent grammar for the literal, identifier, and proxy Core
expression leaves.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of a literal expression leaf. -/
inductive LiteralExpressionParses :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input output : Remainder} {literal : Syntax.CoreLiteral}
      (literalParsed : CoreLiteralParses input literal output) :
      LiteralExpressionParses input {
        span := literal.span
        value := .literal literal
      } output

/-- Exact grammar of an identifier expression leaf, including Boolean names. -/
inductive IdentifierExpressionParses :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier}
      (nameParsed : ExpressionNameParses input name output) :
      IdentifierExpressionParses input {
        span := name.span
        value := .identifier name
      } output

/-- Exact grammar of an `@`-prefixed proxy expression leaf. -/
inductive ProxyExpressionParses :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {type : Syntax.TypeExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .at)
        input markerSpan afterMarker)
      (typeParsed : TypeExprParses afterMarker type output) :
      ProxyExpressionParses input {
        span := SourceSpan.cover markerSpan type.span
        value := .proxy markerSpan type
      } output

/--
Prioritized optional argument list of a leading-dot constructor.  A present
opening parenthesis commits to the no-trailing delimited branch; absence is
recorded only when that opening token is not current.
-/
inductive OptionalDotConstructorArgumentsParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Option (DelimitedList Syntax.Expr) → Remainder → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalDotConstructorArgumentsParses nestedParses input none input
  | present {input output : Remainder}
      {arguments : DelimitedList Syntax.Expr}
      (parsed : NoTrailingDelimitedListParses .leftParen .rightParen
        nestedParses input arguments output) :
      OptionalDotConstructorArgumentsParses nestedParses input
        (some arguments) output

/--
Exact leading-dot constructor grammar, including Boolean-first name parsing,
optional-argument priority, retained marker, and outer range.
-/
inductive DotConstructorParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input afterDot afterName output : Remainder}
      {name : Syntax.Identifier}
      {arguments : Option (DelimitedList Syntax.Expr)}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : ExpressionNameParses afterDot name afterName)
      (argumentsParsed : OptionalDotConstructorArgumentsParses nestedParses
        afterName arguments output) :
      DotConstructorParses nestedParses input {
        span := SourceSpan.cover dotSpan
          (arguments.map (fun values => values.span) |>.getD name.span)
        value := .dotConstructor dotSpan name arguments
      } output

end Solcore.Syntax.DeclarativeGrammar
