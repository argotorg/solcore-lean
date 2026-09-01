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

end Solcore.Syntax.DeclarativeGrammar
