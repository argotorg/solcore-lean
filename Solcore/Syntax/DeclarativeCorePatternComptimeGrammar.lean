import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent grammar for the Core compile-time pattern.

The marker remains an identifier token in the lexer.  Its contextual role is
recorded here by requiring the exact `comptime` spelling before the supplied
expression grammar.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of `comptime expression` in pattern position. -/
inductive ComptimePatternParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {expression : Syntax.Expr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (expressionParsed : expressionParses afterMarker expression output) :
      ComptimePatternParses expressionParses input {
        span := SourceSpan.cover markerSpan expression.span
        value := .comptime markerSpan expression
      } output

end Solcore.Syntax.DeclarativeGrammar
