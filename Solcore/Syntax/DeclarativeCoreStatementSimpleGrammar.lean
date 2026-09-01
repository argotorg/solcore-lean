import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent grammar for the shared optional suffixes and the canonical
Core `let` and `return` statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prioritized optional statement semicolon. -/
inductive OptionalStatementSemicolonParses :
    Remainder → Option SourceSpan → Remainder → Prop where
  | absent {input : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon)) :
      OptionalStatementSemicolonParses input none input
  | present {input output : Remainder} (semicolonSpan : SourceSpan)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) input
        semicolonSpan output) :
      OptionalStatementSemicolonParses input (some semicolonSpan) output

/-- Optional return value, where a current semicolon commits to no value. -/
inductive OptionalReturnValueParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Option Syntax.Expr → Remainder → Prop where
  | absent {input : Remainder} (semicolonSpan : SourceSpan)
      (semicolonCurrent : TokenAt input.tokens input.endIndex input.cursor {
        span := semicolonSpan
        value := .symbol .semicolon
      }) :
      OptionalReturnValueParses expressionParses input none input
  | present {input output : Remainder} {value : Syntax.Expr}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (valueParsed : expressionParses input value output) :
      OptionalReturnValueParses expressionParses input (some value) output

/-- Prioritized optional `: Type` annotation on a Core `let`. -/
inductive OptionalLetTypeParses :
    Remainder → Option Syntax.TypeExpr → Remainder → Prop where
  | absent {input : Remainder}
      (colonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .colon)) :
      OptionalLetTypeParses input none input
  | present {input afterColon output : Remainder} {type : Syntax.TypeExpr}
      (colonSpan : SourceSpan)
      (colonParsed : ExactTokenParses (.symbol .colon) input colonSpan
        afterColon)
      (typeParsed : TypeExprParses afterColon type output) :
      OptionalLetTypeParses input (some type) output

/-- Prioritized optional `= Expr` initializer on a Core `let`. -/
inductive OptionalLetInitializerParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Option Syntax.Expr → Remainder → Prop where
  | absent {input : Remainder}
      (equalAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .equal)) :
      OptionalLetInitializerParses expressionParses input none input
  | present {input afterEqual output : Remainder} {value : Syntax.Expr}
      (equalSpan : SourceSpan)
      (equalParsed : ExactTokenParses (.symbol .equal) input equalSpan
        afterEqual)
      (valueParsed : expressionParses afterEqual value output) :
      OptionalLetInitializerParses expressionParses input (some value) output

/-- Exact semicolon-terminated Core `let` statement grammar. -/
inductive LetStatementParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterName afterType afterInitializer output :
        Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      {initializer : Option Syntax.Expr}
      (markerSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (initializerParsed : OptionalLetInitializerParses expressionParses
        afterType initializer afterInitializer)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer semicolonSpan output) :
      LetStatementParses expressionParses input {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := .letDecl name type initializer
      } output

/-- Exact semicolon-terminated Core `return` statement grammar. -/
inductive ReturnStatementParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterValue output : Remainder}
      {value : Option Syntax.Expr} (markerSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (valueParsed : OptionalReturnValueParses expressionParses afterMarker
        value afterValue)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) afterValue
        semicolonSpan output) :
      ReturnStatementParses expressionParses input {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := .returnStmt value
      } output

end Solcore.Syntax.DeclarativeGrammar
