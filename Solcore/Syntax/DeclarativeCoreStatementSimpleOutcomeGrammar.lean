import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementSimpleGrammar
import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-! Ordinary outcomes for canonical Core `let` and `return` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev OptionalReturnValueOrdinaryParses := OptionalReturnValueParses
abbrev OptionalLetInitializerOrdinaryParses := OptionalLetInitializerParses
abbrev LetStatementOrdinaryParses := LetStatementParses
abbrev ReturnStatementOrdinaryParses := ReturnStatementParses

/-- A present optional let type rejects exactly when its type rejects. -/
inductive OptionalLetTypeRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | typeRejected {input afterColon rejected : Remainder}
      (colonSpan : SourceSpan)
      (colonParsed : ExactTokenParses (.symbol .colon) input colonSpan
        afterColon)
      (rejectedType : typeRejects afterColon rejected) :
      OptionalLetTypeRejects typeRejects input rejected

/-- A present optional initializer rejects exactly when its expression
rejects. -/
inductive OptionalLetInitializerRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | expressionRejected {input afterEqual rejected : Remainder}
      (equalSpan : SourceSpan)
      (equalParsed : ExactTokenParses (.symbol .equal) input equalSpan
        afterEqual)
      (rejectedExpression : expressionRejects afterEqual rejected) :
      OptionalLetInitializerRejects expressionRejects input rejected

/-- A non-semicolon return value rejects exactly through its expression. -/
inductive OptionalReturnValueRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | expressionRejected {input rejected : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (rejectedExpression : expressionRejects input rejected) :
      OptionalReturnValueRejects expressionRejects input rejected

/-- Exact rejection stage of one canonical Core `let` statement. -/
inductive LetStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerRejected {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .letKw)) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (rejectedName : IdentifierRejects afterMarker rejected) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | typeRejected {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (rejectedType : OptionalLetTypeRejects typeRejects afterName rejected) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | initializerRejected
      {input afterMarker afterName afterType rejected : Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (rejectedInitializer : OptionalLetInitializerRejects expressionRejects
        afterType rejected) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | semicolonRejected
      {input afterMarker afterName afterType afterInitializer : Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      {initializer : Option Syntax.Expr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (initializerParsed : OptionalLetInitializerOrdinaryParses
        expressionOrdinary afterType initializer afterInitializer)
      (semicolonAbsent : TokenKindAbsentAt afterInitializer.tokens
        afterInitializer.endIndex afterInitializer.cursor
          (.symbol .semicolon)) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input afterInitializer

/-- Exact rejection stage of one canonical Core `return` statement. -/
inductive ReturnStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerRejected {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .returnKw)) :
      ReturnStatementRejects expressionOrdinary expressionRejects input input
  | valueRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (rejectedValue : OptionalReturnValueRejects expressionRejects
        afterMarker rejected) :
      ReturnStatementRejects expressionOrdinary expressionRejects input
        rejected
  | semicolonRejected {input afterMarker afterValue : Remainder}
      {value : Option Syntax.Expr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (valueParsed : OptionalReturnValueOrdinaryParses expressionOrdinary
        afterMarker value afterValue)
      (semicolonAbsent : TokenKindAbsentAt afterValue.tokens
        afterValue.endIndex afterValue.cursor (.symbol .semicolon)) :
      ReturnStatementRejects expressionOrdinary expressionRejects input
        afterValue

end Solcore.Syntax.DeclarativeGrammar
