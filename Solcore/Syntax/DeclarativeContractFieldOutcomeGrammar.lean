import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-!
Parser-independent ordinary success and exact sequential rejection for one
contract storage field, parameterized by the initializer expression outcome.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional field initializers reuse the exact prioritized strict
success grammar with an abstract expression success relation. -/
abbrev OptionalContractFieldInitializerOrdinaryParses :=
  OptionalContractFieldInitializerParses

/-- A present field initializer rejects only after consuming its exact `=`
token and rejecting the initializer expression. -/
inductive OptionalContractFieldInitializerRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | expressionRejected {input afterEqual rejected : Remainder}
      (equalSpan : SourceSpan)
      (equalParsed : ExactTokenParses (.symbol .equal) input equalSpan
        afterEqual)
      (expressionRejected : expressionRejects afterEqual rejected) :
      OptionalContractFieldInitializerRejects expressionRejects input rejected

/-- Ordinary storage-field success is the existing exact parametric grammar;
public type ordinary success is definitionally the same fixed Core type
grammar used there. -/
abbrev ContractFieldOrdinaryParses := ContractFieldParses

/-- Exact first rejecting stage of one storage-field attempt. -/
inductive ContractFieldRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | nameRejected {input rejected : Remainder}
      (nameRejected : IdentifierRejects input rejected) :
      ContractFieldRejects expressionOrdinary expressionRejects input rejected
  | colonMissing {input afterName : Remainder} {name : Syntax.Identifier}
      (nameParsed : IdentifierParses input name afterName)
      (colonAbsent : TokenKindAbsentAt afterName.tokens afterName.endIndex
        afterName.cursor (.symbol .colon)) :
      ContractFieldRejects expressionOrdinary expressionRejects input afterName
  | typeRejected {input afterName afterColon rejected : Remainder}
      {name : Syntax.Identifier} (colonSpan : SourceSpan)
      (nameParsed : IdentifierParses input name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeRejected : TypeExprRejects afterColon rejected) :
      ContractFieldRejects expressionOrdinary expressionRejects input rejected
  | initializerRejected
      {input afterName afterColon afterType rejected : Remainder}
      {name : Syntax.Identifier} {type : Syntax.TypeExpr}
      (colonSpan : SourceSpan)
      (nameParsed : IdentifierParses input name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeParsed : TypeExprOrdinaryParses afterColon type afterType)
      (initializerRejected : OptionalContractFieldInitializerRejects
        expressionRejects afterType rejected) :
      ContractFieldRejects expressionOrdinary expressionRejects input rejected
  | semicolonMissing
      {input afterName afterColon afterType afterInitializer : Remainder}
      {name : Syntax.Identifier} {type : Syntax.TypeExpr}
      {initializer : Option Syntax.Expr} (colonSpan : SourceSpan)
      (nameParsed : IdentifierParses input name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeParsed : TypeExprOrdinaryParses afterColon type afterType)
      (initializerParsed : OptionalContractFieldInitializerOrdinaryParses
        expressionOrdinary afterType initializer afterInitializer)
      (semicolonAbsent : TokenKindAbsentAt afterInitializer.tokens
        afterInitializer.endIndex afterInitializer.cursor (.symbol .semicolon)) :
      ContractFieldRejects expressionOrdinary expressionRejects input
        afterInitializer

end Solcore.Syntax.DeclarativeGrammar
