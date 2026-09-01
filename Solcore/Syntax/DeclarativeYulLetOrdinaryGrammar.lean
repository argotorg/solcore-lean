import Solcore.Syntax.DeclarativeYulExpressionFuelGrammar
import Solcore.Syntax.DeclarativeYulNameOutcomeGrammar
import Solcore.Syntax.DeclarativeYulStatementBasicGrammar

/-!
Parser-independent ordinary success and exact rejection for public inline-Yul
`let` declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional initializer success with exact `:=` priority. -/
inductive YulLetInitializerOrdinaryParses :
    Remainder → Option Syntax.YulExpr → Remainder → Prop where
  | absent {input : Remainder}
      (operatorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .colonEqual)) :
      YulLetInitializerOrdinaryParses input none input
  | present {input afterOperator output : Remainder}
      {value : Syntax.YulExpr} (operatorSpan : SourceSpan)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) input
        operatorSpan afterOperator)
      (valueParsed : YulExpressionOrdinaryParses afterOperator value output) :
      YulLetInitializerOrdinaryParses input (some value) output

/-- An optional initializer rejects only after a present `:=` when its public
expression rejects.  The rejected remainder is retained exactly. -/
inductive YulLetInitializerRejects : Remainder → Remainder → Prop where
  | expressionRejected
      {input afterOperator rejected : Remainder}
      (operatorSpan : SourceSpan)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) input
        operatorSpan afterOperator)
      (valueRejected : YulExpressionRejects afterOperator rejected) :
      YulLetInitializerRejects input rejected

/-- Ordinary public `let` success, retaining diagnosed names and expression
success while preserving its exact AST and covering span. -/
inductive YulLetStatementOrdinaryParses :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterNames output : Remainder}
      {names : YulNamesOrdinaryValue}
      {initializer : Option Syntax.YulExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (namesParsed : YulNamesOrdinaryParses afterMarker names afterNames)
      (initializerParsed : YulLetInitializerOrdinaryParses afterNames
        initializer output) :
      YulLetStatementOrdinaryParses input {
        span := SourceSpan.cover markerSpan
          (yulLetEnd names.span initializer)
        value := .letDecl names.names initializer
      } output

/-- Exact public `let` rejection at its marker, name sequence, or present
initializer expression. -/
inductive YulLetStatementRejects : Remainder → Remainder → Prop where
  | markerRejected {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .letKw)) :
      YulLetStatementRejects input input
  | namesRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (namesRejected : YulNamesRejects afterMarker rejected) :
      YulLetStatementRejects input rejected
  | initializerRejected
      {input afterMarker afterNames rejected : Remainder}
      {names : YulNamesOrdinaryValue}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (namesParsed : YulNamesOrdinaryParses afterMarker names afterNames)
      (initializerRejected : YulLetInitializerRejects afterNames rejected) :
      YulLetStatementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
