import Solcore.Syntax.DeclarativeYulBlockGrammar
import Solcore.Syntax.DeclarativeYulNamesGrammar

/-!
Parser-independent grammar for inline-Yul function signatures and bodies.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Allow-empty, trailing-comma parameter grammar used by Yul functions. -/
def YulParametersParses (input : Remainder)
    (parameters : DelimitedList Syntax.YulIdentifier)
    (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftParen .rightParen YulNameParses input
    parameters output

/-- Exact arrow and nonempty return-name clause. -/
inductive YulReturnClauseParses :
    Remainder → Syntax.YulReturnClause → Remainder → Prop where
  | parsed {input afterArrow output : Remainder}
      {names : NonemptyList Syntax.YulIdentifier}
      (arrowSpan namesSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (namesParsed : YulNamesParses afterArrow namesSpan names output) :
      YulReturnClauseParses input {
        span := SourceSpan.cover arrowSpan namesSpan
        value := { arrow := arrowSpan, names }
      } output

/-- Prioritized optional function return-name clause. -/
inductive YulReturnsParses :
    Remainder → Option Syntax.YulReturnClause → Remainder → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      YulReturnsParses input none input
  | present {input output : Remainder} {clause : Syntax.YulReturnClause}
      (clauseParsed : YulReturnClauseParses input clause output) :
      YulReturnsParses input (some clause) output

/-- Exact function keyword, signature, returns, body, span, and AST. -/
inductive YulFunctionStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterName afterParameters afterReturns output :
        Remainder}
      {name : Syntax.YulIdentifier}
      {parameters : DelimitedList Syntax.YulIdentifier}
      {returns : Option Syntax.YulReturnClause} {body : List Syntax.YulStmt}
      (markerSpan bodySpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameParses afterMarker name afterName)
      (parametersParsed : YulParametersParses afterName parameters
        afterParameters)
      (returnsParsed : YulReturnsParses afterParameters returns afterReturns)
      (bodyParsed : YulBlockParses statementParses afterReturns bodySpan body
        output) :
      YulFunctionStatementParses statementParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .functionDef name parameters returns body
      } output

end Solcore.Syntax.DeclarativeGrammar
