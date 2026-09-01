import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeYulBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeYulFunctionGrammar
import Solcore.Syntax.DeclarativeYulNameOutcomeGrammar

/-!
Parser-independent ordinary successes and exact sequential rejection traces
for inline-Yul function definitions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnosed Yul names are retained in an allow-empty, trailing-comma
parameter list. -/
def YulParametersOrdinaryParses (input : Remainder)
    (parameters : DelimitedList Syntax.YulIdentifier)
    (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftParen .rightParen YulNameOrdinaryParses
    input parameters output

/-- Exact rejection of an ordinary Yul parameter-list attempt. -/
abbrev YulParametersRejects :=
  DelimitedListRejects .leftParen .rightParen true true
    YulNameOrdinaryParses YulNameRejects

/-- Ordinary arrow and nonempty return-name clause. -/
inductive YulReturnClauseOrdinaryParses :
    Remainder → Syntax.YulReturnClause → Remainder → Prop where
  | parsed {input afterArrow output : Remainder}
      {names : YulNamesOrdinaryValue} (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (namesParsed : YulNamesOrdinaryParses afterArrow names output) :
      YulReturnClauseOrdinaryParses input {
        span := SourceSpan.cover arrowSpan names.span
        value := { arrow := arrowSpan, names := names.names }
      } output

/-- Exact sequential rejection of a direct return-clause attempt. -/
inductive YulReturnClauseRejects : Remainder → Remainder → Prop where
  | arrowMissing {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      YulReturnClauseRejects input input
  | namesRejected {input afterArrow rejected : Remainder}
      (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (namesRejected : YulNamesRejects afterArrow rejected) :
      YulReturnClauseRejects input rejected

/-- Prioritized optional ordinary return-name clause. -/
inductive YulReturnsOrdinaryParses :
    Remainder → Option Syntax.YulReturnClause → Remainder → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      YulReturnsOrdinaryParses input none input
  | present {input output : Remainder} {clause : Syntax.YulReturnClause}
      (clauseParsed : YulReturnClauseOrdinaryParses input clause output) :
      YulReturnsOrdinaryParses input (some clause) output

/-- Optional returns reject only after the preferred arrow branch was taken. -/
inductive YulReturnsRejects : Remainder → Remainder → Prop where
  | namesRejected {input afterArrow rejected : Remainder}
      (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (namesRejected : YulNamesRejects afterArrow rejected) :
      YulReturnsRejects input rejected

/-- Exact ordinary function keyword, signature, returns, body, span, and AST. -/
inductive YulFunctionStatementOrdinaryParses
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterName afterParameters afterReturns output :
        Remainder}
      {name : Syntax.YulIdentifier}
      {parameters : DelimitedList Syntax.YulIdentifier}
      {returns : Option Syntax.YulReturnClause} {body : List Syntax.YulStmt}
      (markerSpan bodySpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameOrdinaryParses afterMarker name afterName)
      (parametersParsed : YulParametersOrdinaryParses afterName parameters
        afterParameters)
      (returnsParsed : YulReturnsOrdinaryParses afterParameters returns
        afterReturns)
      (bodyParsed : YulBlockOrdinaryParses statementOrdinary afterReturns
        bodySpan body output) :
      YulFunctionStatementOrdinaryParses statementOrdinary input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .functionDef name parameters returns body
      } output

/-- Exact first-rejecting stage of an ordinary Yul function attempt. -/
inductive YulFunctionStatementRejects
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .functionKw)) :
      YulFunctionStatementRejects statementOrdinary statementRejects input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameRejected : YulNameRejects afterMarker rejected) :
      YulFunctionStatementRejects statementOrdinary statementRejects input
        rejected
  | parametersRejected {input afterMarker afterName rejected : Remainder}
      {name : Syntax.YulIdentifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameOrdinaryParses afterMarker name afterName)
      (parametersRejected : YulParametersRejects afterName rejected) :
      YulFunctionStatementRejects statementOrdinary statementRejects input
        rejected
  | returnsRejected
      {input afterMarker afterName afterParameters rejected : Remainder}
      {name : Syntax.YulIdentifier}
      {parameters : DelimitedList Syntax.YulIdentifier}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameOrdinaryParses afterMarker name afterName)
      (parametersParsed : YulParametersOrdinaryParses afterName parameters
        afterParameters)
      (returnsRejected : YulReturnsRejects afterParameters rejected) :
      YulFunctionStatementRejects statementOrdinary statementRejects input
        rejected
  | bodyRejected
      {input afterMarker afterName afterParameters afterReturns rejected :
        Remainder}
      {name : Syntax.YulIdentifier}
      {parameters : DelimitedList Syntax.YulIdentifier}
      {returns : Option Syntax.YulReturnClause} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameOrdinaryParses afterMarker name afterName)
      (parametersParsed : YulParametersOrdinaryParses afterName parameters
        afterParameters)
      (returnsParsed : YulReturnsOrdinaryParses afterParameters returns
        afterReturns)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterReturns rejected) :
      YulFunctionStatementRejects statementOrdinary statementRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
