import Solcore.Syntax.DeclarativeCoreMatchCasesOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreMatchScrutineeListOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchScrutineesOutcomeProperties

/-!
Diagnostic-inclusive ordinary success and exact rejection for complete Core
`match` statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success of a complete Core `match`.  Arity and missing-arm
validation only emit diagnostics, so they do not restrict this relation. -/
inductive MatchStatementOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterValues afterScrutinees afterOpening
      afterCases afterDefault output : Remainder}
      {values : DelimitedList Syntax.Expr}
      {scrutinees : NonemptyDelimitedList Syntax.Expr}
      {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .matchKw) input markerSpan
        afterMarker)
      (valuesParsed : MatchScrutineeListOrdinaryParses expressionOrdinary
        afterMarker values afterValues)
      (scrutineesRequired : RequireScrutineesOrdinaryParses values afterValues
        scrutinees afterScrutinees)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) afterScrutinees
        openingSpan afterOpening)
      (casesParsed : MatchCasesOrdinaryParses statementOrdinary
        patternOrdinary afterOpening cases afterCases)
      (defaultParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary
        afterCases defaultBody afterDefault)
      (closingParsed : ExactTokenParses (.symbol .rightBrace) afterDefault
        closingSpan output) :
      MatchStatementOrdinaryParses statementOrdinary expressionOrdinary
        patternOrdinary input {
          span := SourceSpan.cover markerSpan closingSpan
          value := .matchWith scrutinees {
            span := SourceSpan.cover openingSpan closingSpan
            value := { cases, defaultBody }
          }
        } output

/-- Exact first ordinary rejection before diagnostic-only validation begins. -/
inductive MatchStatementRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .matchKw)) :
      MatchStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects
        input input
  | valuesRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .matchKw) input markerSpan
        afterMarker)
      (valuesRejected : MatchScrutineeListRejects expressionOrdinary
        expressionRejects afterMarker rejected) :
      MatchStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects
        input rejected
  | scrutineesRejected {input afterMarker afterValues rejected : Remainder}
      {values : DelimitedList Syntax.Expr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .matchKw) input markerSpan
        afterMarker)
      (valuesParsed : MatchScrutineeListOrdinaryParses expressionOrdinary
        afterMarker values afterValues)
      (scrutineesRejected : RequireScrutineesRejects values afterValues
        rejected) :
      MatchStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects
        input rejected
  | openingMissing {input afterMarker afterValues afterScrutinees : Remainder}
      {values : DelimitedList Syntax.Expr}
      {scrutinees : NonemptyDelimitedList Syntax.Expr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .matchKw) input markerSpan
        afterMarker)
      (valuesParsed : MatchScrutineeListOrdinaryParses expressionOrdinary
        afterMarker values afterValues)
      (scrutineesRequired : RequireScrutineesOrdinaryParses values afterValues
        scrutinees afterScrutinees)
      (openingAbsent : TokenKindAbsentAt afterScrutinees.tokens
        afterScrutinees.endIndex afterScrutinees.cursor
          (.symbol .leftBrace)) :
      MatchStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects
        input afterScrutinees
  | casesRejected {input afterMarker afterValues afterScrutinees afterOpening
      rejected : Remainder} {values : DelimitedList Syntax.Expr}
      {scrutinees : NonemptyDelimitedList Syntax.Expr}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .matchKw) input markerSpan
        afterMarker)
      (valuesParsed : MatchScrutineeListOrdinaryParses expressionOrdinary
        afterMarker values afterValues)
      (scrutineesRequired : RequireScrutineesOrdinaryParses values afterValues
        scrutinees afterScrutinees)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) afterScrutinees
        openingSpan afterOpening)
      (casesRejected : MatchCasesRejects statementOrdinary statementRejects
        patternOrdinary patternRejects afterOpening rejected) :
      MatchStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects
        input rejected
  | defaultRejected {input afterMarker afterValues afterScrutinees afterOpening
      afterCases rejected : Remainder} {values : DelimitedList Syntax.Expr}
      {scrutinees : NonemptyDelimitedList Syntax.Expr}
      {cases : List Syntax.MatchCase} (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .matchKw) input markerSpan
        afterMarker)
      (valuesParsed : MatchScrutineeListOrdinaryParses expressionOrdinary
        afterMarker values afterValues)
      (scrutineesRequired : RequireScrutineesOrdinaryParses values afterValues
        scrutinees afterScrutinees)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) afterScrutinees
        openingSpan afterOpening)
      (casesParsed : MatchCasesOrdinaryParses statementOrdinary
        patternOrdinary afterOpening cases afterCases)
      (defaultRejected : OptionalDefaultBodyRejects statementOrdinary
        statementRejects afterCases rejected) :
      MatchStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects
        input rejected
  | closingMissing {input afterMarker afterValues afterScrutinees afterOpening
      afterCases afterDefault : Remainder}
      {values : DelimitedList Syntax.Expr}
      {scrutinees : NonemptyDelimitedList Syntax.Expr}
      {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .matchKw) input markerSpan
        afterMarker)
      (valuesParsed : MatchScrutineeListOrdinaryParses expressionOrdinary
        afterMarker values afterValues)
      (scrutineesRequired : RequireScrutineesOrdinaryParses values afterValues
        scrutinees afterScrutinees)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) afterScrutinees
        openingSpan afterOpening)
      (casesParsed : MatchCasesOrdinaryParses statementOrdinary
        patternOrdinary afterOpening cases afterCases)
      (defaultParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary
        afterCases defaultBody afterDefault)
      (closingAbsent : TokenKindAbsentAt afterDefault.tokens
        afterDefault.endIndex afterDefault.cursor (.symbol .rightBrace)) :
      MatchStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects
        input afterDefault

end Solcore.Syntax.DeclarativeGrammar
