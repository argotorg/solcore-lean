import Solcore.Syntax.Grammar.Statements
import Solcore.Syntax.DeclarativeCoreMatchScrutineeListOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchScrutineesOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementLayerSelectionOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchCasesOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchDefaultOutcomeProperties
import Solcore.Syntax.DeclarativeCoreAssemblyStatementOutcomeProperties
import Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeProperties
import Solcore.Syntax.DeclarativeCoreForStatementOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementIfOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementSimpleCompleteOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementWhileOutcomeProperties

/-!
One prioritized layer of statement dispatch.

The definitions rest on outcome lemmas for `match`, so those lemmas stay in this file.
Main declarations: `StatementLayerOrdinaryParses`, `StatementLayerRejects`,
`MatchStatementOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchStatementOutcomeGrammar
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementLayerOutcomeGrammar
/-! Concrete ordinary relations for the ordered Core statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive success relation selected for each recognized Core
statement stage.  The final stage has no primary parser. -/
def StatementLayerPrimaryOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    StatementLayerStage → Remainder → Syntax.Statement → Remainder → Prop
  | .letGuard => LetStatementOrdinaryParses expressionOrdinary
  | .returnGuard => ReturnStatementOrdinaryParses expressionOrdinary
  | .matchGuard => MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary
  | .forGuard => ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary
  | .whileGuard => WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary
  | .ifGuard => IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary
  | .assemblyGuard => AssemblyStatementOrdinaryParses
  | .blockGuard => BlockStatementOrdinaryParses statementOrdinary
  | .breakGuard => TerminatedControlStatementOrdinaryParses .breakKw
      .breakStmt
  | .continueGuard => TerminatedControlStatementOrdinaryParses .continueKw
      .continueStmt
  | .fallback => fun _ _ _ => False

/-- Exact rejection relation selected for each recognized Core statement
stage.  The final stage has no primary parser. -/
def StatementLayerPrimaryRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :
    StatementLayerStage → Remainder → Remainder → Prop
  | .letGuard => LetStatementRejects expressionOrdinary expressionRejects
      TypeExprRejects
  | .returnGuard => ReturnStatementRejects expressionOrdinary
      expressionRejects
  | .matchGuard => MatchStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects
  | .forGuard => ForStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects
  | .whileGuard => WhileStatementRejects expressionOrdinary expressionRejects
      statementOrdinary statementRejects
  | .ifGuard => IfStatementRejects expressionOrdinary expressionRejects
      statementOrdinary statementRejects
  | .assemblyGuard => AssemblyStatementRejects
  | .blockGuard => BlockStatementRejects statementOrdinary statementRejects
  | .breakGuard => TerminatedControlStatementRejects .breakKw
  | .continueGuard => TerminatedControlStatementRejects .continueKw
  | .fallback => fun _ _ => False

/-- Concrete ordinary success of one prioritized Core statement layer. -/
abbrev StatementLayerOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :=
  StatementLayerSelectionOrdinaryParses
    (StatementLayerPrimaryOrdinaryParses statementOrdinary expressionOrdinary
      patternOrdinary)
    (StatementLayerPrimaryRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects)
    (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)

/-- Concrete exact rejection of one prioritized Core statement layer. -/
abbrev StatementLayerRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :=
  StatementLayerSelectionRejects
    (StatementLayerPrimaryOrdinaryParses statementOrdinary expressionOrdinary
      patternOrdinary)
    (StatementLayerPrimaryRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects)
    (AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchStatementOrdinaryProperties
/-! Output functionality for diagnostic-inclusive Core match statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem requireScrutinees_outputs_eq
    {leftValues rightValues : DelimitedList Syntax.Expr}
    {input leftOutput rightOutput : Remainder}
    {left right : NonemptyDelimitedList Syntax.Expr}
    (leftParsed : RequireScrutineesOrdinaryParses leftValues input left
      leftOutput)
    (rightParsed : RequireScrutineesOrdinaryParses rightValues input right
      rightOutput) : leftOutput = rightOutput := by
  cases leftParsed
  cases rightParsed
  rfl

/-- Ordinary complete-match success has one final remainder. -/
theorem MatchStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input left afterLeft)
    (rightParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input right afterRight) :
    afterLeft = afterRight := by
  have valuesOutcomes := matchScrutineeListDeterministicOutcomeSpec
    expressionOutcomes
  have casesOutcomes := matchCasesDeterministicOutcomeSpec statementOutcomes
    patternOutcomes
  have defaultOutcomes := optionalDefaultBodyDeterministicOutcomeSpec
    statementOutcomes
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftValues leftRequired leftOpening leftCases leftDefault leftClosing =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightValues rightRequired rightOpening rightCases rightDefault
            rightClosing =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique leftValues
            rightValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq leftRequired
            rightRequired
          cases afterRequiredEq
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          cases afterOpeningEq
          have afterCasesEq := casesOutcomes.successOutputUnique leftCases
            rightCases
          cases afterCasesEq
          have afterDefaultEq := defaultOutcomes.successOutputUnique leftDefault
            rightDefault
          cases afterDefaultEq
          exact exactToken_output_unique leftClosing rightClosing

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchStatementRejectionProperties
/-! Rejection exclusivity for diagnostic-inclusive Core match statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem scrutineeList_conflicts_requireReject
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input afterValues rejected : Remainder}
    {values : DelimitedList Syntax.Expr}
    (valuesParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      values afterValues)
    (requiredRejected : RequireScrutineesRejects values afterValues rejected) :
    False := by
  rcases valuesParsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  cases requiredRejected with
  | empty emptyValues =>
      have impossible : first :: rest = [] := elementsEq.symm.trans emptyValues
      contradiction

/-- Exact pre-validation rejection excludes every ordinary match success. -/
theorem MatchStatementRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input rejected : Remainder}
    (rejection : MatchStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects
        input rejected) :
    ¬ ∃ value output,
      MatchStatementOrdinaryParses statementOrdinary expressionOrdinary
        patternOrdinary input value output := by
  rintro ⟨value, output, successful⟩
  have valuesOutcomes := matchScrutineeListDeterministicOutcomeSpec
    expressionOutcomes
  have casesOutcomes := matchCasesDeterministicOutcomeSpec statementOutcomes
    patternOutcomes
  have defaultOutcomes := optionalDefaultBodyDeterministicOutcomeSpec
    statementOutcomes
  cases successful with
  | parsed successfulMarkerSpan successfulOpeningSpan successfulClosingSpan
        successfulMarker successfulValues successfulRequired
        successfulOpening successfulCases successfulDefault
        successfulClosing =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | valuesRejected rejectedMarkerSpan rejectedMarker rejectedValues =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact valuesOutcomes.successRejectDisjoint rejectedValues
            ⟨_, _, successfulValues⟩
      | scrutineesRejected rejectedMarkerSpan rejectedMarker rejectedValues
            rejectedRequired =>
          exact scrutineeList_conflicts_requireReject rejectedValues
            rejectedRequired
      | openingMissing rejectedMarkerSpan rejectedMarker rejectedValues
            rejectedRequired openingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique
            rejectedValues successfulValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq
            rejectedRequired successfulRequired
          cases afterRequiredEq
          exact absent_conflicts_exact openingAbsent successfulOpening
      | casesRejected rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedValues rejectedRequired rejectedOpening rejectedCases =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique
            rejectedValues successfulValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq
            rejectedRequired successfulRequired
          cases afterRequiredEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          exact casesOutcomes.successRejectDisjoint rejectedCases
            ⟨_, _, successfulCases⟩
      | defaultRejected rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedValues rejectedRequired rejectedOpening rejectedCases
            rejectedDefault =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique
            rejectedValues successfulValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq
            rejectedRequired successfulRequired
          cases afterRequiredEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          have afterCasesEq := casesOutcomes.successOutputUnique rejectedCases
            successfulCases
          cases afterCasesEq
          exact defaultOutcomes.successRejectDisjoint rejectedDefault
            ⟨_, _, successfulDefault⟩
      | closingMissing rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedValues rejectedRequired rejectedOpening rejectedCases
            rejectedDefault closingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique
            rejectedValues successfulValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq
            rejectedRequired successfulRequired
          cases afterRequiredEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          have afterCasesEq := casesOutcomes.successOutputUnique rejectedCases
            successfulCases
          cases afterCasesEq
          have afterDefaultEq := defaultOutcomes.successOutputUnique
            rejectedDefault successfulDefault
          cases afterDefaultEq
          exact absent_conflicts_exact closingAbsent successfulClosing

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchStatementOutcomeProperties
/-! Deterministic diagnostic-inclusive outcomes for complete Core matches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lift recursive term outcomes through a complete Core `match`. -/
theorem matchStatementDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects) :
    DeterministicOutcomeSpec
      (MatchStatementOrdinaryParses statementOrdinary expressionOrdinary
        patternOrdinary)
      (MatchStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary
          patternRejects) where
  successOutputUnique := MatchStatementOrdinaryParses.output_unique
    statementOutcomes expressionOutcomes patternOutcomes
  successRejectDisjoint := MatchStatementRejects.disjointOrdinary
    statementOutcomes expressionOutcomes patternOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementLayerOutcomeProperties
/-! Deterministic concrete outcomes for one ordered Core statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Each recognized stage inherits the deterministic contract of its concrete
Core statement parser. -/
theorem statementLayerPrimaryDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    (stage : StatementLayerStage) (notFallback : stage ≠ .fallback) :
    DeterministicOutcomeSpec
      (StatementLayerPrimaryOrdinaryParses statementOrdinary
        expressionOrdinary patternOrdinary stage)
      (StatementLayerPrimaryRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects
          stage) := by
  cases stage with
  | letGuard =>
      exact letStatementDeterministicOutcomeSpec expressionOutcomes
        typeExprDeterministicOutcomeSpec
  | returnGuard =>
      exact returnStatementDeterministicOutcomeSpec expressionOutcomes
  | matchGuard =>
      exact matchStatementDeterministicOutcomeSpec statementOutcomes
        expressionOutcomes patternOutcomes
  | forGuard =>
      exact forStatementDeterministicOutcomeSpec statementOutcomes
        expressionOutcomes
  | whileGuard =>
      exact whileStatementDeterministicOutcomeSpec expressionOutcomes
        statementOutcomes
  | ifGuard =>
      exact ifStatementDeterministicOutcomeSpec expressionOutcomes
        statementOutcomes
  | assemblyGuard => exact assemblyStatementDeterministicOutcomeSpec
  | blockGuard =>
      exact blockStatementDeterministicOutcomeSpec statementOutcomes
  | breakGuard =>
      exact terminatedControlStatementDeterministicOutcomeSpec .breakKw
        .breakStmt
  | continueGuard =>
      exact terminatedControlStatementDeterministicOutcomeSpec .continueKw
        .continueStmt
  | fallback => contradiction

/-- Recursive statement, expression, and pattern outcomes lift through the
complete let-prioritized Core statement dispatcher. -/
theorem statementLayerDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects) :
    DeterministicOutcomeSpec
      (StatementLayerOrdinaryParses statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects)
      (StatementLayerRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary
          patternRejects) :=
  statementLayerSelectionDeterministicOutcomeSpec
    (StatementLayerPrimaryOrdinaryParses statementOrdinary expressionOrdinary
      patternOrdinary)
    (StatementLayerPrimaryRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects)
    (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)
    (AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects)
    (statementLayerPrimaryDeterministicOutcomeSpec statementOutcomes
      expressionOutcomes patternOutcomes)
    (assignmentOrExpressionStatementDeterministicOutcomeSpec
      expressionOutcomes)

end Solcore.Syntax.DeclarativeGrammar
end
