import Solcore.Syntax.DeclarativeDelimitedFallbackProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingSuccessProperties
import Solcore.Syntax.DeclarativeYulBlockOutcomeProperties
import Solcore.Syntax.DeclarativeYulFunctionOutcomeGrammar
import Solcore.Syntax.DeclarativeYulNameOutcomeProperties

/-!
Functionality, rejection exclusivity, and clean embeddings for ordinary
inline-Yul function outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Ordinary parameter-list output is functional. -/
theorem YulParametersOrdinaryParses.output_unique
    {input : Remainder} {left right : DelimitedList Syntax.YulIdentifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulParametersOrdinaryParses input left afterLeft)
    (rightParsed : YulParametersOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold YulParametersOrdinaryParses at leftParsed rightParsed
  exact TrailingDelimitedListParses.output_unique
    (opening := .leftParen) (closing := .rightParen)
    (elementParses := YulNameOrdinaryParses)
    (fun leftName rightName => leftName.output_unique rightName)
    leftParsed rightParsed

/-- Exact parameter rejection excludes ordinary parameter success. -/
theorem YulParametersRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : YulParametersRejects input rejected) :
    ¬ ∃ parameters output,
      YulParametersOrdinaryParses input parameters output := by
  exact rejection.disjointAllowEmptyTrailing
    yulNameDeterministicOutcomeSpec (fun parsed => parsed)

/-- Ordinary return-clause output is functional. -/
theorem YulReturnClauseOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.YulReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnClauseOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnClauseOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftArrowSpan leftArrow leftNames =>
      cases rightParsed with
      | parsed rightArrowSpan rightArrow rightNames =>
          have afterArrowEq := exactToken_output_unique leftArrow rightArrow
          subst afterArrowEq
          exact leftNames.output_unique rightNames

/-- Direct return-clause rejection excludes ordinary success. -/
theorem YulReturnClauseRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : YulReturnClauseRejects input rejected) :
    ¬ ∃ clause output,
      YulReturnClauseOrdinaryParses input clause output := by
  rintro ⟨clause, output, successful⟩
  cases successful with
  | parsed successfulArrowSpan successfulArrow successfulNames =>
      cases rejection with
      | arrowMissing arrowAbsent =>
          exact absent_conflicts_exact arrowAbsent successfulArrow
      | namesRejected rejectedArrowSpan rejectedArrow namesRejected =>
          have afterArrowEq := exactToken_output_unique rejectedArrow
            successfulArrow
          subst afterArrowEq
          exact namesRejected.disjoint ⟨_, _, successfulNames⟩

/-- Direct return-clause outcomes are deterministic and exclusive. -/
theorem yulReturnClauseDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulReturnClauseOrdinaryParses
      YulReturnClauseRejects where
  successOutputUnique := YulReturnClauseOrdinaryParses.output_unique
  successRejectDisjoint := YulReturnClauseRejects.disjointOrdinary

/-- Optional-return output is functional, including arrow branch priority. -/
theorem YulReturnsOrdinaryParses.output_unique
    {input : Remainder} {left right : Option Syntax.YulReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnsOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnsOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightClause =>
          cases rightClause with
          | parsed arrowSpan arrowParsed namesParsed =>
              exact False.elim
                (absent_conflicts_exact leftAbsent arrowParsed)
  | present leftClause =>
      cases rightParsed with
      | absent rightAbsent =>
          cases leftClause with
          | parsed arrowSpan arrowParsed namesParsed =>
              exact False.elim
                (absent_conflicts_exact rightAbsent arrowParsed)
      | present rightClause =>
          exact leftClause.output_unique rightClause

/-- Preferred optional-return rejection excludes both optional successes. -/
theorem YulReturnsRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : YulReturnsRejects input rejected) :
    ¬ ∃ returns output, YulReturnsOrdinaryParses input returns output := by
  rintro ⟨returns, output, successful⟩
  cases rejection with
  | namesRejected rejectedArrowSpan rejectedArrow namesRejected =>
      cases successful with
      | absent arrowAbsent =>
          exact absent_conflicts_exact arrowAbsent rejectedArrow
      | present clauseParsed =>
          cases clauseParsed with
          | parsed successfulArrowSpan successfulArrow successfulNames =>
              have afterArrowEq := exactToken_output_unique rejectedArrow
                successfulArrow
              subst afterArrowEq
              exact namesRejected.disjoint ⟨_, _, successfulNames⟩

/-- Optional-return outcomes are deterministic and exclusive. -/
theorem yulReturnsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulReturnsOrdinaryParses YulReturnsRejects where
  successOutputUnique := YulReturnsOrdinaryParses.output_unique
  successRejectDisjoint := YulReturnsRejects.disjointOrdinary

/-- Ordinary function success has a unique final remainder. -/
theorem YulFunctionStatementOrdinaryParses.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulFunctionStatementOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : YulFunctionStatementOrdinaryParses statementOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftBodySpan leftMarker leftName leftParameters
        leftReturns leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightBodySpan rightMarker rightName
            rightParameters rightReturns rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          have afterReturnsEq := leftReturns.output_unique rightReturns
          subst afterReturnsEq
          exact leftBody.output_unique outcomes rightBody

/-- Exact function rejection excludes every ordinary function success. -/
theorem YulFunctionStatementRejects.disjointOrdinary
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : YulFunctionStatementRejects statementOrdinary
      statementRejects input rejected) :
    ¬ ∃ statement output,
      YulFunctionStatementOrdinaryParses statementOrdinary input statement
        output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulBodySpan successfulMarker
        successfulName successfulParameters successfulReturns successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker nameRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact nameRejected.disjoint ⟨_, _, successfulName⟩
      | parametersRejected rejectedMarkerSpan rejectedMarker rejectedName
            parametersRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          exact parametersRejected.disjointOrdinary
            ⟨_, _, successfulParameters⟩
      | returnsRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedParameters returnsRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          exact returnsRejected.disjointOrdinary ⟨_, _, successfulReturns⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedParameters rejectedReturns bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterReturnsEq := rejectedReturns.output_unique successfulReturns
          subst afterReturnsEq
          exact bodyRejected.disjointOrdinary outcomes
            ⟨_, _, _, successfulBody⟩

/-- Ordinary function successes and exact rejections form a deterministic
outcome contract. -/
theorem yulFunctionStatementDeterministicOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects) :
    DeterministicOutcomeSpec
      (YulFunctionStatementOrdinaryParses statementOrdinary)
      (YulFunctionStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulFunctionStatementOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    YulFunctionStatementRejects.disjointOrdinary outcomes

/-- Every clean parameter list embeds into ordinary parameter success. -/
theorem YulParametersParses.toOrdinary {input output : Remainder}
    {parameters : DelimitedList Syntax.YulIdentifier}
    (parsed : YulParametersParses input parameters output) :
    YulParametersOrdinaryParses input parameters output :=
  parsed.mapElementRelation YulNameParses.toOrdinary

/-- Every clean return clause embeds into ordinary success. -/
theorem YulReturnClauseParses.toOrdinary {input output : Remainder}
    {clause : Syntax.YulReturnClause}
    (parsed : YulReturnClauseParses input clause output) :
    YulReturnClauseOrdinaryParses input clause output := by
  cases parsed with
  | parsed arrowSpan namesSpan arrowParsed namesParsed =>
      exact .parsed arrowSpan arrowParsed namesParsed.toOrdinary

/-- Every clean optional return clause embeds into ordinary success. -/
theorem YulReturnsParses.toOrdinary {input output : Remainder}
    {returns : Option Syntax.YulReturnClause}
    (parsed : YulReturnsParses input returns output) :
    YulReturnsOrdinaryParses input returns output := by
  cases parsed with
  | absent arrowAbsent => exact .absent arrowAbsent
  | present clauseParsed => exact .present clauseParsed.toOrdinary

/-- Every clean function embeds into ordinary success with identical AST,
span, order, and remainder. -/
theorem YulFunctionStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulFunctionStatementParses statementClean input statement
      output) :
    YulFunctionStatementOrdinaryParses statementOrdinary input statement
      output := by
  cases parsed with
  | parsed markerSpan bodySpan markerParsed nameParsed parametersParsed
        returnsParsed bodyParsed =>
      exact .parsed markerSpan bodySpan markerParsed nameParsed.toOrdinary
        parametersParsed.toOrdinary returnsParsed.toOrdinary
        (bodyParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
