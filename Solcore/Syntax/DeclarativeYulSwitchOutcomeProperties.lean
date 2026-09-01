import Solcore.Syntax.DeclarativeYulSwitchCaseOutcomeProperties

/-!
Deterministic outcomes and clean embedding for complete ordinary inline-Yul
switch statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem switchStages_output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input leftAfterMarker rightAfterMarker leftAfterScrutinee
      rightAfterScrutinee leftAfterCases rightAfterCases leftOutput
      rightOutput : Remainder}
    {leftScrutinee rightScrutinee : Syntax.YulExpr}
    {leftCases rightCases : List Syntax.YulCase}
    {leftDefaultSpan rightDefaultSpan : Option SourceSpan}
    {leftDefaultBody rightDefaultBody : Option (List Syntax.YulStmt)}
    {leftMarkerSpan rightMarkerSpan : SourceSpan}
    (leftMarkerParsed : ExactTokenParses (.keyword .switchKw) input
      leftMarkerSpan leftAfterMarker)
    (leftScrutineeParsed : YulExpressionOrdinaryParses leftAfterMarker
      leftScrutinee leftAfterScrutinee)
    (leftCasesParsed : YulCaseListOrdinaryParses statementOrdinary
      leftAfterScrutinee leftCases leftAfterCases)
    (leftDefaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
      leftAfterCases leftDefaultSpan leftDefaultBody leftOutput)
    (rightMarkerParsed : ExactTokenParses (.keyword .switchKw) input
      rightMarkerSpan rightAfterMarker)
    (rightScrutineeParsed : YulExpressionOrdinaryParses rightAfterMarker
      rightScrutinee rightAfterScrutinee)
    (rightCasesParsed : YulCaseListOrdinaryParses statementOrdinary
      rightAfterScrutinee rightCases rightAfterCases)
    (rightDefaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
      rightAfterCases rightDefaultSpan rightDefaultBody rightOutput) :
    leftOutput = rightOutput := by
  have afterMarkerEq := exactToken_output_unique leftMarkerParsed
    rightMarkerParsed
  subst afterMarkerEq
  have afterScrutineeEq :=
    yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
      leftScrutineeParsed rightScrutineeParsed
  subst afterScrutineeEq
  have afterCasesEq := leftCasesParsed.output_unique statementOutcomes
    rightCasesParsed
  subst afterCasesEq
  exact leftDefaultParsed.output_unique statementOutcomes rightDefaultParsed

private theorem switchStages_disjoint
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input afterMarker afterScrutinee afterCases output rejected : Remainder}
    {scrutinee : Syntax.YulExpr} {cases : List Syntax.YulCase}
    {defaultSpan : Option SourceSpan}
    {defaultBody : Option (List Syntax.YulStmt)} {markerSpan : SourceSpan}
    (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
      afterMarker)
    (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
      afterScrutinee)
    (casesParsed : YulCaseListOrdinaryParses statementOrdinary
      afterScrutinee cases afterCases)
    (defaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
      afterCases defaultSpan defaultBody output)
    (rejection : YulSwitchStatementRejects statementOrdinary statementRejects
      input rejected) : False := by
  cases rejection with
  | markerMissing markerAbsent =>
      exact absent_conflicts_exact markerAbsent markerParsed
  | scrutineeRejected rejectedMarkerSpan rejectedMarkerParsed
        scrutineeRejected =>
      have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
        markerParsed
      subst afterMarkerEq
      exact yulExpressionPublicDeterministicOutcomeSpec
        |>.successRejectDisjoint scrutineeRejected ⟨_, _, scrutineeParsed⟩
  | casesRejected rejectedMarkerSpan rejectedMarkerParsed
        rejectedScrutineeParsed casesRejected =>
      have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
        markerParsed
      subst afterMarkerEq
      have afterScrutineeEq :=
        yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
          rejectedScrutineeParsed scrutineeParsed
      subst afterScrutineeEq
      exact casesRejected.disjointOrdinary statementOutcomes
        ⟨_, _, casesParsed⟩
  | defaultRejected rejectedMarkerSpan rejectedMarkerParsed
        rejectedScrutineeParsed rejectedCasesParsed defaultRejected =>
      have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
        markerParsed
      subst afterMarkerEq
      have afterScrutineeEq :=
        yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
          rejectedScrutineeParsed scrutineeParsed
      subst afterScrutineeEq
      have afterCasesEq := rejectedCasesParsed.output_unique statementOutcomes
        casesParsed
      subst afterCasesEq
      exact defaultRejected.disjointOrdinary statementOutcomes
        ⟨_, _, _, defaultParsed⟩

/-- Ordinary complete-switch success has a unique final remainder. -/
theorem YulSwitchStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulSwitchStatementOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : YulSwitchStatementOrdinaryParses statementOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | nonempty leftMarkerSpan leftMarkerParsed leftScrutineeParsed
        leftCasesParsed leftDefaultParsed =>
      cases rightParsed with
      | nonempty rightMarkerSpan rightMarkerParsed rightScrutineeParsed
            rightCasesParsed rightDefaultParsed =>
          exact switchStages_output_unique statementOutcomes leftMarkerParsed
            leftScrutineeParsed leftCasesParsed leftDefaultParsed
            rightMarkerParsed rightScrutineeParsed rightCasesParsed
            rightDefaultParsed
      | empty rightMarkerSpan rightMarkerParsed rightScrutineeParsed
            rightCasesParsed rightDefaultParsed =>
          exact switchStages_output_unique statementOutcomes leftMarkerParsed
            leftScrutineeParsed leftCasesParsed leftDefaultParsed
            rightMarkerParsed rightScrutineeParsed rightCasesParsed
            rightDefaultParsed
  | empty leftMarkerSpan leftMarkerParsed leftScrutineeParsed leftCasesParsed
        leftDefaultParsed =>
      cases rightParsed with
      | nonempty rightMarkerSpan rightMarkerParsed rightScrutineeParsed
            rightCasesParsed rightDefaultParsed =>
          exact switchStages_output_unique statementOutcomes leftMarkerParsed
            leftScrutineeParsed leftCasesParsed leftDefaultParsed
            rightMarkerParsed rightScrutineeParsed rightCasesParsed
            rightDefaultParsed
      | empty rightMarkerSpan rightMarkerParsed rightScrutineeParsed
            rightCasesParsed rightDefaultParsed =>
          exact switchStages_output_unique statementOutcomes leftMarkerParsed
            leftScrutineeParsed leftCasesParsed leftDefaultParsed
            rightMarkerParsed rightScrutineeParsed rightCasesParsed
            rightDefaultParsed

/-- Exact complete-switch rejection excludes every ordinary success. -/
theorem YulSwitchStatementRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulSwitchStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulSwitchStatementOrdinaryParses statementOrdinary input statement
        output := by
  rintro ⟨statement, output, successful⟩
  cases successful <;>
    apply switchStages_disjoint statementOutcomes <;> assumption

/-- Ordinary switch success and exact rejection form a deterministic outcome. -/
theorem yulSwitchStatementDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (YulSwitchStatementOrdinaryParses statementOrdinary)
      (YulSwitchStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulSwitchStatementOrdinaryParses.output_unique statementOutcomes
  successRejectDisjoint :=
    YulSwitchStatementRejects.disjointOrdinary statementOutcomes

/-- A clean case arm embeds into the ordinary case-arm relation. -/
theorem YulCaseArmParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {arm : Syntax.YulCase}
    (parsed : YulCaseArmParses statementClean input arm output) :
    YulCaseArmOrdinaryParses statementOrdinary input arm output := by
  cases parsed with
  | parsed markerSpan bodySpan markerParsed literalParsed bodyParsed =>
      exact .parsed markerSpan bodySpan markerParsed literalParsed
        (bodyParsed.toOrdinary cleanToOrdinary)

/-- A clean maximal case list embeds into the ordinary list relation. -/
theorem YulCaseListParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {cases : List Syntax.YulCase}
    (parsed : YulCaseListParses statementClean input cases output) :
    YulCaseListOrdinaryParses statementOrdinary input cases output := by
  induction parsed with
  | done caseAbsent => exact .done caseAbsent
  | next armParsed progress tail inductionHypothesis =>
      exact .next (armParsed.toOrdinary cleanToOrdinary) progress
        inductionHypothesis

/-- A clean optional default embeds into its ordinary relation. -/
theorem OptionalYulDefaultParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {defaultSpan : Option SourceSpan}
    {defaultBody : Option (List Syntax.YulStmt)}
    (parsed : OptionalYulDefaultParses statementClean input defaultSpan
      defaultBody output) :
    OptionalYulDefaultOrdinaryParses statementOrdinary input defaultSpan
      defaultBody output := by
  cases parsed with
  | absent defaultAbsent => exact .absent defaultAbsent
  | present markerSpan bodySpan markerParsed bodyParsed =>
      exact .present markerSpan bodySpan markerParsed
        (bodyParsed.toOrdinary cleanToOrdinary)

/-- Every diagnostic-free switch derivation embeds into ordinary success. -/
theorem YulSwitchStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulSwitchStatementParses statementClean YulExpressionParses
      input statement output) :
    YulSwitchStatementOrdinaryParses statementOrdinary input statement
      output := by
  cases parsed with
  | parsed markerSpan markerParsed scrutineeParsed casesParsed
        defaultParsed =>
      exact .nonempty markerSpan markerParsed scrutineeParsed.toOrdinary
        (casesParsed.toOrdinary cleanToOrdinary)
        (defaultParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
