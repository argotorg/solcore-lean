import Solcore.Syntax.DeclarativeYulBlockOutcomeProperties
import Solcore.Syntax.DeclarativeYulStatementControlOutcomeGrammar

/-!
Functionality, rejection exclusivity, and clean embedding for ordinary
inline-Yul `if` and `for` outcomes.
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

/-- Ordinary `if` success has a unique output remainder. -/
theorem YulIfStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulIfStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulIfStatementOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarkerParsed leftConditionParsed
        leftBodyParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarkerParsed rightConditionParsed
            rightBodyParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              leftConditionParsed rightConditionParsed
          subst afterConditionEq
          exact leftBodyParsed.output_unique statementOutcomes rightBodyParsed

/-- Exact `if` rejection excludes every ordinary `if` success. -/
theorem YulIfStatementRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulIfStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulIfStatementOrdinaryParses statementOrdinary input statement output :=
by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarkerParsed
        successfulConditionParsed successfulBodyParsed =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarkerParsed
      | conditionRejected rejectedMarkerSpan rejectedMarkerParsed
            conditionRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact yulExpressionPublicDeterministicOutcomeSpec
            |>.successRejectDisjoint conditionRejected
              ⟨_, _, successfulConditionParsed⟩
      | bodyRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedConditionParsed bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              rejectedConditionParsed successfulConditionParsed
          subst afterConditionEq
          exact bodyRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulBodyParsed⟩

/-- Ordinary `if` success and rejection form a deterministic outcome. -/
theorem yulIfStatementDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (YulIfStatementOrdinaryParses statementOrdinary)
      (YulIfStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulIfStatementOrdinaryParses.output_unique statementOutcomes
  successRejectDisjoint :=
    YulIfStatementRejects.disjointOrdinary statementOutcomes

/-- A clean `if` derivation embeds into the ordinary `if` relation. -/
theorem YulIfStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementCleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulIfStatementParses statementClean YulExpressionParses input
      statement output) :
    YulIfStatementOrdinaryParses statementOrdinary input statement output := by
  cases parsed with
  | parsed markerSpan markerParsed conditionParsed bodyParsed =>
      exact .parsed markerSpan markerParsed conditionParsed.toOrdinary
        (bodyParsed.toOrdinary statementCleanToOrdinary)

/-- Ordinary `for` success has a unique output remainder. -/
theorem YulForStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulForStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulForStatementOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarkerParsed leftInitializerParsed
        leftConditionParsed leftPostParsed leftBodyParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarkerParsed rightInitializerParsed
            rightConditionParsed rightPostParsed rightBodyParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          have afterInitializerEq := leftInitializerParsed.output_unique
            statementOutcomes rightInitializerParsed
          subst afterInitializerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              leftConditionParsed rightConditionParsed
          subst afterConditionEq
          have afterPostEq := leftPostParsed.output_unique statementOutcomes
            rightPostParsed
          subst afterPostEq
          exact leftBodyParsed.output_unique statementOutcomes rightBodyParsed

/-- Exact `for` rejection excludes every ordinary `for` success. -/
theorem YulForStatementRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulForStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulForStatementOrdinaryParses statementOrdinary input statement output :=
by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarkerParsed
        successfulInitializerParsed successfulConditionParsed
        successfulPostParsed successfulBodyParsed =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarkerParsed
      | initializerRejected rejectedMarkerSpan rejectedMarkerParsed
            initializerRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact initializerRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulInitializerParsed⟩
      | conditionRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedInitializerParsed conditionRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterInitializerEq := rejectedInitializerParsed.output_unique
            statementOutcomes successfulInitializerParsed
          subst afterInitializerEq
          exact yulExpressionPublicDeterministicOutcomeSpec
            |>.successRejectDisjoint conditionRejected
              ⟨_, _, successfulConditionParsed⟩
      | postRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedInitializerParsed rejectedConditionParsed postRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterInitializerEq := rejectedInitializerParsed.output_unique
            statementOutcomes successfulInitializerParsed
          subst afterInitializerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              rejectedConditionParsed successfulConditionParsed
          subst afterConditionEq
          exact postRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulPostParsed⟩
      | bodyRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedInitializerParsed rejectedConditionParsed
            rejectedPostParsed bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterInitializerEq := rejectedInitializerParsed.output_unique
            statementOutcomes successfulInitializerParsed
          subst afterInitializerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              rejectedConditionParsed successfulConditionParsed
          subst afterConditionEq
          have afterPostEq := rejectedPostParsed.output_unique
            statementOutcomes successfulPostParsed
          subst afterPostEq
          exact bodyRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulBodyParsed⟩

/-- Ordinary `for` success and rejection form a deterministic outcome. -/
theorem yulForStatementDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (YulForStatementOrdinaryParses statementOrdinary)
      (YulForStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulForStatementOrdinaryParses.output_unique statementOutcomes
  successRejectDisjoint :=
    YulForStatementRejects.disjointOrdinary statementOutcomes

/-- A clean `for` derivation embeds into the ordinary `for` relation. -/
theorem YulForStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementCleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulForStatementParses statementClean YulExpressionParses input
      statement output) :
    YulForStatementOrdinaryParses statementOrdinary input statement output :=
by
  cases parsed with
  | parsed markerSpan markerParsed initializerParsed conditionParsed
        postParsed bodyParsed =>
      exact .parsed markerSpan markerParsed
        (initializerParsed.toOrdinary statementCleanToOrdinary)
        conditionParsed.toOrdinary
        (postParsed.toOrdinary statementCleanToOrdinary)
        (bodyParsed.toOrdinary statementCleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
