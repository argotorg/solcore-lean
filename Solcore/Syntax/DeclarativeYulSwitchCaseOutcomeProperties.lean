import Solcore.Syntax.DeclarativeYulBlockOutcomeProperties
import Solcore.Syntax.DeclarativeYulExpressionOrdinaryCoreProperties
import Solcore.Syntax.DeclarativeYulSwitchOutcomeGrammar

/-!
Functionality, rejection exclusivity, and clean embedding for the internal
case-list and optional-default stages of ordinary inline-Yul switches.
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

/-- Every successful case arm starts at an exact `case` token. -/
theorem YulCaseArmParses.startsAt
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output : Remainder} {arm : Syntax.YulCase}
    (parsed : YulCaseArmOrdinaryParses statementOrdinary input arm output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .keyword .caseKw } := by
  cases parsed with
  | parsed markerSpan bodySpan markerParsed literalParsed bodyParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

/-- Ordinary case-arm success has a unique final remainder. -/
theorem YulCaseArmParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulCaseArmOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulCaseArmOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftBodySpan leftMarkerParsed leftLiteralParsed
        leftBodyParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightBodySpan rightMarkerParsed
            rightLiteralParsed rightBodyParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          have afterLiteralEq := leftLiteralParsed.output_unique
            rightLiteralParsed
          subst afterLiteralEq
          exact leftBodyParsed.output_unique statementOutcomes rightBodyParsed

/-- Exact case-arm rejection excludes ordinary case-arm success. -/
theorem YulCaseArmRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulCaseArmRejects statementOrdinary statementRejects input
      rejected) :
    ¬ ∃ arm output,
      YulCaseArmOrdinaryParses statementOrdinary input arm output := by
  rintro ⟨arm, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulBodySpan successfulMarkerParsed
        successfulLiteralParsed successfulBodyParsed =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarkerParsed
      | literalMissing rejectedMarkerSpan rejectedMarkerParsed
            literalAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact literalAbsent successfulLiteralParsed.startsAt
      | bodyRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedLiteralParsed bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterLiteralEq := rejectedLiteralParsed.output_unique
            successfulLiteralParsed
          subst afterLiteralEq
          exact bodyRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulBodyParsed⟩

/-- Ordinary maximal case-list success has a unique final remainder. -/
theorem YulCaseListParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : List Syntax.YulCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulCaseListOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulCaseListOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done rightAbsent => rfl
      | next rightArmParsed rightProgress rightTail =>
          rcases rightArmParsed.startsAt with ⟨span, present⟩
          exact False.elim (leftAbsent ⟨span, present⟩)
  | next leftArmParsed leftProgress leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          rcases leftArmParsed.startsAt with ⟨span, present⟩
          exact False.elim (rightAbsent ⟨span, present⟩)
      | next rightArmParsed rightProgress rightTail =>
          have afterArmEq := leftArmParsed.output_unique statementOutcomes
            rightArmParsed
          subst afterArmEq
          exact inductionHypothesis rightTail

/-- A rejected case-list iteration excludes maximal ordinary success. -/
theorem YulCaseListRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulCaseListRejects statementOrdinary statementRejects input
      rejected) :
    ¬ ∃ cases output,
      YulCaseListOrdinaryParses statementOrdinary input cases output := by
  induction rejection with
  | firstRejected casePresent armRejected =>
      rintro ⟨cases, output, successful⟩
      cases successful with
      | done caseAbsent => exact caseAbsent casePresent
      | next armParsed progress tail =>
          exact armRejected.disjointOrdinary statementOutcomes
            ⟨_, _, armParsed⟩
  | laterRejected rejectedArmParsed progress tailRejected
        inductionHypothesis =>
      rintro ⟨cases, output, successful⟩
      cases successful with
      | done caseAbsent => exact caseAbsent rejectedArmParsed.startsAt
      | next successfulArmParsed otherProgress successfulTail =>
          have afterArmEq := rejectedArmParsed.output_unique statementOutcomes
            successfulArmParsed
          subst afterArmEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Optional-default success has a unique final remainder. -/
theorem OptionalYulDefaultParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {leftSpan rightSpan : Option SourceSpan}
    {leftBody rightBody : Option (List Syntax.YulStmt)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulDefaultOrdinaryParses statementOrdinary input
      leftSpan leftBody afterLeft)
    (rightParsed : OptionalYulDefaultOrdinaryParses statementOrdinary input
      rightSpan rightBody afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent rightAbsent => rfl
      | present markerSpan bodySpan markerParsed bodyParsed =>
          exact False.elim (absent_conflicts_exact leftAbsent markerParsed)
  | present leftMarkerSpan leftBodySpan leftMarkerParsed leftBodyParsed =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (absent_conflicts_exact rightAbsent leftMarkerParsed)
      | present rightMarkerSpan rightBodySpan rightMarkerParsed
            rightBodyParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          exact leftBodyParsed.output_unique statementOutcomes rightBodyParsed

/-- Exact optional-default rejection excludes ordinary success. -/
theorem OptionalYulDefaultRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : OptionalYulDefaultRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ defaultSpan defaultBody output,
      OptionalYulDefaultOrdinaryParses statementOrdinary input defaultSpan
        defaultBody output := by
  rintro ⟨defaultSpan, defaultBody, output, successful⟩
  cases rejection with
  | bodyRejected rejectedMarkerSpan rejectedMarkerParsed bodyRejected =>
      cases successful with
      | absent defaultAbsent =>
          exact absent_conflicts_exact defaultAbsent rejectedMarkerParsed
      | present successfulMarkerSpan successfulBodySpan successfulMarkerParsed
            successfulBodyParsed =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact bodyRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulBodyParsed⟩

end Solcore.Syntax.DeclarativeGrammar
