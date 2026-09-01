import Solcore.Syntax.DeclarativeCoreMatchCaseOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchCasesOutcomeGrammar

/-! Deterministic outcomes for the maximal Core match-case sequence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every ordinary case starts at an exact `case` token. -/
theorem MatchCaseOrdinaryParses.startsAt
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {input output : Remainder} {arm : Syntax.MatchCase}
    (parsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary input
      arm output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .keyword .caseKw
    } := by
  cases parsed with
  | parsed markerSpan markerParsed patternParsed bodyParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

/-- Ordinary maximal case-list success has one final remainder. -/
theorem MatchCasesOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : List Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done rightAbsent => rfl
      | next rightArm rightProgress rightTail =>
          exact False.elim (leftAbsent rightArm.startsAt)
  | next leftArm leftProgress leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent leftArm.startsAt)
      | next rightArm rightProgress rightTail =>
          have afterArmEq := MatchCaseOrdinaryParses.output_unique
            statementOutcomes patternOutcomes leftArm rightArm
          subst afterArmEq
          exact inductionHypothesis rightTail

/-- Guarded exact case-list rejection excludes maximal ordinary success. -/
theorem MatchCasesRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input rejected : Remainder}
    (rejection : MatchCasesRejects statementOrdinary statementRejects
      patternOrdinary patternRejects input rejected) :
    ¬ ∃ arms output,
      MatchCasesOrdinaryParses statementOrdinary patternOrdinary input arms
        output := by
  induction rejection with
  | firstRejected casePresent armRejected =>
      rintro ⟨arms, output, successful⟩
      cases successful with
      | done caseAbsent => exact caseAbsent casePresent
      | next armParsed progress tail =>
          exact MatchCaseRejects.disjointOrdinary statementOutcomes
            patternOutcomes armRejected ⟨_, _, armParsed⟩
  | laterRejected rejectedArm progress tailRejected inductionHypothesis =>
      rintro ⟨arms, output, successful⟩
      cases successful with
      | done caseAbsent => exact caseAbsent rejectedArm.startsAt
      | next successfulArm otherProgress successfulTail =>
          have afterArmEq := MatchCaseOrdinaryParses.output_unique
            statementOutcomes patternOutcomes rejectedArm successfulArm
          subst afterArmEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Lift supplied statement and pattern outcomes through the case sequence. -/
theorem matchCasesDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects) :
    DeterministicOutcomeSpec
      (MatchCasesOrdinaryParses statementOrdinary patternOrdinary)
      (MatchCasesRejects statementOrdinary statementRejects patternOrdinary
        patternRejects) where
  successOutputUnique := MatchCasesOrdinaryParses.output_unique
    statementOutcomes patternOutcomes
  successRejectDisjoint := MatchCasesRejects.disjointOrdinary
    statementOutcomes patternOutcomes

end Solcore.Syntax.DeclarativeGrammar
