import Solcore.Syntax.DeclarativeCoreMatchCasesOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchComponentValueProperties

/-! Exact forward-order success values for maximal Core match case lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Case-token priority and exact arms fix the maximal forward case list and
its remainder, including ordinary body diagnostics. -/
theorem MatchCasesOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : List Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightArm rightProgress rightTail =>
          exact False.elim (leftAbsent rightArm.startsAt)
  | next leftArm leftProgress leftTail ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent leftArm.startsAt)
      | next rightArm rightProgress rightTail =>
          rcases leftArm.result_unique statementOutcomes patternOutcomes
              rightArm with ⟨armEq, inputEq⟩
          subst armEq
          subst inputEq
          rcases ih rightTail with ⟨tailEq, outputEq⟩
          subst tailEq
          exact ⟨rfl, outputEq⟩

/-- A maximal match case list fixes the exact arm ASTs in source order. -/
theorem MatchCasesOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : List Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : left = right :=
  (leftParsed.result_unique statementOutcomes patternOutcomes rightParsed).1

end Solcore.Syntax.DeclarativeGrammar
