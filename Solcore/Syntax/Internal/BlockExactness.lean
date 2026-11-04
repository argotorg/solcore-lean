import Solcore.Syntax.Grammar.TermLevels
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.PatternOutcomes

/-!
Exactness of the declarative grammar of Core blocks: outcomes fix the whole result.
Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockExactnessProperties
/-! Exact raw Core blocks, conditional on exact fixed-fuel statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact statement outcomes make a block-item sequence fix its statements,
closing span, and final remainder. -/
theorem CoreBlockItemsParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    ∀ {input : Remainder} {left right : List Syntax.Statement}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      CoreBlockItemsParses statementOrdinary input left leftClosing afterLeft →
      CoreBlockItemsParses statementOrdinary input right rightClosing
        afterRight →
      left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | close leftClosing leftToken =>
      intro rightParsed
      cases rightParsed with
      | close rightClosing rightToken =>
          rcases leftToken.result_unique rightToken with ⟨spanEq, outputEq⟩
          exact ⟨rfl, spanEq, outputEq⟩
      | next rightNotAtEnd rightClosingAbsent rightStatement rightProgress
          rightTail =>
          exact False.elim
            (typeTokenAbsent_conflicts_token rightClosingAbsent leftToken.1)
  | next leftNotAtEnd leftClosingAbsent leftStatement leftProgress leftTail
      inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightClosing rightToken =>
          exact False.elim
            (typeTokenAbsent_conflicts_token leftClosingAbsent rightToken.1)
      | next rightNotAtEnd rightClosingAbsent rightStatement rightProgress
          rightTail =>
          rcases outcomes.successResultUnique leftStatement rightStatement with
            ⟨statementEq, afterStatementEq⟩
          subst statementEq
          subst afterStatementEq
          rcases inductionHypothesis rightTail with
            ⟨statementsEq, closingEq, outputEq⟩
          subst statementsEq
          exact ⟨rfl, closingEq, outputEq⟩

/-- Exact statements make a complete raw Core block fix its AST and final
remainder. -/
theorem CoreBlockOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {policy : CoreBlockTailPolicy}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : CoreBlockOrdinaryParses statementOrdinary policy input left
      afterLeft)
    (rightParsed : CoreBlockOrdinaryParses statementOrdinary policy input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpening leftClosing leftToken leftBody =>
      cases rightParsed with
      | parsed rightOpening rightClosing rightToken rightBody =>
          rcases leftToken.result_unique rightToken with
            ⟨openingEq, afterOpeningEq⟩
          subst openingEq
          subst afterOpeningEq
          rcases leftBody.result_unique outcomes rightBody with
            ⟨bodyEq, closingEq, outputEq⟩
          subst bodyEq
          subst closingEq
          exact ⟨rfl, outputEq⟩

/-- Exact statements make a raw Core block fix its AST. -/
theorem CoreBlockOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {policy : CoreBlockTailPolicy}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : CoreBlockOrdinaryParses statementOrdinary policy input left
      afterLeft)
    (rightParsed : CoreBlockOrdinaryParses statementOrdinary policy input right
      afterRight) : left = right :=
  (leftParsed.result_unique outcomes rightParsed).1

/-- Exact statements fix the first rejecting block-item endpoint. -/
theorem CoreBlockItemsRejects.output_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input left right : Remainder}
    (leftRejected : CoreBlockItemsRejects statementOrdinary statementRejects
      input left)
    (rightRejected : CoreBlockItemsRejects statementOrdinary statementRejects
      input right) : left = right := by
  induction leftRejected generalizing right with
  | missingClose leftClosingAbsent leftAtEnd =>
      cases rightRejected with
      | missingClose => rfl
      | statementRejected rightNotAtEnd _ _
      | laterRejected rightNotAtEnd _ _ _ _ =>
          exact False.elim ((Nat.not_lt_of_ge leftAtEnd) rightNotAtEnd)
  | statementRejected leftNotAtEnd leftClosingAbsent leftStatementRejected =>
      cases rightRejected with
      | missingClose _ rightAtEnd =>
          exact False.elim ((Nat.not_lt_of_ge rightAtEnd) leftNotAtEnd)
      | statementRejected _ _ rightStatementRejected =>
          exact outcomes.rejectOutputUnique leftStatementRejected
            rightStatementRejected
      | laterRejected _ _ rightStatement _ _ =>
          exact False.elim
            (outcomes.successRejectDisjoint leftStatementRejected
              ⟨_, _, rightStatement⟩)
  | laterRejected leftNotAtEnd leftClosingAbsent leftStatement leftProgress
      leftTail inductionHypothesis =>
      cases rightRejected with
      | missingClose _ rightAtEnd =>
          exact False.elim ((Nat.not_lt_of_ge rightAtEnd) leftNotAtEnd)
      | statementRejected _ _ rightStatementRejected =>
          exact False.elim
            (outcomes.successRejectDisjoint rightStatementRejected
              ⟨_, _, leftStatement⟩)
      | laterRejected _ _ rightStatement rightProgress rightTail =>
          have afterStatementEq :=
            outcomes.successOutputUnique leftStatement rightStatement
          subst afterStatementEq
          exact inductionHypothesis rightTail

/-- Exact statements fix the first rejecting raw-block endpoint. -/
theorem CoreBlockRejects.output_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {policy : CoreBlockTailPolicy}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input left right : Remainder}
    (leftRejected : CoreBlockRejects statementOrdinary statementRejects policy
      input left)
    (rightRejected : CoreBlockRejects statementOrdinary statementRejects policy
      input right) : left = right := by
  cases leftRejected with
  | openingMissing leftOpeningAbsent =>
      cases rightRejected with
      | openingMissing => rfl
      | itemsRejected _ rightOpening _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token leftOpeningAbsent rightOpening.1)
  | itemsRejected _ leftOpening leftItems =>
      cases rightRejected with
      | openingMissing rightOpeningAbsent =>
          exact False.elim
            (typeTokenAbsent_conflicts_token rightOpeningAbsent leftOpening.1)
      | itemsRejected _ rightOpening rightItems =>
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact leftItems.output_unique outcomes rightItems

/-- Exact statement outcomes lift through the raw Core-block grammar. -/
theorem coreBlockExactOutcomeSpec
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (policy : CoreBlockTailPolicy)
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    ExactDeterministicOutcomeSpec
      (CoreBlockOrdinaryParses statementOrdinary policy)
      (CoreBlockRejects statementOrdinary statementRejects policy) where
  toDeterministicOutcomeSpec := coreBlockDeterministicOutcomeSpec policy
    outcomes.toDeterministicOutcomeSpec
  successValueUnique := CoreBlockOrdinaryParses.value_unique outcomes
  rejectOutputUnique := CoreBlockRejects.output_unique outcomes

/-- Fixed-fuel statement exactness lifts to the public raw Core block. -/
theorem coreBlockPublicExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel))
    (policy : CoreBlockTailPolicy) :
    ExactDeterministicOutcomeSpec (CoreBlockPublicOrdinaryParses policy)
      (CoreBlockPublicRejects policy) where
  toDeterministicOutcomeSpec := coreBlockPublicOutcomeSpec policy
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (leftParsed.result_unique
      (statementOutcomes (coreBlockPublicStatementFuel input)) rightParsed).1
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact leftRejected.output_unique
      (statementOutcomes (coreBlockPublicStatementFuel input)) rightRejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockIsolationExactnessProperties
/-! Exactness transport through balanced Core-block isolation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact block outcomes lift through balanced capture and child-rejection
recovery. -/
theorem IsolatedCoreBlockOrdinaryParses.value_unique
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects
      input left afterLeft)
    (rightParsed : IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | direct leftAbsent leftBody =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact blockOutcomes.successValueUnique leftBody rightBody
      | captured rightCapture rightBody =>
          exact False.elim (leftAbsent ⟨_, rightCapture⟩)
      | recovered rightCapture rightRejected =>
          exact False.elim (leftAbsent ⟨_, rightCapture⟩)
  | captured leftCapture leftBody =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact False.elim (rightAbsent ⟨_, leftCapture⟩)
      | captured rightCapture rightBody =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          exact blockOutcomes.successValueUnique leftBody rightBody
      | recovered rightCapture rightRejected =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          exact False.elim
            (blockOutcomes.successRejectDisjoint rightRejected
              ⟨_, _, leftBody⟩)
  | recovered leftCapture leftRejected =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact False.elim (rightAbsent ⟨_, leftCapture⟩)
      | captured rightCapture rightBody =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          exact False.elim
            (blockOutcomes.successRejectDisjoint leftRejected
              ⟨_, _, rightBody⟩)
      | recovered rightCapture rightRejected =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          rfl

/-- Exact block outcomes make isolated success fix its AST and remainder. -/
theorem IsolatedCoreBlockOrdinaryParses.result_unique
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects
      input left afterLeft)
    (rightParsed : IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique blockOutcomes rightParsed,
    leftParsed.output_unique blockOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

/-- Exact raw-block rejection fixes the isolated external endpoint. -/
theorem IsolatedCoreBlockRejects.output_unique
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input left right : Remainder}
    (leftRejected : IsolatedCoreBlockRejects blockRejects input left)
    (rightRejected : IsolatedCoreBlockRejects blockRejects input right) :
    left = right := by
  cases leftRejected with
  | direct leftAbsent leftBody =>
      cases rightRejected with
      | direct rightAbsent rightBody =>
          exact blockOutcomes.rejectOutputUnique leftBody rightBody

/-- Exact raw-block outcomes lift through balanced isolation. -/
theorem isolatedCoreBlockExactOutcomeSpec
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects) :
    ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects)
      (IsolatedCoreBlockRejects blockRejects) where
  toDeterministicOutcomeSpec :=
    isolatedCoreBlockDeterministicOutcomeSpec
      blockOutcomes.toDeterministicOutcomeSpec
  successValueUnique :=
    IsolatedCoreBlockOrdinaryParses.value_unique blockOutcomes
  rejectOutputUnique :=
    IsolatedCoreBlockRejects.output_unique blockOutcomes

/-- Fixed-fuel statement exactness lifts through every public isolation
policy. -/
theorem isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel))
    (policy : CoreBlockTailPolicy) :
    ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses policy)
      (IsolatedCoreBlockPublicRejects policy) :=
  isolatedCoreBlockExactOutcomeSpec
    (coreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes policy)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternFuelExactnessProperties
/-! Base and successor lifts for exact mutually recursive Core pattern fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fuel zero admits neither an ordinary pattern success nor rejection. -/
theorem corePatternExactOutcomeSpecWithFuel_zero :
    ExactDeterministicOutcomeSpec
      (CorePatternOrdinaryParsesWithFuel 0)
      (CorePatternRejectsWithFuel 0) where
  toDeterministicOutcomeSpec := corePatternOutcomeSpecWithFuel 0
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed
    exact False.elim (CorePatternOrdinaryParsesWithFuel.zero leftParsed)
  rejectOutputUnique := by
    intro input left right leftRejected
    exact False.elim (CorePatternRejectsWithFuel.zero leftRejected)

/-- Pattern and expression exactness at the same preceding fuel supplies
pattern exactness at the successor fuel; no successor expression is assumed. -/
theorem corePatternExactOutcomeSpecWithFuel_succ
    (fuel : Nat)
    (patternOutcomes : ExactDeterministicOutcomeSpec
      (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel))
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec
      (CorePatternOrdinaryParsesWithFuel (fuel + 1))
      (CorePatternRejectsWithFuel (fuel + 1)) := by
  change ExactDeterministicOutcomeSpec
    (CorePatternStepOrdinaryParses (corePatternStepRelationsWithFuel fuel))
    (CorePatternStepRejects (corePatternStepRelationsWithFuel fuel))
  exact corePatternStepExactOutcomeSpec
    (corePatternStepRelationsWithFuel fuel) patternOutcomes expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end
