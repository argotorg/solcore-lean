import Solcore.Syntax.DeclarativeCoreBlockExactnessProperties
import Solcore.Syntax.DeclarativeCoreBlockPublicIsolationOutcomeProperties
import Solcore.Syntax.DeclarativeExactOutcomeSpec

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
