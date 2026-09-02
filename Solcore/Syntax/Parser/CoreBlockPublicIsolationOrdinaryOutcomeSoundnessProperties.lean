import Solcore.Syntax.DeclarativeCoreBlockIsolationExactnessProperties
import Solcore.Syntax.Parser.CoreTermPublicOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.IsolatedCoreBlockOrdinaryOutcomeSoundnessProperties

/-! Executable ordinary outcomes for public Core block isolation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package public isolated-block success and exact external rejection. -/
theorem isolatedCoreBlockPublic_ordinaryOutcome_sound
    (policy : TailExpressionPolicy) :
    (∀ {input output : State} {body : Block},
      isolateBlock (block policy) input = .ok body output →
        DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
          policy.declarative input.declarativeRemainder body
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isolateBlock (block policy) input = .reject failure rejected →
        DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative
          input.declarativeRemainder rejected.declarativeRemainder) :=
  isolateBlock_ordinaryOutcome_sound (block policy)
    (DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative)
    (DeclarativeGrammar.CoreBlockPublicRejects policy.declarative)
    (block_ordinaryOutcome_sound policy).1
    (block_ordinaryOutcome_sound policy).2

/-- Every public isolated-block success follows the capture-aware ordinary
relation. -/
theorem isolatedCoreBlockPublic_success_ordinary_sound
    (policy : TailExpressionPolicy) {input output : State} {body : Block}
    (result : isolateBlock (block policy) input = .ok body output) :
    DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
      policy.declarative input.declarativeRemainder body
        output.declarativeRemainder :=
  (isolatedCoreBlockPublic_ordinaryOutcome_sound policy).1 result

/-- Every public isolated-block rejection is the exact uncaptured raw-block
rejection. -/
theorem isolatedCoreBlockPublic_reject_ordinary_sound
    (policy : TailExpressionPolicy) {input rejected : State}
    {failure : Failure}
    (result : isolateBlock (block policy) input = .reject failure rejected) :
    DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative
      input.declarativeRemainder rejected.declarativeRemainder :=
  (isolatedCoreBlockPublic_ordinaryOutcome_sound policy).2 result

/-- Re-export exact public isolation from exact fixed-fuel statement
outcomes. -/
theorem isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
        policy.declarative)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects
        policy.declarative) :=
  DeclarativeGrammar.isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel
    statementOutcomes policy.declarative

/-- Under exact fixed-fuel statements, two isolated public successes have the
same block AST and final declarative remainder. -/
theorem isolatedCoreBlockPublic_success_result_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {left right : Block}
    (leftResult : isolateBlock (block policy) input = .ok left leftOutput)
    (rightResult : isolateBlock (block policy) input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
      statementOutcomes policy)
    |>.successResultUnique
      (isolatedCoreBlockPublic_success_ordinary_sound policy leftResult)
      (isolatedCoreBlockPublic_success_ordinary_sound policy rightResult)

/-- Under exact fixed-fuel statements, two isolated public rejections have the
same declarative endpoint. -/
theorem isolatedCoreBlockPublic_reject_output_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : isolateBlock (block policy) input =
      .reject leftFailure leftOutput)
    (rightResult : isolateBlock (block policy) input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
      statementOutcomes policy)
    |>.rejectOutputUnique
      (isolatedCoreBlockPublic_reject_ordinary_sound policy leftResult)
      (isolatedCoreBlockPublic_reject_ordinary_sound policy rightResult)

end Solcore.Syntax.Parser
