import Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeProperties
import Solcore.Syntax.Parser.CoreBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.IsolatedCoreBlockOrdinaryOutcomeSoundnessProperties

/-!
Executable ordinary outcomes for isolated raw Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful isolated raw Core block follows the capture-aware
ordinary grammar. -/
theorem isolatedCoreBlock_success_ordinary_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input output : State} {body : Block}
    (result : isolateBlock (coreBlock statement policy) input =
      .ok body output) :
    DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses
      (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
        policy.declarative)
      (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
        policy.declarative)
      input.declarativeRemainder body output.declarativeRemainder :=
  isolateBlock_success_ordinary_sound (coreBlock statement policy)
    (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
      policy.declarative)
    (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
      policy.declarative)
    (coreBlock_success_ordinary_sound statement policy statementOrdinary
      statementSuccessSound)
    (coreBlock_reject_ordinary_sound statement policy statementOrdinary
      statementRejects statementSuccessSound statementRejectSound)
    result

/-- Every externally visible isolated raw Core block rejection is the exact
uncaptured raw rejection. -/
theorem isolatedCoreBlock_reject_ordinary_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : isolateBlock (coreBlock statement policy) input =
      .reject failure rejected) :
    DeclarativeGrammar.IsolatedCoreBlockRejects
      (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
        policy.declarative)
      input.declarativeRemainder rejected.declarativeRemainder :=
  isolateBlock_reject_ordinary_sound (coreBlock statement policy)
    (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
      policy.declarative)
    (coreBlock_reject_ordinary_sound statement policy statementOrdinary
      statementRejects statementSuccessSound statementRejectSound)
    result

/-- Package executable success and rejection for isolated raw Core blocks. -/
theorem isolatedCoreBlock_ordinaryOutcome_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {body : Block},
      isolateBlock (coreBlock statement policy) input = .ok body output →
        DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses
          (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
            policy.declarative)
          (DeclarativeGrammar.CoreBlockRejects statementOrdinary
            statementRejects policy.declarative)
          input.declarativeRemainder body output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isolateBlock (coreBlock statement policy) input =
          .reject failure rejected →
        DeclarativeGrammar.IsolatedCoreBlockRejects
          (DeclarativeGrammar.CoreBlockRejects statementOrdinary
            statementRejects policy.declarative)
          input.declarativeRemainder rejected.declarativeRemainder) :=
  isolateBlock_ordinaryOutcome_sound (coreBlock statement policy)
    (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
      policy.declarative)
    (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
      policy.declarative)
    (coreBlock_success_ordinary_sound statement policy statementOrdinary
      statementSuccessSound)
    (coreBlock_reject_ordinary_sound statement policy statementOrdinary
      statementRejects statementSuccessSound statementRejectSound)

/-- Re-export the deterministic contract for isolated raw Core blocks. -/
theorem isolatedCoreBlock_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (policy : TailExpressionPolicy)
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses
        (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
          policy.declarative)
        (DeclarativeGrammar.CoreBlockRejects statementOrdinary
          statementRejects policy.declarative))
      (DeclarativeGrammar.IsolatedCoreBlockRejects
        (DeclarativeGrammar.CoreBlockRejects statementOrdinary
          statementRejects policy.declarative)) :=
  DeclarativeGrammar.isolatedCoreBlockDeterministicOutcomeSpec
    (coreBlock_ordinaryOutcomeSpec policy statementOutcomes)

end Solcore.Syntax.Parser
