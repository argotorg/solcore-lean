import Solcore.Syntax.Parser.CoreBlockOrdinaryRejectionSoundnessProperties

/-!
Packaged executable ordinary outcomes for raw Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package diagnostic-inclusive success and exact rejection over supplied
statement outcome callbacks. -/
theorem coreBlock_ordinaryOutcome_sound
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
      coreBlock statement policy input = .ok body output →
        DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
          policy.declarative input.declarativeRemainder body
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreBlock statement policy input = .reject failure rejected →
        DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
          policy.declarative input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨coreBlock_success_ordinary_sound statement policy statementOrdinary
      statementSuccessSound,
    coreBlock_reject_ordinary_sound statement policy statementOrdinary
      statementRejects statementSuccessSound statementRejectSound⟩

/-- Re-export the deterministic contract under the executable bridge name. -/
theorem coreBlock_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (policy : TailExpressionPolicy)
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
        policy.declarative)
      (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
        policy.declarative) :=
  DeclarativeGrammar.coreBlockDeterministicOutcomeSpec policy.declarative
    statementOutcomes

end Solcore.Syntax.Parser
