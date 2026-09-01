import Solcore.Syntax.DeclarativeCoreBlockPublicIsolationOutcomeProperties
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

end Solcore.Syntax.Parser
