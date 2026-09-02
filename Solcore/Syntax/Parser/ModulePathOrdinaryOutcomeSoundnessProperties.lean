import Solcore.Syntax.DeclarativeModulePathOutcomeProperties
import Solcore.Syntax.Parser.ModulePathOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ModulePathOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package module-path success and exact prioritized rejection. -/
theorem modulePath_ordinaryOutcome_sound (context : ParseContext) :
    (∀ {input output : State} {path : ModulePath},
      modulePath context input = .ok path output →
        DeclarativeGrammar.ModulePathOrdinaryParses
          input.declarativeRemainder path output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      modulePath context input = .reject failure rejected →
        DeclarativeGrammar.ModulePathRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨modulePath_success_ordinaryOutcome_sound context,
    modulePath_reject_ordinaryOutcome_sound context⟩

/-- Re-export deterministic and exclusive module-path outcomes. -/
theorem modulePath_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ModulePathOrdinaryParses
      DeclarativeGrammar.ModulePathRejects :=
  DeclarativeGrammar.modulePathDeterministicOutcomeSpec

end Solcore.Syntax.Parser
