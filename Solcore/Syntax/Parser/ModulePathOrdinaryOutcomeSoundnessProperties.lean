import Solcore.Syntax.DeclarativeModulePathExactnessProperties
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


/-- Exact values and endpoints for the independent modulePath grammar. -/
theorem modulePath_exactOutcomeSpec  :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ModulePathOrdinaryParses DeclarativeGrammar.ModulePathRejects :=
  DeclarativeGrammar.modulePathExactOutcomeSpec

/-- Executable successes agree on their complete value and remainder. -/
theorem modulePath_success_result_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {left right : ModulePath}
    (leftResult : modulePath context input = .ok left leftOutput)
    (rightResult : modulePath context input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (modulePath_exactOutcomeSpec ).successResultUnique
    (modulePath_success_ordinaryOutcome_sound context leftResult)
    (modulePath_success_ordinaryOutcome_sound context rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem modulePath_reject_output_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : modulePath context input = .reject leftFailure leftOutput)
    (rightResult : modulePath context input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (modulePath_exactOutcomeSpec ).rejectOutputUnique
    (modulePath_reject_ordinaryOutcome_sound context leftResult)
    (modulePath_reject_ordinaryOutcome_sound context rightResult)

end Solcore.Syntax.Parser
