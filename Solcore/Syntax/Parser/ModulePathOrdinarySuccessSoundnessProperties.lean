import Solcore.Syntax.DeclarativeModulePathOutcomeGrammar
import Solcore.Syntax.Parser.ModulePathSoundnessProperties

/-! Broad ordinary-success soundness for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable module-path success follows the existing exact ordinary
grammar without a diagnostic-free premise. -/
theorem modulePath_success_ordinaryOutcome_sound (context : ParseContext)
    {input output : State} {path : ModulePath}
    (result : modulePath context input = .ok path output) :
    DeclarativeGrammar.ModulePathOrdinaryParses input.declarativeRemainder
      path output.declarativeRemainder :=
  modulePath_success_sound context result

end Solcore.Syntax.Parser
