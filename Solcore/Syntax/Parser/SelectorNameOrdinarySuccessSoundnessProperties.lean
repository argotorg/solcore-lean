import Solcore.Syntax.DeclarativeSelectorNameOutcomeGrammar
import Solcore.Syntax.Parser.SelectorNameSoundnessProperties

/-! Broad ordinary-success soundness for import and export selector names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selector-name success follows the exact identifier or
maximal parenthesized-operator grammar without a diagnostic-free premise. -/
theorem selectorName_success_ordinaryOutcome_sound (context : ParseContext)
    {input output : State} {selector : SelectorName}
    (result : selectorName context input = .ok selector output) :
    DeclarativeGrammar.SelectorNameOrdinaryParses
      input.declarativeRemainder selector output.declarativeRemainder :=
  selectorName_success_sound context result

end Solcore.Syntax.Parser
