import Solcore.Syntax.DeclarativeYulBodyGrammar
import Solcore.Syntax.Parser.YulBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulStatementPublicFuelSoundnessProperties

/-! Concrete clean and ordinary outcome soundness for public `yulBody`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free public body success follows the concrete clean Yul
body grammar. -/
theorem yulBody_success_clean_sound
    {input output : State} {body : YulParsedBlock}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulBody input = .ok body output) :
    DeclarativeGrammar.YulBodyParses input.declarativeRemainder body.span
      body.body output.declarativeRemainder :=
  yulBlock_success_sound yulStatement
    DeclarativeGrammar.YulStatementParses
    yulStatement_reflectsDiagnosticFreeOnSuccess
    yulStatement_success_clean_sound diagnosticFree result

/-- Every public body success, including diagnosed statement recovery,
follows the concrete ordinary Yul body grammar. -/
theorem yulBody_success_ordinary_sound
    {input output : State} {body : YulParsedBlock}
    (result : yulBody input = .ok body output) :
    DeclarativeGrammar.YulBodyOrdinaryParses input.declarativeRemainder
      body.span body.body output.declarativeRemainder :=
  yulBlock_success_ordinary_sound yulStatement
    DeclarativeGrammar.YulStatementOrdinaryParses
    yulStatement_success_ordinary_sound result

/-- Every public body rejection follows the exact opening, item-prefix, or
closing-boundary rejection trace. -/
theorem yulBody_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : yulBody input = .reject failure rejected) :
    DeclarativeGrammar.YulBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  yulBlock_reject_ordinary_sound yulStatement
    DeclarativeGrammar.YulStatementOrdinaryParses
    DeclarativeGrammar.YulStatementRejects
    yulStatement_success_ordinary_sound yulStatement_reject_boundary_sound
    result

/-- Package an executable body success for the public deterministic outcome
contract. -/
theorem yulBody_success_outcome_sound
    {input output : State} {body : YulParsedBlock}
    (result : yulBody input = .ok body output) :
    DeclarativeGrammar.YulBodyOutcomeParses input.declarativeRemainder {
      span := body.span
      body := body.body
    } output.declarativeRemainder :=
  yulBody_success_ordinary_sound result

/-- Deterministic parser-independent outcomes exposed beside the executable
public body bridges. -/
theorem yulBody_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulBodyOutcomeParses
      DeclarativeGrammar.YulBodyRejects :=
  DeclarativeGrammar.yulBodyDeterministicOutcomeSpec

end Solcore.Syntax.Parser
