import Solcore.Syntax.DeclarativeYulBodyExactnessProperties
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

/-- Re-export fully exact public Yul body values and rejecting endpoints. -/
theorem yulBody_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulBodyOutcomeParses
      DeclarativeGrammar.YulBodyRejects :=
  DeclarativeGrammar.yulBodyExactOutcomeSpec

/-- Public executable bodies agree on their complete span, body, and remainder. -/
theorem yulBody_success_result_unique
    {input leftOutput rightOutput : State} {left right : YulParsedBlock}
    (leftResult : yulBody input = .ok left leftOutput)
    (rightResult : yulBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases DeclarativeGrammar.YulBodyOrdinaryParses.result_unique
    (yulBody_success_ordinary_sound leftResult)
    (yulBody_success_ordinary_sound rightResult) with ⟨spanEq, bodyEq, outputEq⟩
  refine ⟨?_, outputEq⟩
  cases left
  cases right
  simp_all

/-- Public executable bodies agree on the complete first-failure endpoint. -/
theorem yulBody_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulBody input = .reject leftFailure leftOutput)
    (rightResult : yulBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulBodyRejects.output_unique
    (yulBody_reject_ordinary_sound leftResult)
    (yulBody_reject_ordinary_sound rightResult)

end Solcore.Syntax.Parser
