import Solcore.Syntax.DeclarativeConstructorSelectionExactnessProperties
import Solcore.Syntax.Parser.ConstructorSelectionOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ConstructorSelectionSoundnessProperties

/-! Complete executable broad ordinary outcomes for constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export constructor-selection success as a broad ordinary outcome. -/
theorem constructorSelection_success_ordinaryOutcome_sound
    {input output : State} {selection : ConstructorSelection}
    (result : ExportInternals.constructorSelection input =
      .ok selection output) :
    DeclarativeGrammar.ConstructorSelectionOrdinaryParses
      input.declarativeRemainder selection output.declarativeRemainder :=
  constructorSelection_success_sound result

/-- Package constructor-selection success and exact prioritized rejection. -/
theorem constructorSelection_ordinaryOutcome_sound :
    (∀ {input output : State} {selection : ConstructorSelection},
      ExportInternals.constructorSelection input = .ok selection output →
        DeclarativeGrammar.ConstructorSelectionOrdinaryParses
          input.declarativeRemainder selection output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.constructorSelection input = .reject failure rejected →
        DeclarativeGrammar.ConstructorSelectionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨constructorSelection_success_ordinaryOutcome_sound,
    constructorSelection_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive constructor-selection outcomes. -/
theorem constructorSelection_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorSelectionOrdinaryParses
      DeclarativeGrammar.ConstructorSelectionRejects :=
  DeclarativeGrammar.constructorSelectionDeterministicOutcomeSpec

/-- Re-export exact constructorSelection outcomes with all supplied span data fixed. -/
theorem constructorSelection_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorSelectionOrdinaryParses
      DeclarativeGrammar.ConstructorSelectionRejects :=
  DeclarativeGrammar.constructorSelectionExactOutcomeSpec

/-- Two constructorSelection successes fix the complete AST and declarative remainder. -/
theorem constructorSelection_success_result_unique
    {input leftOutput rightOutput : State} {left right : ConstructorSelection}
    (leftResult : ExportInternals.constructorSelection input = .ok left leftOutput)
    (rightResult : ExportInternals.constructorSelection input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  constructorSelection_exactOutcomeSpec.successResultUnique
    (constructorSelection_success_ordinaryOutcome_sound leftResult)
    (constructorSelection_success_ordinaryOutcome_sound rightResult)

/-- Two constructorSelection rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem constructorSelection_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.constructorSelection input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.constructorSelection input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  constructorSelection_exactOutcomeSpec.rejectOutputUnique
    (constructorSelection_reject_ordinaryOutcome_sound leftResult)
    (constructorSelection_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
