import Solcore.Syntax.DeclarativeFileItemsExactnessProperties
import Solcore.Syntax.Parser.FileItemsOrdinaryOutcomeSoundnessProperties

/-! Exact executable file-item results without exposing the reverse accumulator. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Successful top-item values supply the exact declarative file-loop contract. -/
theorem parseItems_exactOutcomeSpec_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FileItemsOrdinaryParses DeclarativeGrammar.FileItemsRejects :=
  DeclarativeGrammar.fileItemsExactOutcomeSpecOfTopItemValues itemValues

/-- An exact top-item contract supplies exact declarative file-loop outcomes. -/
theorem parseItems_exactOutcomeSpec_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FileItemsOrdinaryParses DeclarativeGrammar.FileItemsRejects :=
  DeclarativeGrammar.fileItemsExactOutcomeSpecOfTopItem itemOutcomes

/-- At fixed fuel and reverse accumulator, executable item loops agree on the
complete forward result and remainder from unique top-item success values. -/
theorem parseItems_success_result_unique_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    (fuel : Nat) (itemsRev : List TopItem)
    {input leftOutput rightOutput : State} {left right : List TopItem}
    (leftResult : parseItems fuel itemsRev input = .ok left leftOutput)
    (rightResult : parseItems fuel itemsRev input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
      left leftOutput leftResult with ⟨leftSuffix, leftEq, leftParsed⟩
  rcases parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
      right rightOutput rightResult with ⟨rightSuffix, rightEq, rightParsed⟩
  rcases (parseItems_exactOutcomeSpec_of_topItemValues itemValues)
      |>.successResultUnique leftParsed rightParsed with ⟨suffixEq, outputEq⟩
  constructor
  · rw [leftEq, rightEq, suffixEq]
  · exact outputEq

/-- Exact top-item outcomes fix an executable item loop's result and remainder. -/
theorem parseItems_success_result_unique_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (fuel : Nat) (itemsRev : List TopItem)
    {input leftOutput rightOutput : State} {left right : List TopItem}
    (leftResult : parseItems fuel itemsRev input = .ok left leftOutput)
    (rightResult : parseItems fuel itemsRev input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  parseItems_success_result_unique_of_topItemValues itemOutcomes.successValueUnique
    fuel itemsRev leftResult rightResult

/-- Executable file-item rejection endpoints agree unconditionally. -/
theorem parseItems_reject_output_unique
    (fuel : Nat) (itemsRev : List TopItem)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : parseItems fuel itemsRev input = .reject leftFailure leftOutput)
    (rightResult : parseItems fuel itemsRev input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FileItemsRejects.output_unique
    (parseItems_reject_ordinaryOutcome_sound fuel itemsRev input
      leftFailure leftOutput leftResult)
    (parseItems_reject_ordinaryOutcome_sound fuel itemsRev input
      rightFailure rightOutput rightResult)

end Solcore.Syntax.Parser.FileInternals
