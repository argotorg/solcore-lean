import Solcore.Syntax.DeclarativeSelectedAliasExactnessProperties
import Solcore.Syntax.DeclarativeSelectedImportExactnessProperties
import Solcore.Syntax.DeclarativeSelectedImportsExactnessProperties
import Solcore.Syntax.DeclarativeHidingClauseExactnessProperties
import Solcore.Syntax.Parser.SelectedAliasOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportsOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.HidingClauseOrdinaryOutcomeSoundnessProperties

/-! Unconditional exact executable outcomes for selected names and hiding clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export full exactness of selectedAlias outcomes. -/
theorem selectedAlias_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.SelectedAliasOrdinaryParses
      DeclarativeGrammar.SelectedAliasRejects :=
  DeclarativeGrammar.selectedAliasExactOutcomeSpec

/-- Successful selectedAlias results agree on their complete AST and remainder. -/
theorem selectedAlias_success_result_unique
    {input leftOutput rightOutput : State} {left right : Option Identifier}
    (leftResult : ImportInternals.selectedAlias input = .ok left leftOutput)
    (rightResult : ImportInternals.selectedAlias input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedAlias_exactOutcomeSpec).successResultUnique
    (selectedAlias_success_ordinaryOutcome_sound leftResult)
    (selectedAlias_success_ordinaryOutcome_sound rightResult)

/-- Rejected selectedAlias results agree on their complete declarative endpoint. -/
theorem selectedAlias_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.selectedAlias input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.selectedAlias input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedAlias_exactOutcomeSpec).rejectOutputUnique
    (selectedAlias_reject_ordinaryOutcome_sound leftResult)
    (selectedAlias_reject_ordinaryOutcome_sound rightResult)

/-- Re-export full exactness of selectedImport outcomes. -/
theorem selectedImport_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.SelectedImportOrdinaryParses
      DeclarativeGrammar.SelectedImportRejects :=
  DeclarativeGrammar.selectedImportExactOutcomeSpec

/-- Successful selectedImport results agree on their complete AST and remainder. -/
theorem selectedImport_success_result_unique
    {input leftOutput rightOutput : State} {left right : SelectedImport}
    (leftResult : selectedImport input = .ok left leftOutput)
    (rightResult : selectedImport input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedImport_exactOutcomeSpec).successResultUnique
    (selectedImport_success_ordinaryOutcome_sound leftResult)
    (selectedImport_success_ordinaryOutcome_sound rightResult)

/-- Rejected selectedImport results agree on their complete declarative endpoint. -/
theorem selectedImport_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : selectedImport input = .reject leftFailure leftOutput)
    (rightResult : selectedImport input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedImport_exactOutcomeSpec).rejectOutputUnique
    (selectedImport_reject_ordinaryOutcome_sound leftResult)
    (selectedImport_reject_ordinaryOutcome_sound rightResult)

/-- Re-export full exactness of selectedImports outcomes. -/
theorem selectedImports_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.SelectedImportsOrdinaryParses
      DeclarativeGrammar.SelectedImportsRejects :=
  DeclarativeGrammar.selectedImportsExactOutcomeSpec

/-- Successful selectedImports results agree on their complete AST and remainder. -/
theorem selectedImports_success_result_unique
    {input leftOutput rightOutput : State} {left right : NonemptyDelimitedList SelectedImport}
    (leftResult : ImportInternals.selectedImports input = .ok left leftOutput)
    (rightResult : ImportInternals.selectedImports input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedImports_exactOutcomeSpec).successResultUnique
    (selectedImports_success_ordinaryOutcome_sound leftResult)
    (selectedImports_success_ordinaryOutcome_sound rightResult)

/-- Rejected selectedImports results agree on their complete declarative endpoint. -/
theorem selectedImports_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.selectedImports input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.selectedImports input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedImports_exactOutcomeSpec).rejectOutputUnique
    (selectedImports_reject_ordinaryOutcome_sound leftResult)
    (selectedImports_reject_ordinaryOutcome_sound rightResult)

/-- Re-export full exactness of hidingClause outcomes. -/
theorem hidingClause_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.HidingClauseOrdinaryParses
      DeclarativeGrammar.HidingClauseRejects :=
  DeclarativeGrammar.hidingClauseExactOutcomeSpec

/-- Successful hidingClause results agree on their complete AST and remainder. -/
theorem hidingClause_success_result_unique
    {input leftOutput rightOutput : State} {left right : HidingClause}
    (leftResult : ImportInternals.hidingClause input = .ok left leftOutput)
    (rightResult : ImportInternals.hidingClause input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (hidingClause_exactOutcomeSpec).successResultUnique
    (hidingClause_success_ordinaryOutcome_sound leftResult)
    (hidingClause_success_ordinaryOutcome_sound rightResult)

/-- Rejected hidingClause results agree on their complete declarative endpoint. -/
theorem hidingClause_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.hidingClause input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.hidingClause input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (hidingClause_exactOutcomeSpec).rejectOutputUnique
    (hidingClause_reject_ordinaryOutcome_sound leftResult)
    (hidingClause_reject_ordinaryOutcome_sound rightResult)

/-- Re-export full exactness of optionalHiding outcomes. -/
theorem optionalHiding_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalHidingOrdinaryParses
      DeclarativeGrammar.OptionalHidingRejects :=
  DeclarativeGrammar.optionalHidingExactOutcomeSpec

/-- Successful optionalHiding results agree on their complete AST and remainder. -/
theorem optionalHiding_success_result_unique
    {input leftOutput rightOutput : State} {left right : Option HidingClause}
    (leftResult : ImportInternals.optionalHiding input = .ok left leftOutput)
    (rightResult : ImportInternals.optionalHiding input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (optionalHiding_exactOutcomeSpec).successResultUnique
    (optionalHiding_success_ordinaryOutcome_sound leftResult)
    (optionalHiding_success_ordinaryOutcome_sound rightResult)

/-- Rejected optionalHiding results agree on their complete declarative endpoint. -/
theorem optionalHiding_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.optionalHiding input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.optionalHiding input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (optionalHiding_exactOutcomeSpec).rejectOutputUnique
    (optionalHiding_reject_ordinaryOutcome_sound leftResult)
    (optionalHiding_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
