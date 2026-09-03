import Solcore.Syntax.DeclarativeSourceFileExactnessProperties
import Solcore.Syntax.Parser.FileItemsExactnessProperties
import Solcore.Syntax.Parser.SourceFileOrdinaryOutcomeSoundnessProperties

/-! Exact executable source-file values and rejection endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Successful top-item values supply exact files at fixed provenance and comments. -/
theorem sourceFile_exactOutcomeSpec_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  DeclarativeGrammar.sourceFileExactOutcomeSpecOfTopItemValues itemValues file comments

/-- An exact top-item contract supplies exact complete source-file outcomes. -/
theorem sourceFile_exactOutcomeSpec_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  DeclarativeGrammar.sourceFileExactOutcomeSpecOfTopItem itemOutcomes file comments

/-- With the same supplied comments and input state, source-file successes
agree on their full attached AST and remainder. -/
theorem sourceFile_success_result_unique_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    (comments : List Comment)
    {input leftOutput rightOutput : State} {left right : ParsedFile}
    (leftResult : sourceFile comments input = .ok left leftOutput)
    (rightResult : sourceFile comments input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (sourceFile_exactOutcomeSpec_of_topItemValues itemValues input.file comments)
    |>.successResultUnique
      (sourceFile_success_ordinaryOutcome_sound leftResult)
      (sourceFile_success_ordinaryOutcome_sound rightResult)

/-- Exact top-item outcomes fix successful source-file ASTs and remainders. -/
theorem sourceFile_success_result_unique_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (comments : List Comment)
    {input leftOutput rightOutput : State} {left right : ParsedFile}
    (leftResult : sourceFile comments input = .ok left leftOutput)
    (rightResult : sourceFile comments input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  sourceFile_success_result_unique_of_topItemValues itemOutcomes.successValueUnique
    comments leftResult rightResult

/-- Executable source-file rejection endpoints agree without top-item exactness. -/
theorem sourceFile_reject_output_unique (comments : List Comment)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : sourceFile comments input = .reject leftFailure leftOutput)
    (rightResult : sourceFile comments input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.SourceFileRejects.output_unique
    (sourceFile_reject_ordinaryOutcome_sound leftResult)
    (sourceFile_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.FileInternals
