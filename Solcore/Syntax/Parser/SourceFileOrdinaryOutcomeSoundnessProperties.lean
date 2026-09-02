import Solcore.Syntax.DeclarativeSourceFileOutcomeProperties
import Solcore.Syntax.Parser.FileItemsOrdinaryOutcomeSoundnessProperties

/-! Complete broad executable outcomes for canonical syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every executable complete-file success follows the recovery-aware item
grammar and exact pure comment-attachment transformation. -/
theorem sourceFile_success_ordinaryOutcome_sound
    {comments : List Comment} {input output : State}
    {parsedFile : ParsedFile}
    (result : sourceFile comments input = .ok parsedFile output) :
    DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsedFile output.declarativeRemainder := by
  unfold sourceFile at result
  split at result
  next reply rawItems afterItems itemsResult =>
      cases result
      rcases parseItems_success_ordinaryOutcome_sound_strong
          (input.remainingCount + 1) [] input rawItems output itemsResult
          with ⟨suffix, itemsEq, itemsParsed⟩
      have rawItemsEq : rawItems = suffix := by simpa using itemsEq
      subst rawItems
      exact .parsed itemsParsed
  next => contradiction
  next => contradiction

/-- Every executable complete-file rejection is exactly the item loop's first
ordinary rejection. -/
theorem sourceFile_reject_ordinaryOutcome_sound
    {comments : List Comment} {input rejected : State} {failure : Failure}
    (result : sourceFile comments input = .reject failure rejected) :
    DeclarativeGrammar.SourceFileRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold sourceFile at result
  split at result
  next => contradiction
  next reply itemsFailure itemsRejected itemsResult =>
      cases result
      exact .itemsRejected
        (parseItems_reject_ordinaryOutcome_sound
          (input.remainingCount + 1) [] input failure rejected itemsResult)
  next => contradiction

/-- Package unconditional executable success and rejection for complete syntax
files. -/
theorem sourceFile_ordinaryOutcome_sound (comments : List Comment) :
    (∀ {input output : State} {parsedFile : ParsedFile},
      sourceFile comments input = .ok parsedFile output →
        DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
          input.declarativeRemainder parsedFile output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      sourceFile comments input = .reject failure rejected →
        DeclarativeGrammar.SourceFileRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨sourceFile_success_ordinaryOutcome_sound,
    sourceFile_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad complete-file outcomes. -/
theorem sourceFile_ordinaryOutcomeSpec
    (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  DeclarativeGrammar.sourceFileDeterministicOutcomeSpec file comments

end Solcore.Syntax.Parser.FileInternals
