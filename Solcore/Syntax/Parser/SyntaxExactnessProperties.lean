import Solcore.Syntax.Parser.TopItemExactnessProperties
import Solcore.Syntax.Parser.PublicSourceFileValueProperties

/-! Unconditional complete-file syntax exactness at the executable boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace FileInternals

/-- All declaration branches supply an exact recovery-aware file loop. -/
theorem parseItems_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FileItemsOrdinaryParses DeclarativeGrammar.FileItemsRejects :=
  DeclarativeGrammar.fileItemsExactOutcomeSpec

/-- At shared fuel and reverse prefix, file loops fix their complete forward result. -/
theorem parseItems_success_result_unique (fuel : Nat) (itemsRev : List TopItem)
    {input leftOutput rightOutput : State} {left right : List TopItem}
    (leftResult : parseItems fuel itemsRev input = .ok left leftOutput)
    (rightResult : parseItems fuel itemsRev input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  parseItems_success_result_unique_of_topItem DeclarativeGrammar.topItemExactOutcomeSpec
    fuel itemsRev leftResult rightResult

/-- Fixed file provenance and comments give exact source-file outcomes. -/
theorem sourceFile_exactOutcomeSpec (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  DeclarativeGrammar.sourceFileExactOutcomeSpec file comments

/-- Complete source-file successes agree on their attached AST and remainder. -/
theorem sourceFile_success_result_unique (comments : List Comment)
    {input leftOutput rightOutput : State} {left right : ParsedFile}
    (leftResult : sourceFile comments input = .ok left leftOutput)
    (rightResult : sourceFile comments input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  sourceFile_success_result_unique_of_topItem DeclarativeGrammar.topItemExactOutcomeSpec
    comments leftResult rightResult

end FileInternals

/-- At fixed source and lexical carriers, successful public parses have one syntax AST. -/
theorem parseLexed_ok_parsed_value_unique
    {file : SourceFile} {lexed : LexedFile} {left right : ParseOutput}
    (leftResult : parseLexed file lexed = .ok left)
    (rightResult : parseLexed file lexed = .ok right) : left.parsed = right.parsed :=
  parseLexed_ok_parsed_value_unique_of_topItem DeclarativeGrammar.topItemExactOutcomeSpec
    leftResult rightResult

/-- Successful parses of one source file have one complete public syntax AST. -/
theorem parse_ok_parsed_value_unique
    {file : SourceFile} {left right : ParseOutput}
    (leftResult : parse file = .ok left)
    (rightResult : parse file = .ok right) : left.parsed = right.parsed :=
  parse_ok_parsed_value_unique_of_topItem DeclarativeGrammar.topItemExactOutcomeSpec
    leftResult rightResult

end Solcore.Syntax.Parser
