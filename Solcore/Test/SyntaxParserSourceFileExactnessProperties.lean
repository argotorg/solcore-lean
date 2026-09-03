import Solcore.Syntax.Parser.PublicSourceFileValueProperties

/-! External consumers of conditional source-file exactness and public AST uniqueness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSourceFileExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @FileInternals.parseItems_exactOutcomeSpec_of_topItemValues
example := @FileInternals.parseItems_exactOutcomeSpec_of_topItem
example := @FileInternals.parseItems_success_result_unique_of_topItemValues
example := @FileInternals.parseItems_success_result_unique_of_topItem
example := @FileInternals.parseItems_reject_output_unique
example := @FileInternals.sourceFile_exactOutcomeSpec_of_topItemValues
example := @FileInternals.sourceFile_exactOutcomeSpec_of_topItem
example := @FileInternals.sourceFile_success_result_unique_of_topItemValues
example := @FileInternals.sourceFile_success_result_unique_of_topItem
example := @FileInternals.sourceFile_reject_output_unique
example := @parseLexed_ok_parsed_value_unique_of_topItemValues
example := @parseLexed_ok_parsed_value_unique_of_topItem
example := @parse_ok_parsed_value_unique_of_topItemValues
example := @parse_ok_parsed_value_unique_of_topItem

example (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (fuel : Nat) (itemsRev : List TopItem)
    {input leftOutput rightOutput : State} {left right : List TopItem}
    (leftResult : FileInternals.parseItems fuel itemsRev input = .ok left leftOutput)
    (rightResult : FileInternals.parseItems fuel itemsRev input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  FileInternals.parseItems_success_result_unique_of_topItem itemOutcomes
    fuel itemsRev leftResult rightResult

example (comments : List Comment)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : sourceFile comments input =
      .reject leftFailure leftOutput)
    (rightResult : sourceFile comments input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  FileInternals.sourceFile_reject_output_unique comments leftResult rightResult

example (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    {file : SourceFile} {lexed : LexedFile} {left right : ParseOutput}
    (leftResult : parseLexed file lexed = .ok left)
    (rightResult : parseLexed file lexed = .ok right) : left.parsed = right.parsed :=
  parseLexed_ok_parsed_value_unique_of_topItem itemOutcomes leftResult rightResult

example (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    {file : SourceFile} {left right : ParseOutput}
    (leftResult : parse file = .ok left)
    (rightResult : parse file = .ok right) : left.parsed = right.parsed :=
  parse_ok_parsed_value_unique_of_topItem itemOutcomes leftResult rightResult

end Solcore.Test.SyntaxParserSourceFileExactnessProperties
