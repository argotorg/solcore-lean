import Solcore.Syntax.Parser.SyntaxExactnessProperties

/-! Consumers of unconditional independent complete-file syntax exactness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSyntaxExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.PlainTopItemOrdinaryParses DeclarativeGrammar.PlainTopItemRejects :=
  plainTopItem_exactOutcomeSpec

example {input output : State} {actual expected : TopItem}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : plainTopItem input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  plainTopItem_exactOutcomeSpec.successResultUnique
    (plainTopItem_success_ordinaryOutcome_sound result) expectedParsed

example := @plainTopItem_success_result_unique
example := @plainTopItem_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects :=
  topItem_exactOutcomeSpec

example {input output : State} {actual expected : TopItem}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : topItem input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  topItem_exactOutcomeSpec.successResultUnique
    (topItem_success_ordinaryOutcome_sound result) expectedParsed

example := @topItem_success_result_unique
example := @topItem_reject_output_unique

example := @parseItems_exactOutcomeSpec
example := @parseItems_success_result_unique
example := @sourceFile_success_result_unique
example := @parseLexed_ok_parsed_value_unique
example := @parse_ok_parsed_value_unique

example (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  sourceFile_exactOutcomeSpec file comments

example (comments : List Comment) {input output : State} {actual expected : ParsedFile}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : sourceFile comments input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (sourceFile_exactOutcomeSpec input.file comments).successResultUnique
    (sourceFile_success_ordinaryOutcome_sound result) expectedParsed

example {file : SourceFile} {lexed : LexedFile} {output : ParseOutput} {expected : ParsedFile}
    (result : parseLexed file lexed = .ok output)
    (expectedParsed : DeclarativeGrammar.PublicSourceFileOrdinaryParses
      file lexed.tokens lexed.comments expected) : output.parsed = expected :=
  DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique
    (parseLexed_ok_publicSourceFileOrdinary_sound result) expectedParsed

example {file : SourceFile} {output : ParseOutput} {expected : ParsedFile}
    (result : parse file = .ok output)
    (expectedParsed : DeclarativeGrammar.PublicSourceFileOrdinaryParses
      file output.tokens output.parsed.comments expected) : output.parsed = expected :=
  DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique
    (parse_ok_publicSourceFileOrdinary_sound result) expectedParsed

end Solcore.Test.SyntaxParserSyntaxExactnessProperties
