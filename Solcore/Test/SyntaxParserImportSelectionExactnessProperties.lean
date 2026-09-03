import Solcore.Syntax.Parser.ImportSelectionExactnessProperties

/-! Independent grammar-result consumers for exact import outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImportSelectionExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @selectedAlias_exactOutcomeSpec
example := @selectedAlias_success_result_unique
example := @selectedAlias_reject_output_unique

example
    {input output : State} {actual expected : Option Identifier}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.selectedAlias input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.SelectedAliasOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (selectedAlias_exactOutcomeSpec).successResultUnique
    (selectedAlias_success_ordinaryOutcome_sound result) expectedParsed

example
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.selectedAlias input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.SelectedAliasRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (selectedAlias_exactOutcomeSpec).rejectOutputUnique
    (selectedAlias_reject_ordinaryOutcome_sound result) expectedRejected

example := @selectedImport_exactOutcomeSpec
example := @selectedImport_success_result_unique
example := @selectedImport_reject_output_unique

example
    {input output : State} {actual expected : SelectedImport}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : selectedImport input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.SelectedImportOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (selectedImport_exactOutcomeSpec).successResultUnique
    (selectedImport_success_ordinaryOutcome_sound result) expectedParsed

example
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : selectedImport input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.SelectedImportRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (selectedImport_exactOutcomeSpec).rejectOutputUnique
    (selectedImport_reject_ordinaryOutcome_sound result) expectedRejected

example := @selectedImports_exactOutcomeSpec
example := @selectedImports_success_result_unique
example := @selectedImports_reject_output_unique

example
    {input output : State} {actual expected : NonemptyDelimitedList SelectedImport}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.selectedImports input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.SelectedImportsOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (selectedImports_exactOutcomeSpec).successResultUnique
    (selectedImports_success_ordinaryOutcome_sound result) expectedParsed

example
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.selectedImports input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.SelectedImportsRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (selectedImports_exactOutcomeSpec).rejectOutputUnique
    (selectedImports_reject_ordinaryOutcome_sound result) expectedRejected

example := @hidingClause_exactOutcomeSpec
example := @hidingClause_success_result_unique
example := @hidingClause_reject_output_unique

example
    {input output : State} {actual expected : HidingClause}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.hidingClause input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.HidingClauseOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (hidingClause_exactOutcomeSpec).successResultUnique
    (hidingClause_success_ordinaryOutcome_sound result) expectedParsed

example
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.hidingClause input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.HidingClauseRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (hidingClause_exactOutcomeSpec).rejectOutputUnique
    (hidingClause_reject_ordinaryOutcome_sound result) expectedRejected

example := @optionalHiding_exactOutcomeSpec
example := @optionalHiding_success_result_unique
example := @optionalHiding_reject_output_unique

example
    {input output : State} {actual expected : Option HidingClause}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.optionalHiding input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.OptionalHidingOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (optionalHiding_exactOutcomeSpec).successResultUnique
    (optionalHiding_success_ordinaryOutcome_sound result) expectedParsed

example
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.optionalHiding input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.OptionalHidingRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (optionalHiding_exactOutcomeSpec).rejectOutputUnique
    (optionalHiding_reject_ordinaryOutcome_sound result) expectedRejected

end Solcore.Test.SyntaxParserImportSelectionExactnessProperties
