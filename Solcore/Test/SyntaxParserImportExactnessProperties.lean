import Solcore.Syntax.Parser.ImportExactnessProperties
import Solcore.Test.SyntaxParserImportSelectionExactnessProperties

/-! Independent grammar-result consumers for exact import outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImportExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @plainImport_exactOutcomeSpec
example := @plainImport_success_result_unique
example := @plainImport_reject_output_unique

example (start : SourceSpan)
    {input output : State} {actual expected : ImportDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.plainImport start input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PlainImportOrdinaryParses start
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (plainImport_exactOutcomeSpec start).successResultUnique
    (plainImport_success_ordinaryOutcome_sound start result) expectedParsed

example (start : SourceSpan)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.plainImport start input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.PlainImportRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (plainImport_exactOutcomeSpec start).rejectOutputUnique
    (plainImport_reject_ordinaryOutcome_sound start result) expectedRejected

example := @namespaceImport_exactOutcomeSpec
example := @namespaceImport_success_result_unique
example := @namespaceImport_reject_output_unique

example (start : SourceSpan)
    {input output : State} {actual expected : ImportDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.namespaceImport start input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.NamespaceImportOrdinaryParses start
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (namespaceImport_exactOutcomeSpec start).successResultUnique
    (namespaceImport_success_ordinaryOutcome_sound start result) expectedParsed

example (start : SourceSpan)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.namespaceImport start input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.NamespaceImportRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (namespaceImport_exactOutcomeSpec start).rejectOutputUnique
    (namespaceImport_reject_ordinaryOutcome_sound start result) expectedRejected

example := @wildcardImport_exactOutcomeSpec
example := @wildcardImport_success_result_unique
example := @wildcardImport_reject_output_unique

example (start : SourceSpan)
    {input output : State} {actual expected : ImportDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.wildcardImport start input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.WildcardImportOrdinaryParses start
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (wildcardImport_exactOutcomeSpec start).successResultUnique
    (wildcardImport_success_ordinaryOutcome_sound start result) expectedParsed

example (start : SourceSpan)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.wildcardImport start input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.WildcardImportRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (wildcardImport_exactOutcomeSpec start).rejectOutputUnique
    (wildcardImport_reject_ordinaryOutcome_sound start result) expectedRejected

example := @selectiveImport_exactOutcomeSpec
example := @selectiveImport_success_result_unique
example := @selectiveImport_reject_output_unique

example (start : SourceSpan)
    {input output : State} {actual expected : ImportDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.selectiveImport start input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.SelectiveImportOrdinaryParses start
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (selectiveImport_exactOutcomeSpec start).successResultUnique
    (selectiveImport_success_ordinaryOutcome_sound start result) expectedParsed

example (start : SourceSpan)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.selectiveImport start input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.SelectiveImportRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (selectiveImport_exactOutcomeSpec start).rejectOutputUnique
    (selectiveImport_reject_ordinaryOutcome_sound start result) expectedRejected

example := @importDecl_exactOutcomeSpec
example := @importDecl_success_result_unique
example := @importDecl_reject_output_unique

example
    {input output : State} {actual expected : ImportDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : importDecl input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.ImportDeclOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (importDecl_exactOutcomeSpec).successResultUnique
    (importDecl_success_ordinaryOutcome_sound result) expectedParsed

example
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : importDecl input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.ImportDeclRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (importDecl_exactOutcomeSpec).rejectOutputUnique
    (importDecl_reject_ordinaryOutcome_sound result) expectedRejected

end Solcore.Test.SyntaxParserImportExactnessProperties
