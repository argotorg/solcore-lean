import Solcore.Syntax.Parser.ConstructorSelectionOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportNameOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.LocalExportItemOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportSelectionOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.LocalExportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PathExportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportDeclarationOrdinaryOutcomeSoundnessProperties

/-! External consumers of exact export selectors, payloads, and declarations. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.ConstructorSelectionOrdinaryParses
    DeclarativeGrammar.ConstructorSelectionRejects :=
  constructorSelection_exactOutcomeSpec

example {input output : State} {actual expected : ConstructorSelection}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.constructorSelection input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.ConstructorSelectionOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  constructorSelection_exactOutcomeSpec.successResultUnique
    (constructorSelection_success_ordinaryOutcome_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.constructorSelection input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.ConstructorSelectionRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  constructorSelection_exactOutcomeSpec.rejectOutputUnique
    (constructorSelection_reject_ordinaryOutcome_sound result) expectedRejected

example := @constructorSelection_success_result_unique
example := @constructorSelection_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.ExportNameOrdinaryParses
    DeclarativeGrammar.ExportNameRejects :=
  exportName_exactOutcomeSpec

example {input output : State} {actual expected : ExportName}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.exportName input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.ExportNameOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  exportName_exactOutcomeSpec.successResultUnique
    (exportName_success_ordinaryOutcome_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.exportName input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.ExportNameRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  exportName_exactOutcomeSpec.rejectOutputUnique
    (exportName_reject_ordinaryOutcome_sound result) expectedRejected

example := @exportName_success_result_unique
example := @exportName_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.LocalExportItemOrdinaryParses
    DeclarativeGrammar.LocalExportItemRejects :=
  localExportItem_exactOutcomeSpec

example {input output : State} {actual expected : LocalExportItem}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.localExportItem input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.LocalExportItemOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  localExportItem_exactOutcomeSpec.successResultUnique
    (localExportItem_success_ordinaryOutcome_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.localExportItem input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.LocalExportItemRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  localExportItem_exactOutcomeSpec.rejectOutputUnique
    (localExportItem_reject_ordinaryOutcome_sound result) expectedRejected

example := @localExportItem_success_result_unique
example := @localExportItem_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.ExportSelectionOrdinaryParses
    DeclarativeGrammar.ExportSelectionRejects :=
  exportSelection_exactOutcomeSpec

example {input output : State} {actual expected : ExportSelection}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.exportSelection input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.ExportSelectionOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  exportSelection_exactOutcomeSpec.successResultUnique
    (exportSelection_success_ordinaryOutcome_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.exportSelection input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.ExportSelectionRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  exportSelection_exactOutcomeSpec.rejectOutputUnique
    (exportSelection_reject_ordinaryOutcome_sound result) expectedRejected

example := @exportSelection_success_result_unique
example := @exportSelection_reject_output_unique

example (start : SourceSpan) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.LocalExportOrdinaryParses start)
    DeclarativeGrammar.LocalExportRejects :=
  localExport_exactOutcomeSpec start

example (start : SourceSpan) {input output : State} {actual expected : ExportDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.localExport start input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.LocalExportOrdinaryParses start
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (localExport_exactOutcomeSpec start).successResultUnique
    (localExport_success_ordinaryOutcome_sound start result) expectedParsed

example (start : SourceSpan) {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.localExport start input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.LocalExportRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (localExport_exactOutcomeSpec start).rejectOutputUnique
    (localExport_reject_ordinaryOutcome_sound start result) expectedRejected

example := @localExport_success_result_unique
example := @localExport_reject_output_unique

example (start : SourceSpan) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.PathExportOrdinaryParses start)
    DeclarativeGrammar.PathExportRejects :=
  pathExport_exactOutcomeSpec start

example (start : SourceSpan) {input output : State} {actual expected : ExportDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.pathExport start input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PathExportOrdinaryParses start
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (pathExport_exactOutcomeSpec start).successResultUnique
    (pathExport_success_ordinaryOutcome_sound start result) expectedParsed

example (start : SourceSpan) {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.pathExport start input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.PathExportRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (pathExport_exactOutcomeSpec start).rejectOutputUnique
    (pathExport_reject_ordinaryOutcome_sound start result) expectedRejected

example := @pathExport_success_result_unique
example := @pathExport_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.ExportDeclOrdinaryParses
    DeclarativeGrammar.ExportDeclRejects :=
  exportDecl_exactOutcomeSpec

example {input output : State} {actual expected : ExportDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : exportDecl input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.ExportDeclOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  exportDecl_exactOutcomeSpec.successResultUnique
    (exportDecl_success_ordinaryOutcome_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : exportDecl input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.ExportDeclRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  exportDecl_exactOutcomeSpec.rejectOutputUnique
    (exportDecl_reject_ordinaryOutcome_sound result) expectedRejected

example := @exportDecl_success_result_unique
example := @exportDecl_reject_output_unique

example := @DeclarativeGrammar.ConstructorNamesParses.result_unique
example := @DeclarativeGrammar.OptionalConstructorSelectionParses.result_unique

end Solcore.Test.SyntaxParserExportExactnessProperties
