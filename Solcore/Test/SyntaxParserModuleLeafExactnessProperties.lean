import Solcore.Syntax.Parser.SelectorNameOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ModulePathOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportPathOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FinishExportOrdinaryOutcomeSoundnessProperties

/-! Independent grammar-result consumers for exact module-syntax leaves. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserModuleLeafExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @selectorName_exactOutcomeSpec
example := @selectorName_success_result_unique
example := @selectorName_reject_output_unique

example (context : ParseContext)
    {input output : State} {actual expected : SelectorName}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : selectorName context input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.SelectorNameOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (selectorName_exactOutcomeSpec ).successResultUnique
    (selectorName_success_ordinaryOutcome_sound context result) expectedParsed

example (context : ParseContext)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : selectorName context input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.SelectorNameRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (selectorName_exactOutcomeSpec ).rejectOutputUnique
    (selectorName_reject_ordinaryOutcome_sound context result) expectedRejected

example := @modulePath_exactOutcomeSpec
example := @modulePath_success_result_unique
example := @modulePath_reject_output_unique

example (context : ParseContext)
    {input output : State} {actual expected : ModulePath}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : modulePath context input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.ModulePathOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (modulePath_exactOutcomeSpec ).successResultUnique
    (modulePath_success_ordinaryOutcome_sound context result) expectedParsed

example (context : ParseContext)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : modulePath context input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.ModulePathRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (modulePath_exactOutcomeSpec ).rejectOutputUnique
    (modulePath_reject_ordinaryOutcome_sound context result) expectedRejected

example := @exportPath_exactOutcomeSpec
example := @exportPath_success_result_unique
example := @exportPath_reject_output_unique

example
    {input output : State} {actual expected : QualifiedName}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.exportPath input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.ExportPathOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (exportPath_exactOutcomeSpec ).successResultUnique
    (exportPath_success_ordinaryOutcome_sound  result) expectedParsed

example
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.exportPath input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.ExportPathRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (exportPath_exactOutcomeSpec ).rejectOutputUnique
    (exportPath_reject_ordinaryOutcome_sound  result) expectedRejected

example := @importTerminator_exactOutcomeSpec
example := @importTerminator_success_result_unique
example := @importTerminator_reject_output_unique

example (lastSpan : SourceSpan)
    {input output : State} {actual expected : SourceSpan}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.terminator lastSpan input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (importTerminator_exactOutcomeSpec lastSpan).successResultUnique
    (importTerminator_success_ordinaryOutcome_sound lastSpan result) expectedParsed

example (lastSpan : SourceSpan)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ImportInternals.terminator lastSpan input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.ImportTerminatorRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (importTerminator_exactOutcomeSpec lastSpan).rejectOutputUnique
    (importTerminator_reject_ordinaryOutcome_sound lastSpan result) expectedRejected

example := @finishExport_exactOutcomeSpec
example := @finishExport_success_result_unique
example := @finishExport_reject_output_unique

example (start : SourceSpan) (value : ExportDeclValue)
    {input output : State} {actual expected : ExportDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.finishExport start value input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.FinishExportOrdinaryParses start value
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (finishExport_exactOutcomeSpec start value).successResultUnique
    (finishExport_success_ordinaryOutcome_sound start value result) expectedParsed

example (start : SourceSpan) (value : ExportDeclValue)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : ExportInternals.finishExport start value input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.FinishExportRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (finishExport_exactOutcomeSpec start value).rejectOutputUnique
    (finishExport_reject_ordinaryOutcome_sound start value result) expectedRejected

end Solcore.Test.SyntaxParserModuleLeafExactnessProperties
