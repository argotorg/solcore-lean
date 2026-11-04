import Solcore.Syntax.FileValidity
import Solcore.Syntax.Module
import Solcore.Syntax.Parser.ExportCanonicalTotalityProperties
import Solcore.Syntax.Parser.ConstructorSelectionOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportConstructorTotalityProperties
import Solcore.Syntax.Parser.ExportNameOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.LocalExportItemOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportSelectionOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.LocalExportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PathExportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportNameTotalityProperties
import Solcore.Syntax.Parser.ExportPathOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportPathSoundnessProperties
import Solcore.Syntax.Parser.ExportPathTotalityProperties
import Solcore.Syntax.Parser.ExportProperties
import Solcore.Syntax.Parser.FinishExportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportSelectionItemTotalityProperties
import Solcore.Syntax.Parser.ExportTotalityProperties
import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.FileCanonicalProperties
import Solcore.Syntax.Parser.FileCanonicalStateProperties
import Solcore.Syntax.Parser.FileCompleteProperties
import Solcore.Syntax.Parser.FileItemProperties
import Solcore.Syntax.Parser.FileItemStrictProperties
import Solcore.Syntax.Parser.FileItemTotalityProperties
import Solcore.Syntax.Parser.FileItemsProperties
import Solcore.Syntax.Parser.FileItemsSoundnessProperties
import Solcore.Syntax.Parser.FileItemsStateProperties
import Solcore.Syntax.Parser.FileItemsTotalityProperties
import Solcore.Syntax.Parser.TopItemRecoveryCompletenessProperties
import Solcore.Syntax.Parser.FileItemsCompletenessProperties
import Solcore.Syntax.Parser.FilePlainTopItemProperties
import Solcore.Syntax.Parser.FilePlainTopItemTotalityProperties
import Solcore.Syntax.Parser.FileRecoveryProperties
import Solcore.Syntax.Parser.FileRecoveryTotalityProperties
import Solcore.Syntax.Parser.SourceFileSoundnessProperties
import Solcore.Syntax.Parser.SourceFileOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TopItemOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PublicSourceFileExecutionWitnessProperties
import Solcore.Syntax.Parser.FileTopItemProperties
import Solcore.Syntax.Parser.HidingClauseOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImportBaseTotalityProperties
import Solcore.Syntax.Parser.ImportProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImportSelectionExactnessProperties
import Solcore.Syntax.Parser.ImportExactnessProperties
import Solcore.Syntax.Parser.ImportDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImportDeclSoundnessProperties
import Solcore.Syntax.Parser.ImportSelectionTotalityProperties
import Solcore.Syntax.Parser.ImportTotalityProperties
import Solcore.Syntax.Parser.SelectorNameOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ModulePath
import Solcore.Syntax.Parser.ModuleDeclarationCompletenessProperties
import Solcore.Syntax.Parser.TopItemCompletenessProperties
import Solcore.Syntax.Parser.NamespaceImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.NamespaceImportSoundnessProperties
import Solcore.Syntax.Parser.PlainImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PlainImportSoundnessProperties
import Solcore.Syntax.Parser.SelectedAliasOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportsOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectiveImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectiveImportSoundnessProperties
import Solcore.Syntax.Parser.PublicParseCompletenessProperties
import Solcore.Syntax.Parser.PublicSourceFileValueProperties
import Solcore.Syntax.Parser.TopItemRecoveryOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TopItemRecoveryTraceCompletenessProperties
import Solcore.Syntax.Parser.WildcardImportNoHidingSoundnessProperties
import Solcore.Syntax.Parser.WildcardImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.WildcardImportSoundnessProperties

/-!
# Module, import and source file tests

Module paths, imports and exports in every selection form, top items, and the source file level
with its loop, recovery and soundness statements.
-/

section
-- leanmerge: from Solcore.Test.SyntaxFileValidity
/-! External consumers for canonical file-validity contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @TopItem.ValidFor
example := @TopItem.ValidFor.importDecl
example := @TopItem.ValidFor.exportDecl
example := @TopItem.ValidFor.contract
example := @TopItem.ValidFor.error
example := @TopItem.ValidFor.span_valid
example := @TopItem.ValidFor.comments_valid
example := @ParsedFile.ValidFor

example {statementValid : SourceFile → Statement → Prop}
    {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {parsed : ParsedFile}
    (valid : ParsedFile.ValidFor statementValid expressionValid file parsed) :
    parsed.source = file.id := valid.1

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxModuleValidity
/-! External consumers for canonical module declaration validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @ModulePath.ValidFor
example := @SelectorName.ValidFor
example := @SelectedImport.ValidFor
example := @HidingClause.ValidFor
example := @ImportDecl.ValidFor
example := @ConstructorSelection.ValidFor
example := @ExportName.ValidFor
example := @LocalExportItem.ValidFor
example := @ExportSelection.ValidFor
example := @ExportDecl.ValidFor
example := @PragmaDecl.ValidFor

example (file : SourceFile) (declaration : ImportDecl)
    (valid : ImportDecl.ValidFor file declaration) :
    declaration.span.ValidFor file :=
  valid.1

example (file : SourceFile) (declaration : ExportDecl)
    (valid : ExportDecl.ValidFor file declaration) :
    declaration.span.ValidFor file :=
  valid.1

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportCanonicalTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportCanonicalTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example : Parser.InvariantFreeOnValid exportDecl :=
  exportDecl_invariantFreeOnValid

example (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportDecl input ≠ .invariant error :=
  exportDecl_ne_invariant input inputValid error

end Solcore.Test.SyntaxParserExportCanonicalTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportConstructorTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportConstructorTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExportInternals

example := @ConstructorSelectionOrdinaryParses
example := @ConstructorSelectionRejects
example := @constructorSelectionDeterministicOutcomeSpec
example := @constructorSelection_success_ordinaryOutcome_sound
example := @constructorSelection_reject_ordinaryOutcome_sound
example := @constructorSelection_ordinaryOutcome_sound
example := @constructorSelection_ordinaryOutcomeSpec

example : Parser.InvariantFreeOnValid constructorSelection :=
  constructorSelection_invariantFreeOnValid

example (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    constructorSelection input ≠ .invariant error :=
  constructorSelection_ne_invariant input inputValid error

end Solcore.Test.SyntaxParserExportConstructorTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportExactnessProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportDeclSoundnessProperties
/-! External consumers for complete export-declaration grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportDeclSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @FinishExportParses
example := @LocalExportTailParses
example := @LocalExportOrdinaryParses
example := @LocalExportRejects
example := @localExportDeterministicOutcomeSpec
example := @ItemsFromExportTailParses
example := @ModuleAsExportTailParses
example := @ModuleExportTailParses
example := @PathExportTailParses
example := @PathExportOrdinaryParses
example := @PathExportRejects
example := @pathExportDeterministicOutcomeSpec
example := @LocalExportDeclParses
example := @ItemsFromExportDeclParses
example := @ModuleAsExportDeclParses
example := @ModuleExportDeclParses
example := @ExportDeclParses
example := @ExportDeclLeftBracePresentAt
example := @ExportDeclOrdinaryParses
example := @ExportDeclRejects
example := @exportDeclDeterministicOutcomeSpec

example := @finishExport_success_sound
example := @localExport_success_sound
example := @localExport_success_ordinaryOutcome_sound
example := @localExport_reject_ordinaryOutcome_sound
example := @localExport_ordinaryOutcome_sound
example := @localExport_ordinaryOutcomeSpec
example := @pathExport_success_sound
example := @pathExport_success_ordinaryOutcome_sound
example := @pathExport_reject_ordinaryOutcome_sound
example := @pathExport_ordinaryOutcome_sound
example := @pathExport_ordinaryOutcomeSpec
example := @exportDecl_success_sound
example := @exportDecl_success_sound_and_validFor
example := @exportDecl_success_ordinaryOutcome_sound
example := @exportDecl_reject_ordinaryOutcome_sound
example := @exportDecl_ordinaryOutcome_sound
example := @exportDecl_ordinaryOutcomeSpec

example {input next : State} {declaration : ExportDecl}
    (inputValid : input.ValidFor)
    (result : exportDecl input = .ok declaration next) :
    ExportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  exportDecl_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserExportDeclSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportNameSoundnessProperties
/-! External consumers for export-name grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportNameSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalConstructorSelectionParses
example := @ExportNameParses
example := @ExportNameOrdinaryParses
example := @ExportNameRejects
example := @exportNameDeterministicOutcomeSpec
example := @exportName_success_sound
example := @exportName_success_sound_and_validFor
example := @exportName_success_ordinaryOutcome_sound
example := @exportName_reject_ordinaryOutcome_sound
example := @exportName_ordinaryOutcome_sound
example := @exportName_ordinaryOutcomeSpec

example {input next : State} {name : ExportName}
    (inputValid : input.ValidFor)
    (result : ExportInternals.exportName input = .ok name next) :
    ExportNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      name.ValidFor input.file :=
  exportName_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserExportNameSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportNameTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportNameTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ExportInternals.exportName_invariantFreeOnValid
example := @ExportInternals.exportName_ordinary
example := @ExportInternals.exportName_ne_invariant
example := @ExportInternals.exportName_cursor_lt_onSuccess
example := @ExportInternals.exportName_elementTotalityContract

end Solcore.Test.SyntaxParserExportNameTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportPathSoundnessProperties
/-! External consumers for maximal export-path grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportPathSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @DotIdentifierAbsentAt
example := @ExportPathTailParses
example := @ExportPathParses
example := @ExportPathOrdinaryParses
example := @ExportPathRejects
example := @exportPathDeterministicOutcomeSpec
example := @exportPath_success_sound
example := @exportPath_success_sound_and_validFor
example := @exportPath_success_ordinaryOutcome_sound
example := @exportPath_reject_ordinaryOutcome_sound
example := @exportPath_ordinaryOutcome_sound
example := @exportPath_ordinaryOutcomeSpec

example {input rejected : State} {failure : Failure}
    (result : ExportInternals.exportPath input = .reject failure rejected) :
    ExportPathRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  exportPath_reject_ordinaryOutcome_sound result

example {input next : State} {path : QualifiedName}
    (inputValid : input.ValidFor)
    (result : ExportInternals.exportPath input = .ok path next) :
    ExportPathParses input.declarativeRemainder path
        next.declarativeRemainder ∧
      path.ValidFor input.file :=
  exportPath_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserExportPathSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportPathTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportPathTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExportInternals

example : Parser.Ordinary exportPath := exportPath_ordinary

example (input : State) (inputValid : input.ValidFor) :
    (∃ path next, exportPath input = .ok path next) ∨
    (∃ failure next, exportPath input = .reject failure next) :=
  exportPath_invariantFreeOnValid input inputValid

end Solcore.Test.SyntaxParserExportPathTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportProperties
/-! External consumers for canonical export parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @FinishExportOrdinaryParses
example := @FinishExportRejects
example := @finishExportDeterministicOutcomeSpec
example := @finishExport_success_ordinaryOutcome_sound
example := @finishExport_reject_ordinaryOutcome_sound
example := @finishExport_ordinaryOutcome_sound
example := @finishExport_ordinaryOutcomeSpec
example := @exportPath_validFor
example := @exportPath_preservesTokenWindow
example := @exportPath_preservesTokensOnSuccess
example := @exportPath_cursorMonotoneOnSuccess
example := @exportPath_startsAtCurrentTokenOnSuccess
example := @constructorSelection_validFor
example := @constructorSelection_preservesTokenWindow
example := @constructorSelection_preservesTokensOnSuccess
example := @constructorSelection_cursorMonotoneOnSuccess
example := @constructorSelection_startsAtCurrentTokenOnSuccess
example := @exportName_validFor
example := @exportName_preservesTokenWindow
example := @exportName_preservesTokensOnSuccess
example := @exportName_cursorMonotoneOnSuccess
example := @exportName_startsAtCurrentTokenOnSuccess
example := @localExportItem_validFor
example := @localExportItem_preservesTokenWindow
example := @localExportItem_preservesTokensOnSuccess
example := @localExportItem_cursorMonotoneOnSuccess
example := @localExportItem_startsAtCurrentTokenOnSuccess
example := @exportSelection_validFor
example := @exportSelection_preservesTokenWindow
example := @exportSelection_preservesTokensOnSuccess
example := @exportSelection_cursorMonotoneOnSuccess
example := @exportSelection_startsAtCurrentTokenOnSuccess
example := @finishExport_validFor
example := @finishExport_preservesTokenWindow
example := @finishExport_preservesTokensOnSuccess
example := @finishExport_cursorMonotoneOnSuccess
example := @finishExport_keepsStartByte
example := @localExport_validFor
example := @localExport_preservesTokenWindow
example := @localExport_preservesTokensOnSuccess
example := @localExport_cursorMonotoneOnSuccess
example := @localExport_keepsStartByte
example := @pathExport_validFor
example := @pathExport_preservesTokenWindow
example := @pathExport_preservesTokensOnSuccess
example := @pathExport_cursorMonotoneOnSuccess
example := @pathExport_keepsStartByte
example := @exportDecl_validFor
example := @exportDecl_preservesTokenWindow
example := @exportDecl_preservesTokensOnSuccess
example := @exportDecl_cursorMonotoneOnSuccess
example := @exportDecl_startsAtCurrentTokenOnSuccess

example (start : SourceSpan) (value : ExportDeclValue)
    {input output : State} {declaration : ExportDecl}
    (result : ExportInternals.finishExport start value input =
      .ok declaration output) :
    FinishExportOrdinaryParses start value input.declarativeRemainder
      declaration output.declarativeRemainder :=
  finishExport_success_ordinaryOutcome_sound start value result

example (start : SourceSpan) (value : ExportDeclValue)
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.finishExport start value input =
      .reject failure rejected) :
    FinishExportRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  finishExport_reject_ordinaryOutcome_sound start value result

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportSelectionItemTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportSelectionItemTotalityProperties

open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExportInternals

example (nameContract : ElementTotalityContract exportName) :
    ElementTotalityContract localExportItem :=
  localExportItem_elementTotalityContract nameContract

example (nameContract : ElementTotalityContract exportName) :
    ExportLeafTotalityContract :=
  exportLeafTotalityContract nameContract

end Solcore.Test.SyntaxParserExportSelectionItemTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportSelectionSoundnessProperties
/-! External consumers for remote export-selection grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportSelectionSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ExportSelectionParses
example := @ExportSelectionOrdinaryParses
example := @ExportSelectionRejects
example := @exportSelectionDeterministicOutcomeSpec
example := @exportSelection_success_sound
example := @exportSelection_success_sound_and_validFor
example := @exportSelection_success_ordinaryOutcome_sound
example := @exportSelection_reject_ordinaryOutcome_sound
example := @exportSelection_ordinaryOutcome_sound
example := @exportSelection_ordinaryOutcomeSpec

example {input next : State} {selection : ExportSelection}
    (inputValid : input.ValidFor)
    (result : ExportInternals.exportSelection input = .ok selection next) :
    ExportSelectionParses input.declarativeRemainder selection
        next.declarativeRemainder ∧
      selection.ValidFor input.file :=
  exportSelection_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserExportSelectionSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExportTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example (contract : ExportLeafTotalityContract) :
    Parser.InvariantFreeOnValid exportDecl :=
  exportDecl_invariantFreeOnValid_of_leafContract contract

example (contract : ExportLeafTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportDecl input ≠ .invariant error :=
  exportDecl_ne_invariant_of_leafContract contract input inputValid error

end Solcore.Test.SyntaxParserExportTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExports
/-! Executable export parser regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def parserSource : SourceId := {
  origin := .main
  path := "parser-exports.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := parserSource, content }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.lexicalDiagnostics []
        s!"{label} lexical diagnostics"
      unless output.parsed.items.all
          (fun item => item.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid item span")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid diagnostic span")
      pure output

private inductive ConstructorShape where
  | all
  | named (names : List String)
  deriving Repr, BEq

private inductive ExportNameShape where
  | wildcard
  | identifier (name : String) (constructors : Option ConstructorShape)
  | operator (spelling : String)
  deriving Repr, BEq

private inductive LocalExportShape where
  | name (name : ExportNameShape)
  | moduleWildcard (path : List String)
  deriving Repr, BEq

private inductive ExportShape where
  | local (items : List LocalExportShape)
  | wholeModule (path : List String)
  | moduleAlias (path : List String) (alias : String)
  | itemsFromWildcard (path : List String)
  | itemsFromSelected (path : List String) (items : List ExportNameShape)
  deriving Repr, BEq

private def identifierTexts (names : NonemptyList Identifier) : List String :=
  names.toList.map (fun name => name.value)

private def qualifiedComponents (name : QualifiedName) : List String :=
  identifierTexts name.value.components

private def constructorShape
    (selection : ConstructorSelection) : ConstructorShape :=
  match selection.value with
  | .all _ => .all
  | .named names => .named (identifierTexts names)

private def exportNameShape (name : ExportName) : ExportNameShape :=
  match name.value with
  | .wildcard _ => .wildcard
  | .identifier identifier constructors =>
      .identifier identifier.value (constructors.map constructorShape)
  | .operator spelling => .operator spelling.value

private def localExportShape (item : LocalExportItem) : LocalExportShape :=
  match item.value with
  | .name name => .name (exportNameShape name)
  | .moduleWildcard path _ => .moduleWildcard (qualifiedComponents path)

private def exportShape (declaration : ExportDecl) : ExportShape :=
  match declaration.value with
  | .local items => .local (items.elements.map localExportShape)
  | .module path => .wholeModule (qualifiedComponents path)
  | .moduleAs path alias =>
      .moduleAlias (qualifiedComponents path) alias.value
  | .itemsFrom path selection =>
      match selection.value with
      | .wildcard _ => .itemsFromWildcard (qualifiedComponents path)
      | .selected items => .itemsFromSelected
          (qualifiedComponents path) (items.elements.map exportNameShape)

private def exportDecls (output : ParseOutput) : List ExportDecl :=
  output.parsed.items.filterMap fun item => match item.value with
    | .exportDecl declaration => some declaration
    | _ => none

private def testExportForms : IO Unit := do
  let output ← checkedParse "canonical exports" (String.intercalate "\n" [
    "export {};",
    "export {value, *, lib.deep.*, (==), Option(*), Result(Ok, Err),};",
    "export pkg.deep;",
    "export pkg.deep as alias;",
    "export pkg.deep.*;",
    "export pkg.deep.{};",
    "export pkg.deep.{value, *, (:=), Option(Some),};"
  ])
  assertEqual output.parseDiagnostics [] "canonical export diagnostics"
  assertEqual ((exportDecls output).map exportShape) [
    .local [],
    .local [
      .name (.identifier "value" none), .name .wildcard,
      .moduleWildcard ["lib", "deep"], .name (.operator "=="),
      .name (.identifier "Option" (some .all)),
      .name (.identifier "Result" (some (.named ["Ok", "Err"])))
    ],
    .wholeModule ["pkg", "deep"],
    .moduleAlias ["pkg", "deep"] "alias",
    .itemsFromWildcard ["pkg", "deep"],
    .itemsFromSelected ["pkg", "deep"] [],
    .itemsFromSelected ["pkg", "deep"] [
      .identifier "value" none, .wildcard, .operator ":=",
      .identifier "Option" (some (.named ["Some"]))
    ]
  ] "canonical export forms and written distinctions"

private def testExportSpans : IO Unit := do
  let output ← checkedParse "export spans"
    "export pkg.deep.{Option(Some, None), (==), *,};"
  assertEqual output.parseDiagnostics [] "export span diagnostics"
  match exportDecls output with
  | [{ span, value := .itemsFrom path selection }] =>
      assertEqual (byteRange span) (0, 47) "export declaration span"
      assertEqual (byteRange path.span) (7, 15) "export module span"
      assertEqual (byteRange selection.span) (16, 46) "export selection span"
      match selection.value with
      | .selected { elements := [option, operator, wildcard], .. } =>
          assertEqual (byteRange option.span) (17, 35) "constructor export span"
          assertEqual (byteRange operator.span) (37, 41) "operator export span"
          assertEqual (byteRange wildcard.span) (43, 44) "wildcard export span"
      | value => throw (IO.userError
          s!"export spans: unexpected selection {reprStr value}")
  | declarations => throw (IO.userError
      s!"export spans: unexpected declarations {reprStr declarations}")

private def testConstructorTrailingCommaStops : IO Unit := do
  let output ← checkedParse "constructor trailing comma"
    "export {Option(Some,)};\ntype Later = word;"
  assertEqual output.parsed.items.length 0
    "malformed recognized declaration stops later parsing"
  match output.parseDiagnostics with
  | [{ span, kind := .unexpected (some (.symbol .rightParen))
        { head := .identifier, tail := [] } .exportDecl }] =>
      assertEqual (byteRange span) (20, 21)
        "constructor trailing-comma rejection span"
  | diagnostics => throw (IO.userError
      s!"constructor trailing comma: unexpected diagnostics {reprStr diagnostics}")

/-- Run canonical export parser regressions. -/
def testSyntaxParserExports : IO Unit := do
  testExportForms
  testExportSpans
  testConstructorTrailingCommaStops

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileCanonicalProperties
namespace Tests
open Solcore.Syntax.Parser
example := @FileInternals.sourceFile_canonical_reply_validFor
example := @parseLexed_ok_canonical_validFor
example := @parse_ok_canonical_validFor
end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileCanonicalStateProperties
/-! External consumers for canonical complete-file state laws. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.parseItems_canonical_preservesTokenWindow
example := @FileInternals.parseItems_canonical_preservesTokensOnSuccess
example := @FileInternals.parseItems_canonical_cursorMonotoneOnSuccess
example := @FileInternals.sourceFile_canonical_preservesTokenWindow
example := @FileInternals.sourceFile_canonical_preservesTokensOnSuccess
example := @FileInternals.sourceFile_canonical_cursorMonotoneOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileCompleteProperties
set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @FileInternals.contractDecl_canonical_inputs
example := @FileInternals.parseItemsItem_complete_contract
example := @FileInternals.parseItemsItem_complete_validFor
example := @FileInternals.sourceFile_complete_reply_validFor
example := @FileInternals.parseItems_complete_preservesTokenWindow
example := @FileInternals.parseItems_complete_preservesTokensOnSuccess
example := @FileInternals.parseItems_complete_cursorMonotoneOnSuccess
example := @FileInternals.sourceFile_complete_preservesTokenWindow
example := @FileInternals.sourceFile_complete_preservesTokensOnSuccess
example := @FileInternals.sourceFile_complete_cursorMonotoneOnSuccess
example := @parseLexed_ok_complete_validFor
example := @parse_ok_complete_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileItemProperties
namespace Tests
open Solcore.Syntax.Parser
example := @FileInternals.parseItemsItem_contract
example (inputs : FileInternals.ContractDeclInputs) :
    Parser.PreservesTokensOnSuccess FileInternals.parseItemsItem :=
  (FileInternals.parseItemsItem_contract inputs).preservesTokensOnSuccess
end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileItemStrictProperties
namespace Tests
open Solcore.Syntax.Parser
example := @importDecl_cursor_lt_onSuccess
example := @exportDecl_cursor_lt_onSuccess
example := @typeAlias_cursor_lt_onSuccess
example := @functionDecl_cursor_lt_onSuccess
example := @enumDecl_cursor_lt_onSuccess
example := @FileInternals.plainTopItem_cursor_lt_onSuccess
example := @FileInternals.parseItemsItem_cursor_lt_onSuccess
end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileItemTotalityProperties
/-! External consumers for derive-aware complete-file totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFileItemTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @attachDeriveAttribute_invariantFreeOnValid
example := @topItem_invariantFreeOnValid
example := @parseItemsItem_invariantFreeOnValid
example := @parseItemsItemInvariantFree_of_plainTopItemContract
example := @sourceFile_exists_ok_of_plainTopItemContract
example := @parseLexed_exists_ok_of_plainTopItemContract
example := @parseLexed_ne_error_of_plainTopItemContract
example := @parse_exists_ok_of_plainTopItemContract
example := @parse_ne_error_of_plainTopItemContract

example (contract : PlainTopItemTotalityContract) :
    ParseItemsItemInvariantFree :=
  parseItemsItemInvariantFree_of_plainTopItemContract contract

example (contract : PlainTopItemTotalityContract) (file : SourceFile) :
    ∃ output, parse file = .ok output :=
  parse_exists_ok_of_plainTopItemContract contract file

end Solcore.Test.SyntaxParserFileItemTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileItemsProperties
/-! External consumers for complete-file item validity. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.parseItemsItem
example := @FileInternals.parseItems_validFor
example := @FileInternals.sourceFile_reply_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileItemsSoundnessProperties
/-! External consumers for generic complete-file item-loop soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFileItemsSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @TopItemsParses
example := @TopItemsParses.output_atEnd
example := @parseItems_success_sound_of_diagnosticFree

example
    (itemParses : Remainder → TopItem → Remainder → Prop)
    (itemSound : ∀ {input next : State} {item : TopItem},
      next.diagnosticsRev = [] →
      parseItemsItem input = .ok item next →
      itemParses input.declarativeRemainder item next.declarativeRemainder)
    (itemReflectsDiagnosticFree : ∀ {input next : State} {item : TopItem},
      parseItemsItem input = .ok item next →
      next.diagnosticsRev = [] → input.diagnosticsRev = [])
    {fuel : Nat} {itemsRev : List TopItem} {input next : State}
    {items : List TopItem} (diagnosticFree : next.diagnosticsRev = [])
    (parsed : parseItems fuel itemsRev input = .ok items next) :
    ∃ suffix,
      items = itemsRev.reverse ++ suffix ∧
      TopItemsParses itemParses input.declarativeRemainder suffix
        next.declarativeRemainder :=
  parseItems_success_sound_of_diagnosticFree itemParses itemSound
    itemReflectsDiagnosticFree diagnosticFree parsed

end Solcore.Test.SyntaxParserFileItemsSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileItemsStateProperties
/-! External consumers for complete-file state-transition laws. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.parseItems_preservesTokenWindow
example := @FileInternals.parseItems_preservesTokensOnSuccess
example := @FileInternals.parseItems_cursorMonotoneOnSuccess
example := @FileInternals.sourceFile_preservesTokenWindow
example := @FileInternals.sourceFile_preservesTokensOnSuccess
example := @FileInternals.sourceFile_cursorMonotoneOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileItemsTotalityProperties
/-! External consumers for conditional complete-file totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.ParseItemsItemInvariantFree
example := @FileInternals.parseItems_exists_ok_of_remainingCount_lt
example := @FileInternals.parseItems_production_exists_ok
example := @FileInternals.sourceFile_exists_ok

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileLoopCompletenessProperties
/-! Compile-time consumers for recovery and exact file-loop prefix handling. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFileLoopCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @recoverTopItem_ordinary_success_iff
example := @recoverTopItem_ordinary_reject_iff
example := @parseItems_ordinary_success_iff_of_remainingCount_lt
example := @parseItems_production_ordinary_success_iff

example {input : State} {value : TopItem}
    {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder value remainder) :
    ∃ output, recoverTopItem input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  recoverTopItem_ordinary_success_iff.mp parsed

example {input : State} {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TopItemRecoveryRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, recoverTopItem input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  recoverTopItem_ordinary_reject_iff.mp rejection

example (fuel : Nat) (itemsRev : List TopItem)
    {input : State} (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    {suffix : List TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder suffix remainder) :
    ∃ output, parseItems fuel itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output ∧
      output.declarativeRemainder = remainder :=
  (parseItems_ordinary_success_iff_of_remainingCount_lt
    fuel itemsRev inputValid adequate).mp parsed

example (itemsRev : List TopItem)
    {input output : State} (inputValid : input.ValidFor) {suffix : List TopItem}
    (result : parseItems (input.remainingCount + 1) itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output) :
    DeclarativeGrammar.FileItemsOrdinaryParses input.declarativeRemainder suffix
      output.declarativeRemainder :=
  (parseItems_production_ordinary_success_iff itemsRev inputValid).mpr
    ⟨output, result, rfl⟩

example {input : State} (inputValid : input.ValidFor)
    {items : List TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder items remainder) :
    ∃ output, parseItems (input.remainingCount + 1) [] input = .ok items output ∧
      output.declarativeRemainder = remainder := by
  simpa using (parseItems_production_ordinary_success_iff [] inputValid).mp parsed

example (earlier latest : TopItem)
    {input : State} (inputValid : input.ValidFor)
    {suffix : List TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder suffix remainder) :
    ∃ output, parseItems (input.remainingCount + 1) [latest, earlier] input =
      .ok ([earlier, latest] ++ suffix) output ∧
      output.declarativeRemainder = remainder := by
  simpa using (parseItems_production_ordinary_success_iff
    [latest, earlier] inputValid).mp parsed

end Solcore.Test.SyntaxParserFileLoopCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFilePlainTopItemProperties
namespace Tests
open Solcore.Syntax.Parser
example := @FileInternals.plainTopItem_contract
example (inputs : FileInternals.ContractDeclInputs) :
    Parser.PreservesTokensOnSuccess FileInternals.plainTopItem :=
  (FileInternals.plainTopItem_contract inputs).preservesTokensOnSuccess
end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFilePlainTopItemTotalityProperties
/-! External consumers for conditional plain top-item totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFilePlainTopItemTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @mapTopItem_invariantFreeOnValid
example := @PlainTopItemTotalityContract
example := @plainTopItem_invariantFreeOnValid
example := @plainTopItem_ne_invariant

example (contract : PlainTopItemTotalityContract)
    (input : State) (valid : input.ValidFor)
    (error : ParserInvariantError) :
    plainTopItem input ≠ .invariant error :=
  plainTopItem_ne_invariant contract input valid error

end Solcore.Test.SyntaxParserFilePlainTopItemTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileRecoveryProperties
/-! External consumers for canonical top-level recovery contracts. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.finishRecoveredTopItem
example := @FileInternals.recoverTopItemAux
example := @FileInternals.recoverTopItem
example := @FileInternals.RecoveredTopItemValid
example := @FileInternals.finishRecoveredTopItem_validFor
example := @FileInternals.recoverTopItemAux_validFor
example := @FileInternals.recoverTopItem_validFor
example := @FileInternals.finishRecoveredTopItem_preservesTokenWindow
example := @FileInternals.recoverTopItemAux_preservesTokenWindow
example := @FileInternals.recoverTopItemAux_preservesTokensOnSuccess
example := @FileInternals.recoverTopItemAux_ok_state_shape
example := @FileInternals.recoverTopItemAux_cursorMonotoneOnSuccess
example := @FileInternals.recoverTopItem_preservesTokenWindow
example := @FileInternals.recoverTopItem_preservesTokensOnSuccess
example := @FileInternals.recoverTopItem_ok_state_shape
example := @FileInternals.recoverTopItem_cursor_lt_onSuccess
example := @FileInternals.recoverTopItem_cursorMonotoneOnSuccess
example := @FileInternals.recoverTopItem_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileRecoveryTotalityProperties
/-! External consumers for top-level recovery totality contracts. -/

namespace Tests

open Solcore.Syntax.Parser

example :=
  @FileInternals.recoverTopItemAux_exists_ok_of_remainingCount_lt
example := @FileInternals.recoverTopItemAux_production_exists_ok
example := @FileInternals.recoverTopItem_ordinary
example := @FileInternals.recoverTopItem_ne_invariant
example := @FileInternals.recoverTopItem_exists_ok_of_validFor_not_atEnd
example := @FileInternals.recoverTopItem_eq_rejectAt_of_atEnd
example := @FileInternals.recoverTopItem_exists_ok_iff_not_atEnd

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileSoundnessProperties
/-! External consumers for parametric complete-file grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFileSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TopItemKindsAbsentAt
example := @PlainTopItemParses
example := @TopItemParses
example := @TopItemsParses
example := @SourceFileParses
example := @PlainTopItemTokenPresentAt
example := @PlainTopItemBranch
example := @PlainTopItemBranchSelected
example := @PlainTopItemOrdinaryParses
example := @PlainTopItemRejects
example := @plainTopItemDeterministicOutcomeSpec
example := @TopItemDeriveAttaches
example := @TopItemOrdinaryParses
example := @TopItemRejects
example := @topItemDeterministicOutcomeSpec
example := @TopItemRecoveryStops
example := @TopItemRecoveryScanParses
example := @TopItemRecoveryParses
example := @TopItemRecoveryRejects
example := @topItemRecoveryDeterministicOutcomeSpec
example := @TopItemRejectsWithPreservedWindow
example := @FileItemsOrdinaryParses
example := @FileItemsRejects
example := @fileItemsDeterministicOutcomeSpec
example := @SourceFileOrdinaryParses
example := @SourceFileRejects
example := @sourceFileDeterministicOutcomeSpec
example := @sourceFileRootRemainder
example := @nestingExceededParsedFile
example := @PublicSourceFileOrdinaryParses
example := @publicSourceFileOrdinaryParses_iff
example := @PublicSourceFileOrdinaryParses.shape
example := @PublicSourceFileOrdinaryParses.eq_nestingExceededParsedFile
example := @PublicSourceFileOrdinaryParses.sourceFile_of_clears

example := @FileInternals.plainTopItem_reflectsDiagnosticFreeOnSuccess
example := @FileInternals.plainTopItem_success_sound
example := @FileInternals.plainTopItem_success_ordinaryOutcome_sound
example := @FileInternals.plainTopItem_reject_ordinaryOutcome_sound
example := @FileInternals.plainTopItem_ordinaryOutcome_sound
example := @FileInternals.plainTopItem_ordinaryOutcomeSpec
example := @FileInternals.attachDeriveAttribute_reflectsDiagnosticFreeOnSuccess
example := @FileInternals.attachDeriveAttribute_success_ordinaryOutcome_sound
example := @FileInternals.attachDeriveAttribute_total_success
example := @FileInternals.topItem_reflectsDiagnosticFreeOnSuccess
example := @FileInternals.topItem_success_sound
example := @FileInternals.topItem_success_ordinaryOutcome_sound
example := @FileInternals.topItem_reject_ordinaryOutcome_sound
example := @FileInternals.topItem_ordinaryOutcome_sound
example := @FileInternals.topItem_ordinaryOutcomeSpec
example := @FileInternals.atTopItemStart_eq_true_of_topItemRecoveryBoundary
example := @FileInternals.topItemRecoveryStops_of_guard_eq_true
example := @FileInternals.topItemRecoveryStops_of_advance?_eq_none
example := @FileInternals.no_topItemRecoveryStops_of_nonBoundary_token
example := @FileInternals.recoverTopItemAux_success_ordinaryOutcome_sound
example := @FileInternals.recoverTopItem_success_ordinaryOutcome_sound
example := @FileInternals.recoverTopItem_reject_ordinaryOutcome_sound
example := @FileInternals.recoverTopItem_ordinaryOutcome_sound
example := @FileInternals.recoverTopItem_ordinaryOutcomeSpec
example := @FileInternals.topItemRejectsWithPreservedWindow_of_result
example := @FileInternals.rewoundTopItem_declarativeRemainder_eq
example := @FileInternals.parseItems_success_ordinaryOutcome_sound_strong
example := @FileInternals.parseItems_reject_ordinaryOutcome_sound
example := @FileInternals.parseItems_ordinaryOutcome_sound
example := @FileInternals.parseItems_ordinaryOutcomeSpec
example := @FileInternals.sourceFile_success_ordinaryOutcome_sound
example := @FileInternals.sourceFile_reject_ordinaryOutcome_sound
example := @FileInternals.sourceFile_ordinaryOutcome_sound
example := @FileInternals.sourceFile_ordinaryOutcomeSpec
example := @parseLexed_ok_publicSourceFileOrdinary_sound
example := @parseLexed_ok_publicSourceFileOrdinary_sound_and_validFor
example := @parse_ok_publicSourceFileOrdinary_sound
example := @parse_ok_publicSourceFileOrdinary_sound_and_validFor
example := @nestingExceededParseOutput
example := @parseLexed_eq_ok_of_nestingExceeds
example := @parseLexed_ok_eq_nestingExceededParseOutput
example := @parseLexed_ok_parseDiagnostics_eq_of_nestingExceeds
example := @sourceFileParseOutput
example := @parseLexed_ok_sourceFile_executionWitness_of_nestingClears
example := @parseLexed_ok_parseDiagnostics_executionWitness_of_nestingClears
example := @parse_ok_sourceFile_executionWitness_of_nestingClears
example := @FileInternals.parseItems_success_sound_of_diagnosticFree
example := @FileInternals.sourceFile_success_sound
example := @FileInternals.sourceFile_success_sound_and_validFor

example := @TopItemsParses.output_atEnd
example := @SourceFileParses.output_atEnd

example
    (expressionParses : Remainder → Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Block → Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {comments : List Comment} {input next : State} {parsedFile : ParsedFile}
    (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    SourceFileParses
          (TopItemParses expressionParses allowBodyParses requiredBodyParses)
          input.file comments input.declarativeRemainder parsedFile
            next.declarativeRemainder ∧
      ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor input.file
        parsedFile :=
  FileInternals.sourceFile_success_sound_and_validFor expressionParses
    allowBodyParses requiredBodyParses expressionReflects expressionSound
    allowBodyReflects allowBodySound requiredBodyReflects requiredBodySound
    inputValid commentsValid diagnosticFree result

example
    {itemParses : Remainder → TopItem → Remainder → Prop}
    {file : SourceFile} {comments : List Comment}
    {input output : Remainder} {parsedFile : ParsedFile}
    (parsed : SourceFileParses itemParses file comments input parsedFile
      output) :
    output.endIndex ≤ output.cursor :=
  parsed.output_atEnd

end Solcore.Test.SyntaxParserFileSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFileTopItemProperties
/-! External consumers for top-level wrapping and derive attachment. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.TopItemSpanAligned
example := @FileInternals.TopItemContract
example := @FileInternals.wrapImport_contract
example := @FileInternals.wrapExport_contract
example := @FileInternals.wrapPragma_contract
example := @FileInternals.wrapTypeAlias_contract
example := @FileInternals.wrapFunction_contract
example := @FileInternals.wrapEnum_contract
example := @FileInternals.wrapTrait_contract
example := @FileInternals.wrapImpl_contract
example := @FileInternals.wrapContract_contract
example := @FileInternals.extendTopItemStart_contract
example := @FileInternals.attachDeriveAttribute_reply_validFor
example := @FileInternals.attachDeriveAttribute_preservesTokenWindow
example := @FileInternals.attachDeriveAttribute_preservesTokensOnSuccess
example := @FileInternals.attachDeriveAttribute_cursorMonotoneOnSuccess
example := @FileInternals.attachDeriveAttribute_preservesDeriveStartOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserHidingClauseSoundnessProperties
/-! External consumers for hiding-clause grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserHidingClauseSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NonemptySelectorListParses
example := @HidingClauseParses
example := @OptionalHidingParses
example := @HidingClauseOrdinaryParses
example := @HidingClauseRejects
example := @OptionalHidingOrdinaryParses
example := @OptionalHidingRejects
example := @hidingClauseDeterministicOutcomeSpec
example := @optionalHidingDeterministicOutcomeSpec
example := @contextualAbsentAt_of_isContextual_eq_false
example := @requireSelectorNames_success_shape
example := @hidingClause_success_sound
example := @hidingClause_success_sound_and_validFor
example := @optionalHiding_success_sound
example := @optionalHiding_success_sound_and_validFor
example := @hidingClause_ordinaryOutcome_sound
example := @hidingClause_ordinaryOutcomeSpec
example := @optionalHiding_ordinaryOutcome_sound
example := @optionalHiding_ordinaryOutcomeSpec

example {input next : State} {hidden : Option HidingClause}
    (inputValid : input.ValidFor)
    (result : ImportInternals.optionalHiding input = .ok hidden next) :
    OptionalHidingParses input.declarativeRemainder hidden
        next.declarativeRemainder ∧
      Option.ValidFor HidingClause.ValidFor input.file hidden :=
  optionalHiding_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserHidingClauseSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImportBaseTotalityProperties
/-! External consumers for basic import-parser totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @ImportInternals.terminator_ordinary
example := @ImportInternals.terminator_ne_invariant
example := @ImportInternals.finish_ordinary
example := @ImportInternals.finish_ne_invariant
example := @ImportInternals.plainImport_ordinary
example := @ImportInternals.plainImport_ne_invariant
example := @ImportInternals.namespaceImport_ordinary
example := @ImportInternals.namespaceImport_ne_invariant

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImportProperties
/-! External consumers for canonical import parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ImportTerminatorOrdinaryParses
example := @ImportTerminatorRejects
example := @importTerminatorDeterministicOutcomeSpec
example := @importTerminator_success_ordinaryOutcome_sound
example := @importTerminator_reject_ordinaryOutcome_sound
example := @importTerminator_ordinaryOutcome_sound
example := @importTerminator_ordinaryOutcomeSpec
example := selectedAlias_validFor
example := selectedAlias_preservesTokenWindow
example := selectedAlias_preservesTokensOnSuccess
example := selectedAlias_cursorMonotoneOnSuccess
example := hidingClause_validFor
example := hidingClause_preservesTokenWindow
example := hidingClause_preservesTokensOnSuccess
example := hidingClause_cursorMonotoneOnSuccess
example := hidingClause_startsAtCurrentTokenOnSuccess
example := optionalHiding_validFor
example := optionalHiding_preservesTokenWindow
example := optionalHiding_preservesTokensOnSuccess
example := optionalHiding_cursorMonotoneOnSuccess
example := @importTerminator_validFor
example := @finishImport_validFor
example := @plainImport_validFor
example := @namespaceImport_validFor
example := @wildcardImport_validFor
example := @selectiveImport_validFor
example := importDecl_validFor
example := @importTerminator_preservesTokenWindow
example := @importTerminator_preservesTokensOnSuccess
example := @importTerminator_cursorMonotoneOnSuccess
example := @finishImport_preservesTokenWindow
example := @finishImport_preservesTokensOnSuccess
example := @finishImport_cursorMonotoneOnSuccess
example := @finishImport_keepsStartByte
example := @plainImport_preservesTokenWindow
example := @plainImport_cursorMonotoneOnSuccess
example := @namespaceImport_preservesTokenWindow
example := @namespaceImport_cursorMonotoneOnSuccess
example := @wildcardImport_preservesTokenWindow
example := @wildcardImport_cursorMonotoneOnSuccess
example := @plainImport_keepsStartByte
example := @namespaceImport_keepsStartByte
example := @wildcardImport_keepsStartByte
example := @selectiveImport_preservesTokenWindow
example := @selectiveImport_cursorMonotoneOnSuccess
example := importDecl_preservesTokenWindow
example := importDecl_preservesTokensOnSuccess
example := importDecl_cursorMonotoneOnSuccess
example := @selectiveImport_keepsStartByte
example := importDecl_startsAtCurrentTokenOnSuccess
example := selectedImport_validFor
example := selectedImport_preservesTokenWindow
example := selectedImport_preservesTokensOnSuccess
example := selectedImport_cursorMonotoneOnSuccess
example := selectedImport_startsAtCurrentTokenOnSuccess
example := selectedImports_validFor
example := selectedImports_preservesTokenWindow
example := selectedImports_preservesTokensOnSuccess
example := selectedImports_cursorMonotoneOnSuccess
example := selectedImports_startsAtCurrentTokenOnSuccess

example (lastSpan : SourceSpan) {input output : State}
    {endSpan : SourceSpan}
    (result : ImportInternals.terminator lastSpan input = .ok endSpan output) :
    ImportTerminatorOrdinaryParses lastSpan input.declarativeRemainder
      endSpan output.declarativeRemainder :=
  importTerminator_success_ordinaryOutcome_sound lastSpan result

example (lastSpan : SourceSpan) {input rejected : State} {failure : Failure}
    (result : ImportInternals.terminator lastSpan input =
      .reject failure rejected) :
    ImportTerminatorRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  importTerminator_reject_ordinaryOutcome_sound lastSpan result

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImportSelectionExactnessProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImportExactnessProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImportDeclSoundnessProperties
/-! External consumers for aggregate import grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImportDeclSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ImportDeclParses
example := @ImportDeclParses.ofPlain
example := @ImportDeclParses.ofNamespace
example := @ImportDeclParses.ofWildcard
example := @ImportDeclParses.ofSelected
example := @ImportDeclOrdinaryParses
example := @ImportDeclRejects
example := @importDeclDeterministicOutcomeSpec
example := @importDecl_success_sound
example := @importDecl_success_sound_and_validFor
example := @importDecl_success_ordinaryOutcome_sound
example := @importDecl_reject_ordinaryOutcome_sound
example := @importDecl_ordinaryOutcome_sound
example := @importDecl_ordinaryOutcomeSpec

example {input next : State} {declaration : ImportDecl}
    (result : importDecl input = .ok declaration next) :
    ImportDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  importDecl_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : importDecl input = .reject failure rejected) :
    ImportDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  importDecl_reject_ordinaryOutcome_sound result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : importDecl input = .ok declaration next) :
    ImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_success_sound_and_validFor inputValid diagnosticFree result

end Solcore.Test.SyntaxParserImportDeclSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImportSelectionTotalityProperties
/-! External consumers for selected-import totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImportSelectionTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ImportInternals

example := @selectedAlias_ordinary
example := @selectedAlias_ne_invariant
example := @selectedImport_ordinary
example := @selectedImport_ne_invariant
example := @selectedImport_cursor_lt_onSuccess
example := @selectedImport_elementTotalityContract
example := @requireSelected_ordinary_of_delimited_success
example := @requireSelected_ne_invariant_of_delimited_success
example := @requireSelectorNames_ordinary_of_delimited_success
example := @requireSelectorNames_ne_invariant_of_delimited_success
example := @selectedImports_ordinary
example := @selectedImports_invariantFreeOnValid
example := @selectedImports_ne_invariant
example := @hidingClause_ordinary
example := @hidingClause_invariantFreeOnValid
example := @hidingClause_ne_invariant
example := @optionalHiding_ordinary
example := @optionalHiding_invariantFreeOnValid
example := @optionalHiding_ne_invariant

example : ElementTotalityContract selectedImport :=
  selectedImport_elementTotalityContract

end Solcore.Test.SyntaxParserImportSelectionTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImportTotalityProperties
/-! External consumers for complete import-declaration totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImportTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ImportInternals

example := @wildcardImport_ordinary
example := @wildcardImport_ne_invariant
example := @wildcardImport_invariantFreeOnValid
example := @selectiveImport_ordinary
example := @selectiveImport_ne_invariant
example := @selectiveImport_invariantFreeOnValid
example := @importDecl_ordinary
example := @importDecl_ne_invariant
example := @importDecl_invariantFreeOnValid

/-- The result has exactly the type required by plain top-item dispatch. -/
example : Parser.InvariantFreeOnValid importDecl :=
  importDecl_invariantFreeOnValid

end Solcore.Test.SyntaxParserImportTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserModuleLeafExactnessProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParserModulePathProperties
/-! External consumers for module-path provenance and shape contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @qualifiedName_ok_state_shape
example := @qualifiedName_preservesTokensOnSuccess
example := @ModulePath.ValidFor
example := @modulePath_validFor
example := @modulePath_preservesTokenWindow
example := @modulePath_preservesTokensOnSuccess
example := @modulePath_startsAtCurrentTokenOnSuccess
example := @modulePath_cursor_lt_onSuccess
example := @modulePath_cursorMonotoneOnSuccess

example (file : SourceFile) (path : ModulePath)
    (valid : ModulePath.ValidFor file path) :
    path.span.ValidFor file ∧
      (∀ component ∈ path.value.components.toList,
        component.span.ValidFor file) :=
  ⟨valid.1, valid.2.2⟩

example (context : ParseContext) :
    (modulePath context).ValidFor ModulePath.ValidFor :=
  modulePath_validFor context

example (context : ParseContext) :
    (modulePath context).ValidFor ModulePath.ValidFor ∧
      Parser.PreservesTokensOnSuccess (modulePath context) ∧
      Parser.CursorMonotoneOnSuccess (modulePath context) ∧
      Parser.StartsAtCurrentTokenOnSuccess (modulePath context) (·.span) :=
  ⟨modulePath_validFor context,
    modulePath_preservesTokensOnSuccess context,
    modulePath_cursorMonotoneOnSuccess context,
    modulePath_startsAtCurrentTokenOnSuccess context⟩

example (context : ParseContext) {input next : State} {path : ModulePath}
    (inputValid : input.ValidFor)
    (result : modulePath context input = .ok path next) :
    ModulePath.ValidFor input.file path ∧ next.ValidFor ∧
      next.file = input.file ∧ input.cursor < next.cursor ∧
      next.tokens = input.tokens ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = path.span.startByte := by
  have valid := modulePath_validFor context input inputValid
  rw [result] at valid
  exact ⟨valid.1, valid.2.1, valid.2.2,
    modulePath_cursor_lt_onSuccess context result,
    modulePath_preservesTokensOnSuccess context input path next result,
    modulePath_startsAtCurrentTokenOnSuccess context input path next result⟩

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserModulePathSoundnessProperties
/-! External consumers for canonical module-path success soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserModulePathSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ModulePathParses
example := @ModulePathOrdinaryParses
example := @ModulePathRejects
example := @modulePathDeterministicOutcomeSpec
example := @modulePath_success_sound
example := @modulePath_success_sound_and_validFor
example := @modulePath_success_ordinaryOutcome_sound
example := @modulePath_reject_ordinaryOutcome_sound
example := @modulePath_ordinaryOutcome_sound
example := @modulePath_ordinaryOutcomeSpec

example (context : ParseContext) {input next : State} {path : ModulePath}
    (result : modulePath context input = .ok path next) :
    ModulePathParses input.declarativeRemainder path
      next.declarativeRemainder :=
  modulePath_success_sound context result

example (context : ParseContext) {input next : State} {path : ModulePath}
    (inputValid : input.ValidFor)
    (result : modulePath context input = .ok path next) :
    ModulePathParses input.declarativeRemainder path
        next.declarativeRemainder ∧
      path.ValidFor input.file :=
  modulePath_success_sound_and_validFor context inputValid result

end Solcore.Test.SyntaxParserModulePathSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserModulePathTotalityProperties
/-! External consumers for module-path totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @modulePath_ordinary
example := @modulePath_ne_invariant
example := @modulePath_invariantFreeOnValid
example := @modulePath_elementTotalityContract

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserModuleTopItemCompletenessProperties
/-! External consumers of both directions of module and top-item completeness.
The pragma examples intentionally require no state-validity hypothesis. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserModuleTopItemCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example {input : State} (inputValid : input.ValidFor)
    {value : ImportDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ImportDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, importDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (importDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ImportDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : importDecl input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ImportDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (importDecl_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ImportDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, importDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (importDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : importDecl input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ImportDeclRejects input.declarativeRemainder rejected :=
  (importDecl_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : ExportDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExportDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, exportDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (exportDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ExportDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : exportDecl input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ExportDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (exportDecl_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ExportDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, exportDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (exportDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : exportDecl input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ExportDeclRejects input.declarativeRemainder rejected :=
  (exportDecl_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State}
    {value : PragmaDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.PragmaDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, pragmaDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (pragmaDecl_ordinary_success_iff).mp parsed

example {input : State}
    {value : PragmaDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : pragmaDecl input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.PragmaDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (pragmaDecl_ordinary_success_iff).mpr ⟨output, result, remainderEq⟩

example {input : State}
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.PragmaDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, pragmaDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (pragmaDecl_ordinary_reject_iff).mp rejection

example {input : State}
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : pragmaDecl input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.PragmaDeclRejects input.declarativeRemainder rejected :=
  (pragmaDecl_ordinary_reject_iff).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, plainTopItem input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (plainTopItem_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : plainTopItem input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder value remainder :=
  (plainTopItem_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.PlainTopItemRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, plainTopItem input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (plainTopItem_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : plainTopItem input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.PlainTopItemRejects input.declarativeRemainder rejected :=
  (plainTopItem_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, topItem input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (topItem_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : topItem input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder value remainder :=
  (topItem_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TopItemRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, topItem input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (topItem_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : topItem input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.TopItemRejects input.declarativeRemainder rejected :=
  (topItem_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserModuleTopItemCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserModules
/-! Executable import and pragma parser regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def parserSource_variant : SourceId := {
  origin := .main
  path := "parser-modules.sol"
}

private def checkedParse_variant (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := parserSource_variant, content }
  match Parser.parse file with
  | .error error =>
      throw (IO.userError
        s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.lexicalDiagnostics []
        s!"{label} lexical diagnostics"
      unless output.parsed.items.all
          (fun item => item.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid item span")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid diagnostic span")
      pure output

private structure PathShape where
  rooted : Bool
  components : List String
  deriving Repr, BEq

private inductive SelectorShape where
  | identifier (name : String)
  | operator (spelling : String)
  deriving Repr, BEq

private structure SelectedShape where
  source : SelectorShape
  alias : Option String
  deriving Repr, BEq

private inductive ImportShape where
  | plain (path : PathShape)
  | namespaceAlias (path : PathShape) (alias : String)
  | wildcard (path : PathShape) (hidden : Option (List SelectorShape))
  | selected
      (items : List SelectedShape)
      (path : PathShape)
      (hidden : Option (List SelectorShape))
  deriving Repr, BEq

private def pathShape (path : ModulePath) : PathShape := {
  rooted := path.value.externalMarker.isSome
  components := identifierTexts path.value.components
}

private def selectorShape (selector : SelectorName) : SelectorShape :=
  match selector.value with
  | .identifier name => .identifier name.value
  | .operator spelling => .operator spelling

private def hidingShape (clause : HidingClause) : List SelectorShape :=
  clause.value.names.toList.map selectorShape

private def importShape (declaration : ImportDecl) : ImportShape :=
  match declaration.value with
  | .plain path => .plain (pathShape path)
  | .namespace path alias => .namespaceAlias (pathShape path) alias.value
  | .wildcard path hidden =>
      .wildcard (pathShape path) (hidden.map hidingShape)
  | .selected items path hidden =>
      .selected
        (items.elements.toList.map fun item => {
          source := selectorShape item.value.source
          alias := item.value.alias.map (fun name => name.value)
        })
        (pathShape path) (hidden.map hidingShape)

private def importDecls (output : ParseOutput) : List ImportDecl :=
  output.parsed.items.filterMap fun item => match item.value with
    | .importDecl declaration => some declaration
    | _ => none

private def pragmaDecls (output : ParseOutput) : List PragmaDecl :=
  output.parsed.items.filterMap fun item => match item.value with
    | .pragmaDecl declaration => some declaration
    | _ => none

private def testImportForms : IO Unit := do
  let output ← checkedParse_variant "canonical imports" (String.intercalate "\n" [
    "import alpha.beta;",
    "import @vendor.pkg;",
    "import * as ns from lib.deep;",
    "import * as ext from @vendor.deep;",
    "import * from lib.all;",
    "import * from @vendor.all hiding {gone, (!),};",
    "import {foo, bar as baz, (==) as eq,} from @pkg.names hiding {foo, (+=),};"
  ])
  assertEqual output.parseDiagnostics [] "canonical import diagnostics"
  assertEqual ((importDecls output).map importShape) [
    .plain ⟨false, ["alpha", "beta"]⟩,
    .plain ⟨true, ["vendor", "pkg"]⟩,
    .namespaceAlias ⟨false, ["lib", "deep"]⟩ "ns",
    .namespaceAlias ⟨true, ["vendor", "deep"]⟩ "ext",
    .wildcard ⟨false, ["lib", "all"]⟩ none,
    .wildcard ⟨true, ["vendor", "all"]⟩
      (some [.identifier "gone", .operator "!"]),
    .selected [
        ⟨.identifier "foo", none⟩,
        ⟨.identifier "bar", some "baz"⟩,
        ⟨.operator "==", some "eq"⟩
      ] ⟨true, ["pkg", "names"]⟩
      (some [.identifier "foo", .operator "+="])
  ] "canonical import forms"

private def operatorSpellings : List String := [
  ":=", "->", "=>", "==", "!=", ">=", "<=", "&&", "||",
  "+=", "-=", "*=", "/=", "^=", "&=", "|=", "%=", "~=",
  "+", "-", "*", "/", "%", "!", "~", "<", ">", "=", "|",
  "&", "^", ":", "+-"
]

private def testOperatorSelectors : IO Unit := do
  let selectors := operatorSpellings.map (fun spelling =>
    "(" ++ spelling ++ ")")
  let output ← checkedParse_variant "operator selectors"
    ("import {" ++ String.intercalate ", " selectors ++ "} from ops;")
  assertEqual output.parseDiagnostics [] "operator selector diagnostics"
  match (importDecls output).map importShape with
  | [.selected items _ none] =>
      assertEqual (items.map (fun item => item.source))
        (operatorSpellings.map .operator) "operator selector spellings"
  | shapes => throw (IO.userError
      s!"operator selectors: unexpected imports {reprStr shapes}")

private def testImportSpans : IO Unit := do
  let output ← checkedParse_variant "import spans"
    "import {foo as bar, (==),} from @pkg.mod hiding {gone,};"
  assertEqual output.parseDiagnostics [] "import span diagnostics"
  match importDecls output with
  | [{ span, value := .selected selection path (some hidden) }] =>
      assertEqual (byteRange span) (0, 56) "import declaration span"
      assertEqual (byteRange selection.span) (7, 26) "import selection span"
      match selection.elements.toList with
      | [first, operator] =>
          assertEqual (byteRange first.span) (8, 18) "aliased import span"
          assertEqual (byteRange operator.span) (20, 24) "operator import span"
      | values => throw (IO.userError
          s!"import spans: unexpected selection {reprStr values}")
      assertEqual (byteRange path.span) (32, 40) "external module span"
      assertEqual (path.value.externalMarker.map byteRange) (some (32, 33))
        "external marker span"
      assertEqual (byteRange hidden.span) (41, 55) "hiding clause span"
      assertEqual (hidden.value.names.toList.map
        (fun name => byteRange name.span)) [(49, 53)] "hidden-name span"
  | declarations => throw (IO.userError
      s!"import spans: unexpected declarations {reprStr declarations}")

private def testPragmaFormsAndHyphens : IO Unit := do
  let output ← checkedParse_variant "pragma forms" (String.intercalate "\n" [
    "pragma solcore;",
    "pragma solcore feature,experimental,;",
    "pragma sol-core 型,;"
  ])
  assertEqual output.parseDiagnostics [] "pragma-name hyphen policy"
  assertEqual ((pragmaDecls output).map fun declaration =>
      (declaration.value.name.value,
        declaration.value.items.map (fun item => item.value))) [
    ("solcore", []),
    ("solcore", ["feature", "experimental"]),
    ("sol-core", ["型"])
  ] "empty and trailing pragma items"
  match pragmaDecls output with
  | [_, _, declaration] =>
      assertEqual (byteRange declaration.span) (54, 75) "UTF-8 pragma span"
      assertEqual (byteRange declaration.value.name.span) (61, 69)
        "hyphenated pragma-name span"
      assertEqual (declaration.value.items.map
        (fun item => byteRange item.span)) [(70, 73)] "UTF-8 pragma item span"
  | declarations => throw (IO.userError
      s!"pragma spans: unexpected declarations {reprStr declarations}")

  let invalid ← checkedParse_variant "pragma item hyphen"
    "pragma sol-core bad-item;"
  match pragmaDecls invalid with
  | [declaration] =>
      assertEqual declaration.value.name.value "sol-core"
        "pragma name remains raw"
  | declarations => throw (IO.userError
      s!"pragma item hyphen: unexpected declarations {reprStr declarations}")
  match invalid.parseDiagnostics with
  | [{ span, kind := .invalidIdentifierHyphen "bad-item" }] =>
      assertEqual (byteRange span) (16, 24) "pragma item hyphen span"
  | diagnostics => throw (IO.userError
      s!"pragma item hyphen: unexpected diagnostics {reprStr diagnostics}")

private def testMissingImportSemicolon : IO Unit := do
  let output ← checkedParse_variant "missing import semicolon"
    "import pkg\ntype Later = word;"
  match output.parsed.items with
  | [
      { span := importSpan, value := .importDecl importDeclaration, .. },
      { value := .typeAlias alias, .. }
    ] =>
      assertEqual (importShape importDeclaration) (.plain ⟨false, ["pkg"]⟩)
        "missing semicolon import shape"
      assertEqual (byteRange importSpan) (0, 10) "missing semicolon import span"
      assertEqual alias.value.name.value "Later" "following item preserved"
  | items => throw (IO.userError
      s!"missing import semicolon: unexpected items {reprStr items}")
  match output.parseDiagnostics with
  | [{ span, kind := .constraintViolation
        (.trailingSemicolonRequired .importDecl) }] =>
      assertEqual (byteRange span) (11, 15) "missing semicolon diagnostic span"
  | diagnostics => throw (IO.userError
      s!"missing import semicolon: unexpected diagnostics {reprStr diagnostics}")

/-! Run canonical import and pragma parser regressions. -/
def testSyntaxParserModules : IO Unit := do
  testImportForms
  testOperatorSelectors
  testImportSpans
  testPragmaFormsAndHyphens
  testMissingImportSemicolon

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserNamespaceImportSoundnessProperties
/-! External consumers for diagnostic-free namespace-import soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserNamespaceImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NamespaceImportTailParses
example := @NamespaceImportDeclParses
example := @NamespaceImportOrdinaryParses
example := @NamespaceImportRejects
example := @namespaceImportDeterministicOutcomeSpec
example := @contextual_ok_tokenAt
example := @importBind_success_components
example := @finishImport_success_value
example := @plainImport_success_value
example := @namespaceImport_success_value
example := @wildcardImport_success_value
example := @selectiveImport_success_value
example := @namespaceImport_success_sound_of_diagnosticFree
example := @importDecl_namespace_success_sound
example := @importDecl_namespace_success_sound_and_validFor
example := @namespaceImport_success_ordinaryOutcome_sound
example := @namespaceImport_reject_ordinaryOutcome_sound
example := @namespaceImport_ordinaryOutcome_sound
example := @namespaceImport_ordinaryOutcomeSpec

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl}
    (result : ImportInternals.namespaceImport start input =
      .ok declaration next) :
    NamespaceImportOrdinaryParses start input.declarativeRemainder declaration
      next.declarativeRemainder :=
  namespaceImport_success_ordinaryOutcome_sound start result

example (start : SourceSpan) {input rejected : State} {failure : Failure}
    (result : ImportInternals.namespaceImport start input =
      .reject failure rejected) :
    NamespaceImportRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  namespaceImport_reject_ordinaryOutcome_sound start result

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl} (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.namespaceImport start input =
      .ok declaration next) :
    NamespaceImportTailParses start input.declarativeRemainder declaration
      next.declarativeRemainder :=
  namespaceImport_success_sound_of_diagnosticFree start diagnosticFree result

example {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (namespaceShape :
      ∃ path alias, declaration.value = .namespace path alias)
    (result : importDecl input = .ok declaration next) :
    NamespaceImportDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  importDecl_namespace_success_sound diagnosticFree namespaceShape result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (namespaceShape :
      ∃ path alias, declaration.value = .namespace path alias)
    (result : importDecl input = .ok declaration next) :
    NamespaceImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_namespace_success_sound_and_validFor inputValid diagnosticFree
    namespaceShape result

end Solcore.Test.SyntaxParserNamespaceImportSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPlainImportSoundnessProperties
/-! External consumers for diagnostic-free plain-import soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPlainImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @PlainImportTailParses
example := @PlainImportDeclParses
example := @PlainImportOrdinaryParses
example := @PlainImportRejects
example := @plainImportDeterministicOutcomeSpec
example := @importTerminator_success_sound_of_diagnosticFree
example := @plainImport_success_sound_of_diagnosticFree
example := @importDecl_plain_success_sound
example := @importDecl_plain_success_sound_and_validFor
example := @plainImport_success_ordinaryOutcome_sound
example := @plainImport_reject_ordinaryOutcome_sound
example := @plainImport_ordinaryOutcome_sound
example := @plainImport_ordinaryOutcomeSpec

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl}
    (result : ImportInternals.plainImport start input =
      .ok declaration next) :
    PlainImportOrdinaryParses start input.declarativeRemainder declaration
      next.declarativeRemainder :=
  plainImport_success_ordinaryOutcome_sound start result

example (start : SourceSpan) {input rejected : State} {failure : Failure}
    (result : ImportInternals.plainImport start input =
      .reject failure rejected) :
    PlainImportRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  plainImport_reject_ordinaryOutcome_sound start result

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl} (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.plainImport start input =
      .ok declaration next) :
    PlainImportTailParses start input.declarativeRemainder declaration
      next.declarativeRemainder :=
  plainImport_success_sound_of_diagnosticFree start diagnosticFree result

example {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (plainShape : ∃ path, declaration.value = .plain path)
    (result : importDecl input = .ok declaration next) :
    PlainImportDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  importDecl_plain_success_sound diagnosticFree plainShape result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (plainShape : ∃ path, declaration.value = .plain path)
    (result : importDecl input = .ok declaration next) :
    PlainImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_plain_success_sound_and_validFor inputValid diagnosticFree
    plainShape result

end Solcore.Test.SyntaxParserPlainImportSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSelectedImportSoundnessProperties
/-! External consumers for selected-import item grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSelectedImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @SelectedAliasParses
example := @SelectedAliasOrdinaryParses
example := @SelectedAliasRejects
example := @selectedAliasDeterministicOutcomeSpec
example := @SelectedImportParses
example := @SelectedImportOrdinaryParses
example := @SelectedImportRejects
example := @selectedImportDeterministicOutcomeSpec
example := @keywordAbsentAt_of_isKeyword_eq_false
example := @selectedAlias_success_sound
example := @selectedAlias_success_sound_and_validFor
example := @selectedAlias_success_ordinaryOutcome_sound
example := @selectedAlias_reject_ordinaryOutcome_sound
example := @selectedAlias_ordinaryOutcome_sound
example := @selectedAlias_ordinaryOutcomeSpec
example := @selectedImport_success_sound
example := @selectedImport_success_sound_and_validFor
example := @selectedImport_success_ordinaryOutcome_sound
example := @selectedImport_reject_ordinaryOutcome_sound
example := @selectedImport_ordinaryOutcome_sound
example := @selectedImport_ordinaryOutcomeSpec

example {input next : State} {selection : SelectedImport}
    (inputValid : input.ValidFor)
    (result : selectedImport input = .ok selection next) :
    SelectedImportParses input.declarativeRemainder selection
        next.declarativeRemainder ∧
      selection.ValidFor input.file :=
  selectedImport_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserSelectedImportSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSelectedImportsSoundnessProperties
/-! External consumers for selected-import list grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSelectedImportsSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @SelectedImportsParses
example := @SelectedImportsOrdinaryParses
example := @SelectedImportsRejects
example := @selectedImportsDeterministicOutcomeSpec
example := @requireSelected_success_shape
example := @selectedImports_success_sound
example := @selectedImports_success_sound_and_validFor
example := @selectedImports_success_ordinaryOutcome_sound
example := @selectedImports_reject_ordinaryOutcome_sound
example := @selectedImports_ordinaryOutcome_sound
example := @selectedImports_ordinaryOutcomeSpec

example {input next : State}
    {selection : NonemptyDelimitedList SelectedImport}
    (inputValid : input.ValidFor)
    (result : ImportInternals.selectedImports input = .ok selection next) :
    SelectedImportsParses input.declarativeRemainder selection
        next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor SelectedImport.ValidFor input.file
        selection :=
  selectedImports_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserSelectedImportsSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSelectiveImportSoundnessProperties
/-! External consumers for complete selected-import grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSelectiveImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @SelectiveImportTailParses
example := @SelectiveImportDeclParses
example := @SelectiveImportOrdinaryParses
example := @SelectiveImportRejects
example := @selectiveImportDeterministicOutcomeSpec
example := @selectiveImport_success_sound_of_diagnosticFree
example := @importDecl_selected_success_sound
example := @importDecl_selected_success_sound_and_validFor
example := @selectiveImport_success_ordinaryOutcome_sound
example := @selectiveImport_reject_ordinaryOutcome_sound
example := @selectiveImport_ordinaryOutcome_sound
example := @selectiveImport_ordinaryOutcomeSpec

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl}
    (result : ImportInternals.selectiveImport start input =
      .ok declaration next) :
    SelectiveImportOrdinaryParses start input.declarativeRemainder declaration
      next.declarativeRemainder :=
  selectiveImport_success_ordinaryOutcome_sound start result

example (start : SourceSpan) {input rejected : State} {failure : Failure}
    (result : ImportInternals.selectiveImport start input =
      .reject failure rejected) :
    SelectiveImportRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  selectiveImport_reject_ordinaryOutcome_sound start result

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.selectiveImport start input =
      .ok declaration next) :
    SelectiveImportTailParses start input.declarativeRemainder declaration
      next.declarativeRemainder :=
  selectiveImport_success_sound_of_diagnosticFree start diagnosticFree result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (selectedShape : ∃ selection path hidden,
      declaration.value = .selected selection path hidden)
    (result : importDecl input = .ok declaration next) :
    SelectiveImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_selected_success_sound_and_validFor inputValid diagnosticFree
    selectedShape result

end Solcore.Test.SyntaxParserSelectiveImportSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSourceFileCompletenessProperties
/-! Independent forward and reverse consumers of complete public syntax parsing. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSourceFileCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @FileInternals.sourceFile_ordinary_iff_exists_ok_of_topItem
example := @FileInternals.sourceFile_ordinary_iff_exists_ok
example := @parseLexed_exists_ok_iff_publicSourceFileOrdinary_of_topItem
example := @parseLexed_exists_ok_iff_publicSourceFileOrdinary
example := @parse_exists_ok_iff_publicSourceFileOrdinary_of_topItem
example := @parse_exists_ok_iff_publicSourceFileOrdinary

example (comments : List Comment) {input : State} (inputValid : input.ValidFor)
    {parsed : ParsedFile} {afterParsed : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsed afterParsed) :
    ∃ output, sourceFile comments input = .ok parsed output ∧
      output.declarativeRemainder = afterParsed :=
  (FileInternals.sourceFile_ordinary_iff_exists_ok comments inputValid).mp expected

example (comments : List Comment) {input output : State} (inputValid : input.ValidFor)
    {parsed : ParsedFile}
    (result : sourceFile comments input = .ok parsed output) :
    DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsed output.declarativeRemainder :=
  (FileInternals.sourceFile_ordinary_iff_exists_ok comments inputValid).mpr
    ⟨output, result, rfl⟩

example (file : SourceFile) (lexed : LexedFile) (parsed : ParsedFile)
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (expected : DeclarativeGrammar.PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ∃ output, parseLexed file lexed = .ok output ∧ output.parsed = parsed :=
  (parseLexed_exists_ok_iff_publicSourceFileOrdinary file lexed parsed).mpr
    ⟨accepted, expected⟩

example (file : SourceFile) (lexed : LexedFile) {output : ParseOutput}
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
      DeclarativeGrammar.PublicSourceFileOrdinaryParses file
        lexed.tokens lexed.comments output.parsed :=
  (parseLexed_exists_ok_iff_publicSourceFileOrdinary file lexed output.parsed).mp
    ⟨output, result, rfl⟩

example (file : SourceFile) (lexed : LexedFile) (parsed : ParsedFile)
    (lexing : Lexer.lex file = .ok lexed)
    (expected : DeclarativeGrammar.PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ∃ output, parse file = .ok output ∧ output.parsed = parsed :=
  (parse_exists_ok_iff_publicSourceFileOrdinary file parsed).mpr
    ⟨lexed, lexing, expected⟩

example (file : SourceFile) {output : ParseOutput}
    (result : parse file = .ok output) :
    ∃ lexed, Lexer.lex file = .ok lexed ∧
      DeclarativeGrammar.PublicSourceFileOrdinaryParses file
        lexed.tokens lexed.comments output.parsed :=
  (parse_exists_ok_iff_publicSourceFileOrdinary file output.parsed).mp
    ⟨output, result, rfl⟩

end Solcore.Test.SyntaxParserSourceFileCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSourceFileExactnessProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTopItemRecoveryExactnessProperties
/-! Standalone consumers of exact top-item recovery, without clean-input premises. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTopItemRecoveryExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @DeclarativeGrammar.TopItemRecoveryScanParses.result_unique
example := @recoverTopItem_success_result_unique
example := @recoverTopItem_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.TopItemRecoveryParses DeclarativeGrammar.TopItemRecoveryRejects :=
  recoverTopItem_exactOutcomeSpec

example {input output : State} {actual expected : TopItem}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : recoverTopItem input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  recoverTopItem_exactOutcomeSpec.successResultUnique
    (recoverTopItem_success_ordinaryOutcome_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : recoverTopItem input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.TopItemRecoveryRejects
      input.declarativeRemainder expected) : output.declarativeRemainder = expected :=
  recoverTopItem_exactOutcomeSpec.rejectOutputUnique
    (recoverTopItem_reject_ordinaryOutcome_sound result) expectedRejected

end Solcore.Test.SyntaxParserTopItemRecoveryExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTopItemRecoveryTraceProperties
/-! Consumers of exact recovery traces, including nonempty prior diagnostics. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTopItemRecoveryTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @finishRecoveredTopItem_success_diagnosticsRev_eq
example := @recoverTopItemAux_success_diagnosticsRev_eq
example := @recoverTopItem_success_diagnosticsRev_eq
example := @finishRecoveredTopItem_success_diagnostics_eq
example := @recoverTopItemAux_success_diagnostics_eq
example := @recoverTopItem_reject_diagnosticsRev_eq
example := @recoverTopItem_ordinary_success_iff_with_trace
example := @recoverTopItem_ordinary_reject_iff_with_trace

example {input output : State} {item : TopItem}
    (result : recoverTopItem input = .ok item output) :
    output.diagnostics = input.diagnostics ++
      [{ span := item.span, kind := .recovered .topItem }] :=
  recoverTopItem_success_diagnostics_eq result

example {input output : State} {failure : Failure}
    (result : recoverTopItem input = .reject failure output) :
    output.diagnostics = input.diagnostics :=
  recoverTopItem_reject_diagnostics_eq result

example {input : State} {item : TopItem}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan}
    (parsed : DeclarativeGrammar.TopItemRecoveryTraceParses
      input.declarativeRemainder item remainder trace) :
    ∃ output, recoverTopItem input = .ok item output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ topItemRecoveryDiagnostics trace :=
  recoverTopItem_trace_success_iff.mp parsed

example {input output : State} {item : TopItem}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan}
    (result : recoverTopItem input = .ok item output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++
      topItemRecoveryDiagnostics trace) :
    DeclarativeGrammar.TopItemRecoveryTraceParses
      input.declarativeRemainder item remainder trace :=
  recoverTopItem_trace_success_iff.mpr ⟨output, result, after, diagnostics⟩

example {input : State} {remainder : DeclarativeGrammar.Remainder}
    {trace : List SourceSpan}
    (rejected : DeclarativeGrammar.TopItemRecoveryTraceRejects
      input.declarativeRemainder remainder trace) :
    ∃ failure output, recoverTopItem input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ topItemRecoveryDiagnostics trace :=
  recoverTopItem_trace_reject_iff.mp rejected

example {input output : State} {failure : Failure}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan}
    (result : recoverTopItem input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++
      topItemRecoveryDiagnostics trace) :
    DeclarativeGrammar.TopItemRecoveryTraceRejects
      input.declarativeRemainder remainder trace :=
  recoverTopItem_trace_reject_iff.mpr
    ⟨failure, output, result, after, diagnostics⟩

example {input output : State} {actual expected : TopItem}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan}
    (result : recoverTopItem input = .ok actual output)
    (parsed : DeclarativeGrammar.TopItemRecoveryTraceParses
      input.declarativeRemainder expected remainder trace) :
    actual = expected ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ topItemRecoveryDiagnostics trace := by
  rcases DeclarativeGrammar.topItemRecoveryTraceParses_iff.mp parsed with
    ⟨ordinary, rfl⟩
  rcases recoverTopItem_exactOutcomeSpec.successResultUnique
      (recoverTopItem_success_ordinaryOutcome_sound result) ordinary with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, recoverTopItem_success_diagnostics_eq result⟩

example (trace : List SourceSpan) :
    (topItemRecoveryDiagnostics trace).map ParseDiagnostic.span = trace :=
  topItemRecoveryDiagnostics_spans trace

example {left right : List SourceSpan}
    (equal : topItemRecoveryDiagnostics left = topItemRecoveryDiagnostics right) :
    left = right :=
  topItemRecoveryDiagnostics_injective equal

end Solcore.Test.SyntaxParserTopItemRecoveryTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserWildcardImportNoHidingSoundnessProperties
/-! External consumers for wildcard-import no-hiding soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserWildcardImportNoHidingSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @WildcardImportNoHidingTailParses
example := @WildcardImportNoHidingDeclParses
example := @optionalHiding_none_success_state
example := @wildcardImport_noHiding_success_sound_of_diagnosticFree
example := @importDecl_wildcardNoHiding_success_sound
example := @importDecl_wildcardNoHiding_success_sound_and_validFor

example {input next : State}
    (result : ImportInternals.optionalHiding input = .ok none next) :
    next = input :=
  optionalHiding_none_success_state result

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl} (diagnosticFree : next.diagnosticsRev = [])
    (noHidingShape :
      ∃ path, declaration.value = .wildcard path none)
    (result : ImportInternals.wildcardImport start input =
      .ok declaration next) :
    WildcardImportNoHidingTailParses start input.declarativeRemainder
      declaration next.declarativeRemainder :=
  wildcardImport_noHiding_success_sound_of_diagnosticFree start
    diagnosticFree noHidingShape result

example {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (noHidingShape :
      ∃ path, declaration.value = .wildcard path none)
    (result : importDecl input = .ok declaration next) :
    WildcardImportNoHidingDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  importDecl_wildcardNoHiding_success_sound diagnosticFree noHidingShape
    result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (noHidingShape :
      ∃ path, declaration.value = .wildcard path none)
    (result : importDecl input = .ok declaration next) :
    WildcardImportNoHidingDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_wildcardNoHiding_success_sound_and_validFor inputValid
    diagnosticFree noHidingShape result

end Solcore.Test.SyntaxParserWildcardImportNoHidingSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserWildcardImportSoundnessProperties
/-! External consumers for complete wildcard-import grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserWildcardImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @WildcardImportTailParses
example := @WildcardImportDeclParses
example := @WildcardImportOrdinaryParses
example := @WildcardImportRejects
example := @wildcardImportDeterministicOutcomeSpec
example := @wildcardImport_success_sound_of_diagnosticFree
example := @importDecl_wildcard_success_sound
example := @importDecl_wildcardWithHiding_success_sound
example := @importDecl_wildcard_success_sound_and_validFor
example := @importDecl_wildcardWithHiding_success_sound_and_validFor
example := @wildcardImport_success_ordinaryOutcome_sound
example := @wildcardImport_reject_ordinaryOutcome_sound
example := @wildcardImport_ordinaryOutcome_sound
example := @wildcardImport_ordinaryOutcomeSpec

example (start : SourceSpan) {input next : State}
    {declaration : ImportDecl}
    (result : ImportInternals.wildcardImport start input =
      .ok declaration next) :
    WildcardImportOrdinaryParses start input.declarativeRemainder declaration
      next.declarativeRemainder :=
  wildcardImport_success_ordinaryOutcome_sound start result

example (start : SourceSpan) {input rejected : State} {failure : Failure}
    (result : ImportInternals.wildcardImport start input =
      .reject failure rejected) :
    WildcardImportRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  wildcardImport_reject_ordinaryOutcome_sound start result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (wildcardShape : ∃ path hidden,
      declaration.value = .wildcard path hidden)
    (result : importDecl input = .ok declaration next) :
    WildcardImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_wildcard_success_sound_and_validFor inputValid diagnosticFree
    wildcardShape result

example {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (withHidingShape : ∃ path clause,
      declaration.value = .wildcard path (some clause))
    (result : importDecl input = .ok declaration next) :
    WildcardImportDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  importDecl_wildcardWithHiding_success_sound diagnosticFree withHidingShape
    result

end Solcore.Test.SyntaxParserWildcardImportSoundnessProperties
end
