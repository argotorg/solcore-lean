import Solcore.Syntax.Parser.SelectiveImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectiveImportSoundnessProperties

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
