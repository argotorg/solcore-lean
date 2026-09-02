import Solcore.Syntax.Parser.ExportDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.LocalExportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PathExportOrdinaryOutcomeSoundnessProperties

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
