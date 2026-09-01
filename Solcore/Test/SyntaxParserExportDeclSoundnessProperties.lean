import Solcore.Syntax.Parser.ExportDeclSoundnessProperties

/-! External consumers for complete export-declaration grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportDeclSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @FinishExportParses
example := @LocalExportTailParses
example := @ItemsFromExportTailParses
example := @ModuleAsExportTailParses
example := @ModuleExportTailParses
example := @PathExportTailParses
example := @LocalExportDeclParses
example := @ItemsFromExportDeclParses
example := @ModuleAsExportDeclParses
example := @ModuleExportDeclParses
example := @ExportDeclParses

example := @finishExport_success_sound
example := @localExport_success_sound
example := @pathExport_success_sound
example := @exportDecl_success_sound
example := @exportDecl_success_sound_and_validFor

example {input next : State} {declaration : ExportDecl}
    (inputValid : input.ValidFor)
    (result : exportDecl input = .ok declaration next) :
    ExportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  exportDecl_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserExportDeclSoundnessProperties
