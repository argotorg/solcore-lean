import Solcore.Syntax.Parser.ExportNameSoundnessProperties

/-! External consumers for export-name grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportNameSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalConstructorSelectionParses
example := @ExportNameParses
example := @exportName_success_sound
example := @exportName_success_sound_and_validFor

example {input next : State} {name : ExportName}
    (inputValid : input.ValidFor)
    (result : ExportInternals.exportName input = .ok name next) :
    ExportNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      name.ValidFor input.file :=
  exportName_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserExportNameSoundnessProperties
