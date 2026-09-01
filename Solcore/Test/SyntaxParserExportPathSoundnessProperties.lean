import Solcore.Syntax.Parser.ExportPathSoundnessProperties

/-! External consumers for maximal export-path grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportPathSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @DotIdentifierAbsentAt
example := @ExportPathTailParses
example := @ExportPathParses
example := @exportPath_success_sound
example := @exportPath_success_sound_and_validFor

example {input next : State} {path : QualifiedName}
    (inputValid : input.ValidFor)
    (result : ExportInternals.exportPath input = .ok path next) :
    ExportPathParses input.declarativeRemainder path
        next.declarativeRemainder ∧
      path.ValidFor input.file :=
  exportPath_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserExportPathSoundnessProperties
