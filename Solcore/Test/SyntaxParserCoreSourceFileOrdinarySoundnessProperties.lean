import Solcore.Syntax.Parser.CoreSourceFileOrdinarySoundnessProperties

/-! External consumers for concrete ordinary Core-file grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreSourceFileOrdinarySoundnessProperties

open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @CoreTopItemOrdinaryParses
example := @CoreSourceFileOrdinaryParses
example := @CoreSourceFileOrdinaryParses.output_atEnd

example := @FileInternals.sourceFile_success_coreOrdinary_sound
example := @FileInternals.sourceFile_success_coreOrdinary_sound_and_validFor

end Solcore.Test.SyntaxParserCoreSourceFileOrdinarySoundnessProperties
