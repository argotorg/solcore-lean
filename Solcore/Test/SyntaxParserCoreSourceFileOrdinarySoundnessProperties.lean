import Solcore.Syntax.Parser.CorePublicParseOrdinarySoundnessProperties

/-! External consumers for concrete ordinary Core-file grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreSourceFileOrdinarySoundnessProperties

open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @CoreTopItemOrdinaryParses
example := @CoreSourceFileOrdinaryParses
example := @CoreSourceFileOrdinaryParsesFromStart
example := @CoreSourceFileOrdinaryParses.output_atEnd

example := @FileInternals.sourceFile_success_coreOrdinary_sound
example := @FileInternals.sourceFile_success_coreOrdinary_sound_and_validFor
example := @parseLexed_ok_coreOrdinary_sound
example := @parseLexed_ok_coreOrdinary_sound_and_validFor
example := @parse_ok_coreOrdinary_sound
example := @parse_ok_coreOrdinary_sound_and_validFor

end Solcore.Test.SyntaxParserCoreSourceFileOrdinarySoundnessProperties
