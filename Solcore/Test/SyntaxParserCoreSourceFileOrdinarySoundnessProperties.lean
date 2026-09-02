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
example := @FileInternals.sourceFile_success_coreOrdinary_sound_toEnd
example := @FileInternals.sourceFile_success_coreOrdinary_sound_and_validFor
example := @parseLexed_ok_coreOrdinary_sound
example := @parseLexed_ok_coreOrdinary_sound_and_validFor
example := @parse_ok_coreOrdinary_sound
example := @parse_ok_coreOrdinary_sound_and_validFor

example {file : Solcore.Syntax.SourceFile}
    {tokens : List Solcore.Syntax.Token}
    {comments : List Solcore.Syntax.Comment}
    {parsedFile : Solcore.Syntax.ParsedFile}
    (parsed : CoreSourceFileOrdinaryParsesFromStart file tokens comments
      parsedFile) :
    CoreSourceFileOrdinaryParses file comments {
      tokens := tokens.toArray
      endIndex := tokens.length
      cursor := 0
    } parsedFile {
      tokens := tokens.toArray
      endIndex := tokens.length
      cursor := tokens.length
    } :=
  parsed

example {file : Solcore.Syntax.SourceFile}
    {output : Solcore.Syntax.ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parse file = .ok output) :
    CoreSourceFileOrdinaryParses file output.parsed.comments {
      tokens := output.tokens.toArray
      endIndex := output.tokens.length
      cursor := 0
    } output.parsed {
      tokens := output.tokens.toArray
      endIndex := output.tokens.length
      cursor := output.tokens.length
    } :=
  parse_ok_coreOrdinary_sound diagnosticFree result

end Solcore.Test.SyntaxParserCoreSourceFileOrdinarySoundnessProperties
