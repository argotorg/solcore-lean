import Solcore.Syntax.Parser.PlainImportSoundnessProperties

/-! External consumers for diagnostic-free plain-import soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPlainImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @PlainImportTailParses
example := @PlainImportDeclParses
example := @importTerminator_success_sound_of_diagnosticFree
example := @plainImport_success_sound_of_diagnosticFree
example := @importDecl_plain_success_sound
example := @importDecl_plain_success_sound_and_validFor

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
