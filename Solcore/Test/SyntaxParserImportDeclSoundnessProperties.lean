import Solcore.Syntax.Parser.ImportDeclSoundnessProperties

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
example := @importDecl_success_sound
example := @importDecl_success_sound_and_validFor

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : importDecl input = .ok declaration next) :
    ImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_success_sound_and_validFor inputValid diagnosticFree result

end Solcore.Test.SyntaxParserImportDeclSoundnessProperties
