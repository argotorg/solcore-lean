import Solcore.Syntax.Parser.ImportDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImportDeclSoundnessProperties
import Solcore.Test.SyntaxParserImportExactnessProperties

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
example := @ImportDeclOrdinaryParses
example := @ImportDeclRejects
example := @importDeclDeterministicOutcomeSpec
example := @importDecl_success_sound
example := @importDecl_success_sound_and_validFor
example := @importDecl_success_ordinaryOutcome_sound
example := @importDecl_reject_ordinaryOutcome_sound
example := @importDecl_ordinaryOutcome_sound
example := @importDecl_ordinaryOutcomeSpec

example {input next : State} {declaration : ImportDecl}
    (result : importDecl input = .ok declaration next) :
    ImportDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  importDecl_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : importDecl input = .reject failure rejected) :
    ImportDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  importDecl_reject_ordinaryOutcome_sound result

example {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : importDecl input = .ok declaration next) :
    ImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  importDecl_success_sound_and_validFor inputValid diagnosticFree result

end Solcore.Test.SyntaxParserImportDeclSoundnessProperties
