import Solcore.Syntax.Parser.TypeAliasSoundnessProperties

/-! External consumers for transparent type-alias grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeAliasSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalTypeAliasParametersParses
example := @TypeAliasDeclParses
example := @parseTypeAliasParameters_success_sound
example := @TypeAliasInternals.parseAliasValue_success_sound_of_diagnosticFree
example := @typeAlias_success_sound
example := @typeAlias_success_sound_and_validFor

example {input next : State} {declaration : TypeAliasDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    TypeAliasDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  typeAlias_success_sound diagnosticFree result

example {input next : State} {declaration : TypeAliasDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    TypeAliasDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  typeAlias_success_sound_and_validFor inputValid diagnosticFree result

end Solcore.Test.SyntaxParserTypeAliasSoundnessProperties
