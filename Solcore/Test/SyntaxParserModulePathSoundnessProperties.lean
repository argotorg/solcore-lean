import Solcore.Syntax.Parser.ModulePathSoundnessProperties

/-! External consumers for canonical module-path success soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserModulePathSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ModulePathParses
example := @modulePath_success_sound
example := @modulePath_success_sound_and_validFor

example (context : ParseContext) {input next : State} {path : ModulePath}
    (result : modulePath context input = .ok path next) :
    ModulePathParses input.declarativeRemainder path
      next.declarativeRemainder :=
  modulePath_success_sound context result

example (context : ParseContext) {input next : State} {path : ModulePath}
    (inputValid : input.ValidFor)
    (result : modulePath context input = .ok path next) :
    ModulePathParses input.declarativeRemainder path
        next.declarativeRemainder ∧
      path.ValidFor input.file :=
  modulePath_success_sound_and_validFor context inputValid result

end Solcore.Test.SyntaxParserModulePathSoundnessProperties
