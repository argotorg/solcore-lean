import Solcore.Syntax.Parser.DeriveTargetSoundnessProperties

/-! External consumers for derive-target grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveTargetSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ReservedDeriveTargetKeyword
example := @DeriveComponentParses
example := @DeriveTargetTailParses
example := @DeriveTargetParses
example := @deriveComponent_success_sound
example := @deriveTarget_success_sound
example := @deriveTarget_success_sound_and_validFor

example {input next : State} {target : DeriveTarget}
    (result : deriveTarget input = .ok target next) :
    DeriveTargetParses input.declarativeRemainder target
      next.declarativeRemainder :=
  deriveTarget_success_sound result

example {input next : State} {target : DeriveTarget}
    (inputValid : input.ValidFor)
    (result : deriveTarget input = .ok target next) :
    DeriveTargetParses input.declarativeRemainder target
        next.declarativeRemainder ∧
      target.ValidFor input.file :=
  deriveTarget_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserDeriveTargetSoundnessProperties
