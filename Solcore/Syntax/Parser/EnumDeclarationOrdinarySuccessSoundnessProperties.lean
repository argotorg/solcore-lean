import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.EnumDeclSoundnessProperties

/-! Ordinary-success bridge for complete enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful enum declaration follows the exact ordinary grammar for
the supplied, non-consuming derive attribute. -/
theorem enumDecl_success_ordinaryOutcome_sound
    (deriveAttribute : Option DeriveAttribute)
    {input output : State} {declaration : EnumDecl}
    (result : enumDecl deriveAttribute input = .ok declaration output) :
    DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute
      input.declarativeRemainder declaration output.declarativeRemainder :=
  enumDecl_success_sound deriveAttribute result

end Solcore.Syntax.Parser
