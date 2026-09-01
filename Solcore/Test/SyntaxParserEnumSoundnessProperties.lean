import Solcore.Syntax.Parser.EnumDeclSoundnessProperties

/-! External consumers for algebraic-enum grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEnumSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalEnumConstructorFieldsParses
example := @EnumConstructorParses
example := @EnumBodyParses
example := @EnumDeclParses
example := @EnumInternals.enumConstructorFields_success_sound
example := @EnumInternals.enumConstructor_success_sound
example := @EnumInternals.enumBody_success_sound
example := @enumDecl_success_sound
example := @enumDecl_success_sound_and_validFor
example := @enumDecl_none_success_sound_and_validFor

example {input next : State} {declaration : EnumDecl}
    (result : enumDecl none input = .ok declaration next) :
    EnumDeclParses none input.declarativeRemainder declaration
      next.declarativeRemainder :=
  enumDecl_success_sound none result

example {input next : State} {declaration : EnumDecl}
    (inputValid : input.ValidFor)
    (result : enumDecl none input = .ok declaration next) :
    EnumDeclParses none input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  enumDecl_none_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserEnumSoundnessProperties
