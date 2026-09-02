import Solcore.Syntax.Parser.EnumDeclarationOrdinaryOutcomeSoundnessProperties

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
example := @OptionalEnumConstructorFieldsOrdinaryParses
example := @OptionalEnumConstructorFieldsRejects
example := @optionalEnumConstructorFieldsDeterministicOutcomeSpec
example := @EnumConstructorOrdinaryParses
example := @EnumConstructorRejects
example := @enumConstructorDeterministicOutcomeSpec
example := @EnumBodyOrdinaryParses
example := @EnumBodyOrdinaryOutcomeParses
example := @EnumBodyRejects
example := @enumBodyDeterministicOutcomeSpec
example := @EnumDeclOrdinaryParses
example := @EnumDeclRejects
example := @enumDeclDeterministicOutcomeSpec
example := @EnumInternals.enumConstructorFields_success_sound
example := @EnumInternals.enumConstructor_success_sound
example := @EnumInternals.enumBody_success_sound
example := @enumDecl_success_sound
example := @enumDecl_success_sound_and_validFor
example := @enumDecl_none_success_sound_and_validFor
example := @EnumInternals.enumConstructorFields_success_ordinaryOutcome_sound
example := @EnumInternals.enumConstructorFields_reject_ordinaryOutcome_sound
example := @EnumInternals.enumConstructorFields_ordinaryOutcome_sound
example := @EnumInternals.enumConstructorFields_ordinaryOutcomeSpec
example := @EnumInternals.enumConstructor_success_ordinaryOutcome_sound
example := @EnumInternals.enumConstructor_reject_ordinaryOutcome_sound
example := @EnumInternals.enumConstructor_ordinaryOutcome_sound
example := @EnumInternals.enumConstructor_ordinaryOutcomeSpec
example := @EnumInternals.enumBody_success_ordinaryOutcome_sound
example := @EnumInternals.enumBody_reject_ordinaryOutcome_sound
example := @EnumInternals.enumBody_ordinaryOutcome_sound
example := @EnumInternals.enumBody_ordinaryOutcomeSpec
example := @enumDecl_success_ordinaryOutcome_sound
example := @enumDecl_reject_ordinaryOutcome_sound
example := @enumDecl_ordinaryOutcome_sound
example := @enumDecl_ordinaryOutcomeSpec

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

example {input rejected : State} {failure : Failure}
    (result : enumDecl none input = .reject failure rejected) :
    EnumDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  enumDecl_reject_ordinaryOutcome_sound none result

end Solcore.Test.SyntaxParserEnumSoundnessProperties
