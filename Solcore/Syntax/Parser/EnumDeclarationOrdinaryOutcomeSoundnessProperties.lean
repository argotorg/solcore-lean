import Solcore.Syntax.DeclarativeEnumDeclarationExactnessProperties
import Solcore.Syntax.Parser.EnumDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.EnumDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package enum-declaration success and exact four-stage rejection. -/
theorem enumDecl_ordinaryOutcome_sound
    (deriveAttribute : Option DeriveAttribute) :
    (∀ {input output : State} {declaration : EnumDecl},
      enumDecl deriveAttribute input = .ok declaration output →
        DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      enumDecl deriveAttribute input = .reject failure rejected →
        DeclarativeGrammar.EnumDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨enumDecl_success_ordinaryOutcome_sound deriveAttribute,
    enumDecl_reject_ordinaryOutcome_sound deriveAttribute⟩

/-- Re-export deterministic and exclusive outcomes for one supplied derive
attribute. -/
theorem enumDecl_ordinaryOutcomeSpec
    (deriveAttribute : Option DeriveAttribute) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute)
      DeclarativeGrammar.EnumDeclRejects :=
  DeclarativeGrammar.enumDeclDeterministicOutcomeSpec deriveAttribute

/-- Re-export exact enum-declaration outcomes at any fixed derive attribute. -/
theorem enumDecl_exactOutcomeSpec
    (deriveAttribute : Option DeriveAttribute) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute)
      DeclarativeGrammar.EnumDeclRejects :=
  DeclarativeGrammar.enumDeclExactOutcomeSpec deriveAttribute

/-- At any fixed derive attribute, successful enum declarations fix their AST
and declarative remainder. -/
theorem enumDecl_success_result_unique
    (deriveAttribute : Option DeriveAttribute)
    {input leftOutput rightOutput : State} {left right : EnumDecl}
    (leftResult : enumDecl deriveAttribute input = .ok left leftOutput)
    (rightResult : enumDecl deriveAttribute input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumDeclOrdinaryParses.result_unique deriveAttribute
    (enumDecl_success_ordinaryOutcome_sound deriveAttribute leftResult)
    (enumDecl_success_ordinaryOutcome_sound deriveAttribute rightResult)

/-- At any fixed derive attribute, enum-declaration rejections have one
declarative endpoint. -/
theorem enumDecl_reject_output_unique
    (deriveAttribute : Option DeriveAttribute)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : enumDecl deriveAttribute input = .reject leftFailure leftOutput)
    (rightResult : enumDecl deriveAttribute input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumDeclRejects.output_unique
    (enumDecl_reject_ordinaryOutcome_sound deriveAttribute leftResult)
    (enumDecl_reject_ordinaryOutcome_sound deriveAttribute rightResult)

end Solcore.Syntax.Parser
