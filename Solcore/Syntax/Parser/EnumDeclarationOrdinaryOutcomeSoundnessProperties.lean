import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeProperties
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

end Solcore.Syntax.Parser
