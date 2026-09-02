import Solcore.Syntax.DeclarativeTraitDeclarationExactnessProperties
import Solcore.Syntax.Parser.TraitBodyOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TraitDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TraitDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable trait-declaration success and exact five-stage
rejection. -/
theorem traitDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : TraitDecl},
      traitDecl input = .ok declaration output →
        DeclarativeGrammar.TraitDeclOrdinaryParses input.declarativeRemainder
          declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      traitDecl input = .reject failure rejected →
        DeclarativeGrammar.TraitDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨traitDecl_success_ordinaryOutcome_sound,
    traitDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad trait-declaration outcomes. -/
theorem traitDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TraitDeclOrdinaryParses
      DeclarativeGrammar.TraitDeclRejects :=
  DeclarativeGrammar.traitDeclDeterministicOutcomeSpec

/-- Re-export unconditional exact trait-declaration outcomes. -/
theorem traitDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TraitDeclOrdinaryParses
      DeclarativeGrammar.TraitDeclRejects :=
  DeclarativeGrammar.traitDeclExactOutcomeSpec

/-- Two successful trait declarations have the same AST and declarative
remainder. -/
theorem traitDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : TraitDecl}
    (leftResult : traitDecl input = .ok left leftOutput)
    (rightResult : traitDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitDeclOrdinaryParses.result_unique
    (traitDecl_success_ordinaryOutcome_sound leftResult)
    (traitDecl_success_ordinaryOutcome_sound rightResult)

/-- Two trait-declaration rejections have the same declarative endpoint. -/
theorem traitDecl_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : traitDecl input = .reject leftFailure leftOutput)
    (rightResult : traitDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitDeclRejects.output_unique
    (traitDecl_reject_ordinaryOutcome_sound leftResult)
    (traitDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
