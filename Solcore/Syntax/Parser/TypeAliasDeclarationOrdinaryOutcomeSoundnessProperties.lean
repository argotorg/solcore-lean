import Solcore.Syntax.DeclarativeTypeAliasDeclarationExactnessProperties
import Solcore.Syntax.Parser.TypeAliasDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable type-alias success and rejection. -/
theorem typeAlias_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : TypeAliasDecl},
      typeAlias input = .ok declaration output →
        DeclarativeGrammar.TypeAliasDeclOrdinaryParses
          input.declarativeRemainder declaration
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      typeAlias input = .reject failure rejected →
        DeclarativeGrammar.TypeAliasDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨typeAlias_success_ordinaryOutcome_sound,
    typeAlias_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic broad type-alias outcomes. -/
theorem typeAlias_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      DeclarativeGrammar.TypeAliasDeclRejects :=
  DeclarativeGrammar.typeAliasDeclDeterministicOutcomeSpec

/-- Re-export full type-alias AST and rejection-endpoint functionality. -/
theorem typeAlias_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      DeclarativeGrammar.TypeAliasDeclRejects :=
  DeclarativeGrammar.typeAliasDeclExactOutcomeSpec

/-- Two successful executable reflections have the same declaration AST and
final declarative remainder. -/
theorem typeAlias_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : TypeAliasDecl}
    (leftResult : typeAlias input = .ok left leftOutput)
    (rightResult : typeAlias input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasDeclOrdinaryParses.result_unique
    (typeAlias_success_ordinaryOutcome_sound leftResult)
    (typeAlias_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same first failing
declarative endpoint. -/
theorem typeAlias_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : typeAlias input = .reject leftFailure leftOutput)
    (rightResult : typeAlias input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasDeclRejects.output_unique
    (typeAlias_reject_ordinaryOutcome_sound leftResult)
    (typeAlias_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
