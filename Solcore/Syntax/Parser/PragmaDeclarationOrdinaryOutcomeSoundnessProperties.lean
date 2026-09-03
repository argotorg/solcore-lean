import Solcore.Syntax.DeclarativePragmaExactnessProperties
import Solcore.Syntax.Parser.PragmaDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.PragmaDeclarationOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.PragmaSoundnessProperties

/-! Complete executable ordinary outcomes for pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable pragma success and rejection. -/
theorem pragmaDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : PragmaDecl},
      pragmaDecl input = .ok declaration output →
        DeclarativeGrammar.PragmaDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      pragmaDecl input = .reject failure rejected →
        DeclarativeGrammar.PragmaDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨pragmaDecl_success_ordinaryOutcome_sound,
    pragmaDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive parser-independent pragma outcomes. -/
theorem pragmaDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PragmaDeclOrdinaryParses
      DeclarativeGrammar.PragmaDeclRejects :=
  DeclarativeGrammar.pragmaDeclDeterministicOutcomeSpec

/-- Re-export unconditional exact ordinary pragma-declaration outcomes. -/
theorem pragmaDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PragmaDeclOrdinaryParses
      DeclarativeGrammar.PragmaDeclRejects :=
  DeclarativeGrammar.pragmaDeclExactOutcomeSpec

/-- Two successful pragma declarations have the same AST and declarative
remainder. -/
theorem pragmaDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : PragmaDecl}
    (leftResult : pragmaDecl input = .ok left leftOutput)
    (rightResult : pragmaDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pragmaDecl_exactOutcomeSpec.successResultUnique
    (pragmaDecl_success_ordinaryOutcome_sound leftResult)
    (pragmaDecl_success_ordinaryOutcome_sound rightResult)

/-- Two rejected pragma declarations have the same declarative endpoint;
no failure diagnostic payload equality is asserted. -/
theorem pragmaDecl_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : pragmaDecl input = .reject leftFailure leftOutput)
    (rightResult : pragmaDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pragmaDecl_exactOutcomeSpec.rejectOutputUnique
    (pragmaDecl_reject_ordinaryOutcome_sound leftResult)
    (pragmaDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
