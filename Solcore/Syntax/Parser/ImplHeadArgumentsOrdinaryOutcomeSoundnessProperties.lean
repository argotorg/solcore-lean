import Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeProperties
import Solcore.Syntax.Parser.ImplHeadArgumentsOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImplHeadArgumentsOrdinarySuccessSoundnessProperties

/-! Complete broad ordinary outcomes for implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- Package the executable delimited/refinement success and the only ordinary
rejection stage. -/
theorem implHeadArguments_ordinaryOutcome_sound :
    (∀ {input afterValues output : State}
      {values : DelimitedList TypeExpr}
      {arguments : NonemptyDelimitedList TypeExpr},
      delimited .less .greater false typeExpr .typeExpr .topLevel input =
          .ok values afterValues →
        requireImplArguments values afterValues = .ok arguments output →
          DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
            input.declarativeRemainder arguments
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      delimited .less .greater false typeExpr .typeExpr .topLevel input =
          .reject failure rejected →
        DeclarativeGrammar.ImplHeadArgumentsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨implHeadArguments_success_ordinaryOutcome_sound,
    implHeadArguments_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad implementation head argument
outcomes. -/
theorem implHeadArguments_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
      DeclarativeGrammar.ImplHeadArgumentsRejects :=
  DeclarativeGrammar.implHeadArgumentsDeterministicOutcomeSpec

end Solcore.Syntax.Parser.ImplInternals
