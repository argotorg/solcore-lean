import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionParameterPublicOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionParametersOutcomeGrammar

/-! Deterministic exact outcomes for recovery-aware function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A successful function-parameter list has one final remainder. -/
theorem FunctionParametersOrdinaryParses.output_unique
    {input : Remainder}
    {left right : DelimitedList Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParametersOrdinaryParses input left afterLeft)
    (rightParsed : FunctionParametersOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold FunctionParametersOrdinaryParses at leftParsed rightParsed
  exact TrailingDelimitedListParses.output_unique
    (opening := .leftParen) (closing := .rightParen)
    (elementParses := FunctionParameterOrdinaryParses
      TypeExprOrdinaryParses TypeExprRejects)
    (FunctionParameterOrdinaryParses.output_unique
      typeExprDeterministicOutcomeSpec) leftParsed rightParsed

/-- Exact list rejection excludes every ordinary list success. -/
theorem FunctionParametersRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FunctionParametersRejects input rejected) :
    ¬ ∃ parameters output,
      FunctionParametersOrdinaryParses input parameters output := by
  unfold FunctionParametersOrdinaryParses
  exact rejection.disjointAllowEmptyTrailing
    (functionParameterDeterministicOutcomeSpec
      typeExprDeterministicOutcomeSpec) (fun parsed => parsed)

/-- Recovery-aware function-parameter lists have deterministic and exclusive
ordinary outcomes. -/
theorem functionParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FunctionParametersOrdinaryParses
      FunctionParametersRejects where
  successOutputUnique := FunctionParametersOrdinaryParses.output_unique
  successRejectDisjoint := FunctionParametersRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
