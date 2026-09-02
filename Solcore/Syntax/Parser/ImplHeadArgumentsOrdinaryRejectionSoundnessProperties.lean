import Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.Impl

/-! Exact ordinary rejection for implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- The nonempty refinement is pure or invariant and never rejects. -/
theorem requireImplArguments_ne_reject
    (values : DelimitedList TypeExpr) (input rejected : State)
    (failure : Failure) :
    requireImplArguments values input ≠ .reject failure rejected := by
  unfold requireImplArguments
  cases values.elements <;> simp [pure]

/-- Every executable head-list rejection comes from the committed delimited
stage and retains its exact rejected remainder. -/
theorem implHeadArguments_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : delimited .less .greater false typeExpr .typeExpr .topLevel
      input = .reject failure rejected) :
    DeclarativeGrammar.ImplHeadArgumentsRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  exact delimited_reject_sound .less .greater false typeExpr
    DeclarativeGrammar.TypeExprOrdinaryParses
    DeclarativeGrammar.TypeExprRejects .typeExpr .topLevel
    typeExpr_ordinaryOutcome_sound.1 typeExpr_ordinaryOutcome_sound.2 result

end Solcore.Syntax.Parser.ImplInternals
