import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedNonemptyTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeGrammar

/-! Deterministic exact outcomes for implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary implementation head arguments have one final remainder. -/
theorem ImplHeadArgumentsOrdinaryParses.output_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplHeadArgumentsOrdinaryParses input left afterLeft)
    (rightParsed : ImplHeadArgumentsOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold ImplHeadArgumentsOrdinaryParses at leftParsed rightParsed
  exact NonemptyTrailingDelimitedListParses.output_unique
    (opening := .less) (closing := .greater)
    (elementParses := TypeExprOrdinaryParses)
    typeExprDeterministicOutcomeSpec.successOutputUnique leftParsed rightParsed

/-- Exact list rejection excludes every ordinary implementation argument
success. -/
theorem ImplHeadArgumentsRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ImplHeadArgumentsRejects input rejected) :
    ¬ ∃ arguments output,
      ImplHeadArgumentsOrdinaryParses input arguments output := by
  intro successful
  rcases successful with ⟨arguments, output, parsed⟩
  exact DelimitedListRejects.disjointNonemptyTrailing
    typeExprDeterministicOutcomeSpec (fun ordinary => ordinary) rejection
      ⟨_, _, parsed⟩

/-- Implementation head arguments have deterministic and exclusive broad
ordinary outcomes. -/
theorem implHeadArgumentsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImplHeadArgumentsOrdinaryParses
      ImplHeadArgumentsRejects where
  successOutputUnique := ImplHeadArgumentsOrdinaryParses.output_unique
  successRejectDisjoint := ImplHeadArgumentsRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
