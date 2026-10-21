import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.Frontend.SourceInference.LocalLetRequirementTiming
import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

/-! A generalization origin retains the exact executed receipt and its path
from the same accepted body call. No arbitrary accepted initializer is
substituted for an initializer reached by that body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem

inductive Origin (root : CallIndex) : TypedBinder → ExpressionId → Prop where
  | statement {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
      (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
      (here : CallOccurrence root
        (.statement (fuel + 1) context source expectedReturn initial result)) :
      Origin root receipt.binding.1 receipt.value.id
  | header {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial : State} {result : ForItemForm × State}
      (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
      (here : CallOccurrence root
        (.forItem (fuel + 1) context source initial result.1 result.2)) :
      Origin root receipt.binding.1 receipt.value.id

/-- An origin in an actual child remains an origin in every enclosing call
on the same inference path. -/
theorem Origin.rebase {root child : CallIndex}
    {binder : TypedBinder} {initializer : ExpressionId}
    (here : CallOccurrence root child)
    (origin : Origin child binder initializer) :
    Origin root binder initializer := by
  cases origin with
  | statement receipt reached => exact .statement receipt (here.trans reached)
  | header receipt reached => exact .header receipt (here.trans reached)

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
