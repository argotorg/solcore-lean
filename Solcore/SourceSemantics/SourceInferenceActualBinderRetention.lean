import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.Frontend.SourceInference.LocalGeneralizationInference

/-! Actual inference retains initialized binders even when it updates expression evidence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open LocalGeneralizationEvents

theorem CallIndex.bindersRetained {call : CallIndex} (accepted : call.Accepted) :
    BindersRetained call.initial.nodes call.final.nodes := by
  cases call with
  | expression => exact (inferExprFuel_origins_progress accepted).retained
  | constructorApplication => exact (inferConstructorApplicationFuel_origins_progress accepted).retained
  | constructorArguments => exact (inferConstructorArgumentsFuel_origins_progress accepted).retained
  | statements => exact (inferStatementsFuel_origins_progress accepted).retained
  | statement => exact (inferStatementFuel_origins_progress accepted).retained
  | forItems => exact (inferForItemsFuel_origins_progress accepted).retained
  | forItem => exact (inferForItemFuel_origins_progress accepted).retained
  | place => exact (inferPlaceFuel_origins_progress accepted).retained
  | assignedValue => exact (inferAssignedValueFuel_origins_progress accepted).retained
  | expressions => exact (inferExprsFuel_origins_progress accepted).retained
  | matchCases => exact (inferMatchCasesFuel_origins_progress accepted).retained

namespace ActualBinderRetention

theorem of_nodes_eq {before after : State} (same : after.nodes = before.nodes) :
    BindersRetained before.nodes after.nodes := same.symm ▸ BindersRetained.refl _

theorem unify_retained {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    BindersRetained before.nodes after.nodes :=
  of_nodes_eq (unify_occurrenceState_eq accepted).1

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
