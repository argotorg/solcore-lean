import Solcore.SourceSemantics.SourceInferenceActualCallGraphClosurePrefixes
import Solcore.SourceSemantics.SourceCompiledBodyCallIndex
import Solcore.Frontend.SourceInference.LocalLetRequirementTiming
import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming
import Solcore.SourceSemantics.WellFormed

/-! Empty actual body initialization supplies graph closure at every reached
call and at the exact pre-generalization initializer checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution

theorem childEdgesExist_of_nodesClosed {state : State} (closed : NodesClosed state.nodes)
    (roots : List NodeId) : ChildEdgesExist (state.toTypedSource roots) :=
  closed

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem actualCall_nodesClosed (selected : BodySelection compiled row fuel)
    {call : CallIndex} (here : selected.InferenceCall call) :
    NodesClosed call.initial.nodes :=
  here.nodesClosed NodesClosed.nil

/-- Both closure and the returned root come from the same initializer run. -/
theorem statement_initializer_graph (selected : BodySelection compiled row fuel)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.statement (childFuel + 1) context source expectedReturn entry result)) :
    NodesClosed receipt.ready.nodes ∧
      NodeIdsPresent [.expression receipt.value.id] receipt.ready.nodes := by
  have graph := Detail.inferExprFuel_occurrenceGraph receipt.child
  exact ⟨graph.graph.closed (selected.actualCall_nodesClosed here), graph.returned⟩

theorem header_initializer_graph (selected : BodySelection compiled row fuel)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.forItem (childFuel + 1) context source entry result.1 result.2)) :
    NodesClosed receipt.ready.nodes ∧
      NodeIdsPresent [.expression receipt.value.id] receipt.ready.nodes := by
  have graph := Detail.inferExprFuel_occurrenceGraph receipt.child
  exact ⟨graph.graph.closed (selected.actualCall_nodesClosed here), graph.returned⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
