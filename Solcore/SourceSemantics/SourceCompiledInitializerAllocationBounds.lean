import Solcore.SourceSemantics.SourceInferenceActualBoundaryPrefixes
import Solcore.SourceSemantics.SourceCompiledActualBodyInputs
import Solcore.Frontend.SourceInference.LocalLetRequirementTiming
import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

/-! Recorded initialized binders stay below the actual local allocator at
every reached call and at the exact ready state of its initializer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution
open LocalGeneralizationBoundaries
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

private theorem annotationExpected {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {type : Option Ty}
    (annotation : LocalLetRequirementTiming.Annotation context source type) :
    AnnotationExpected context source type := by
  cases annotation with
  | none => exact .absent
  | some accepted => exact .present accepted

private theorem initial_ready (selected : BodySelection compiled row fuel) :
    LocalGeneralizationEvents.Ready selected.inferenceCall.initial := by
  refine ⟨State.initial_requirementsWellFormed _ _ _, ?_, ?_⟩
  · intro id impossible
    exact False.elim (List.not_mem_nil impossible)
  · intro node impossible
    exact False.elim (List.not_mem_nil impossible)

theorem actualCall_initializedAllocated (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    InitializedBindersAllocated call.initial :=
  (here.boundaries_prefix (selected.inferenceCall_inputs checked)).initializedAllocated
    (initial_ready selected) (State.initial_localBindersBelowNextLocal _ _ _)
    (InitializedBindersAllocated.empty rfl)

theorem actualCall_final_initializedAllocated (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    InitializedBindersAllocated call.final := by
  have inputs := selected.inferenceCall_inputs checked
  have entryProgress := here.boundaries_prefix inputs
  exact (entryProgress.trans (call.boundaryProgress (here.inputs inputs) here.accepted)).initializedAllocated
    (initial_ready selected) (State.initial_localBindersBelowNextLocal _ _ _)
    (InitializedBindersAllocated.empty rfl)

/-- The statement receipt and its actual recursive edge select the same
initializer result; the bound is derived from the forward successful computation. -/
theorem statement_initializer_allocated (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.statement (childFuel + 1) context source expectedReturn entry result)) :
    InitializedBindersAllocated receipt.ready := by
  have annotation := annotationExpected receipt.annotationAccepted
  have step := ChildStep.statement_initializer here.accepted receipt.form rfl annotation receipt.child
  exact selected.actualCall_final_initializedAllocated checked (.child here step)

/-- The same actual checkpoint is available for initializer and post headers. -/
theorem header_initializer_allocated (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.forItem (childFuel + 1) context source entry result.1 result.2)) :
    InitializedBindersAllocated receipt.ready := by
  have annotation := annotationExpected receipt.annotationAccepted
  have step := ChildStep.forItem_initializer here.accepted receipt.form annotation receipt.child
  exact selected.actualCall_final_initializedAllocated checked (.child here step)

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
