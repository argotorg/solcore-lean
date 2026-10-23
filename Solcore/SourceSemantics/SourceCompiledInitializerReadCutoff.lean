import Solcore.SourceSemantics.SourceInferenceActualReadCutoffPrefixes
import Solcore.SourceSemantics.SourceCompiledActualBodyInputs
import Solcore.Frontend.SourceInference.LocalLetRequirementTiming
import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

/-! Actual body initialization supplies read cutoffs at every reached call
and at the exact initializer return state used for generalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution
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

theorem actualCall_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    LocalReadCutoff call.initial :=
  here.read_cutoff (selected.inferenceCall_inputs checked)
    (State.initial_localBindersBelowNextLocal _ _ _)
    (by intro id impossible; cases impossible)
    (by intro node impossible; cases impossible)

theorem actualCall_final_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    LocalReadCutoff call.final := by
  have inputs := selected.inferenceCall_inputs checked
  exact CallIndex.localReadCutoff here.accepted (here.inputs inputs)
    (ActualLocalAllocator.occurrence_bound inputs
      (State.initial_localBindersBelowNextLocal _ _ _) here)
    (here.direct_prefix.allocated inputs.wellFormed (by intro id impossible; cases impossible))
    (selected.actualCall_read_cutoff checked here)

/-- The statement receipt and its actual recursive edge select the same
initializer result; no final-table cutoff is moved backwards. -/
theorem statement_initializer_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.statement (childFuel + 1) context source expectedReturn entry result)) :
    LocalReadCutoff receipt.ready := by
  have annotation := annotationExpected receipt.annotationAccepted
  have step := ChildStep.statement_initializer here.accepted receipt.form rfl annotation receipt.child
  exact selected.actualCall_final_read_cutoff checked (.child here step)

/-- The same actual checkpoint is available for initializer and post headers. -/
theorem header_initializer_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.forItem (childFuel + 1) context source entry result.1 result.2)) :
    LocalReadCutoff receipt.ready := by
  have annotation := annotationExpected receipt.annotationAccepted
  have step := ChildStep.forItem_initializer here.accepted receipt.form annotation receipt.child
  exact selected.actualCall_final_read_cutoff checked (.child here step)

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
