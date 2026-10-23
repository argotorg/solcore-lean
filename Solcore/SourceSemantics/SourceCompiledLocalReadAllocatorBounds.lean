import Solcore.SourceSemantics.SourceInferenceActualLocalAllocatorCalls
import Solcore.SourceSemantics.SourceCompiledActualLocalReadCalls
import Solcore.SourceSemantics.SourceCompiledActualBodyInputs

/-! The actual body entry and exact issuing lookup determine each local
reference's stable-identity bound. This is not a bound at an unrelated later
initializer checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceCompiledGeneralizedSoundness
open SourceInferenceExecution
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {raw : Workspace.RawWorkspace}

theorem actualCall_localBound (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    call.initial.LocalBindersBelowNextLocal :=
  ActualLocalAllocator.occurrence_bound (selected.inferenceCall_inputs checked)
    (State.initial_localBindersBelowNextLocal _ _ _) here

/-- The full binder returned by this real lookup was already allocated on
entry to the issuing expression call. -/
theorem specialized_local_read_bound (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {node : ExpressionNode} (member : .expression node ∈ row.function.typedBody.nodes)
    {name : String} {binder : Resolved.LocalId} (form : node.form = .reference name (.local binder)) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧ node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      selected.InferenceCall (ActualLocalRead.lookupCall lookup) ∧
      lookup.binder ∈ lookup.initial.localBinders ∧
      binder = lookup.binder.id ∧ binder.binderIndex < lookup.initial.nextLocal := by
  obtain ⟨lookup, sameId, sameForm, here, present⟩ := selected.specialized_local_read_active member form
  have sameBinder : binder = lookup.binder.id := by
    have same := form.symm.trans sameForm
    exact ReferenceResolution.local.inj (ExpressionForm.reference.inj same).2
  refine ⟨lookup, sameId, sameForm, here, present, sameBinder, ?_⟩
  rw [sameBinder]
  exact selected.actualCall_localBound checked here lookup.binder present

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
