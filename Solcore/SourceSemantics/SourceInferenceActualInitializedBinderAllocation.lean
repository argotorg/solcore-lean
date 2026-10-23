import Solcore.Frontend.SourceInference.InitializedBinderAllocation
import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedInference
import Solcore.SourceSemantics.SourceInferenceActualCallProperties
import Solcore.SourceSemantics.Ownership

/-! The same eleven accepted inference families preserve recorded binder
allocation bounds through the existing generalization-event proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open LocalGeneralizationBoundaries

theorem CallIndex.boundaryProgress {call : CallIndex}
    (inputs : call.Inputs) (accepted : call.Accepted) :
    LocalGeneralizationBoundaries.Progress call.initial call.final := by
  cases call with
  | expression => exact inferExprFuel_boundaries_progress accepted
  | constructorApplication => exact inferConstructorApplicationFuel_boundaries_progress accepted
  | constructorArguments => exact inferConstructorArgumentsFuel_boundaries_progress accepted
  | statements => exact inferStatementsFuel_boundaries_progress accepted
  | statement => exact inferStatementFuel_boundaries_progress accepted
  | forItems => exact inferForItemsFuel_boundaries_progress accepted
  | forItem => exact inferForItemFuel_boundaries_progress accepted
  | place => exact inferPlaceFuel_boundaries_progress accepted
  | assignedValue => exact inferAssignedValueFuel_boundaries_progress accepted
  | expressions => exact inferExprsFuel_boundaries_progress accepted
  | matchCases fuel context scrutinee expected saved cases initial result =>
    have scope : initial.lexicalScope = saved := inputs.bounds.2.2
    have subset : saved.binders ⊆ initial.localBinders := by
      rw [← scope]
      exact fun _ member => member
    exact inferMatchCasesFuel_boundaries_progress subset accepted

theorem CallIndex.initializedAllocated {call : CallIndex}
    (inputs : call.Inputs) (accepted : call.Accepted)
    (ready : LocalGeneralizationEvents.Ready call.initial)
    (below : call.initial.LocalBindersBelowNextLocal)
    (allocated : InitializedBindersAllocated call.initial) :
    InitializedBindersAllocated call.final :=
  (call.boundaryProgress inputs accepted).initializedAllocated ready below allocated

private theorem item_collector (item : ForItemForm) :
    item.initializedLetBinders = (forItemInitializedLetBindings item).map (·.binder) := by
  cases item with
  | letDecl _ initializer => cases initializer <;> rfl
  | expression | assignValue | assignBitNot => rfl

private theorem statement_collector (form : StatementForm) :
    form.initializedLetBinders = (statementInitializedLetBindings form).map (·.binder) := by
  cases form with
  | letDecl _ initializer => cases initializer <;> rfl
  | forLoop =>
    simp only [StatementForm.initializedLetBinders, statementInitializedLetBindings,
      List.map_append, List.map_flatMap, ← item_collector]
  | returnStmt | expression | assignValue | assignBitNot | ifThen | block
  | matchWith | whileLoop | breakStmt | continueStmt => rfl

/-- The operational inventory bound applies to the semantic initialized binding
collector without changing either collector's identities. -/
theorem initialized_binding_allocated {state : State}
    (allocated : InitializedBindersAllocated state)
    {binding : InitializedLetBinding}
    (member : binding ∈ initializedLetBindings (state.toTypedSource [])) :
    binding.binder.id.binderIndex ≤ state.nextLocal := by
  obtain ⟨node, present, bound⟩ := List.mem_flatMap.mp member
  cases node with
  | expression _ => cases bound
  | statement statement =>
    apply allocated (.statement statement) present binding.binder
    change binding.binder ∈ statement.form.initializedLetBinders
    rw [statement_collector]
    exact List.mem_map.mpr ⟨binding, bound, rfl⟩

end Solcore.SourceSemantics.SourceInferenceExecution
