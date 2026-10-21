import Solcore.SourceSemantics.SourceInferenceActualExpressionBinderRetention
import Solcore.SourceSemantics.SourceInferenceActualNonExpressionBinderRetention
import Solcore.SourceSemantics.SourceInferenceActualCaptureRetention

/-! An actual child keeps both declarations recorded in its node table and
header declarations awaiting their enclosing loop statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference
open LocalGeneralizationEvents (BindersRetained)

private theorem item_binders (item : ForItemForm) :
    item.initializedLetBinders = (forItemInitializedLetBindings item).map (·.binder) := by
  cases item <;> try rfl
  rename_i binder initializer
  cases initializer <;> rfl

private theorem statement_binders (form : StatementForm) :
    form.initializedLetBinders = (statementInitializedLetBindings form).map (·.binder) := by
  cases form <;> try rfl
  · rename_i binder initializer
    cases initializer <;> rfl
  · simp only [StatementForm.initializedLetBinders, statementInitializedLetBindings,
      List.map_append, List.map_flatMap]
    simp only [← item_binders]

private theorem source_binders (source : TypedSource) :
    source.initializedLetBinders = (initializedLetBindings source).map (·.binder) := by
  simp only [TypedSource.initializedLetBinders, initializedLetBindings, List.map_flatMap]
  apply congrArg (fun f : Node → List TypedBinder => source.nodes.flatMap f)
  funext node
  cases node with
  | expression node => rfl
  | statement node => exact statement_binders node.form

def CallIndex.initializedBinders (call : CallIndex) : List TypedBinder :=
  call.final.nodes.flatMap Node.initializedLetBinders ++ call.returnedBindings.map (·.binder)

theorem ChildStep.binders_retained {parent child : CallIndex}
    (step : ChildStep parent child) :
    BindersRetained child.final.nodes parent.final.nodes := by
  cases parent <;> first
  | exact step.expression_binders_retained
  | exact step.nonexpression_binders_retained (by trivial)

theorem ChildStep.initialized_binders {parent child : CallIndex}
    (step : ChildStep parent child) :
    child.initializedBinders ⊆ parent.initializedBinders := by
  intro binder present
  rcases List.mem_append.mp present with recorded | pending
  · exact List.mem_append_left _ (step.binders_retained recorded)
  · obtain ⟨binding, member, same⟩ := List.mem_map.mp pending
    rcases List.mem_append.mp (step.returned_bindings member) with recorded | pending
    · apply List.mem_append_left
      change binder ∈ (parent.final.toTypedSource []).initializedLetBinders
      rw [source_binders]
      exact List.mem_map.mpr ⟨binding, recorded, same⟩
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨binding, pending, same⟩)

theorem CallOccurrence.initialized_binders {root call : CallIndex}
    (here : CallOccurrence root call) :
    call.initializedBinders ⊆ root.initializedBinders := by
  induction here with
  | root accepted => exact fun _ present => present
  | child prior step ih => exact fun _ present => ih (step.initialized_binders present)

end Solcore.SourceSemantics.SourceInferenceExecution
