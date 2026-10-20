import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! The assignment prefix keeps its actual operator guard and expected type.
Both semantic and lifetime traversals can consume these same child calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

private theorem accepted_bind {α β : Type} {action : Except Error α}
    {next : α → Except Error β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem assignedValue_actual_prefix
    {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final : State}
    {assignment : AssignmentResolution} {inferred : InferredExpression}
    (accepted : inferAssignedValueFuel fuel context target operator value initial =
      .ok (assignment, inferred, final)) :
    ∃ place placeState fitted,
      inferPlaceFuel fuel context target initial = .ok (place, placeState) ∧
      (match operator with | .equal => pure placeState | _ => unify placeState place.type .word) =
        (Except.ok fitted : Except Error State) ∧
      inferExprFuel fuel context value (some (assignmentExpected operator fitted place.type)) fitted =
        .ok (inferred, final) ∧
      assignment.target = { place with type := final.resolve place.type } := by
  unfold inferAssignedValueFuel at accepted
  obtain ⟨⟨place, placeState⟩, placeCall, afterPlace⟩ := accepted_bind accepted
  cases operator <;>
    obtain ⟨fitted, fitting, afterFitting⟩ := accepted_bind afterPlace
  all_goals
    obtain ⟨⟨result, state⟩, valueCall, returned⟩ := accepted_bind afterFitting
    cases returned
    exact ⟨place, placeState, fitted, placeCall, fitting, valueCall, rfl⟩

end Solcore.SourceSemantics.SourceInferenceExecution
