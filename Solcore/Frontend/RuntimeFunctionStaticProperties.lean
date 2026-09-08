import Solcore.Frontend.RuntimeParametersStaticProperties
import Solcore.Frontend.RuntimeFunctionEntryProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties

/-! Equal ordered argument types preserve exact static preparation, including
failure. Runtime environments, results, suspended states, and costs may differ. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionPrepares.transport_argument_types {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {leftArguments rightArguments : List TypedRuntimeArgument} {left : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration leftArguments left)
    (sameArgumentTypes : leftArguments.map (·.type) = rightArguments.map (·.type)) :
    ∃ right, RuntimeFunctionPrepares types owner declaration rightArguments right ∧
      right.inputs.ids = left.inputs.ids ∧ right.inputs.names = left.inputs.names ∧
      right.inputs.context = left.inputs.context ∧ right.core = left.core ∧
      right.returnType = left.returnType := by
  obtain ⟨rightInputs, parameters, namesEq, contextEq⟩ :=
    preparation.parameters.transport_types (rightInitial := .empty) rfl rfl sameArgumentTypes
  have idsEq : rightInputs.ids = left.inputs.ids := by
    rw [← LocalInputs.context_ids, ← LocalInputs.context_ids, contextEq]
  have erased : rightInputs.toTypeInputs = left.inputs.toTypeInputs :=
    parameters.erase_values.result_unique preparation.parameters.erase_values
  have body : TypedLetReturnTreeElaborates types owner rightInputs.toTypeInputs declaration.value.body
      left.core left.returnType := by
    rw [erased]
    exact preparation.body
  exact ⟨⟨rightInputs, left.core, left.returnType⟩, ⟨preparation.header, parameters, body⟩,
    idsEq, namesEq, contextEq, rfl, rfl⟩

/-- `Option` equality includes both-sided rejection; successful results retain
their exact static projections without equating the prepared runtime values. -/
theorem prepareRuntimeFunction?_static_projection_eq {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {leftArguments rightArguments : List TypedRuntimeArgument}
    (sameArgumentTypes : leftArguments.map (·.type) = rightArguments.map (·.type)) :
    (prepareRuntimeFunction? types owner declaration leftArguments).map
        (fun prepared => (prepared.inputs.ids, prepared.inputs.names, prepared.inputs.context,
          prepared.core, prepared.returnType)) =
      (prepareRuntimeFunction? types owner declaration rightArguments).map
        (fun prepared => (prepared.inputs.ids, prepared.inputs.names, prepared.inputs.context,
          prepared.core, prepared.returnType)) := by
  cases leftResult : prepareRuntimeFunction? types owner declaration leftArguments with
  | none =>
      cases rightResult : prepareRuntimeFunction? types owner declaration rightArguments with
      | none => rfl
      | some right =>
          obtain ⟨left, preparation, _⟩ :=
            (prepareRuntimeFunction?_sound rightResult).transport_argument_types sameArgumentTypes.symm
          have accepted := preparation.complete
          rw [leftResult] at accepted
          cases accepted
  | some left =>
      obtain ⟨right, preparation, idsEq, namesEq, contextEq, coreEq, typeEq⟩ :=
        (prepareRuntimeFunction?_sound leftResult).transport_argument_types sameArgumentTypes
      rw [preparation.complete]
      simp only [Option.map_some, idsEq, namesEq, contextEq, coreEq, typeEq]

end Solcore.Frontend
