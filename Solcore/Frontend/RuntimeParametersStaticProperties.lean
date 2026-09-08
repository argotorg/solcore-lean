import Solcore.Frontend.RuntimeParametersProperties
import Solcore.Frontend.LocalInputsProperties

/-! Replacing supplied values while retaining their ordered structural types
preserves parameter-binding names and contexts. Runtime values need not agree. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeParametersBindFrom.transport_types {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {leftInitial leftFinal : LocalInputs}
    {parameters : List Syntax.FunctionParameter} {leftArguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom types owner leftInitial parameters leftArguments leftFinal)
    {rightInitial : LocalInputs} {rightArguments : List TypedRuntimeArgument}
    (sameNames : leftInitial.names = rightInitial.names)
    (sameContext : leftInitial.context = rightInitial.context)
    (sameArgumentTypes : leftArguments.map (·.type) = rightArguments.map (·.type)) :
    ∃ rightFinal, RuntimeParametersBindFrom types owner rightInitial parameters rightArguments rightFinal ∧
      rightFinal.names = leftFinal.names ∧ rightFinal.context = leftFinal.context := by
  induction bound generalizing rightInitial rightArguments with
  | nil =>
      cases rightArguments with
      | nil => exact ⟨rightInitial, .nil, sameNames.symm, sameContext.symm⟩
      | cons argument rest => simp only [List.map_nil, List.map_cons, reduceCtorEq] at sameArgumentTypes
  | @cons initial final span name annotation parameters argument arguments meaning unused tail ih =>
      cases rightArguments with
      | nil => simp only [List.map_cons, List.map_nil, reduceCtorEq] at sameArgumentTypes
      | cons rightArgument rightArguments =>
          obtain ⟨sameHead, sameTail⟩ := List.cons.inj (by simpa only [List.map_cons] using sameArgumentTypes)
          have sameIds : initial.ids = rightInitial.ids := by
            rw [← LocalInputs.context_ids, ← LocalInputs.context_ids, sameContext]
          have nextNames :
              (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped).names =
                (rightInitial.bindFresh owner name.value rightArgument.type rightArgument.value
                  rightArgument.valueTyped).names := by
            simp only [LocalInputs.bindFresh_names, sameNames, sameIds]
          have nextContext :
              (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped).context =
                (rightInitial.bindFresh owner name.value rightArgument.type rightArgument.value
                  rightArgument.valueTyped).context := by
            simp only [LocalInputs.bindFresh_context, sameContext, sameIds, sameHead]
          obtain ⟨rightFinal, rightTail, finalNames, finalContext⟩ := ih nextNames nextContext sameTail
          refine ⟨rightFinal, .cons ?_ ?_ rightTail, finalNames, finalContext⟩
          · exact sameHead ▸ meaning
          · simpa only [← sameNames] using unused

end Solcore.Frontend
