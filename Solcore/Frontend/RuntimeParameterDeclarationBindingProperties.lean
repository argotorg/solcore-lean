import Solcore.Frontend.LocalInputsTypeErasure
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeParametersProperties

/-! Runtime binding erases to static declaration. Conversely, matching actual
typed arguments reconstruct exactly the declared static bundle. No inhabitance
assumption or fabricated runtime value is used, including for arbitrary Core types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeParametersBindFrom.erase_values {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalInputs} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom types owner initial parameters arguments final) :
    RuntimeParametersDeclareFrom types owner initial.toTypeInputs parameters final.toTypeInputs := by
  induction bound with
  | nil => exact .nil
  | cons meaning unused _ ih =>
      exact .cons meaning (by simpa only [LocalInputs.toTypeInputs_names] using unused)
        (by simpa only [LocalInputs.toTypeInputs_bindFresh] using ih)

theorem RuntimeParametersBind.erase_values {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalInputs} {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBind types owner parameters arguments inputs) :
    RuntimeParametersDeclare types owner parameters inputs.toTypeInputs := by
  simpa only [LocalInputs.toTypeInputs_empty] using RuntimeParametersBindFrom.erase_values bound

/-- The existential list records only annotation types. Its reconstruction
clause must still be supplied every actual argument and its structural evidence. -/
private theorem declaration_restore_data {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom types owner initial parameters final) :
    ∃ addedTypes : List Core.Ty,
      Resolved.LocalScope.values final.context = addedTypes.reverse ++ Resolved.LocalScope.values initial.context ∧
      ∀ (runtimeInitial : LocalInputs) (arguments : List TypedRuntimeArgument),
        runtimeInitial.toTypeInputs = initial → arguments.map (·.type) = addedTypes →
        ∃ runtimeFinal, RuntimeParametersBindFrom types owner runtimeInitial parameters arguments runtimeFinal ∧
          runtimeFinal.toTypeInputs = final := by
  induction declared with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      intro runtimeInitial arguments erased matching
      cases arguments with
      | nil => exact ⟨runtimeInitial, .nil, erased⟩
      | cons argument arguments => simp only [List.map_cons, reduceCtorEq] at matching
  | @cons initial final span name annotation type parameters meaning unused _ ih =>
      obtain ⟨tailTypes, finalTypes, restoreTail⟩ := ih
      refine ⟨type :: tailTypes, ?_, ?_⟩
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
          LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values, List.map_cons] using finalTypes
      · intro runtimeInitial arguments erased matching
        cases arguments with
        | nil => simp only [List.map_nil, reduceCtorEq] at matching
        | cons argument arguments =>
            obtain ⟨sameHead, sameTail⟩ := List.cons.inj (by simpa only [List.map_cons] using matching)
            have nextErased :
                (runtimeInitial.bindFresh owner name.value argument.type argument.value argument.valueTyped).toTypeInputs =
                  initial.bindFresh owner name.value type := by
              rw [LocalInputs.toTypeInputs_bindFresh, erased, sameHead]
            obtain ⟨runtimeFinal, tailBound, finalErased⟩ := restoreTail
              (runtimeInitial.bindFresh owner name.value argument.type argument.value argument.valueTyped)
              arguments nextErased sameTail
            have namesEq : runtimeInitial.names = initial.names := by
              rw [← LocalInputs.toTypeInputs_names, erased]
            exact ⟨runtimeFinal, .cons (sameHead.symm ▸ meaning)
              (by simpa only [namesEq] using unused) tailBound, finalErased⟩

/-- General initial inputs are retained. The type-list equation includes their
source-order prefix and all newly supplied types, hence also fixes arity. -/
theorem RuntimeParametersDeclareFrom.bind_typed_arguments
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom types owner initial parameters final)
    (runtimeInitial : LocalInputs) (initialErased : runtimeInitial.toTypeInputs = initial)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : (Resolved.LocalScope.values initial.context).reverse ++ arguments.map (·.type) =
      (Resolved.LocalScope.values final.context).reverse) :
    ∃ runtimeFinal, RuntimeParametersBindFrom types owner runtimeInitial parameters arguments runtimeFinal ∧
      runtimeFinal.toTypeInputs = final := by
  obtain ⟨addedTypes, finalTypes, restore⟩ := declaration_restore_data declared
  have argumentTypes : arguments.map (·.type) = addedTypes :=
    List.append_cancel_left (by
      simpa only [finalTypes, List.reverse_append, List.reverse_reverse] using matchingTypes)
  exact restore runtimeInitial arguments initialErased argumentTypes

/-- Static declaration alone does not produce values. An exactly matching list
of supplied typed arguments is what reconstructs the independent runtime binding. -/
theorem RuntimeParametersDeclare.bind_typed_arguments
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclare types owner parameters inputs)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values inputs.context).reverse) :
    ∃ runtimeInputs, RuntimeParametersBind types owner parameters arguments runtimeInputs ∧
      runtimeInputs.toTypeInputs = inputs :=
  RuntimeParametersDeclareFrom.bind_typed_arguments declared .empty rfl arguments
    (by simpa only [LocalTypeInputs.empty_context, Resolved.LocalScope.values, List.map_nil,
      List.reverse_nil, List.nil_append] using matchingTypes)

end Solcore.Frontend
