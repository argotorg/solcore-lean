import Solcore.Frontend.RuntimeParameterDeclarationsOwnerProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Frontend.TerminalReturnBodyRenamingProperties

/-! Value-free compilation retains its exact Core, declared type and ordered
parameter types across owners. Identity-bearing inputs are relabeled, not equated. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Static declaration and whole terminal-body evidence transport directly.
No actual arguments or inhabitants of the parameter types are required. -/
theorem RuntimeFunctionCompiles.mapOwner {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    RuntimeFunctionCompiles types (mapping owner) declaration
      { compiled with inputs := (compiled.inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)) } := by
  refine ⟨compilation.header, compilation.parameters.map_owner mapping injective, ?_⟩
  simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
  exact compilation.body.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)

private def swapOwner (left right owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  if owner = left then right else if owner = right then left else owner

private theorem swapOwner_left (left right : Resolved.DeclarationId) :
    swapOwner left right left = right := by simp [swapOwner]

private theorem swapOwner_involutive (left right owner : Resolved.DeclarationId) :
    swapOwner left right (swapOwner left right owner) = owner := by
  by_cases same : left = right
  · subst right
    by_cases present : owner = left <;> simp [swapOwner, present]
  · by_cases isLeft : owner = left
    · subst owner
      simp [swapOwner, Ne.symm same]
    · by_cases isRight : owner = right
      · subst owner
        simp [swapOwner, Ne.symm same]
      · simp [swapOwner, isLeft, isRight]

private theorem swapOwner_injective (left right : Resolved.DeclarationId) :
    Function.Injective (swapOwner left right) := by
  intro first second same
  simpa only [swapOwner_involutive] using congrArg (swapOwner left right) same

private theorem changeOwner {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (newOwner : Resolved.DeclarationId) :
    ∃ next, RuntimeFunctionCompiles types newOwner declaration next ∧
      next.core = compiled.core ∧ next.returnType = compiled.returnType ∧
      Resolved.LocalScope.values next.inputs.context =
        Resolved.LocalScope.values compiled.inputs.context := by
  refine ⟨{ compiled with inputs := (compiled.inputs.mapIds (ownerLocalIdMap (swapOwner owner newOwner))
    (ownerLocalIdMap_injective _ (swapOwner_injective owner newOwner))) }, ?_, rfl, rfl, ?_⟩
  · simpa only [swapOwner_left] using
      compilation.mapOwner (swapOwner owner newOwner) (swapOwner_injective owner newOwner)
  · simp only [LocalTypeInputs.mapIds_context, Resolved.LocalScope.values_mapIds]

/-- The complete optional static projection agrees, including rejection.
The result does not assert equality of owner-bearing tables or compiled records. -/
theorem compileRuntimeFunction?_owner_projection_eq
    (types : TypeNameTable) (leftOwner rightOwner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) :
    (compileRuntimeFunction? types leftOwner declaration).map
        (fun compiled => (compiled.core, compiled.returnType,
          Resolved.LocalScope.values compiled.inputs.context)) =
      (compileRuntimeFunction? types rightOwner declaration).map
        (fun compiled => (compiled.core, compiled.returnType,
          Resolved.LocalScope.values compiled.inputs.context)) := by
  cases leftResult : compileRuntimeFunction? types leftOwner declaration with
  | none =>
      cases rightResult : compileRuntimeFunction? types rightOwner declaration with
      | none => rfl
      | some right =>
          obtain ⟨left, compilation, _, _, _⟩ := changeOwner (compileRuntimeFunction?_sound rightResult) leftOwner
          have accepted := compilation.complete
          rw [leftResult] at accepted
          cases accepted
  | some left =>
      obtain ⟨right, compilation, coreEq, typeEq, valuesEq⟩ :=
        changeOwner (compileRuntimeFunction?_sound leftResult) rightOwner
      rw [compilation.complete]
      simp only [Option.map_some, coreEq, typeEq, valuesEq]

end Solcore.Frontend
