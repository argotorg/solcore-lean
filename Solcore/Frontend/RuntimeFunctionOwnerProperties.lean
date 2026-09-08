import Solcore.Frontend.TerminalReturnBodyRenamingProperties
import Solcore.Frontend.RuntimeParametersOwnerProperties
import Solcore.Frontend.RuntimeFunctionEntryProperties

/-! Owner relabeling preserves exact prepared Core and runtime values, not
the identity-bearing name tables or contexts. Arbitrary owners are connected
by an injective swap, never by overwriting every local identity's owner. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Covariance uses a globally injective owner map and leaves binder indices
unchanged. The exact Core and declared type are retained in the output record. -/
theorem RuntimeFunctionPrepares.mapOwner {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    RuntimeFunctionPrepares types (mapping owner) declaration arguments
      { prepared with inputs := (prepared.inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)) } := by
  refine ⟨preparation.header, preparation.parameters.map_owner mapping injective, ?_⟩
  simp only [LocalInputs.mapIds_names, LocalInputs.mapIds_context]
  exact preparation.body.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)

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
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared)
    (newOwner : Resolved.DeclarationId) :
    ∃ next, RuntimeFunctionPrepares types newOwner declaration arguments next ∧
      next.core = prepared.core ∧ next.returnType = prepared.returnType ∧
      Resolved.LocalScope.values next.inputs.environment =
        Resolved.LocalScope.values prepared.inputs.environment := by
  refine ⟨{ prepared with inputs := (prepared.inputs.mapIds (ownerLocalIdMap (swapOwner owner newOwner))
    (ownerLocalIdMap_injective _ (swapOwner_injective owner newOwner))) }, ?_, rfl, rfl, ?_⟩
  · simpa only [swapOwner_left] using
      preparation.mapOwner (swapOwner owner newOwner) (swapOwner_injective owner newOwner)
  · simp only [LocalInputs.mapIds_environment, Resolved.LocalScope.values_mapIds]

/-- The optional projection preserves failure and the exact executable data.
Identity-bearing tables are related by relabeling, not equated with each other. -/
theorem prepareRuntimeFunction?_owner_projection_eq
    (types : TypeNameTable) (leftOwner rightOwner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    (prepareRuntimeFunction? types leftOwner declaration arguments).map
        (fun prepared => (prepared.core, prepared.returnType,
          Resolved.LocalScope.values prepared.inputs.environment)) =
      (prepareRuntimeFunction? types rightOwner declaration arguments).map
        (fun prepared => (prepared.core, prepared.returnType,
          Resolved.LocalScope.values prepared.inputs.environment)) := by
  cases leftResult : prepareRuntimeFunction? types leftOwner declaration arguments with
  | none =>
      cases rightResult : prepareRuntimeFunction? types rightOwner declaration arguments with
      | none => rfl
      | some right =>
          obtain ⟨left, preparation, _, _, _⟩ := changeOwner (prepareRuntimeFunction?_sound rightResult) leftOwner
          have accepted := preparation.complete
          rw [leftResult] at accepted
          cases accepted
  | some left =>
      obtain ⟨right, preparation, coreEq, typeEq, valuesEq⟩ :=
        changeOwner (prepareRuntimeFunction?_sound leftResult) rightOwner
      rw [preparation.complete]
      simp only [Option.map_some, coreEq, typeEq, valuesEq]

/-- Identical Core and value sequences give identical full results at the same
fuel and store, including suspended states and both-sided preparation failure. -/
theorem runRuntimeFunction?_owner_eq
    (types : TypeNameTable) (leftOwner rightOwner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types leftOwner declaration arguments fuel store =
      runRuntimeFunction? types rightOwner declaration arguments fuel store := by
  have same := prepareRuntimeFunction?_owner_projection_eq types leftOwner rightOwner declaration arguments
  cases left : prepareRuntimeFunction? types leftOwner declaration arguments <;>
    cases right : prepareRuntimeFunction? types rightOwner declaration arguments <;>
    simp_all [runRuntimeFunction?]

end Solcore.Frontend
