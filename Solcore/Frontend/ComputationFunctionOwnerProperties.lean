import Solcore.Frontend.RuntimeParameterDeclarationsOwnerProperties
import Solcore.Frontend.RuntimeParametersOwnerProperties
import Solcore.Frontend.LocalTypeInputsOwnerProperties
import Solcore.Frontend.ComputationReturnTreeOwnerProperties
import Solcore.Frontend.ComputationFunctionProperties
import Solcore.Frontend.LocalInputsTypeErasureRenamingProperties

/-! One injective owner map preserves independent shared function evidence,
exact optional compiled/prepared records, and every full Core run result.
Parameter reflection retains original inputs; only IDs change, never values. -/

set_option autoImplicit false
namespace Solcore.Frontend
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
include injective

private theorem inputs_bindFresh (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value typed).mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective) =
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).bindFresh
        (mapping owner) name type value typed := by
  have sameFresh : Resolved.freshLocalId (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).ids =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner inputs.ids) := by
    rw [LocalInputs.mapIds_ids]
    exact Resolved.freshLocalId_map_owner mapping injective owner inputs.ids
  cases inputs
  simp only [LocalInputs.mapIds, LocalInputs.bindFresh, List.map_cons,
    TypedLocalBinding.mapIds, LocalInputs.mk.injEq]
  congr 2
  exact sameFresh.symm

private theorem declare_reflect {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {renamed output : LocalTypeInputs} {params : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom types (mapping owner) renamed params output) :
    ∀ original : LocalTypeInputs,
      renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) →
      ∃ previous, RuntimeParametersDeclareFrom types owner original params previous ∧
        output = previous.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) := by
  induction declared with
  | nil => intro original same; exact ⟨original, .nil, same⟩
  | cons meaning unused _ ih =>
      intro original same
      have unusedOriginal := unused
      rw [same] at unusedOriginal
      simp only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
        Function.comp_def] at unusedOriginal
      obtain ⟨previous, tail, mapped⟩ := ih (original.bindFresh owner _ _) (by
        rw [same]; exact (LocalTypeInputs.bindFresh_mapOwner original owner mapping injective _ _).symm)
      exact ⟨previous, .cons meaning unusedOriginal tail, mapped⟩

private theorem bind_reflect {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {renamed output : LocalInputs} {params : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom types (mapping owner) renamed params arguments output) :
    ∀ original : LocalInputs,
      renamed = original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) →
      ∃ previous, RuntimeParametersBindFrom types owner original params arguments previous ∧
        output = previous.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) := by
  induction bound with
  | nil => intro original same; exact ⟨original, .nil, same⟩
  | cons meaning unused _ ih =>
      intro original same
      have unusedOriginal := unused
      rw [same] at unusedOriginal
      simp only [LocalInputs.mapIds_names, LocalNameTable.mapIds, List.map_map,
        Function.comp_def] at unusedOriginal
      obtain ⟨previous, tail, mapped⟩ := ih (original.bindFresh owner _ _ _ _) (by
        rw [same]; exact (inputs_bindFresh mapping injective original owner _ _ _ _).symm)
      exact ⟨previous, .cons meaning unusedOriginal tail, mapped⟩

private theorem declareRuntimeParameters?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) :
    declareRuntimeParameters? types (mapping owner) params =
      (declareRuntimeParameters? types owner params).map
        (fun inputs => inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) := by
  cases old : declareRuntimeParameters? types owner params with
  | some inputs =>
      simpa only [old, Option.map_some] using
        ((declareRuntimeParameters?_sound old).map_owner mapping injective).complete
  | none =>
      cases next : declareRuntimeParameters? types (mapping owner) params with
      | none => rfl
      | some output =>
          obtain ⟨previous, declared, _⟩ := declare_reflect mapping injective (declareRuntimeParameters?_sound next) .empty rfl
          have contradiction := RuntimeParametersDeclare.complete declared
          rw [old] at contradiction
          cases contradiction

private theorem bindRuntimeParameters?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) (arguments : List TypedRuntimeArgument) :
    bindRuntimeParameters? types (mapping owner) params arguments =
      (bindRuntimeParameters? types owner params arguments).map
        (fun inputs => inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) := by
  cases old : bindRuntimeParameters? types owner params arguments with
  | some inputs =>
      simpa only [old, Option.map_some] using
        (bindRuntimeParameters?_iff.mpr ((bindRuntimeParameters?_iff.mp old).map_owner mapping injective))
  | none =>
      cases next : bindRuntimeParameters? types (mapping owner) params arguments with
      | none => rfl
      | some output =>
          obtain ⟨previous, bound, _⟩ := bind_reflect mapping injective (bindRuntimeParameters?_iff.mp next) .empty rfl
          have contradiction := bindRuntimeParameters?_iff.mpr bound
          rw [old] at contradiction
          cases contradiction

private theorem typeMap_injective : Function.Injective (fun inputs : LocalTypeInputs =>
    inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) := by
  have rowsInjective : Function.Injective (LocalTypeBinding.mapIds (ownerLocalIdMap mapping)) := by
    rintro ⟨a,i,t⟩ ⟨b,j,u⟩ same
    simpa only [LocalTypeBinding.mapIds, LocalTypeBinding.mk.injEq,
      (ownerLocalIdMap_injective mapping injective).eq_iff] using same
  intro left right same
  have rows := (List.map_inj_right rowsInjective).mp (congrArg LocalTypeInputs.bindings same)
  cases left; cases right; cases rows; rfl

private theorem inputsMap_injective : Function.Injective (fun inputs : LocalInputs =>
    inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) := by
  have rowsInjective : Function.Injective (TypedLocalBinding.mapIds (ownerLocalIdMap mapping)) := by
    rintro ⟨a,i,t,v,h⟩ ⟨b,j,u,w,g⟩ same
    simpa only [TypedLocalBinding.mapIds, TypedLocalBinding.mk.injEq,
      (ownerLocalIdMap_injective mapping injective).eq_iff] using same
  intro left right same
  have rows := (List.map_inj_right rowsInjective).mp (congrArg LocalInputs.bindings same)
  cases left; cases right; cases rows; rfl

private theorem runtimeParametersDeclare_mapOwner_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {inputs : LocalTypeInputs} :
    RuntimeParametersDeclare types (mapping owner) params
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) ↔
      RuntimeParametersDeclare types owner params inputs := by
  constructor
  · intro declared
    obtain ⟨previous, original, same⟩ := declare_reflect mapping injective declared .empty rfl
    have inputsSame := typeMap_injective mapping injective same
    exact inputsSame ▸ original
  · intro declared
    exact declared.map_owner mapping injective

private theorem runtimeParametersBind_mapOwner_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument} {inputs : LocalInputs} :
    RuntimeParametersBind types (mapping owner) params arguments
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) ↔
      RuntimeParametersBind types owner params arguments inputs := by
  constructor
  · intro bound
    obtain ⟨previous, original, same⟩ := bind_reflect mapping injective bound .empty rfl
    have inputsSame := inputsMap_injective mapping injective same
    exact inputsSame ▸ original
  · intro bound
    exact bound.map_owner mapping injective

variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}

/-- Independent value-free compilation preserves the exact mapped record
under the same child's elaboration covariance, without a checker premise. -/
theorem computationFunctionCompiles_mapOwner_iff
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} :
    ComputationFunctionCompiles ChildElab types (mapping owner) declaration
        {compiled with inputs := compiled.inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)} ↔
      ComputationFunctionCompiles ChildElab types owner declaration compiled := by
  constructor
  · intro evidence
    exact ⟨evidence.header, (runtimeParametersDeclare_mapOwner_iff mapping injective).mp evidence.parameters,
      (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mp evidence.body⟩
  · intro evidence
    exact ⟨evidence.header, (runtimeParametersDeclare_mapOwner_iff mapping injective).mpr evidence.parameters,
      (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mpr evidence.body⟩

/-- Independent preparation keeps the original actual arguments and every
record field except the explicitly relabeled local input identities. -/
theorem computationFunctionPrepares_mapOwner_iff
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction} :
    ComputationFunctionPrepares ChildElab types (mapping owner) declaration arguments
        {prepared with inputs := prepared.inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)} ↔
      ComputationFunctionPrepares ChildElab types owner declaration arguments prepared := by
  constructor
  · intro evidence
    refine ⟨evidence.header, (runtimeParametersBind_mapOwner_iff mapping injective).mp evidence.parameters, ?_⟩
    exact (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mp
      (by simpa only [LocalInputs.toTypeInputs_mapIds] using evidence.body)
  · intro evidence
    refine ⟨evidence.header, (runtimeParametersBind_mapOwner_iff mapping injective).mpr evidence.parameters, ?_⟩
    simpa only [LocalInputs.toTypeInputs_mapIds] using
      (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mpr evidence.body

variable (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (covariance : ∀ table context source,
      checkChild (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source =
        checkChild table context source)
include covariance

/-- Complete optional compilation is mapped, including absence; the same
arbitrary child checker supplies covariance only for this owner map. -/
theorem compileComputationFunction?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) :
    compileComputationFunction? checkChild types (mapping owner) declaration =
      (compileComputationFunction? checkChild types owner declaration).map
        (fun compiled => {compiled with inputs := (compiled.inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective))}) := by
  unfold compileComputationFunction?
  rw [declareRuntimeParameters?_mapOwner mapping injective]
  cases interpretRuntimeFunctionHeader? types declaration.value.signature <;>
    cases declareRuntimeParameters? types owner declaration.value.signature.parameters.elements <;>
    simp only [bind, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some]
  rw [elaborateComputationReturnTree?_mapOwner mapping injective checkChild covariance]
  cases elaborateComputationReturnTree? checkChild types owner _ declaration.value.body with
  | none => rfl
  | some result => rcases result with ⟨core,type⟩; dsimp; split <;> rfl

/-- Complete optional preparation preserves actual bound rows and captures.
No structural argument value or parameter inhabitant is reconstructed. -/
theorem prepareComputationFunction?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    prepareComputationFunction? checkChild types (mapping owner) declaration arguments =
      (prepareComputationFunction? checkChild types owner declaration arguments).map
        (fun prepared => {prepared with inputs := (prepared.inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective))}) := by
  unfold prepareComputationFunction?
  rw [bindRuntimeParameters?_mapOwner mapping injective]
  cases interpretRuntimeFunctionHeader? types declaration.value.signature <;>
    cases bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments <;>
    simp only [bind, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some]
  rw [LocalInputs.toTypeInputs_mapIds, elaborateComputationReturnTree?_mapOwner mapping injective checkChild covariance]
  cases elaborateComputationReturnTree? checkChild types owner _ declaration.value.body with
  | none => rfl
  | some result => rcases result with ⟨core,type⟩; dsimp; split <;> rfl

/-- Equal Core and actual value sequences retain the full result at the same
fuel and store, including faults and checkpoints; this is not a safety claim. -/
theorem runComputationFunction?_mapOwner (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? checkChild types (mapping owner) declaration arguments fuel store =
      runComputationFunction? checkChild types owner declaration arguments fuel store := by
  unfold runComputationFunction?
  rw [prepareComputationFunction?_mapOwner mapping injective checkChild covariance]
  cases prepareComputationFunction? checkChild types owner declaration arguments <;>
    simp only [Option.map_none, Option.map_some, bind, Option.bind_none, Option.bind_some,
      LocalInputs.mapIds_environment, Resolved.LocalScope.values_mapIds]

end Solcore.Frontend
