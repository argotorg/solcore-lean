import Solcore.Frontend.ComputationFunctionEntry
import Solcore.Frontend.ComputationReturnTreeRuntimeWorldProperties
import Solcore.Frontend.RuntimeParametersLayout

/-! Checkpoint safety of the literal prepared Core state uses only child Core
typing and one runtime world for actual arguments, store and typed caller frames.
The caller result type may differ from the prepared return type. No checker,
source cost, termination or optional-runner acceptance is inferred. -/

set_option autoImplicit false
namespace Solcore.Frontend

private theorem arguments_runtime_environment {world : Core.StoreTyping}
    (arguments : List TypedRuntimeArgument)
    (typed : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type) :
    Core.RuntimeEnvironmentHasTypes world (arguments.map (·.value)) (arguments.map (·.type)) := by
  revert typed
  induction arguments with
  | nil => intro _; exact .nil
  | cons argument arguments ih =>
      intro typed
      exact .cons (typed argument (by simp)) (ih (fun value member => typed value (by simp [member])))

private theorem prepared_runtime_environment {world : Core.StoreTyping}
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    {inputs : LocalInputs} (bound : RuntimeParametersBind types owner parameters arguments inputs)
    (typed : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type) :
    Core.RuntimeEnvironmentHasTypes world inputs.environment.values inputs.context.values := by
  have reversed := arguments_runtime_environment arguments.reverse
    (fun argument member => typed argument (List.mem_reverse.mp member))
  simpa only [LocalInputs.environment, LocalInputs.context, Resolved.LocalScope.values,
    List.map_map, Function.comp_def, bound.argument_values, bound.argument_types] using reversed

/-- Preserve typing and exclude faults for the literal initial state, every
genuine checkpoint, and every additional fuel from that saved state. -/
theorem ComputationFunctionPrepares.runtime_checkpoint_safety
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared)
    {world : Core.StoreTyping} {store : Core.Store}
    (argumentsTyped : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type)
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation prepared.returnType resultType) :
    Core.StateHasType ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩ resultType ∧
      (∀ fuel error faultState, Core.runStateful fuel
        ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩ ≠ .fault error faultState) ∧
      ∀ {spent checkpoint}, Core.runStateful spent
        ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩ = .outOfFuel checkpoint →
        Core.StateHasType checkpoint resultType ∧
          ∀ additional error faultState,
            Core.runStateful additional checkpoint ≠ .fault error faultState := by
  have environmentTyped := prepared_runtime_environment preparation.parameters argumentsTyped
  exact preparation.body.runtime_checkpoint_safety childCoreType
    (by simpa only [LocalInputs.toTypeInputs_context] using environmentTyped) storeTyped continuationTyped

/-- A genuine saved store has an existential extension of the supplied world;
every further path extends that same saved world and retains store typing. -/
theorem ComputationFunctionPrepares.runtime_checkpoint_world_extension
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared)
    {world : Core.StoreTyping} {store : Core.Store}
    (argumentsTyped : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type)
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation prepared.returnType resultType)
    {spent : Nat} {checkpoint : Core.State}
    (exhausted : Core.runStateful spent
      ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩ = .outOfFuel checkpoint) :
    ∃ savedWorld, Core.WorldExtends world savedWorld ∧ Core.StoreHasTypes savedWorld checkpoint.store ∧
      ∀ {steps next}, Core.Steps steps checkpoint next →
        ∃ future, Core.WorldExtends savedWorld future ∧ Core.StoreHasTypes future next.store := by
  have environmentTyped := prepared_runtime_environment preparation.parameters argumentsTyped
  exact preparation.body.runtime_checkpoint_world_extension childCoreType
    (by simpa only [LocalInputs.toTypeInputs_context] using environmentTyped) storeTyped continuationTyped exhausted

end Solcore.Frontend
