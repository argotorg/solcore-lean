import Solcore.Frontend.ComputationFunctionProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeSafetyProperties
import Solcore.Frontend.RuntimeParametersLayout

/-! Original actual arguments and the supplied store share one runtime world.
Structural input records alone do not provide these premises. Preparation and
all runner outcomes retain the same exact record and reverse-once values. -/

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

theorem ComputationFunctionPrepares.runtime_typed_execution
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    {F : Core.Expr → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childInserts : ∀ {core}, F core → ∀ leading suffix inserted {initialStore finalStore value},
      Core.Evaluates (leading ++ inserted :: suffix) initialStore (core.weakenAt leading.length) value finalStore ↔
        Core.Evaluates (leading ++ suffix) initialStore core value finalStore)
    (childExecution : ∀ {table context environment source core type},
      ChildElab table context source core type → environment.ids = context.ids →
      ∀ {initialStore finalStore value}, ChildEval table environment initialStore source value finalStore ↔
        Core.Evaluates environment.values initialStore core value finalStore)
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    (childSteps : ∀ {table context environment initialStore finalStore source value cost},
      ChildCost table environment initialStore source value finalStore cost →
      ∀ {core type}, ChildElab table context source core type → environment.ids = context.ids →
      ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared)
    {world : Core.StoreTyping} {store : Core.Store}
    (argumentsTyped : ∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type)
    (storeTyped : Core.StoreHasTypes world store) :
    prepareComputationFunction? checkChild types owner declaration arguments = some prepared ∧
    ∃ finalWorld finalStore value cost,
      Core.WorldExtends world finalWorld ∧ Core.StoreHasTypes finalWorld finalStore ∧
      Core.RuntimeValueHasType finalWorld value prepared.returnType ∧
      ComputationReturnTreeEvaluatesWithCost ChildCost owner prepared.inputs.names prepared.inputs.environment
        store declaration.value.body value finalStore cost ∧
      (∀ continuation, Core.Steps cost
        ⟨.eval prepared.core prepared.inputs.environment.values, continuation, store⟩
        ⟨.ret value, continuation, finalStore⟩) ∧
      (∀ fuel, (Core.runStateful fuel (.initial prepared.core prepared.inputs.environment.values store) =
          .done value finalStore ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, Core.runStateful fuel (.initial prepared.core prepared.inputs.environment.values store) =
          .outOfFuel checkpoint) ↔ fuel < cost)) ∧
      ∀ fuel, runComputationFunction? checkChild types owner declaration arguments fuel store =
        some (prepared.returnType, Core.runStateful fuel (.initial prepared.core prepared.inputs.environment.values store)) := by
  have accepted := (prepareComputationFunction?_iff childCorrect).mpr preparation
  have environmentTyped := prepared_runtime_environment preparation.parameters argumentsTyped
  have sameIds : prepared.inputs.environment.ids = prepared.inputs.toTypeInputs.context.ids := by
    simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.sameIds
  have execution := ComputationReturnTreeElaborates.runtime_typed_execution (F := F)
    (ChildElab := ChildElab) (ChildEval := ChildEval) (ChildCost := ChildCost)
    childCoreType childMembership childWeakening childInserts childExecution childCostIff childPaths childSteps
    preparation.body sameIds (by simpa only [LocalInputs.toTypeInputs_context] using environmentTyped) storeTyped
  obtain ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, costed, paths, thresholds⟩ := execution
  refine ⟨accepted, finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, ?_, paths, thresholds, ?_⟩
  · simpa only [LocalInputs.toTypeInputs_names] using costed
  · intro fuel
    simp only [runComputationFunction?, accepted, bind, Option.bind_some, pure]

end Solcore.Frontend
