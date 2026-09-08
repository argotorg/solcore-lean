import Solcore.Frontend.RuntimeFunctionExecutionFactorization
import Solcore.Frontend.RuntimeFunctionEntryExecutionProperties

/-! Independent entry costs describe the actual compiled Core with the actual
supplied argument values. Compilation provenance remains mandatory; an arbitrary
compiled record and an argument-type match alone do not establish safety. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace RuntimeFunctionEvaluatesWithCost

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
  {compiled : CompiledRuntimeFunction} {initialStore finalStore : Core.Store}
  {type : Core.Ty} {value : Core.Value} {cost fuel : Nat}

/-- Cost evidence already supplies the ordered argument guard and the declared
result type for every independent compilation of this same declaration. -/
theorem compiled_contract
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse ∧
      type = compiled.returnType := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation _ =>
      have same : prepared.toCompiled = compiled := preparation.compiles.result_unique compilation
      exact ⟨(runtimeFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, same⟩).2,
        congrArg CompiledRuntimeFunction.returnType same⟩

/-- The source cost fixes a Core path, not just a terminal observation. The
runtime environment is the reversed list of supplied values, not invented data. -/
theorem compiled_toSteps
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    Core.Steps cost
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore)
      (Core.State.final value finalStore) := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      have same : prepared.toCompiled = compiled := preparation.compiles.result_unique compilation
      have coreEq : prepared.core = compiled.core := congrArg CompiledRuntimeFunction.core same
      have valuesEq : Resolved.LocalScope.values prepared.inputs.environment =
          arguments.reverse.map (·.value) := by
        simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map,
          Function.comp_def] using preparation.parameters.argument_values
      rw [← LocalInputs.toTypeInputs_names prepared.inputs] at bodyCost
      simpa only [coreEq, valuesEq] using
        bodyCost.checked_toSteps preparation.body.complete
          (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.sameIds)

theorem compiled_run_done_iff
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    Core.runStateful fuel
        (Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore) =
      .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.compiled_toSteps compilation).runStateful_done_iff

theorem compiled_run_outOfFuel_iff
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    (∃ suspended, Core.runStateful fuel
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore) =
        .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.compiled_toSteps compilation).runStateful_outOfFuel_iff

end RuntimeFunctionEvaluatesWithCost

/-- Actual typed arguments matching a proven compilation supply a typed result
and both exact compiled-Core fuel boundaries. No inhabitance is inferred from
the static parameter types, and the initial store remains arbitrary. -/
theorem RuntimeFunctionCompiles.typed_compiled_execution
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) =
      (Resolved.LocalScope.values compiled.inputs.context).reverse) (store : Core.Store) :
    ∃ value cost, RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        store compiled.returnType value store cost ∧ Core.ValueHasType value compiled.returnType ∧
      ∀ fuel,
        (Core.runStateful fuel
          (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) =
            .done value store ↔ cost ≤ fuel) ∧
        ((∃ suspended, Core.runStateful fuel
          (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) =
            .outOfFuel suspended) ↔ fuel < cost) := by
  obtain ⟨prepared, preparation, same⟩ := compilation.prepare_arguments arguments matchingTypes
  have returnEq : prepared.returnType = compiled.returnType :=
    congrArg CompiledRuntimeFunction.returnType same
  obtain ⟨value, cost, evaluation, valueTyped, _⟩ := preparation.hasType.typed_cost_execution store
  have compiledEvaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      store compiled.returnType value store cost := returnEq ▸ evaluation
  exact ⟨value, cost, compiledEvaluation, returnEq ▸ valueTyped,
    fun _ => ⟨compiledEvaluation.compiled_run_done_iff compilation,
      compiledEvaluation.compiled_run_outOfFuel_iff compilation⟩⟩

/-- Only independently compiled records receive this safety guarantee. The
argument guard checks arity and type order; it is not a substitute for provenance. -/
theorem RuntimeFunctionCompiles.compiled_never_faults
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) =
      (Resolved.LocalScope.values compiled.inputs.context).reverse)
    (fuel : Nat) (store : Core.Store) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful fuel
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) ≠
        .fault error faultState := by
  intro fault
  have entryFault := (compilation.run_eq arguments matchingTypes fuel store).trans
    (congrArg (fun result => some (compiled.returnType, result)) fault)
  exact runRuntimeFunction?_never_faults types owner declaration arguments fuel store
    compiled.returnType error faultState entryFault

end Solcore.Frontend
