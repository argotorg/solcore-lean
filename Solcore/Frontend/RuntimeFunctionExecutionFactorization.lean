import Solcore.Frontend.RuntimeFunctionPreparationFactorization

/-! Exact execution through value-free compilation uses the actual supplied
argument values in reverse source order. The unchanged runner retains every
stateful result, including suspended states; compilation and the ordered type
guard retain the whole entry contract. No additional runner is defined. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Independent compilation and matching typed arguments determine the complete
initial machine state, not only its inferred type or eventual return value. -/
theorem RuntimeFunctionCompiles.run_eq {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types owner declaration arguments fuel store =
      some (compiled.returnType, Core.runStateful fuel
        (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store)) := by
  obtain ⟨prepared, preparation, erased⟩ := compilation.prepare_arguments arguments matchingTypes
  have valuesEq : Resolved.LocalScope.values prepared.inputs.environment =
      arguments.reverse.map (·.value) := by
    simpa only [Resolved.LocalScope.values, LocalInputs.environment, List.map_map,
      Function.comp_def] using preparation.parameters.argument_values
  have coreEq : prepared.core = compiled.core := congrArg CompiledRuntimeFunction.core erased
  have typeEq : prepared.returnType = compiled.returnType :=
    congrArg CompiledRuntimeFunction.returnType erased
  simp only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some,
    pure, valuesEq, coreEq, typeEq]

/-- Failure is exact as well: failed compilation or a mismatched ordered type
list rejects preparation, while acceptance preserves the full Core result. -/
theorem runRuntimeFunction?_factorization (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types owner declaration arguments fuel store =
      (do
        let compiled ← compileRuntimeFunction? types owner declaration
        if arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse then
          some (compiled.returnType, Core.runStateful fuel
            (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store))
        else none) := by
  cases compiledResult : compileRuntimeFunction? types owner declaration with
  | none =>
      have rejected : prepareRuntimeFunction? types owner declaration arguments = none := by
        cases preparedResult : prepareRuntimeFunction? types owner declaration arguments with
        | none => rfl
        | some prepared =>
            have projected := prepareRuntimeFunction?_factorization types owner declaration arguments
            simp only [preparedResult, Option.map_some, compiledResult, bind, Option.bind_none,
              reduceCtorEq] at projected
      simp only [runRuntimeFunction?, rejected, bind, Option.bind_none]
  | some compiled =>
      by_cases matching : arguments.map (·.type) =
          (Resolved.LocalScope.values compiled.inputs.context).reverse
      · simpa only [bind, Option.bind_some, matching, ↓reduceIte] using
          (compileRuntimeFunction?_sound compiledResult).run_eq arguments matching fuel store
      · have rejected : prepareRuntimeFunction? types owner declaration arguments = none := by
          cases preparedResult : prepareRuntimeFunction? types owner declaration arguments with
          | none => rfl
          | some prepared =>
              have projected := prepareRuntimeFunction?_factorization types owner declaration arguments
              simp only [preparedResult, Option.map_some, compiledResult, bind, Option.bind_some,
                matching, ↓reduceIte, reduceCtorEq] at projected
        simp only [runRuntimeFunction?, rejected, bind, Option.bind_none,
          Option.bind_some, matching, ↓reduceIte]

/-- Successful optional execution has independent compilation provenance,
the exact supplied argument guard, and the exact actual Core execution. -/
theorem runRuntimeFunction?_eq_some_compiled_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {fuel : Nat} {store : Core.Store}
    {returnType : Core.Ty} {result : Core.StatefulRunResult} :
    runRuntimeFunction? types owner declaration arguments fuel store = some (returnType, result) ↔
      ∃ compiled, RuntimeFunctionCompiles types owner declaration compiled ∧
        arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse ∧
        returnType = compiled.returnType ∧
        Core.runStateful fuel (Core.State.initial compiled.core
          (arguments.reverse.map (·.value)) store) = result := by
  rw [runRuntimeFunction?_factorization]
  simp only [bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨compiled, accepted, execution⟩
    split at execution
    next matching =>
      obtain ⟨typeEq, resultEq⟩ := Prod.mk.inj (Option.some.inj execution)
      exact ⟨compiled, compileRuntimeFunction?_sound accepted, matching, typeEq.symm, resultEq⟩
    next => cases execution
  · rintro ⟨compiled, compilation, matching, typeEq, execution⟩
    exact ⟨compiled, compilation.complete, by simp only [matching, ↓reduceIte, typeEq, execution]⟩

end Solcore.Frontend
