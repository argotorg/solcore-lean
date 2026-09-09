import Solcore.Frontend.RuntimeApplicationFunctionCompilationProperties
import Solcore.Frontend.RuntimeApplicationFunctionEntryProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization

/-! New whole-entry provenance factors through original static parameters and
the actual supplied arguments. Reusing the data projection does not reuse the
old body's safety, store or fuel contracts. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeApplicationFunctionPrepares.compiles
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeApplicationFunctionPrepares types owner declaration arguments prepared) :
    RuntimeApplicationFunctionCompiles types owner declaration prepared.toCompiled := by
  refine ⟨preparation.header, preparation.parameters.erase_values, ?_⟩
  simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_names,
    LocalInputs.toTypeInputs_context] using preparation.body

theorem RuntimeApplicationFunctionCompiles.prepare_arguments
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse) :
    ∃ prepared, RuntimeApplicationFunctionPrepares types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled := by
  obtain ⟨inputs, bound, erased⟩ := compilation.parameters.bind_typed_arguments arguments matchingTypes
  refine ⟨⟨inputs, compiled.core, compiled.returnType⟩, ⟨compilation.header, bound, ?_⟩, ?_⟩
  · change LocalApplicationReturnBodyElaborates inputs.names inputs.context
      declaration.value.body compiled.core compiled.returnType
    rw [← LocalInputs.toTypeInputs_names inputs, ← LocalInputs.toTypeInputs_context inputs, erased]
    exact compilation.body
  · simp only [PreparedRuntimeFunction.toCompiled, erased]

theorem runtimeApplicationFunctionPrepares_toCompiled_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {compiled : CompiledRuntimeFunction} :
    (∃ prepared, RuntimeApplicationFunctionPrepares types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled) ↔
      RuntimeApplicationFunctionCompiles types owner declaration compiled ∧
        arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse := by
  constructor
  · rintro ⟨prepared, preparation, rfl⟩
    refine ⟨preparation.compiles, ?_⟩
    have layout := congrArg List.reverse preparation.parameters.argument_types.symm
    simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_context,
      Resolved.LocalScope.values, LocalInputs.context, List.map_map, Function.comp_def,
      List.map_reverse, List.reverse_reverse] using layout
  · rintro ⟨compilation, matchingTypes⟩
    exact compilation.prepare_arguments arguments matchingTypes

/-- Include every failure and the original ordered argument-type guard. -/
theorem prepareRuntimeApplicationFunction?_factorization
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    (prepareRuntimeApplicationFunction? types owner declaration arguments).map PreparedRuntimeFunction.toCompiled =
      (do
        let compiled ← compileRuntimeApplicationFunction? types owner declaration
        if arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse then
          some compiled
        else none) := by
  cases compiledResult : compileRuntimeApplicationFunction? types owner declaration with
  | none =>
      have rejected : prepareRuntimeApplicationFunction? types owner declaration arguments = none := by
        apply prepareRuntimeApplicationFunction?_eq_none_iff.mpr
        rintro ⟨prepared, preparation⟩
        have accepted := preparation.compiles.complete
        rw [compiledResult] at accepted
        cases accepted
      simp only [rejected, Option.map_none, bind, Option.bind_none]
  | some compiled =>
      have compilation := compileRuntimeApplicationFunction?_sound compiledResult
      by_cases matching : arguments.map (·.type) =
          (Resolved.LocalScope.values compiled.inputs.context).reverse
      · obtain ⟨prepared, preparation, erased⟩ := compilation.prepare_arguments arguments matching
        simp only [preparation.complete, Option.map_some, erased, bind, Option.bind_some,
          matching, ↓reduceIte]
      · have rejected : prepareRuntimeApplicationFunction? types owner declaration arguments = none := by
          apply prepareRuntimeApplicationFunction?_eq_none_iff.mpr
          rintro ⟨prepared, preparation⟩
          have erased := preparation.compiles.result_unique compilation
          exact matching (runtimeApplicationFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, erased⟩).2
        simp only [rejected, Option.map_none, bind, Option.bind_some, matching, ↓reduceIte]

/-- The guard supplies actual values in source order; binding reverses them
once. This equality retains all outcomes and the supplied store, not just done. -/
theorem RuntimeApplicationFunctionCompiles.run_eq
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeApplicationFunction? types owner declaration arguments fuel store =
      some (compiled.returnType, Core.runStateful fuel
        (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store)) := by
  obtain ⟨prepared, preparation, erased⟩ := compilation.prepare_arguments arguments matchingTypes
  have coreEq : prepared.core = compiled.core := congrArg CompiledRuntimeFunction.core erased
  have returnEq : prepared.returnType = compiled.returnType := congrArg CompiledRuntimeFunction.returnType erased
  have valuesEq : Resolved.LocalScope.values prepared.inputs.environment = arguments.reverse.map (·.value) := by
    simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map, Function.comp_def]
      using preparation.parameters.argument_values
  simp only [runRuntimeApplicationFunction?, preparation.complete, bind, Option.bind_some, pure,
    coreEq, returnEq, valuesEq]

end Solcore.Frontend
