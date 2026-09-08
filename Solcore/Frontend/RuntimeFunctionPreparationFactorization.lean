import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Frontend.RuntimeFunctionEntryProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.RuntimeParametersLayout

/-! Value-free compilation factors the existing runtime preparation exactly.
Reconstruction uses the supplied typed arguments, never invented inhabitants.
The type-list guard retains argument count and source order. -/

set_option autoImplicit false

namespace Solcore.Frontend

def PreparedRuntimeFunction.toCompiled (prepared : PreparedRuntimeFunction) : CompiledRuntimeFunction :=
  { inputs := prepared.inputs.toTypeInputs, core := prepared.core, returnType := prepared.returnType }

theorem RuntimeFunctionPrepares.compiles {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    RuntimeFunctionCompiles types owner declaration prepared.toCompiled := by
  refine ⟨preparation.header, preparation.parameters.erase_values, ?_⟩
  simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_names,
    LocalInputs.toTypeInputs_context] using preparation.body

theorem RuntimeFunctionCompiles.prepare_arguments {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse) :
    ∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled := by
  obtain ⟨inputs, bound, erased⟩ := compilation.parameters.bind_typed_arguments arguments matchingTypes
  have namesEq : inputs.names = compiled.inputs.names := by
    rw [← LocalInputs.toTypeInputs_names, erased]
  have contextEq : inputs.context = compiled.inputs.context := by
    rw [← LocalInputs.toTypeInputs_context, erased]
  refine ⟨⟨inputs, compiled.core, compiled.returnType⟩,
    ⟨compilation.header, bound, ?_⟩, ?_⟩
  · simpa only [namesEq, contextEq] using compilation.body
  · simp only [PreparedRuntimeFunction.toCompiled, erased]

/-- A compiled record needs independent compilation evidence as well as the
exact supplied argument types; the record alone does not imply preparation. -/
theorem runtimeFunctionPrepares_toCompiled_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {compiled : CompiledRuntimeFunction} :
    (∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled) ↔
    RuntimeFunctionCompiles types owner declaration compiled ∧
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

/-- Equality includes failure: static compilation and the ordered type guard
account for every rejection of the unchanged runtime preparation endpoint. -/
theorem prepareRuntimeFunction?_factorization (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    (prepareRuntimeFunction? types owner declaration arguments).map PreparedRuntimeFunction.toCompiled =
      (do
        let compiled ← compileRuntimeFunction? types owner declaration
        if arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse then
          some compiled
        else none) := by
  cases compiledResult : compileRuntimeFunction? types owner declaration with
  | none =>
      have rejected : prepareRuntimeFunction? types owner declaration arguments = none := by
        apply prepareRuntimeFunction?_eq_none_iff.mpr
        rintro ⟨prepared, preparation⟩
        have accepted := preparation.compiles.complete
        rw [compiledResult] at accepted
        cases accepted
      simp only [rejected, Option.map_none, bind, Option.bind_none]
  | some compiled =>
      have compilation := compileRuntimeFunction?_sound compiledResult
      by_cases matching : arguments.map (·.type) =
          (Resolved.LocalScope.values compiled.inputs.context).reverse
      · obtain ⟨prepared, preparation, erased⟩ := compilation.prepare_arguments arguments matching
        simp only [preparation.complete, Option.map_some, erased, bind,
          Option.bind_some, matching, ↓reduceIte]
      · have rejected : prepareRuntimeFunction? types owner declaration arguments = none := by
          apply prepareRuntimeFunction?_eq_none_iff.mpr
          rintro ⟨prepared, preparation⟩
          have erased := preparation.compiles.result_unique compilation
          exact matching (runtimeFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, erased⟩).2
        simp only [rejected, Option.map_none, bind, Option.bind_some,
          matching, ↓reduceIte]

end Solcore.Frontend
