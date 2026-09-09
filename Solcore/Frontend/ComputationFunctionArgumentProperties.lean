import Solcore.Frontend.ComputationFunctionCompilation
import Solcore.Frontend.ComputationFunctionEntry
import Solcore.Frontend.RuntimeFunctionPreparationFactorization

/-! Independent preparation and compilation factor through the supplied actual
arguments for the same arbitrary child elaboration. Preserve original values,
captures and argument order without a checker, invented inhabitants or runtime world. -/

set_option autoImplicit false
namespace Solcore.Frontend
variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}

/-- Erasing actual values preserves independent compilation of the exact record. -/
theorem ComputationFunctionPrepares.compiles {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared) :
    ComputationFunctionCompiles ChildElab types owner declaration prepared.toCompiled :=
  ⟨preparation.header, preparation.parameters.erase_values, preparation.body⟩

/-- Reconstruct preparation from the supplied typed arguments, preserving the
compiled projection. The type equation fixes arity and original argument order. -/
theorem ComputationFunctionCompiles.prepare_arguments {compiled : CompiledRuntimeFunction}
    (compilation : ComputationFunctionCompiles ChildElab types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matching : arguments.map (·.type) = compiled.inputs.context.values.reverse) :
    ∃ prepared, ComputationFunctionPrepares ChildElab types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled := by
  obtain ⟨inputs, bound, erased⟩ := compilation.parameters.bind_typed_arguments arguments matching
  refine ⟨⟨inputs, compiled.core, compiled.returnType⟩, ⟨compilation.header, bound, ?_⟩, ?_⟩
  · simpa only [erased] using compilation.body
  · simp only [PreparedRuntimeFunction.toCompiled, erased]

/-- A fixed compiled projection is preparable exactly when independent compilation
holds and the supplied argument types match; the record alone is insufficient. -/
theorem computationFunctionPrepares_toCompiled_iff {arguments : List TypedRuntimeArgument}
    {compiled : CompiledRuntimeFunction} :
    (∃ prepared, ComputationFunctionPrepares ChildElab types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled) ↔
    ComputationFunctionCompiles ChildElab types owner declaration compiled ∧
      arguments.map (·.type) = compiled.inputs.context.values.reverse := by
  constructor
  · rintro ⟨prepared, preparation, rfl⟩
    refine ⟨preparation.compiles, ?_⟩
    have layout := congrArg List.reverse preparation.parameters.argument_types.symm
    simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_context,
      Resolved.LocalScope.values, LocalInputs.context, List.map_map, Function.comp_def,
      List.map_reverse, List.reverse_reverse] using layout
  · rintro ⟨compilation, matching⟩
    exact compilation.prepare_arguments arguments matching

/-- Preparation retains the supplied actual values and captures, reversed once
into the input environment. -/
theorem ComputationFunctionPrepares.argument_values {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab types owner declaration arguments prepared) :
    prepared.inputs.environment.values = arguments.reverse.map (·.value) := by
  simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map, Function.comp_def]
    using preparation.parameters.argument_values

/-- For the same actual arguments, equal compiled projections give equal prepared
records. No uniqueness of the arbitrary child elaboration is assumed. -/
theorem ComputationFunctionPrepares.unique_of_toCompiled_eq {arguments : List TypedRuntimeArgument}
    {left right : PreparedRuntimeFunction}
    (first : ComputationFunctionPrepares ChildElab types owner declaration arguments left)
    (second : ComputationFunctionPrepares ChildElab types owner declaration arguments right)
    (erased : left.toCompiled = right.toCompiled) : left = right := by
  have sameInputs := RuntimeParametersBindFrom.result_unique first.parameters second.parameters
  have sameCore : left.core = right.core := congrArg CompiledRuntimeFunction.core erased
  have sameType : left.returnType = right.returnType := congrArg CompiledRuntimeFunction.returnType erased
  cases left; cases right; cases sameInputs; cases sameCore; cases sameType; rfl

end Solcore.Frontend
