import Solcore.Frontend.ComputationFunctionProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization

/-! Operational factorization holds for every child checker. The private graph
supports these equations, not independent source semantics. Actual arguments
and every Core result for the separately supplied store are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

private def CheckGraph (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (table : LocalNameTable) (context : Resolved.Context) (source : Syntax.Expr)
    (core : Core.Expr) (type : Core.Ty) : Prop := checkChild table context source = some (core, type)

variable {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

private theorem checked_compile_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileComputationFunction? checkChild types owner declaration = some compiled ↔
      ComputationFunctionCompiles (CheckGraph checkChild) types owner declaration compiled :=
  compileComputationFunction?_iff (checkChild := checkChild) (ChildElab := CheckGraph checkChild) Iff.rfl

private theorem checked_prepare_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareComputationFunction? checkChild types owner declaration arguments = some prepared ↔
      ComputationFunctionPrepares (CheckGraph checkChild) types owner declaration arguments prepared :=
  prepareComputationFunction?_iff (checkChild := checkChild) (ChildElab := CheckGraph checkChild) Iff.rfl

private theorem compiles_of_prepares
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares (CheckGraph checkChild) types owner declaration arguments prepared) :
    ComputationFunctionCompiles (CheckGraph checkChild) types owner declaration prepared.toCompiled :=
  ⟨preparation.header, preparation.parameters.erase_values, preparation.body⟩

private theorem compilation_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {left right : CompiledRuntimeFunction}
    (first : ComputationFunctionCompiles (CheckGraph checkChild) types owner declaration left)
    (second : ComputationFunctionCompiles (CheckGraph checkChild) types owner declaration right) : left = right :=
  Option.some.inj ((checked_compile_iff.mpr first).symm.trans
    (checked_compile_iff.mpr second))

private theorem reconstruct
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : ComputationFunctionCompiles (CheckGraph checkChild) types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matching : arguments.map (·.type) = compiled.inputs.context.values.reverse) :
    ∃ prepared, ComputationFunctionPrepares (CheckGraph checkChild) types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled := by
  obtain ⟨inputs, bound, erased⟩ := compilation.parameters.bind_typed_arguments arguments matching
  refine ⟨⟨inputs, compiled.core, compiled.returnType⟩,
    ⟨compilation.header, bound, ?_⟩, ?_⟩
  · simpa only [erased] using compilation.body
  · simp only [PreparedRuntimeFunction.toCompiled, erased]

private theorem matching_of_prepares
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares (CheckGraph checkChild) types owner declaration arguments prepared) :
    arguments.map (·.type) = prepared.toCompiled.inputs.context.values.reverse := by
  have layout := congrArg List.reverse preparation.parameters.argument_types.symm
  simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_context,
    Resolved.LocalScope.values, LocalInputs.context, List.map_map, Function.comp_def,
    List.map_reverse, List.reverse_reverse] using layout

private theorem reject_of_compile_none
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} (arguments : List TypedRuntimeArgument)
    (rejected : compileComputationFunction? checkChild types owner declaration = none) :
    prepareComputationFunction? checkChild types owner declaration arguments = none := by
  cases accepted : prepareComputationFunction? checkChild types owner declaration arguments with
  | none => rfl
  | some prepared =>
      have compilation := compiles_of_prepares (checked_prepare_iff.mp accepted)
      have compiled := checked_compile_iff.mpr compilation
      rw [rejected] at compiled
      cases compiled

private theorem reject_of_mismatch
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : ComputationFunctionCompiles (CheckGraph checkChild) types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (mismatch : arguments.map (·.type) ≠ compiled.inputs.context.values.reverse) :
    prepareComputationFunction? checkChild types owner declaration arguments = none := by
  cases accepted : prepareComputationFunction? checkChild types owner declaration arguments with
  | none => rfl
  | some prepared =>
      have preparation := checked_prepare_iff.mp accepted
      have erased := compilation_unique (compiles_of_prepares preparation) compilation
      have matching := matching_of_prepares preparation
      rw [erased] at matching
      exact False.elim (mismatch matching)

theorem prepareComputationFunction?_factorization
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    (prepareComputationFunction? checkChild types owner declaration arguments).map PreparedRuntimeFunction.toCompiled =
      (do
        let compiled ← compileComputationFunction? checkChild types owner declaration
        if arguments.map (·.type) = compiled.inputs.context.values.reverse then
          some compiled
        else none) := by
  cases compiledResult : compileComputationFunction? checkChild types owner declaration with
  | none =>
      simp only [reject_of_compile_none arguments compiledResult, Option.map_none, bind, Option.bind_none]
  | some compiled =>
      have compilation := checked_compile_iff.mp compiledResult
      by_cases matching : arguments.map (·.type) = compiled.inputs.context.values.reverse
      · obtain ⟨prepared, preparation, erased⟩ := reconstruct compilation arguments matching
        simp only [checked_prepare_iff.mpr preparation, Option.map_some,
          erased, bind, Option.bind_some, matching, ↓reduceIte]
      · simp only [reject_of_mismatch compilation arguments matching, Option.map_none,
          bind, Option.bind_some, matching, ↓reduceIte]

/-- The type guard does not reject same-typed value swaps. Actual arguments,
not their erased projection, determine the full runtime result and checkpoint. -/
theorem runComputationFunction?_factorization
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) :
    runComputationFunction? checkChild types owner declaration arguments fuel store =
      (do
        let compiled ← compileComputationFunction? checkChild types owner declaration
        if arguments.map (·.type) = compiled.inputs.context.values.reverse then
          some (compiled.returnType, Core.runStateful fuel
            (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store))
        else none) := by
  cases compiledResult : compileComputationFunction? checkChild types owner declaration with
  | none =>
      simp only [runComputationFunction?, reject_of_compile_none arguments compiledResult,
        bind, Option.bind_none]
  | some compiled =>
      have compilation := checked_compile_iff.mp compiledResult
      by_cases matching : arguments.map (·.type) = compiled.inputs.context.values.reverse
      · obtain ⟨prepared, preparation, erased⟩ := reconstruct compilation arguments matching
        have coreEq : prepared.core = compiled.core := congrArg CompiledRuntimeFunction.core erased
        have typeEq : prepared.returnType = compiled.returnType := congrArg CompiledRuntimeFunction.returnType erased
        have valuesEq : prepared.inputs.environment.values = arguments.reverse.map (·.value) := by
          simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map, Function.comp_def]
            using preparation.parameters.argument_values
        simp only [runComputationFunction?, checked_prepare_iff.mpr preparation,
          bind, Option.bind_some, pure, coreEq, typeEq, valuesEq, matching, ↓reduceIte]
      · simp only [runComputationFunction?, reject_of_mismatch compilation arguments matching,
          bind, Option.bind_none, Option.bind_some, matching, ↓reduceIte]

end Solcore.Frontend
