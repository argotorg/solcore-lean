import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.LocalComputation

/-! Runtime computation-function compilation, entry, and factorization. -/

/-!
## Consolidated module: `Solcore.Frontend.RuntimeComputationFunctionCompilation`
-/

/-! Value-free compilation of original mixed bodies under the unchanged header
and parameter policy. Reusing an output record does not grant old provenance. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeComputationFunctionCompiles (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature compiled.returnType
  parameters : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements
    compiled.inputs
  body : LocalComputationReturnTreeElaborates types owner compiled.inputs
    declaration.value.body compiled.core compiled.returnType

def compileRuntimeComputationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) : Option CompiledRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← declareRuntimeParameters? types owner declaration.value.signature.parameters.elements
  let (core, inferredType) ← elaborateLocalComputationReturnTree? types owner inputs declaration.value.body
  if inferredType = returnType then return { inputs, core, returnType }
  else none

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeComputationFunctionEntry`
-/

/-! Original actual arguments prepare a separate mixed-body entry. The same
input record supplies the type-only view and the actual runtime environment. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeComputationFunctionPrepares (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature prepared.returnType
  parameters : RuntimeParametersBind types owner declaration.value.signature.parameters.elements
    arguments prepared.inputs
  body : LocalComputationReturnTreeElaborates types owner prepared.inputs.toTypeInputs
    declaration.value.body prepared.core prepared.returnType

def prepareRuntimeComputationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option PreparedRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
  let (core, inferredType) ← elaborateLocalComputationReturnTree? types owner inputs.toTypeInputs declaration.value.body
  if inferredType = returnType then return { inputs, core, returnType }
  else none

/-- The separately supplied store is not checked by structural preparation.
Keep every present Core result, including faults and actual suspended states. -/
def runRuntimeComputationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let prepared ← prepareRuntimeComputationFunction? types owner declaration arguments
  return (prepared.returnType, Core.runStateful fuel
    (Core.State.initial prepared.core prepared.inputs.environment.values store))

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeComputationFunctionProperties`
-/

/-! Exact whole-record success is characterized by this profile's independent
header, parameter and mixed-body evidence. Actual preparation retains its own
input record; neither erasure nor old entry provenance supplies runtime values. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem compileRuntimeComputationFunction?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileRuntimeComputationFunction? types owner declaration = some compiled ↔
      RuntimeComputationFunctionCompiles types owner declaration compiled := by
  constructor
  · intro accepted
    simp only [compileRuntimeComputationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
    obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
    split at result
    next same =>
      change inferredType = returnType at same
      subst inferredType
      cases result
      exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, declareRuntimeParameters?_sound parameters,
        elaborateLocalComputationReturnTree?_iff.mp body⟩
    next => cases result
  · intro compilation
    simp only [compileRuntimeComputationFunction?, interpretRuntimeFunctionHeader?_iff.mpr compilation.header,
      compilation.parameters.complete, elaborateLocalComputationReturnTree?_iff.mpr compilation.body,
      bind, Option.bind_some, ↓reduceIte, pure]

theorem prepareRuntimeComputationFunction?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareRuntimeComputationFunction? types owner declaration arguments = some prepared ↔
      RuntimeComputationFunctionPrepares types owner declaration arguments prepared := by
  constructor
  · intro accepted
    simp only [prepareRuntimeComputationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
    obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
    split at result
    next same =>
      change inferredType = returnType at same
      subst inferredType
      cases result
      exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, bindRuntimeParameters?_sound parameters,
        elaborateLocalComputationReturnTree?_iff.mp body⟩
    next => cases result
  · intro preparation
    simp only [prepareRuntimeComputationFunction?, interpretRuntimeFunctionHeader?_iff.mpr preparation.header,
      preparation.parameters.complete, elaborateLocalComputationReturnTree?_iff.mpr preparation.body,
      bind, Option.bind_some, ↓reduceIte, pure]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeComputationFunctionFactorizationProperties`
-/

/-! Static compilation and the original ordered argument types account for
every preparation failure. Execution additionally retains the actual supplied
values, reversed once, and every Core result for the separately supplied store. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem compiles_of_prepares
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeComputationFunctionPrepares types owner declaration arguments prepared) :
    RuntimeComputationFunctionCompiles types owner declaration prepared.toCompiled :=
  ⟨preparation.header, preparation.parameters.erase_values, preparation.body⟩

private theorem compilation_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {left right : CompiledRuntimeFunction}
    (first : RuntimeComputationFunctionCompiles types owner declaration left)
    (second : RuntimeComputationFunctionCompiles types owner declaration right) : left = right :=
  Option.some.inj ((compileRuntimeComputationFunction?_iff.mpr first).symm.trans
    (compileRuntimeComputationFunction?_iff.mpr second))

private theorem reconstruct
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeComputationFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matching : arguments.map (·.type) = compiled.inputs.context.values.reverse) :
    ∃ prepared, RuntimeComputationFunctionPrepares types owner declaration arguments prepared ∧
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
    (preparation : RuntimeComputationFunctionPrepares types owner declaration arguments prepared) :
    arguments.map (·.type) = prepared.toCompiled.inputs.context.values.reverse := by
  have layout := congrArg List.reverse preparation.parameters.argument_types.symm
  simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_context,
    Resolved.LocalScope.values, LocalInputs.context, List.map_map, Function.comp_def,
    List.map_reverse, List.reverse_reverse] using layout

private theorem reject_of_compile_none
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} (arguments : List TypedRuntimeArgument)
    (rejected : compileRuntimeComputationFunction? types owner declaration = none) :
    prepareRuntimeComputationFunction? types owner declaration arguments = none := by
  cases accepted : prepareRuntimeComputationFunction? types owner declaration arguments with
  | none => rfl
  | some prepared =>
      have compilation := compiles_of_prepares (prepareRuntimeComputationFunction?_iff.mp accepted)
      have compiled := compileRuntimeComputationFunction?_iff.mpr compilation
      rw [rejected] at compiled
      cases compiled

private theorem reject_of_mismatch
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeComputationFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (mismatch : arguments.map (·.type) ≠ compiled.inputs.context.values.reverse) :
    prepareRuntimeComputationFunction? types owner declaration arguments = none := by
  cases accepted : prepareRuntimeComputationFunction? types owner declaration arguments with
  | none => rfl
  | some prepared =>
      have preparation := prepareRuntimeComputationFunction?_iff.mp accepted
      have erased := compilation_unique (compiles_of_prepares preparation) compilation
      have matching := matching_of_prepares preparation
      rw [erased] at matching
      exact False.elim (mismatch matching)

theorem prepareRuntimeComputationFunction?_factorization
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    (prepareRuntimeComputationFunction? types owner declaration arguments).map PreparedRuntimeFunction.toCompiled =
      (do
        let compiled ← compileRuntimeComputationFunction? types owner declaration
        if arguments.map (·.type) = compiled.inputs.context.values.reverse then
          some compiled
        else none) := by
  cases compiledResult : compileRuntimeComputationFunction? types owner declaration with
  | none =>
      simp only [reject_of_compile_none arguments compiledResult, Option.map_none, bind, Option.bind_none]
  | some compiled =>
      have compilation := compileRuntimeComputationFunction?_iff.mp compiledResult
      by_cases matching : arguments.map (·.type) = compiled.inputs.context.values.reverse
      · obtain ⟨prepared, preparation, erased⟩ := reconstruct compilation arguments matching
        simp only [prepareRuntimeComputationFunction?_iff.mpr preparation, Option.map_some,
          erased, bind, Option.bind_some, matching, ↓reduceIte]
      · simp only [reject_of_mismatch compilation arguments matching, Option.map_none,
          bind, Option.bind_some, matching, ↓reduceIte]

/-- The type guard does not reject same-typed value swaps. Actual arguments,
not their erased projection, determine the full runtime result and checkpoint. -/
theorem runRuntimeComputationFunction?_factorization
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeComputationFunction? types owner declaration arguments fuel store =
      (do
        let compiled ← compileRuntimeComputationFunction? types owner declaration
        if arguments.map (·.type) = compiled.inputs.context.values.reverse then
          some (compiled.returnType, Core.runStateful fuel
            (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store))
        else none) := by
  cases compiledResult : compileRuntimeComputationFunction? types owner declaration with
  | none =>
      simp only [runRuntimeComputationFunction?, reject_of_compile_none arguments compiledResult,
        bind, Option.bind_none]
  | some compiled =>
      have compilation := compileRuntimeComputationFunction?_iff.mp compiledResult
      by_cases matching : arguments.map (·.type) = compiled.inputs.context.values.reverse
      · obtain ⟨prepared, preparation, erased⟩ := reconstruct compilation arguments matching
        have coreEq : prepared.core = compiled.core := congrArg CompiledRuntimeFunction.core erased
        have typeEq : prepared.returnType = compiled.returnType := congrArg CompiledRuntimeFunction.returnType erased
        have valuesEq : prepared.inputs.environment.values = arguments.reverse.map (·.value) := by
          simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map, Function.comp_def]
            using preparation.parameters.argument_values
        simp only [runRuntimeComputationFunction?, prepareRuntimeComputationFunction?_iff.mpr preparation,
          bind, Option.bind_some, pure, coreEq, typeEq, valuesEq, matching, ↓reduceIte]
      · simp only [runRuntimeComputationFunction?, reject_of_mismatch compilation arguments matching,
          bind, Option.bind_none, Option.bind_some, matching, ↓reduceIte]

end Solcore.Frontend
