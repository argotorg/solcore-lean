import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.LocalApplication

/-! Runtime application-function compilation, entry, and factorization. -/

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionCompilation`
-/

/-! Value-free compilation for a separate original application-return entry.
The existing output record is data only; this profile has its own provenance. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeApplicationFunctionCompiles (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature compiled.returnType
  parameters : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements
    compiled.inputs
  body : LocalApplicationReturnBodyElaborates compiled.inputs.names compiled.inputs.context
    declaration.value.body compiled.core compiled.returnType

def compileRuntimeApplicationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) : Option CompiledRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← declareRuntimeParameters? types owner declaration.value.signature.parameters.elements
  let (core, inferredType) ← elaborateLocalApplicationReturnBody? inputs.names inputs.context declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionCompilationProperties`
-/

/-! Exact value-free compilation belongs to this application-return profile.
The shared data record supplies no old compilation or runtime safety evidence. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeApplicationFunctionCompiles.complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled) :
    compileRuntimeApplicationFunction? types owner declaration = some compiled := by
  simp only [compileRuntimeApplicationFunction?, interpretRuntimeFunctionHeader?_iff.mpr compilation.header,
    compilation.parameters.complete, compilation.body.complete, bind, Option.bind_some,
    ↓reduceIte, pure]

theorem compileRuntimeApplicationFunction?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (accepted : compileRuntimeApplicationFunction? types owner declaration = some compiled) :
    RuntimeApplicationFunctionCompiles types owner declaration compiled := by
  simp only [compileRuntimeApplicationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
  split at result
  next same =>
    change inferredType = returnType at same
    subst inferredType
    cases result
    exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, declareRuntimeParameters?_sound parameters,
      elaborateLocalApplicationReturnBody?_sound body⟩
  next => cases result

theorem compileRuntimeApplicationFunction?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileRuntimeApplicationFunction? types owner declaration = some compiled ↔
      RuntimeApplicationFunctionCompiles types owner declaration compiled :=
  ⟨compileRuntimeApplicationFunction?_sound, RuntimeApplicationFunctionCompiles.complete⟩

/-- Independent parameter identity and exact original body evidence determine
the entire record, not just a Core expression with the same result type. -/
theorem RuntimeApplicationFunctionCompiles.result_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {left right : CompiledRuntimeFunction}
    (first : RuntimeApplicationFunctionCompiles types owner declaration left)
    (second : RuntimeApplicationFunctionCompiles types owner declaration right) : left = right := by
  rcases left with ⟨leftInputs, leftCore, leftType⟩
  rcases right with ⟨rightInputs, rightCore, rightType⟩
  have sameInputs : leftInputs = rightInputs := first.parameters.result_unique second.parameters
  subst rightInputs
  obtain ⟨sameCore, sameType⟩ := first.body.result_unique second.body
  cases sameCore
  cases sameType
  rfl

theorem compileRuntimeApplicationFunction?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl} :
    compileRuntimeApplicationFunction? types owner declaration = none ↔
      ¬ ∃ compiled, RuntimeApplicationFunctionCompiles types owner declaration compiled := by
  constructor
  · intro rejected ⟨compiled, compilation⟩
    have accepted := compilation.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : compileRuntimeApplicationFunction? types owner declaration with
    | none => rfl
    | some compiled => exact False.elim (missing ⟨compiled, compileRuntimeApplicationFunction?_sound accepted⟩)

/-- The exact output remains open in the original parameter context. No actual
arguments, world, store or execution guarantee follow from this static law. -/
theorem RuntimeApplicationFunctionCompiles.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled) :
    Core.HasType (Resolved.LocalScope.values compiled.inputs.context) compiled.core compiled.returnType :=
  compilation.body.core_hasType

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionEntry`
-/

/-! A separate explicit whole-function entry using the original actual typed
arguments. Header, parameter and exact body evidence belong to this profile,
not to the unchanged pure/recursive entry sharing the data-only output record. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeApplicationFunctionPrepares (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature prepared.returnType
  parameters : RuntimeParametersBind types owner declaration.value.signature.parameters.elements
    arguments prepared.inputs
  body : LocalApplicationReturnBodyElaborates prepared.inputs.names prepared.inputs.context
    declaration.value.body prepared.core prepared.returnType

def prepareRuntimeApplicationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option PreparedRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
  let (core, inferredType) ← elaborateLocalApplicationReturnBody? inputs.names inputs.context declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

/-- Preserve faults and genuine exhaustion as present results. Structural
argument evidence does not validate the actual store or referenced locations. -/
def runRuntimeApplicationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let prepared ← prepareRuntimeApplicationFunction? types owner declaration arguments
  return (prepared.returnType, Core.runStateful fuel
    (Core.State.initial prepared.core (Resolved.LocalScope.values prepared.inputs.environment) store))

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionEntryProperties`
-/

/-! Exact whole-entry preparation fixes the actual input record and original
body Core. Full execution equations do not assert safety for arbitrary stores. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeApplicationFunctionPrepares.complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeApplicationFunctionPrepares types owner declaration arguments prepared) :
    prepareRuntimeApplicationFunction? types owner declaration arguments = some prepared := by
  simp only [prepareRuntimeApplicationFunction?, interpretRuntimeFunctionHeader?_iff.mpr preparation.header,
    preparation.parameters.complete, preparation.body.complete, bind, Option.bind_some,
    ↓reduceIte, pure]

theorem prepareRuntimeApplicationFunction?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (accepted : prepareRuntimeApplicationFunction? types owner declaration arguments = some prepared) :
    RuntimeApplicationFunctionPrepares types owner declaration arguments prepared := by
  simp only [prepareRuntimeApplicationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
  split at result
  next same =>
    change inferredType = returnType at same
    subst inferredType
    cases result
    exact ⟨interpretRuntimeFunctionHeader?_iff.mp header,
      bindRuntimeParameters?_sound parameters, elaborateLocalApplicationReturnBody?_sound body⟩
  next => cases result

theorem prepareRuntimeApplicationFunction?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareRuntimeApplicationFunction? types owner declaration arguments = some prepared ↔
      RuntimeApplicationFunctionPrepares types owner declaration arguments prepared :=
  ⟨prepareRuntimeApplicationFunction?_sound, RuntimeApplicationFunctionPrepares.complete⟩

/-- Independent actual binding and exact body provenance determine every field. -/
theorem RuntimeApplicationFunctionPrepares.result_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {left right : PreparedRuntimeFunction}
    (first : RuntimeApplicationFunctionPrepares types owner declaration arguments left)
    (second : RuntimeApplicationFunctionPrepares types owner declaration arguments right) : left = right := by
  rcases left with ⟨leftInputs, leftCore, leftType⟩
  rcases right with ⟨rightInputs, rightCore, rightType⟩
  have inputsEq : leftInputs = rightInputs := first.parameters.result_unique second.parameters
  subst rightInputs
  obtain ⟨coreEq, typeEq⟩ := first.body.result_unique second.body
  cases coreEq
  cases typeEq
  rfl

theorem prepareRuntimeApplicationFunction?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument} :
    prepareRuntimeApplicationFunction? types owner declaration arguments = none ↔
      ¬ ∃ prepared, RuntimeApplicationFunctionPrepares types owner declaration arguments prepared := by
  constructor
  · intro rejected ⟨prepared, preparation⟩
    have accepted := preparation.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : prepareRuntimeApplicationFunction? types owner declaration arguments with
    | none => rfl
    | some prepared => exact False.elim (missing ⟨prepared, prepareRuntimeApplicationFunction?_sound accepted⟩)

theorem RuntimeApplicationFunctionPrepares.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeApplicationFunctionPrepares types owner declaration arguments prepared) :
    Core.HasType (Resolved.LocalScope.values prepared.inputs.context) prepared.core prepared.returnType :=
  preparation.body.core_hasType

theorem runRuntimeApplicationFunction?_eq_some_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {fuel : Nat} {store : Core.Store}
    {type : Core.Ty} {result : Core.StatefulRunResult} :
    runRuntimeApplicationFunction? types owner declaration arguments fuel store = some (type, result) ↔
      ∃ prepared, RuntimeApplicationFunctionPrepares types owner declaration arguments prepared ∧
        prepared.returnType = type ∧ Core.runStateful fuel (Core.State.initial prepared.core
          (Resolved.LocalScope.values prepared.inputs.environment) store) = result := by
  simp only [runRuntimeApplicationFunction?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨prepared, accepted, same⟩
    cases same
    exact ⟨prepared, prepareRuntimeApplicationFunction?_iff.mp accepted, rfl, rfl⟩
  · rintro ⟨prepared, preparation, sameType, execution⟩
    exact ⟨prepared, preparation.complete, by simp only [sameType, execution]⟩

theorem runRuntimeApplicationFunction?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} (fuel : Nat) (store : Core.Store) :
    runRuntimeApplicationFunction? types owner declaration arguments fuel store = none ↔
      prepareRuntimeApplicationFunction? types owner declaration arguments = none := by
  cases prepared : prepareRuntimeApplicationFunction? types owner declaration arguments with
  | none => simp [runRuntimeApplicationFunction?, prepared]
  | some result => simp [runRuntimeApplicationFunction?, prepared]

/-- The whole original contract transports every body outcome unchanged,
including faults and the complete state of genuine exhaustion. -/
theorem RuntimeApplicationFunctionPrepares.run_eq_body
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeApplicationFunctionPrepares types owner declaration arguments prepared)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeApplicationFunction? types owner declaration arguments fuel store =
      prepared.inputs.runApplicationReturnBody? fuel declaration.value.body store := by
  simp only [runRuntimeApplicationFunction?, preparation.complete,
    LocalInputs.runApplicationReturnBody?, LocalInputs.checkApplicationReturnBody?,
    preparation.body.complete, bind, Option.bind_some, pure]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionFactorizationProperties`
-/

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
