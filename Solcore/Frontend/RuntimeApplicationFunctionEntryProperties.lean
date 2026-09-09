import Solcore.Frontend.RuntimeApplicationFunctionEntry
import Solcore.Frontend.LocalApplicationReturnBodyProperties

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
