import Solcore.Frontend.RuntimeParametersTypeExtensionProperties
import Solcore.Frontend.RuntimeFunctionHeaderTypeExtensionProperties
import Solcore.Frontend.RuntimeFunctionEntryProperties
import Solcore.Frontend.TypedLetReturnTreeTypeExtensionProperties

/-! Meaning-preserving extension retains the complete actual prepared record
and every successful run result. Mutual extension also retains rejection. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Transport exact provenance with the same original declaration and actual
arguments. No erased projection is used to identify value-bearing records. -/
theorem RuntimeFunctionPrepares.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares old owner declaration arguments prepared)
    (extension : TypeNameTable.Extends old new) :
    RuntimeFunctionPrepares new owner declaration arguments prepared :=
  ⟨preparation.header.extend_types extension,
    RuntimeParametersBind.extend_types preparation.parameters extension,
    preparation.body.extend_types extension⟩

theorem RuntimeFunctionHasType.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {returnType : Core.Ty}
    (typing : RuntimeFunctionHasType old owner declaration arguments returnType)
    (extension : TypeNameTable.Extends old new) :
    RuntimeFunctionHasType new owner declaration arguments returnType := by
  obtain ⟨inputs, header, parameters, body⟩ := typing
  exact ⟨inputs, header.extend_types extension,
    RuntimeParametersBind.extend_types parameters extension, body.extend_types extension⟩

theorem prepareRuntimeFunction?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (extension : TypeNameTable.Extends old new)
    (accepted : prepareRuntimeFunction? old owner declaration arguments = some prepared) :
    prepareRuntimeFunction? new owner declaration arguments = some prepared :=
  ((prepareRuntimeFunction?_sound accepted).extend_types extension).complete

/-- Equality includes absence and the actual input values, not just the
compiled Core, declared return type or argument type list. -/
theorem prepareRuntimeFunction?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) :
    prepareRuntimeFunction? old owner declaration arguments =
      prepareRuntimeFunction? new owner declaration arguments := by
  cases oldResult : prepareRuntimeFunction? old owner declaration arguments with
  | none =>
      cases newResult : prepareRuntimeFunction? new owner declaration arguments with
      | none => rfl
      | some prepared =>
          have preserved := prepareRuntimeFunction?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some prepared => exact (prepareRuntimeFunction?_some_of_extends forward oldResult).symm

/-- Present exhaustion is preserved with its full saved state, just as every
other present outcome is. There is no extra work or change to the caller store. -/
theorem runRuntimeFunction?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {fuel : Nat} {store : Core.Store}
    {outcome : Core.Ty × Core.StatefulRunResult}
    (extension : TypeNameTable.Extends old new)
    (accepted : runRuntimeFunction? old owner declaration arguments fuel store = some outcome) :
    runRuntimeFunction? new owner declaration arguments fuel store = some outcome := by
  cases preparedResult : prepareRuntimeFunction? old owner declaration arguments with
  | none => simp only [runRuntimeFunction?, preparedResult, bind, Option.bind_none,
      reduceCtorEq] at accepted
  | some prepared =>
      have preserved := prepareRuntimeFunction?_some_of_extends extension preparedResult
      simpa only [runRuntimeFunction?, preparedResult, preserved] using accepted

theorem runRuntimeFunction?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? old owner declaration arguments fuel store =
      runRuntimeFunction? new owner declaration arguments fuel store := by
  simp only [runRuntimeFunction?,
    prepareRuntimeFunction?_eq_of_mutual_extends forward backward owner declaration arguments]

end Solcore.Frontend
