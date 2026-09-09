import Solcore.Frontend.ComputationReturnTreeTypeExtensionProperties
import Solcore.Frontend.ComputationFunctionProperties
import Solcore.Frontend.RuntimeFunctionHeaderTypeExtensionProperties
import Solcore.Frontend.RuntimeParameterDeclarationsTypeExtensionProperties
import Solcore.Frontend.RuntimeParametersTypeExtensionProperties

/-! Meaning-preserving caller tables retain independent function provenance,
complete actual preparations and every present run result. Executable laws use
the same arbitrary child operation, without a child correctness hypothesis. -/

set_option autoImplicit false

namespace Solcore.Frontend

private def CheckGraph
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (table : LocalNameTable) (context : Resolved.Context) (source : Syntax.Expr)
    (core : Core.Expr) (type : Core.Ty) : Prop :=
  checkChild table context source = some (core, type)

theorem ComputationFunctionCompiles.extend_types
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : ComputationFunctionCompiles ChildElab old owner declaration compiled)
    (extension : TypeNameTable.Extends old new) :
    ComputationFunctionCompiles ChildElab new owner declaration compiled :=
  ⟨compilation.header.extend_types extension,
    RuntimeParametersDeclare.extend_types compilation.parameters extension,
    compilation.body.extend_types extension⟩

/-- Preserve the original value-bearing record, not merely its erased view. -/
theorem ComputationFunctionPrepares.extend_types
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : ComputationFunctionPrepares ChildElab old owner declaration arguments prepared)
    (extension : TypeNameTable.Extends old new) :
    ComputationFunctionPrepares ChildElab new owner declaration arguments prepared :=
  ⟨preparation.header.extend_types extension,
    RuntimeParametersBind.extend_types preparation.parameters extension,
    preparation.body.extend_types extension⟩

theorem compileComputationFunction?_some_of_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (extension : TypeNameTable.Extends old new)
    (accepted : compileComputationFunction? checkChild old owner declaration = some compiled) :
    compileComputationFunction? checkChild new owner declaration = some compiled := by
  have compilation := (compileComputationFunction?_iff
    (checkChild := checkChild) (ChildElab := CheckGraph checkChild) Iff.rfl).mp accepted
  exact (compileComputationFunction?_iff
    (checkChild := checkChild) (ChildElab := CheckGraph checkChild) Iff.rfl).mpr
      (compilation.extend_types extension)

theorem prepareComputationFunction?_some_of_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} (extension : TypeNameTable.Extends old new)
    (accepted : prepareComputationFunction? checkChild old owner declaration arguments = some prepared) :
    prepareComputationFunction? checkChild new owner declaration arguments = some prepared := by
  have preparation := (prepareComputationFunction?_iff
    (checkChild := checkChild) (ChildElab := CheckGraph checkChild) Iff.rfl).mp accepted
  exact (prepareComputationFunction?_iff
    (checkChild := checkChild) (ChildElab := CheckGraph checkChild) Iff.rfl).mpr
      (preparation.extend_types extension)

/-- Absence is retained only when both directions preserve named meanings. -/
theorem compileComputationFunction?_eq_of_mutual_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl) :
    compileComputationFunction? checkChild old owner declaration =
      compileComputationFunction? checkChild new owner declaration := by
  cases oldResult : compileComputationFunction? checkChild old owner declaration with
  | none =>
      cases newResult : compileComputationFunction? checkChild new owner declaration with
      | none => rfl
      | some compiled =>
          have preserved := compileComputationFunction?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some compiled => exact (compileComputationFunction?_some_of_extends forward oldResult).symm

/-- Equality includes all actual input values and retained captures. -/
theorem prepareComputationFunction?_eq_of_mutual_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) :
    prepareComputationFunction? checkChild old owner declaration arguments =
      prepareComputationFunction? checkChild new owner declaration arguments := by
  cases oldResult : prepareComputationFunction? checkChild old owner declaration arguments with
  | none =>
      cases newResult : prepareComputationFunction? checkChild new owner declaration arguments with
      | none => rfl
      | some prepared =>
          have preserved := prepareComputationFunction?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some prepared => exact (prepareComputationFunction?_some_of_extends forward oldResult).symm

/-- Present faults and exhaustion retain their exact stores and saved states;
this is transport, not a safety or runtime-validation assertion. -/
theorem runComputationFunction?_some_of_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {fuel : Nat} {store : Core.Store} {outcome : Core.Ty × Core.StatefulRunResult}
    (extension : TypeNameTable.Extends old new)
    (accepted : runComputationFunction? checkChild old owner declaration arguments fuel store = some outcome) :
    runComputationFunction? checkChild new owner declaration arguments fuel store = some outcome := by
  cases preparedResult : prepareComputationFunction? checkChild old owner declaration arguments with
  | none => simp only [runComputationFunction?, preparedResult, bind, Option.bind_none,
      reduceCtorEq] at accepted
  | some prepared =>
      have preserved := prepareComputationFunction?_some_of_extends extension preparedResult
      simpa only [runComputationFunction?, preparedResult, preserved] using accepted

theorem runComputationFunction?_eq_of_mutual_extends
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? checkChild old owner declaration arguments fuel store =
      runComputationFunction? checkChild new owner declaration arguments fuel store := by
  simp only [runComputationFunction?,
    prepareComputationFunction?_eq_of_mutual_extends forward backward owner declaration arguments]

end Solcore.Frontend
