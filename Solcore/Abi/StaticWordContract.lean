import Solcore.Abi.StaticWordCodec
import Solcore.Abi.StaticWordDispatcher
import Solcore.ContractRuntime.BalancedTopLevelExecution

/-! Admission and balanced top-level execution for Static Word ABI contracts. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Core
open Solcore.ContractRuntime

/--
A validated Static Word method table paired with exactly the checked dispatcher
generated from that table. The source method list remains in the type, so an
admitted value cannot lose its validation provenance.
-/
structure StaticWordContract (methods : List Method) where
  private mk ::
  table : MethodTable
  table_valid : MethodTable.validate methods = .ok table
  checkedCore : CheckedCoreContract
  checkedCore_eq : checkedCore = table.generate

namespace StaticWordContract

/-- Validate a finite method list and retain the validator's exact error. -/
def admit (methods : List Method) :
    Except MethodTableError (StaticWordContract methods) :=
  match validated : MethodTable.validate methods with
  | .error failure => .error failure
  | .ok table => .ok {
      table := table
      table_valid := validated
      checkedCore := table.generate
      checkedCore_eq := rfl
    }

/-- Admission rejects with precisely the method-table validation error. -/
@[simp] theorem admit_eq_error_iff
    (methods : List Method) (failure : MethodTableError) :
    admit methods = .error failure ↔
      MethodTable.validate methods = .error failure := by
  unfold admit
  split <;> simp_all

/-- One method carrying proof that it belongs to this validated table. -/
structure Member
    {methods : List Method}
    (contract : StaticWordContract methods) where
  private mk ::
  indexed : IndexedMethod
  present : indexed ∈ contract.table.entries

/-- Seal an explicit table-membership proof for use at the call boundary. -/
def member
    {methods : List Method}
    (contract : StaticWordContract methods)
    (indexed : IndexedMethod)
    (present : indexed ∈ contract.table.entries) : contract.Member :=
  ⟨indexed, present⟩

/-- The nonempty validation invariant always exposes one callable member. -/
def firstMember
    {methods : List Method}
    (contract : StaticWordContract methods) : contract.Member :=
  match entriesEq : contract.table.entries with
  | [] => False.elim (contract.table.nonempty entriesEq)
  | first :: _rest =>
      ⟨first, by simp [entriesEq]⟩

/-- Canonical calldata for a selected validated method. -/
def Member.inputData
    {methods : List Method}
    {contract : StaticWordContract methods}
    (selected : contract.Member)
    (argument : Word) : HostStorageDriver.InputData := {
  bytes := encodeCall selected.indexed.selector argument
  size_lt_wordModulus := by
    simp [encodeCall_size, callSize, wordModulus]
}

@[simp] theorem Member.inputData_bytes
    {methods : List Method}
    {contract : StaticWordContract methods}
    (selected : contract.Member)
    (argument : Word) :
    (selected.inputData argument).bytes =
      encodeCall selected.indexed.selector argument := by
  rfl

/-- Construct the exact direct invocation used by the raw ABI entry point. -/
def rawInvocation
    (target caller : Address)
    (callValue : Word)
    (inputData : HostStorageDriver.InputData) : TopLevelInvocation := {
  target := target
  caller := caller
  callValue := callValue
  inputData := inputData
}

/--
Delegate explicit calldata to the sealed balanced top-level runner without
changing its total result type or execution environment.
-/
def runRaw
    {methods : List Method}
    {initialWorld : WorldState}
    (contract : StaticWordContract methods)
    (target caller : Address)
    (callValue : Word)
    (inputData : HostStorageDriver.InputData)
    (installed : InstalledCheckedCoreContract initialWorld target
      contract.checkedCore)
    (environment : ExecutionEnvironment)
    (fuel : Nat) :
    BalancedTopLevelExecution.Result initialWorld contract.checkedCore
      (rawInvocation target caller callValue inputData) :=
  BalancedTopLevelExecution.runWithEnvironment contract.checkedCore
    (rawInvocation target caller callValue inputData) installed environment fuel

/-- Invocation whose selector is sealed by membership in the validated table. -/
def callInvocation
    {methods : List Method}
    {contract : StaticWordContract methods}
    (target caller : Address)
    (callValue : Word)
    (selected : contract.Member)
    (argument : Word) : TopLevelInvocation :=
  rawInvocation target caller callValue (selected.inputData argument)

@[simp] theorem callInvocation_inputData_bytes
    {methods : List Method}
    {contract : StaticWordContract methods}
    (target caller : Address)
    (callValue : Word)
    (selected : contract.Member)
    (argument : Word) :
    (callInvocation target caller callValue selected argument).inputData.bytes =
      encodeCall selected.indexed.selector argument := by
  rfl

/-- Execute canonical calldata for one member of the admitted method table. -/
def run
    {methods : List Method}
    {initialWorld : WorldState}
    (contract : StaticWordContract methods)
    (target caller : Address)
    (callValue : Word)
    (selected : contract.Member)
    (argument : Word)
    (installed : InstalledCheckedCoreContract initialWorld target
      contract.checkedCore)
    (environment : ExecutionEnvironment)
    (fuel : Nat) :
    BalancedTopLevelExecution.Result initialWorld contract.checkedCore
      (callInvocation target caller callValue selected argument) :=
  runRaw contract target caller callValue (selected.inputData argument)
    installed environment fuel

end StaticWordContract

end Solcore.Abi.V1
