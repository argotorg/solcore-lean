import Solcore.Abi.StaticWordContract

/-! Admission and balanced-entry consumers for Static Word ABI contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open Solcore.Abi.V1

private def name (text : String) (valid : isValidMethodName text = true) :
    MethodName :=
  ⟨text, valid⟩

private def identityProgram : Program := {
  resultType := .function .word .word
  body := .lambda .word .word (.var 0)
}

private def incrementProgram : Program := {
  resultType := .function .word .word
  body := .lambda .word .word
    (.binary .wordAdd (.var 0) (.word ⟨1, by decide⟩))
}

private def identityImplementation : WordImplementation :=
  ⟨⟨identityProgram, by decide⟩, rfl, rfl⟩

private def incrementImplementation : WordImplementation :=
  ⟨⟨incrementProgram, by decide⟩, rfl, rfl⟩

private def identityMethod : Method := {
  metadata := .staticWord (name "identity" (by decide))
  implementation := identityImplementation
}

private def incrementMethod : Method := {
  metadata := .staticWord (name "increment" (by decide))
  implementation := incrementImplementation
}

private def methods : List Method := [identityMethod, incrementMethod]

private def target : Address := ⟨0x51, by decide⟩
private def caller : Address := ⟨0x52, by decide⟩
private def argument : Word := ⟨0x123, by decide⟩

private def admissionAccepted : Bool :=
  match StaticWordContract.admit methods with
  | .error _ => false
  | .ok _ => true

private theorem admissionAccepted_exact : admissionAccepted = true := by
  native_decide

/-- A consumer can recover both sealed provenance equations after admission. -/
private theorem admittedCarriesExactProvenance
    (contract : StaticWordContract methods) :
    MethodTable.validate methods = .ok contract.table ∧
      contract.checkedCore = contract.table.generate :=
  ⟨contract.table_valid, contract.checkedCore_eq⟩

private def invocationBytesAgree : Bool :=
  match StaticWordContract.admit methods with
  | .error _ => false
  | .ok contract =>
      let selected := contract.firstMember
      let canonical := StaticWordContract.callInvocation
        target caller Word.zero selected argument
      let raw := StaticWordContract.rawInvocation target caller Word.zero
        (selected.inputData argument)
      raw.inputData.bytes == canonical.inputData.bytes &&
        canonical.inputData.bytes ==
          encodeCall selected.indexed.selector argument

private theorem invocationBytesAgree_exact : invocationBytesAgree = true := by
  native_decide

private def accountFor
    (contract : StaticWordContract methods) : Account :=
  Account.empty.withCode contract.checkedCore.code

private def worldFor
    (contract : StaticWordContract methods) : WorldState :=
  WorldState.empty.putAccount target (accountFor contract)

/-- The installation witness retains the admitted dispatcher's exact type. -/
private def installedFor
    (contract : StaticWordContract methods) :
    InstalledCheckedCoreContract (worldFor contract) target
      contract.checkedCore := {
  account := accountFor contract
  account_present := by rfl
  code_present := by rfl
}

private def environment : ExecutionEnvironment :=
  .callsOnly { lookup := fun _ => none }

/-- The convenience entry is definitionally the raw balanced entry. -/
private theorem convenienceDelegatesExactly
    (contract : StaticWordContract methods)
    (selected : contract.Member)
    (fuel : Nat) :
    contract.run target caller Word.zero selected argument
        (installedFor contract) environment fuel =
      contract.runRaw target caller Word.zero (selected.inputData argument)
        (installedFor contract) environment fuel := by
  rfl

private def dependentEntriesRun : Bool :=
  match StaticWordContract.admit methods with
  | .error _ => false
  | .ok contract =>
      let selected := contract.firstMember
      let raw := contract.runRaw target caller Word.zero
        (selected.inputData argument) (installedFor contract) environment 0
      let canonical := contract.run target caller Word.zero selected argument
        (installedFor contract) environment 0
      match raw.view, canonical.view with
      | .execution _, .execution _ => true
      | _, _ => false

private theorem dependentEntriesRun_exact : dependentEntriesRun = true := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testAbiStaticWordContract : IO Unit := do
  assertTrue admissionAccepted
    "the identity/increment Static Word contract was not admitted"
  assertTrue invocationBytesAgree
    "raw and membership-sealed ABI invocations used different calldata"
  assertTrue dependentEntriesRun
    "the admitted contract did not enter both balanced execution adapters"

end Tests
