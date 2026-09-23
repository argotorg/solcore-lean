import Solcore.ContractRuntime.AccountCodeProperties
import Solcore.ContractRuntime.CheckedCoreProgramHostPromotion
import Solcore.ContractRuntime.WorldStateCodeProperties

/-! Runtime and direct-law regressions for address-selected host code. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def cellProgram : Program := {
  resultType := .cell .bool
  body := .newCell .bool (.bool true)
}

private def unitProgram : Program := {
  resultType := .unit
  body := .unit
}

private theorem cellProgram_checked : cellProgram.checkHost = true := by decide
private theorem unitProgram_checked : unitProgram.check = true := by decide

private def checkedCellProgram : CheckedHostCoreProgram :=
  ⟨cellProgram, cellProgram_checked⟩

private def checkedUnitProgram : CheckedHostCoreProgram :=
  (⟨unitProgram, unitProgram_checked⟩ : CheckedCoreProgram).toHost

private theorem compileTimePurePromotionRegression :
    checkedUnitProgram.program = unitProgram :=
  CheckedCoreProgram.toHost_program
    (⟨unitProgram, unitProgram_checked⟩ : CheckedCoreProgram)

private def addressA : Address := ⟨0, by decide⟩
private def addressB : Address := ⟨1, by decide⟩
private def slot : Word := ⟨0x11, by decide⟩
private def initialValue : Word := ⟨0xaa, by decide⟩
private def updatedValue : Word := ⟨0xbb, by decide⟩

private def accountA : Account :=
  (Account.empty.storageWrite slot initialValue).withCode checkedCellProgram

private def accountB : Account :=
  Account.empty.withCode checkedUnitProgram

private def twoCodeAccounts : WorldState :=
  WorldState.empty
    |>.putAccount addressA accountA
    |>.putAccount addressB accountB

private theorem compileTimeWithCodeStorageRegression
    (account : Account)
    (code : CheckedHostCoreProgram)
    (storedSlot : Word) :
    (account.withCode code).storageValue? storedSlot =
      account.storageValue? storedSlot :=
  Account.storageValue?_withCode account code storedSlot

private theorem compileTimeStoragePreservationRegression
    (account : Account)
    (code : CheckedHostCoreProgram)
    (writtenSlot value : Word) :
    ((account.withCode code).storageWrite writtenSlot value).code? = some code := by
  rw [Account.code?_storageWrite]
  exact Account.code?_withCode account code

private theorem compileTimeSelectionRegression
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.code? codeAddress = some code :=
  WorldState.code?_of_present state codeAddress account code
    accountPresent codePresent

private theorem compileTimeExecutionRegression
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.runCode? codeAddress fuel = some (code.runStateful fuel) :=
  WorldState.runCode?_of_present state codeAddress account code fuel
    accountPresent codePresent

private theorem compileTimeWorldNoFaultRegression
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat)
    (error : MachineFault)
    (faultState : State) :
    state.runCode? codeAddress fuel ≠ some (.fault error faultState) :=
  WorldState.runCode?_ne_some_fault state codeAddress fuel error faultState

def testWorldStateCode : IO Unit := do
  match Account.empty.code? with
  | none => pure ()
  | some _ => throw (IO.userError "an empty Account unexpectedly had code")
  match WorldState.empty.runCode? addressA 3 with
  | none => pure ()
  | some _ => throw (IO.userError "an absent Account unexpectedly executed")
  let withoutCode := WorldState.empty.putAccount addressA Account.empty
  match withoutCode.runCode? addressA 3 with
  | none => pure ()
  | some _ => throw (IO.userError "an Account without code unexpectedly executed")
  match twoCodeAccounts.code? addressA with
  | none => throw (IO.userError "address A did not select its checked code")
  | some code =>
      assertTrue (code.program == cellProgram)
        "address A selected code from another Account"
  assertTrue
    (twoCodeAccounts.runCode? addressA 3 ==
      some (.done (.cellRef .bool 0) [.bool true]))
    "address A must retain the stateful cell-program result"
  assertTrue
    (twoCodeAccounts.runCode? addressB 1 == some (.done .unit []))
    "address B must execute its own unit program"
  assertTrue (accountA.storageRead slot == initialValue)
    "associating checked code must preserve existing storage"
  match twoCodeAccounts.runCode? addressA 2 with
  | some (.outOfFuel _) => pure ()
  | result =>
      throw (IO.userError
        s!"selected insufficient-fuel execution changed class: {reprStr result}")
  let writtenAccount := accountA.storageWrite slot updatedValue
  assertTrue (writtenAccount.storageRead slot == updatedValue)
    "the storage write did not update the selected slot"
  match writtenAccount.code? with
  | none => throw (IO.userError "a storage write erased checked code")
  | some code =>
      assertTrue (code.program == cellProgram)
        "a storage write replaced checked code"
  let writtenWorld := twoCodeAccounts.putAccount addressA writtenAccount
  assertTrue
    (writtenWorld.runCode? addressA 3 ==
      some (.done (.cellRef .bool 0) [.bool true]))
    "a storage write changed selected checked-code execution"

end Tests
