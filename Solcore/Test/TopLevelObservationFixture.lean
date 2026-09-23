import Solcore.ContractRuntime.Account
import Solcore.ContractRuntime.TopLevelExecution
import Solcore.ContractRuntime.WorldState

/-! Read-only checked program observing every direct top-level address/input role. -/

set_option autoImplicit false

namespace Tests.TopLevelObservationFixture

open Solcore.Core
open Solcore.ContractRuntime

def targetAddress : Address := ⟨0x10, by decide⟩
def alternateTargetAddress : Address := ⟨0x11, by decide⟩
def callerAddress : Address := ⟨0x20, by decide⟩
def alternateCallerAddress : Address := ⟨0x21, by decide⟩
def otherAddress : Address := ⟨0x30, by decide⟩

def retainedSlot : Word := ⟨0x51, by decide⟩
def retainedValue : Word := ⟨0x52, by decide⟩
def otherSlot : Word := ⟨0x61, by decide⟩
def otherValue : Word := ⟨0x62, by decide⟩
def observedOffset : Word := ⟨1, by decide⟩
def missingByteResult : Word := ⟨0xee, by decide⟩
def callerWeight : Word := ⟨1, by decide⟩
def sizeWeight : Word := ⟨3, by decide⟩
def byteWeight : Word := ⟨5, by decide⟩
def codeWeight : Word := ⟨7, by decide⟩
def currentWeight : Word := ⟨11, by decide⟩
def storageWeight : Word := ⟨13, by decide⟩

def inputData : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x7f, 0x01].toByteArray
  size_lt_wordModulus := by decide
}

/-- Same size as `inputData`, with only the observed byte changed. -/
def differentByteInputData : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x80, 0x01].toByteArray
  size_lt_wordModulus := by decide
}

/-- Same observed byte as `inputData`, with only the size changed. -/
def differentSizeInputData : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x7f, 0x01, 0x02].toByteArray
  size_lt_wordModulus := by decide
}

def missingByteInputData : HostStorageDriver.InputData := {
  bytes := [0xa5].toByteArray
  size_lt_wordModulus := by decide
}

private def addObservations
    (caller size byte code current storage : Expr) : Expr :=
  .binary .wordAdd
    (.binary .wordAdd
      (.binary .wordAdd
        (.binary .wordAdd
          (.binary .wordAdd
            (.binary .wordMul caller (.word callerWeight))
            (.binary .wordMul size (.word sizeWeight)))
          (.binary .wordMul byte (.word byteWeight)))
        (.binary .wordMul code (.word codeWeight)))
      (.binary .wordMul current (.word currentWeight)))
    (.binary .wordMul storage (.word storageWeight))

/-
After the sixth `let`, the retained observations have these indexes inside the
right `caseE` branch: byte 0, storage 1, current 2, code 3, size 5, caller 6.
-/
def observedResultExpr : Expr :=
  .caseE (.var 3)
    (.word missingByteResult)
    (addObservations
      (.var 6) (.var 5) (.var 0) (.var 3) (.var 2) (.var 1))

/-!
Observe caller, input size, one optional input byte, and all three direct-call
target roles. The program performs no storage write and returns their modular
weighted sum, or `missingByteResult` when the byte is absent. Distinct weights
separate caller, size, byte, and target variation. In a direct call the three
target roles intentionally have the same value; their individual derivation
laws complement this runtime observation.
-/
def program : Program := {
  resultType := .word
  body :=
    .letE
      (.apply (.var HostFunction.callerAddress.index) .unit)
      (.letE
        (.apply (.var (HostFunction.inputDataSize.index + 1)) .unit)
        (.letE
          (.apply
            (.var (HostFunction.inputDataByte?.index + 2))
            (.word observedOffset))
          (.letE
            (.apply (.var (HostFunction.codeAddress.index + 3)) .unit)
            (.letE
              (.apply (.var (HostFunction.currentAddress.index + 4)) .unit)
              (.letE
                (.apply
                  (.var (HostFunction.storageAddress.index + 5)) .unit)
                observedResultExpr)))))
}

theorem program_host_checked : program.checkHost = true := by
  decide

def code : CheckedHostCoreProgram :=
  ⟨program, program_host_checked⟩

def wordCode : CheckedHostCoreWordProgram :=
  ⟨code, rfl⟩

def contract : CheckedCoreContract :=
  CheckedCoreContract.returnWord wordCode

def targetAccount : Account :=
  Account.empty
    |>.storageWrite retainedSlot retainedValue
    |>.withCode contract.code

def otherAccount : Account :=
  Account.empty.storageWrite otherSlot otherValue

/-- Install the same checked contract at one caller-selected direct target. -/
def worldAt (target : Address) : WorldState :=
  WorldState.empty
    |>.putAccount otherAddress otherAccount
    |>.putAccount target targetAccount

def installedAt (target : Address) :
    InstalledCheckedCoreContract (worldAt target) target contract := {
  account := targetAccount
  account_present := by
    exact WorldState.account?_putAccount_same
      (WorldState.empty.putAccount otherAddress otherAccount)
      target targetAccount
  code_present := by
    change targetAccount.code? = some contract.code
    simp [targetAccount]
}

def invocationAt
    (target caller : Address)
    (input : HostStorageDriver.InputData) : TopLevelInvocation := {
  target := target
  caller := caller
  callValue := Word.zero
  inputData := input
}

def checksum
    (target caller : Address)
    (size byte : Word) : Word :=
  let total := (addressToWord caller).mul callerWeight
  let total := total.add (size.mul sizeWeight)
  let total := total.add (byte.mul byteWeight)
  let total := total.add ((addressToWord target).mul codeWeight)
  let total := total.add ((addressToWord target).mul currentWeight)
  total.add ((addressToWord target).mul storageWeight)

def expectedResult
    (target caller : Address)
    (input : HostStorageDriver.InputData) : Word :=
  match input.byte? observedOffset with
  | none => missingByteResult
  | some byte => checksum target caller input.sizeWord byte

def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

def completionFuel : Nat := 256

end Tests.TopLevelObservationFixture
