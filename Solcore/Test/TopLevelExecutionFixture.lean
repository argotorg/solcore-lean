import Solcore.ContractRuntime.Account
import Solcore.ContractRuntime.TopLevelExecution
import Solcore.ContractRuntime.WorldState

/-! Checked program and explicit-state fixture for ADR-0145 top-level execution. -/

set_option autoImplicit false

namespace Tests.TopLevelExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime

def targetAddress : Address := ⟨0x10, by decide⟩
def callerAddress : Address := ⟨0x20, by decide⟩
def otherAddress : Address := ⟨0x30, by decide⟩

def targetSlot : Word := ⟨0x51, by decide⟩
def oldValue : Word := ⟨0x52, by decide⟩
def writtenValue : Word := ⟨0x53, by decide⟩
def retainedSlot : Word := ⟨0x61, by decide⟩
def retainedValue : Word := ⟨0x62, by decide⟩
def otherSlot : Word := ⟨0x71, by decide⟩
def otherValue : Word := ⟨0x72, by decide⟩

def returnSelector : Word := Word.zero
def revertSelector : Word := ⟨1, by decide⟩
def trapSelector : Word := ⟨2, by decide⟩
def returnPayload : Word := ⟨0xa1, by decide⟩
def revertPayload : Word := ⟨0xb2, by decide⟩
def trapCode : Word := ⟨0xc3, by decide⟩

def inputData : HostStorageDriver.InputData := {
  bytes := [0x11, 0x22, 0x33].toByteArray
  size_lt_wordModulus := by decide
}

def returnedExpr (payload : Word) : Expr :=
  .inLeft (.sum .word .word) (.word payload)

def revertedExpr (payload : Word) : Expr :=
  .inRight .word (.inLeft .word (.word payload))

def trappedExpr (reason : Word) : Expr :=
  .inRight .word (.inRight .word (.word reason))

/-- Write storage, observe call value, and dynamically select the halt kind. -/
def program : Program := {
  resultType := .sum .word (.sum .word .word)
  body :=
    .letE
      (.apply
        (.var HostFunction.storageWrite.index)
        (.pair (.word targetSlot) (.word writtenValue)))
      (.letE
        (.apply (.var (HostFunction.callValue.index + 1)) .unit)
        (.ifE
          (.binary .wordEq (.var 0) (.word returnSelector))
          (returnedExpr returnPayload)
          (.ifE
            (.binary .wordEq (.var 0) (.word revertSelector))
            (revertedExpr revertPayload)
            (trappedExpr trapCode))))
}

theorem program_host_checked : program.checkHost = true := by
  decide

def code : CheckedHostCoreProgram :=
  ⟨program, program_host_checked⟩

def contract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 code rfl

def targetAccount : Account :=
  Account.empty
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue
    |>.withCode code

def otherAccount : Account :=
  Account.empty.storageWrite otherSlot otherValue

def initialWorld : WorldState :=
  WorldState.empty
    |>.putAccount otherAddress otherAccount
    |>.putAccount targetAddress targetAccount

def installed :
    InstalledCheckedCoreContract initialWorld targetAddress contract := {
  account := targetAccount
  account_present := by
    exact WorldState.account?_putAccount_same
      (WorldState.empty.putAccount otherAddress otherAccount)
      targetAddress targetAccount
  code_present := by
    change targetAccount.code? = some code
    simp [targetAccount]
}

def invocationWith (selector : Word) : TopLevelInvocation := {
  target := targetAddress
  caller := callerAddress
  callValue := selector
  inputData := inputData
}

def returnedInvocation : TopLevelInvocation :=
  invocationWith returnSelector

def revertedInvocation : TopLevelInvocation :=
  invocationWith revertSelector

def trappedInvocation : TopLevelInvocation :=
  invocationWith trapSelector

def runWith (selector : Word) (fuel : Nat) :=
  TopLevelExecution.run contract (invocationWith selector) installed fuel

def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

def speculativeTargetValue
    (result : TopLevelTerminalResult initialWorld targetAddress) : Option Word :=
  storageValueAt? result.terminalContext.context.values.working.1
    targetAddress targetSlot

def finalTargetValue
    (result : TopLevelTerminalResult initialWorld targetAddress) : Option Word :=
  storageValueAt? result.finalWorld targetAddress targetSlot

def writeRequestFuel : Nat := 9
def postWriteFuel : Nat := 10
def callValueRequestFuel : Nat := 16
def postCallValueFuel : Nat := 17
def returnCompletionFuel : Nat := 28
def revertTrapCompletionFuel : Nat := 37

end Tests.TopLevelExecutionFixture
