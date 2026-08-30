import Solcore.Semantics.OneLevelNestedExecution

/-! Executable checked-contract fixtures for one-level nested calls. -/

set_option autoImplicit false

namespace Tests.OneLevelNestedExecutionFixture

open Solcore.Core
open Solcore.Semantics

def rootAddress : Address := ⟨0x10, by decide⟩
def childAddress : Address := ⟨0x20, by decide⟩
def unavailableAddress : Address := ⟨0x30, by decide⟩
def callerAddress : Address := ⟨0x40, by decide⟩

def childTargetWord : Word := addressToWord childAddress
def unavailableTargetWord : Word := addressToWord unavailableAddress
def invalidTargetWord : Word := ⟨2 ^ 160, by decide⟩
def rootTargetWord : Word := addressToWord rootAddress

def callInput : Word := ⟨0x77, by decide⟩
def childSlot : Word := ⟨0x51, by decide⟩
def rootSlot : Word := ⟨0x52, by decide⟩
def childOldValue : Word := ⟨0x61, by decide⟩
def childNewValue : Word := ⟨0x62, by decide⟩
def childPayload : Word := ⟨0x71, by decide⟩
def childRevertPayload : Word := ⟨0x72, by decide⟩
def childTrapReason : Word := ⟨0x73, by decide⟩
def rootRevertPayload : Word := ⟨0x81, by decide⟩
def rootTrapReason : Word := ⟨0x82, by decide⟩

def returnedExpr (payload : Expr) : Expr :=
  .inLeft (.sum .word .word) payload

def revertedExpr (payload : Expr) : Expr :=
  .inRight .word (.inLeft .word payload)

def trappedExpr (reason : Expr) : Expr :=
  .inRight .word (.inRight .word reason)

/-- What the root does after receiving a successful child return. -/
inductive RootReturnPolicy where
  | commit
  | revert
  | trap
  deriving Repr, BEq, DecidableEq

def rootReturnedBranch : RootReturnPolicy → Expr
  | .commit => returnedExpr (.var 0)
  | .revert => revertedExpr (.word rootRevertPayload)
  | .trap => trappedExpr (.word rootTrapReason)

/--
Decode all four typed call-result branches. Child return follows the selected
root policy; child revert/trap propagate; dispatch failure becomes a root trap.
-/
def consumeCallResult (policy : RootReturnPolicy) (call : Expr) : Expr :=
  .caseE call
    (rootReturnedBranch policy)
    (.caseE (.var 0)
      (revertedExpr (.var 0))
      (.caseE (.var 0)
        (trappedExpr (.var 0))
        (trappedExpr (.var 0))))

def rootProgram (policy : RootReturnPolicy) (target : Word) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeCallResult policy
    (.apply (.var HostFunction.callContractWord.index)
      (.pair (.word target) (.word callInput)))
}

theorem rootProgram_checked (policy : RootReturnPolicy) (target : Word) :
    (rootProgram policy target).checkHost = true := by
  cases policy <;> rfl

def rootContract
    (policy : RootReturnPolicy) (target : Word) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootProgram policy target, rootProgram_checked policy target⟩ rfl

def childTerminalExpr : CheckedCoreWordOutcome → Expr
  | .returned data => returnedExpr (.word data)
  | .reverted data => revertedExpr (.word data)
  | .trapped reason => trappedExpr (.word reason)

def childTerminalProgram (outcome : CheckedCoreWordOutcome) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word childSlot) (.word childNewValue)))
      (childTerminalExpr outcome)
}

theorem childTerminalProgram_checked (outcome : CheckedCoreWordOutcome) :
    (childTerminalProgram outcome).checkHost = true := by
  cases outcome <;> rfl

def childTerminalContract
    (outcome : CheckedCoreWordOutcome) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨childTerminalProgram outcome, childTerminalProgram_checked outcome⟩
    rfl

def childReturnContract : CheckedCoreContract :=
  childTerminalContract (.returned childPayload)

def childRevertContract : CheckedCoreContract :=
  childTerminalContract (.reverted childRevertPayload)

def childTrapContract : CheckedCoreContract :=
  childTerminalContract (.trapped childTrapReason)

/-- Map a leaf-level depth failure back into a successful Word result. -/
def consumeDepthProbe (call : Expr) : Expr :=
  .caseE call
    (returnedExpr (.var 0))
    (.caseE (.var 0)
      (returnedExpr (.var 0))
      (.caseE (.var 0)
        (returnedExpr (.var 0))
        (returnedExpr (.var 0))))

/-- Write child storage, then attempt a forbidden grandchild call. -/
def childDepthProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word childSlot) (.word childNewValue)))
      (consumeDepthProbe
        (.apply (.var (HostFunction.callContractWord.index + 1))
          (.pair (.word rootTargetWord) (.word callInput))))
}

theorem childDepthProgram_checked :
    childDepthProgram.checkHost = true := by
  decide

def childDepthContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨childDepthProgram, childDepthProgram_checked⟩ rfl

def rootAccount (root : CheckedCoreContract) : Account :=
  Account.empty.withCode root.code

def childAccount (child : CheckedCoreContract) : Account :=
  (Account.empty.withCode child.code).storageWrite childSlot childOldValue

def initialWorld
    (root child : CheckedCoreContract) : WorldState :=
  WorldState.empty
    |>.putAccount rootAddress (rootAccount root)
    |>.putAccount childAddress (childAccount child)

def installedRoot
    (root child : CheckedCoreContract) :
    InstalledCheckedCoreContract (initialWorld root child) rootAddress root := {
  account := rootAccount root
  account_present := by rfl
  code_present := by rfl
}

def registry
    (root child : CheckedCoreContract) : CheckedContractRegistry := {
  lookup := fun address =>
    if address = rootAddress then some root
    else if address = childAddress then some child
    else none
}

def invocation : TopLevelInvocation := {
  target := rootAddress
  caller := callerAddress
  callValue := Word.zero
  inputData := HostStorageDriver.InputData.ofWord callInput
}

def runScenario
    (root child : CheckedCoreContract) (fuel : Nat) :
    OneLevelNestedExecution.Result (initialWorld root child) root invocation :=
  OneLevelNestedExecution.run root invocation (installedRoot root child)
    (registry root child) fuel

def childStorageValue?
    (world : WorldState) : Option Word :=
  (world.account? childAddress).bind fun account =>
    account.storageValue? childSlot

def rootStorageValue?
    (world : WorldState) : Option Word :=
  (world.account? rootAddress).bind fun account =>
    account.storageValue? rootSlot

end Tests.OneLevelNestedExecutionFixture
