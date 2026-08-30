import Solcore.Semantics.ExecutionEnvironment
import Solcore.Test.OneLevelNestedExecutionFixture

/-! Reusable checked programs and explicit state for creation E2E tests. -/

set_option autoImplicit false

namespace Tests.Adr0148CreationEndToEndFixture

open Solcore.Core
open Solcore.Semantics
open Tests.OneLevelNestedExecutionFixture

def creator : Address := ⟨0x2480, by decide⟩
def created : Address := ⟨0x2481, by decide⟩
def externalCaller : Address := ⟨0x2482, by decide⟩
def unrelated : Address := ⟨0x2483, by decide⟩

def templateId : Word := ⟨0x24, by decide⟩
def oldNonce : Word := ⟨7, by decide⟩
def creationValue : Word := ⟨3, by decide⟩
def creatorBalance : Word := ⟨11, by decide⟩
def unrelatedBalance : Word := ⟨19, by decide⟩
def initializerInput : Word := ⟨0xabcdef, by decide⟩
def runtimeSentinel : Word := ⟨0x5151, by decide⟩
def rootRevertReason : Word := ⟨0x5252, by decide⟩
def rootTrapReason : Word := ⟨0x5353, by decide⟩

def callerSlot : Word := ⟨0x101, by decide⟩
def valueSlot : Word := ⟨0x102, by decide⟩
def inputWordSlot : Word := ⟨0x103, by decide⟩
def inputSizeSlot : Word := ⟨0x104, by decide⟩
def storageAddressSlot : Word := ⟨0x105, by decide⟩
def currentAddressSlot : Word := ⟨0x106, by decide⟩
def codeAddressSlot : Word := ⟨0x107, by decide⟩
def runtimeSlot : Word := ⟨0x108, by decide⟩

def returned (payload : Expr) : Expr :=
  .inLeft (.sum .word .word) payload

def reverted (payload : Expr) : Expr :=
  .inRight .word (.inLeft .word payload)

def trapped (reason : Expr) : Expr :=
  .inRight .word (.inRight .word reason)

/-- Outcome selected by a root after creation returned an Address. -/
inductive RootPolicy where
  | commit
  | revert
  | trap
  deriving Repr, BEq, DecidableEq

def rootSuccess : RootPolicy → Expr
  | .commit => returned (.var 0)
  | .revert => reverted (.word rootRevertReason)
  | .trap => trapped (.word rootTrapReason)

/-- Decode the common creation/call result wire at the current lexical depth. -/
def consumeResult (policy : RootPolicy) (operation : Expr) : Expr :=
  .caseE operation
    (rootSuccess policy)
    (.caseE (.var 0)
      (reverted (.var 0))
      (.caseE (.var 0)
        (trapped (.var 0))
        (trapped (.var 0))))

def creationExpr (depth : Nat := 0) : Expr :=
  .apply (.var (HostFunction.createContractWord.index + depth))
    (.pair (.word templateId)
      (.pair (.word creationValue) (.word initializerInput)))

def rootCreationProgram (policy : RootPolicy) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeResult policy creationExpr
}

theorem rootCreationProgram_checked (policy : RootPolicy) :
    (rootCreationProgram policy).checkHost = true := by
  cases policy <;> native_decide

def rootCreationContract (policy : RootPolicy) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootCreationProgram policy, rootCreationProgram_checked policy⟩ rfl

/-- Create, then call the returned Address in the same root execution. -/
def rootCreateThenCallProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .caseE creationExpr
      (consumeResult .commit
        (.apply (.var (HostFunction.callContractWord.index + 1))
          (.pair (.var 0) (.word runtimeSentinel))))
      (.caseE (.var 0)
        (reverted (.var 0))
        (.caseE (.var 0)
          (trapped (.var 0))
          (trapped (.var 0))))
}

theorem rootCreateThenCallProgram_checked :
    rootCreateThenCallProgram.checkHost = true := by native_decide

def rootCreateThenCallContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootCreateThenCallProgram, rootCreateThenCallProgram_checked⟩ rfl

/-- One direct observation followed by a write to a unique storage slot. -/
def observeAndWrite
    (depth hostIndex : Nat) (argument : Expr) (slot : Word)
    (rest : Expr) : Expr :=
  .letE
    (.apply (.var (hostIndex + depth)) argument)
    (.letE
      (.apply (.var (HostFunction.storageWrite.index + depth + 1))
        (.pair (.word slot) (.var 0)))
      rest)

def observerTail (depth : Nat) : Expr :=
  observeAndWrite depth HostFunction.callerAddress.index .unit callerSlot
    (observeAndWrite (depth + 2) HostFunction.callValue.index .unit valueSlot
      (observeAndWrite (depth + 4) HostFunction.inputDataSize.index .unit inputSizeSlot
        (observeAndWrite (depth + 6) HostFunction.storageAddress.index .unit
          storageAddressSlot
          (observeAndWrite (depth + 8) HostFunction.currentAddress.index .unit
            currentAddressSlot
            (observeAndWrite (depth + 10) HostFunction.codeAddress.index .unit
              codeAddressSlot (returned (.word initializerInput)))))))

/-- Observe input word zero and every initializer execution identity field. -/
def observerInitializerProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .caseE
      (.apply (.var HostFunction.inputDataWordBE?.index) (.word Word.zero))
      (trapped (.word Word.zero))
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word inputWordSlot) (.var 0)))
        (observerTail 2))
}

theorem observerInitializerProgram_checked :
    observerInitializerProgram.checkHost = true := by native_decide

def observerInitializer : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨observerInitializerProgram, observerInitializerProgram_checked⟩ rfl

/-- Deployed runtime leaves an observable write and returns a sentinel. -/
def runtimeProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word runtimeSlot) (.word runtimeSentinel)))
      (returned (.word runtimeSentinel))
}

theorem runtimeProgram_checked : runtimeProgram.checkHost = true := by
  native_decide

def runtime : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨runtimeProgram, runtimeProgram_checked⟩ rfl

def template : CheckedCreationTemplate := {
  initializer := observerInitializer
  runtime := runtime
}

def environment : ExecutionEnvironment := {
  callRegistry := {
    lookup := fun address => if address = created then some runtime else none
  }
  creationTemplates := {
    lookup := fun identifier => if identifier = templateId then some template else none
  }
  creationAddressPolicy := {
    derive := fun actualCreator nonce =>
      if actualCreator = creator ∧ nonce = oldNonce then created else unrelated
  }
}

def rootAccount (contract : CheckedCoreContract) : Account :=
  Account.empty.withBalance creatorBalance |>.withNonce oldNonce
    |>.withCode contract.code

def unrelatedAccount : Account :=
  Account.empty.withBalance unrelatedBalance

def initialWorld (contract : CheckedCoreContract) : WorldState :=
  WorldState.empty
    |>.putAccount unrelated unrelatedAccount
    |>.putAccount creator (rootAccount contract)

def rootInstalled (contract : CheckedCoreContract) :
    InstalledCheckedCoreContract (initialWorld contract) creator contract := {
  account := rootAccount contract
  account_present := by rfl
  code_present := by rfl
}

def invocation : TopLevelInvocation := {
  target := creator
  caller := externalCaller
  callValue := Word.zero
  inputData := HostStorageDriver.InputData.ofWord initializerInput
}

end Tests.Adr0148CreationEndToEndFixture
