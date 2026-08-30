import Solcore.Semantics.OneLevelNestedExecutionResumptionProperties
import Solcore.Test.OneLevelNestedExecutionFixture

/-! Actual checked-Core fixtures for depth-one value-bearing calls. -/

set_option autoImplicit false

namespace Tests.Adr0147NestedValueExecutionFixture

open Solcore.Core
open Solcore.Semantics
open Tests.OneLevelNestedExecutionFixture

def transferValue : Word := ⟨3, by decide⟩
def rootInitialBalance : Word := ⟨10, by decide⟩
def rootFinalBalance : Word := ⟨7, by decide⟩
def childInitialBalance : Word := ⟨4, by decide⟩
def childFinalBalance : Word := ⟨7, by decide⟩
def insufficientBalance : Word := ⟨2, by decide⟩
def maximumBalance : Word := ⟨2 ^ 256 - 1, by decide⟩
def untouchedAddress : Address := ⟨0x90, by decide⟩
def untouchedBalance : Word := ⟨9, by decide⟩
def valueSlot : Word := ⟨0xa1, by decide⟩
def sentinel : Word := ⟨0xa2, by decide⟩

def valueCallExpr (target value input : Word) : Expr :=
  .apply (.var HostFunction.callContractWordWithValue.index)
    (.pair (.word target) (.pair (.word value) (.word input)))

def valueRootProgram (policy : RootReturnPolicy) (target value : Word) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeCallResult policy (valueCallExpr target value callInput)
}

theorem valueRootProgram_checked
    (policy : RootReturnPolicy) (target value : Word) :
    (valueRootProgram policy target value).checkHost = true := by
  cases policy <;> rfl

def valueRootContract
    (policy : RootReturnPolicy) (target value : Word) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨valueRootProgram policy target value,
      valueRootProgram_checked policy target value⟩ rfl

def valueChildProgram (outcome : CheckedCoreWordOutcome) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.callValue.index) .unit)
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word valueSlot) (.var 0)))
        (match outcome with
        | .returned _ => returnedExpr (.var 1)
        | .reverted data => revertedExpr (.word data)
        | .trapped reason => trappedExpr (.word reason)))
}

theorem valueChildProgram_checked (outcome : CheckedCoreWordOutcome) :
    (valueChildProgram outcome).checkHost = true := by
  cases outcome <;> rfl

def valueChildContract (outcome : CheckedCoreWordOutcome) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨valueChildProgram outcome, valueChildProgram_checked outcome⟩ rfl

def returningChild : CheckedCoreContract :=
  valueChildContract (.returned sentinel)
def revertingChild : CheckedCoreContract :=
  valueChildContract (.reverted childRevertPayload)
def trappingChild : CheckedCoreContract :=
  valueChildContract (.trapped childTrapReason)

def accountWithBalance (contract : CheckedCoreContract) (balance : Word) : Account :=
  (Account.empty.withCode contract.code).withBalance balance

def scenarioWorld (root child : CheckedCoreContract)
    (rootBalance childBalance : Word) : WorldState :=
  WorldState.empty
    |>.putAccount rootAddress (accountWithBalance root rootBalance)
    |>.putAccount childAddress (accountWithBalance child childBalance)
    |>.putAccount untouchedAddress (Account.empty.withBalance untouchedBalance)

def scenarioInstalled (root child : CheckedCoreContract)
    (rootBalance childBalance : Word) :
    InstalledCheckedCoreContract
      (scenarioWorld root child rootBalance childBalance) rootAddress root := {
  account := accountWithBalance root rootBalance
  account_present := by rfl
  code_present := by rfl
}

def runValueScenario (policy : RootReturnPolicy) (child : CheckedCoreContract)
    (rootBalance childBalance : Word) (fuel : Nat) :=
  let root := valueRootContract policy childTargetWord transferValue
  OneLevelNestedExecution.run root invocation
    (scenarioInstalled root child rootBalance childBalance)
    (registry root child) fuel

def legacyWorld (root child : CheckedCoreContract) : WorldState :=
  scenarioWorld root child rootInitialBalance childInitialBalance

def runLegacyScenario (fuel : Nat) :=
  let root := rootContract .commit childTargetWord
  OneLevelNestedExecution.run root invocation
    (scenarioInstalled root childReturnContract rootInitialBalance
      childInitialBalance)
    (registry root childReturnContract) fuel

def balance? (world : WorldState) (address : Address) : Option Word :=
  world.balance? address

def valueStored? (world : WorldState) : Option Word :=
  (world.account? childAddress).bind fun account =>
    account.storageValue? valueSlot

end Tests.Adr0147NestedValueExecutionFixture
