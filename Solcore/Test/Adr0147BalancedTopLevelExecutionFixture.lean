import Solcore.ContractRuntime.BalancedTopLevelExecutionProperties
import Solcore.Test.TopLevelExecutionFixture

/-! Actual checked-Core worlds for balance-aware top-level execution tests. -/

set_option autoImplicit false

namespace Tests.Adr0147BalancedTopLevelExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open Tests.TopLevelExecutionFixture

def zero : Word := Word.zero
def one : Word := ⟨1, by decide⟩
def two : Word := ⟨2, by decide⟩
def three : Word := ⟨3, by decide⟩
def four : Word := ⟨4, by decide⟩
def five : Word := ⟨5, by decide⟩
def eight : Word := ⟨8, by decide⟩
def nine : Word := ⟨9, by decide⟩
def ten : Word := ⟨10, by decide⟩

/-- A minimal checker-accepted root that always returns the fixture payload. -/
def returningProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := returnedExpr returnPayload
}

theorem returningProgram_checked : returningProgram.checkHost = true := by
  rfl

def returningContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨returningProgram, returningProgram_checked⟩ rfl

def callerAccount (balance : Word) : Account :=
  Account.empty.withBalance balance

def targetAccountFor
    (root : CheckedCoreContract) (balance : Word) : Account :=
  (targetAccount.withCode root.code).withBalance balance

/-- A cross-account world retaining the original storage and unrelated account. -/
def worldWithBalances
    (root : CheckedCoreContract)
    (callerBalance targetBalance : Word) : WorldState :=
  WorldState.empty
    |>.putAccount otherAddress otherAccount
    |>.putAccount callerAddress (callerAccount callerBalance)
    |>.putAccount targetAddress (targetAccountFor root targetBalance)

def installedWithBalances
    (root : CheckedCoreContract)
    (callerBalance targetBalance : Word) :
    InstalledCheckedCoreContract
      (worldWithBalances root callerBalance targetBalance)
      targetAddress root := {
  account := targetAccountFor root targetBalance
  account_present := by rfl
  code_present := by rfl
}

/-- A world with installed target code but no ordinary external caller account. -/
def worldWithoutCaller
    (root : CheckedCoreContract)
    (targetBalance : Word) : WorldState :=
  WorldState.empty
    |>.putAccount otherAddress otherAccount
    |>.putAccount targetAddress (targetAccountFor root targetBalance)

def installedWithoutCaller
    (root : CheckedCoreContract)
    (targetBalance : Word) :
    InstalledCheckedCoreContract
      (worldWithoutCaller root targetBalance) targetAddress root := {
  account := targetAccountFor root targetBalance
  account_present := by rfl
  code_present := by rfl
}

def invocationFrom (caller : Address) (value : Word) : TopLevelInvocation := {
  target := targetAddress
  caller := caller
  callValue := value
  inputData := inputData
}

def emptyRegistry : CheckedContractRegistry := {
  lookup := fun _ => none
}

def runWithBalances
    (root : CheckedCoreContract)
    (callerBalance targetBalance value : Word)
    (fuel : Nat) :=
  BalancedTopLevelExecution.run root
    (invocationFrom callerAddress value)
    (installedWithBalances root callerBalance targetBalance)
    emptyRegistry fuel

def runWithoutCaller
    (root : CheckedCoreContract)
    (targetBalance : Word)
    (caller : Address)
    (value : Word)
    (fuel : Nat) :=
  BalancedTopLevelExecution.run root (invocationFrom caller value)
    (installedWithoutCaller root targetBalance) emptyRegistry fuel

def completionFuel : Nat := 128

end Tests.Adr0147BalancedTopLevelExecutionFixture
