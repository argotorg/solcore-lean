import Solcore.ContractRuntime.Account
import Solcore.ContractRuntime.TopLevelExecution

/-! Checked root fixture for executable transaction-log finalization. -/

set_option autoImplicit false

namespace Tests.Adr0149TopLevelLogsFixture

open Solcore.Core
open Solcore.ContractRuntime

def targetAddress : Address := ⟨0x1490, by decide⟩
def callerAddress : Address := ⟨0x1491, by decide⟩

def returnSelector : Word := Word.zero
def revertSelector : Word := ⟨1, by decide⟩
def trapSelector : Word := ⟨2, by decide⟩

def firstTopic : Word := ⟨0x11, by decide⟩
def firstPayload : Word := ⟨0xa1, by decide⟩
/-- Deliberately duplicate the first entry to make multiplicity observable. -/
def secondTopic : Word := firstTopic
def secondPayload : Word := firstPayload

def returnPayload : Word := ⟨0xc3, by decide⟩
def revertPayload : Word := ⟨0xd4, by decide⟩
def trapReason : Word := ⟨0xe5, by decide⟩

def returnedExpr : Expr :=
  .inLeft (.sum .word .word) (.word returnPayload)

def revertedExpr : Expr :=
  .inRight .word (.inLeft .word (.word revertPayload))

def trappedExpr : Expr :=
  .inRight .word (.inRight .word (.word trapReason))

def emitExpr (environmentOffset : Nat) (topic payload : Word) : Expr :=
  .apply
    (.var (HostFunction.emitLogWord.index + environmentOffset))
    (.pair (.word topic) (.word payload))

/-- Emit two ordered word logs, then select the root outcome from call value. -/
def program : Program := {
  resultType := .sum .word (.sum .word .word)
  body :=
    .letE (emitExpr 0 firstTopic firstPayload)
      (.letE (emitExpr 1 secondTopic secondPayload)
        (.letE
          (.apply (.var (HostFunction.callValue.index + 2)) .unit)
          (.ifE
            (.binary .wordEq (.var 0) (.word returnSelector))
            returnedExpr
            (.ifE
              (.binary .wordEq (.var 0) (.word revertSelector))
              revertedExpr
              trappedExpr))))
}

theorem program_host_checked : program.checkHost = true := by
  decide

def code : CheckedHostCoreProgram :=
  ⟨program, program_host_checked⟩

def contract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 code rfl

def targetAccount : Account :=
  Account.empty.withCode code

def initialWorld : WorldState :=
  WorldState.empty.putAccount targetAddress targetAccount

def emptyInputData : HostStorageDriver.InputData := {
  bytes := [].toByteArray
  size_lt_wordModulus := by decide
}

def installed :
    InstalledCheckedCoreContract initialWorld targetAddress contract := {
  account := targetAccount
  account_present := by
    exact WorldState.account?_putAccount_same
      WorldState.empty targetAddress targetAccount
  code_present := by
    change targetAccount.code? = some code
    simp [targetAccount]
}

def invocationWith (selector : Word) : TopLevelInvocation := {
  target := targetAddress
  caller := callerAddress
  callValue := selector
  inputData := emptyInputData
}

def runWith (selector : Word) (fuel : Nat) :=
  TopLevelExecution.run contract (invocationWith selector) installed fuel

def firstLog : CheckedCoreWordLog := {
  emitter := targetAddress
  topic := firstTopic
  payload := firstPayload
}

def secondLog : CheckedCoreWordLog := {
  emitter := targetAddress
  topic := secondTopic
  payload := secondPayload
}

def expectedLogs : List CheckedCoreWordLog := [firstLog, secondLog]

end Tests.Adr0149TopLevelLogsFixture
