import Solcore.Abi.StaticWordContract
import Solcore.Semantics.WorldStateDelta

/-! Explicit ABI/world fixture for the first Static Word vertical execution. -/

set_option autoImplicit false

namespace Tests.AbiStaticWordEndToEndFixture

open Solcore.Core
open Solcore.Semantics
open Solcore.Abi.V1

def target : Address := ⟨0x1500, by decide⟩
def caller : Address := ⟨0x1501, by decide⟩

def callerBalance : Word := ⟨10, by decide⟩
def targetBalance : Word := ⟨3, by decide⟩
def callValue : Word := ⟨1, by decide⟩
def callerBalanceAfter : Word := ⟨9, by decide⟩
def targetBalanceAfter : Word := ⟨4, by decide⟩

def storageSlot : Word := ⟨0x150, by decide⟩
def logTopic : Word := ⟨0x151, by decide⟩
def argument : Word := ⟨0x123456, by decide⟩

def methodName : MethodName :=
  ⟨"storeAndLog", by decide⟩

/-- Store the argument, emit it once, and return it unchanged. -/
def implementationProgram : Program := {
  resultType := .function .word .word
  body :=
    .lambda .word .word
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word storageSlot) (.var 0)))
        (.letE
          (.apply (.var (HostFunction.emitLogWord.index + 2))
            (.pair (.word logTopic) (.var 1)))
          (.var 2)))
}

theorem implementationProgram_checked :
    implementationProgram.checkHost = true := by
  native_decide

def implementation : WordImplementation :=
  ⟨⟨implementationProgram, implementationProgram_checked⟩, rfl, rfl⟩

def method : Method := {
  metadata := .staticWord methodName
  implementation := implementation
}

def methods : List Method := [method]

private def admitted? : Option (StaticWordContract methods) :=
  (StaticWordContract.admit methods).toOption

private theorem admitted?_isSome : admitted?.isSome := by
  native_decide

/-- The concrete validated ABI contract used by every run in this fixture. -/
def contract : StaticWordContract methods :=
  admitted?.get admitted?_isSome

def selected : contract.Member :=
  contract.firstMember

def callerAccount : Account :=
  Account.empty.withBalance callerBalance

def targetAccount : Account :=
  Account.empty.withBalance targetBalance
    |>.withCode contract.checkedCore.code

def initialWorld : WorldState :=
  WorldState.empty
    |>.putAccount caller callerAccount
    |>.putAccount target targetAccount

def installed :
    InstalledCheckedCoreContract initialWorld target contract.checkedCore := {
  account := targetAccount
  account_present := by rfl
  code_present := by rfl
}

/-- No ambient call or creation capability is left implicit. -/
def environment : ExecutionEnvironment := {
  callRegistry := { lookup := fun _ => none }
  creationTemplates := .empty
  creationAddressPolicy := ExecutionEnvironment.inertCreationAddressPolicy
}

def canonicalInput : HostStorageDriver.InputData :=
  selected.inputData argument

def suffixedInput : HostStorageDriver.InputData := {
  bytes := canonicalInput.bytes.append [0xaa, 0xbb].toByteArray
  size_lt_wordModulus := by
    simp [canonicalInput, StaticWordContract.Member.inputData,
      encodeCall_size, callSize, wordModulus]
}

def shortInput : HostStorageDriver.InputData := {
  bytes := [0xaa, 0xbb, 0xcc].toByteArray
  size_lt_wordModulus := by decide
}

def unknownSelector : Selector :=
  ⟨#v[0xde, 0xad, 0xbe, 0xef]⟩

def unknownInput : HostStorageDriver.InputData := {
  bytes := encodeCall unknownSelector argument
  size_lt_wordModulus := by
    simp [encodeCall_size, callSize, wordModulus]
}

def expectedLog : CheckedCoreWordLog := {
  emitter := target
  topic := logTopic
  payload := argument
}

def completionFuel : Nat := 1024

def runRaw (input : HostStorageDriver.InputData) (fuel : Nat) :=
  contract.runRaw target caller callValue input installed environment fuel

def runCanonical (fuel : Nat) :=
  contract.run target caller callValue selected argument installed environment fuel

end Tests.AbiStaticWordEndToEndFixture
