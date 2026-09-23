import Solcore.Abi.StaticWord
import Solcore.ContractRuntime.HostStorageDriver
import Solcore.ContractRuntime.WorldState

/-! Compile-time and runtime consumers for checked Static Word dispatchers. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
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

private def fMetadata : MethodMetadata :=
  .staticWord (name "f" (by decide))

private def fooMetadata : MethodMetadata :=
  .staticWord (name "foo" (by decide))

private def methods : List Method := [
  ⟨fMetadata, identityImplementation⟩,
  ⟨fooMetadata, incrementImplementation⟩
]

private def generated? : Option CheckedCoreContract :=
  match MethodTable.validate methods with
  | .error _ => none
  | .ok table => some table.generate

private def revertedValue (reason : Word) : Value :=
  .inRight .word (.inLeft .word (.word reason))

private def returnedValue (word : Word) : Value :=
  .inLeft (.sum .word .word) (.word word)

private def routeShape : List Word → Expr → Bool
  | [], .inRight .word (.inLeft .word (.word reason)) =>
      reason == unknownSelectorReason
  | selector :: rest,
      .ifE
        (.binary .wordEq (.var 1) (.word actualSelector))
        (.inLeft (.sum .word .word) (.apply _ (.var 0)))
        fallback =>
      actualSelector == selector && routeShape rest fallback
  | _, _ => false

/-- Recognize the calldata guards, host-index shifts, local layout, and routes. -/
private def hasDispatcherShape (table : MethodTable) : Bool :=
  match table.dispatchProgram.body with
  | .letE
      (.apply (.var sizeHost) .unit)
      (.ifE
        (.binary .wordGt (.word minimum) (.var 0))
        (.inRight .word (.inLeft .word (.word shortReason)))
        (.caseE
          (.apply (.var selectorHost) (.word selectorOffset))
          (.inRight .word (.inLeft .word (.word missingSelectorReason)))
          (.letE
            (.binary .wordShr (.var 0) (.word shift))
            (.caseE
              (.apply (.var argumentHost) (.word argumentOffset))
              (.inRight .word (.inLeft .word (.word missingArgumentReason)))
              routes)))) =>
      sizeHost == HostFunction.inputDataSize.index &&
        minimum == minimumCallDataSize &&
        shortReason == malformedCalldataReason &&
        selectorHost == HostFunction.inputDataWordBE?.index + 1 &&
        selectorOffset == Word.zero &&
        missingSelectorReason == malformedCalldataReason &&
        shift == selectorRightShift &&
        argumentHost == HostFunction.inputDataWordBE?.index + 3 &&
        argumentOffset.val == 4 &&
        missingArgumentReason == malformedCalldataReason &&
        routeShape
          (table.entries.map (fun entry => entry.selector.toWord)) routes
  | _ => false

private theorem compileTimeGeneratedContract : generated?.isSome = true := by
  native_decide

private theorem compileTimeKnownSelectors :
    fMetadata.selector.toUInt32.toNat = 0xb3de648b ∧
      fooMetadata.selector.toUInt32.toNat = 0x2fbebd38 := by
  native_decide

private theorem compileTimeReasonConstants :
    malformedCalldataReason.val = 0 ∧ unknownSelectorReason.val = 1 := by
  decide

private def checkedProgramShape : Bool :=
  match MethodTable.validate methods with
  | .error _ => false
  | .ok table => table.dispatchProgram.checkHost && hasDispatcherShape table

private theorem compileTimeProgramShape : checkedProgramShape = true := by
  native_decide

private def address : Address := ⟨0x10, by decide⟩

private def world : WorldState :=
  WorldState.empty.putAccount address Account.empty

private def context : HostStorageDriver.Context Unit Unit := {
  context := {
    storageAddress := address
    values := {
      checkpoint := ⟨world, ⟨(), ()⟩⟩
      working := (world, ⟨(), ()⟩)
    }
  }
  storageAccount := Account.empty
  storageAccount_present :=
    WorldState.account?_putAccount_same WorldState.empty address Account.empty
}

private def inputs (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := address
  callValue := Word.zero
  callerAddress := address
  inputData := inputData
  currentAddress := address
}

private def shortInput : HostStorageDriver.InputData := {
  bytes := ByteArray.empty
  size_lt_wordModulus := by decide
}

private def callInput (selector : Selector) (argument : Word) :
    HostStorageDriver.InputData := {
  bytes := encodeCall selector argument
  size_lt_wordModulus := by simp [encodeCall_size, callSize, wordModulus]
}

private def unknownSelector : Selector :=
  ⟨#v[0xde, 0xad, 0xbe, 0xef]⟩

private def argument : Word := ⟨0x123, by decide⟩
private def incremented : Word := ⟨0x124, by decide⟩

private def execute
    (inputData : HostStorageDriver.InputData) : Option HostDriverOutcome :=
  generated?.map fun contract =>
    (contract.code.runWithStorage context (inputs inputData) 256).outcome

private theorem compileTimeRuntimeRouting :
    execute shortInput = some (.done
      (revertedValue malformedCalldataReason) []) ∧
    execute (callInput unknownSelector argument) = some (.done
      (revertedValue unknownSelectorReason) []) ∧
    execute (callInput fMetadata.selector argument) = some (.done
      (returnedValue argument) []) ∧
    execute (callInput fooMetadata.selector argument) = some (.done
      (returnedValue incremented) []) := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testAbiStaticWordDispatcher : IO Unit := do
  assertTrue generated?.isSome
    "the validated Static Word table did not generate checked Core code"
  match MethodTable.validate methods with
  | .error _ =>
      throw (IO.userError "the distinct Static Word methods were rejected")
  | .ok table =>
      assertTrue table.dispatchProgram.checkHost
        "the ordinary host checker rejected generated dispatcher syntax"
      assertTrue (hasDispatcherShape table)
        "the generated dispatcher changed its guarded local or host layout"
  assertTrue
    (fMetadata.selector.toUInt32.toNat == 0xb3de648b &&
      fooMetadata.selector.toUInt32.toNat == 0x2fbebd38)
    "generated routes did not retain the known Ethereum selectors"
  assertTrue
    (execute shortInput == some (.done
      (revertedValue malformedCalldataReason) []))
    "short calldata did not complete with malformed reason zero"
  assertTrue
    (execute (callInput unknownSelector argument) == some (.done
      (revertedValue unknownSelectorReason) []))
    "an unknown selector did not complete with reason one"
  assertTrue
    (execute (callInput fMetadata.selector argument) == some (.done
      (returnedValue argument) []))
    "the identity route did not receive the decoded ABI word"
  assertTrue
    (execute (callInput fooMetadata.selector argument) == some (.done
      (returnedValue incremented) []))
    "the increment route did not execute its checked implementation"

end Tests
