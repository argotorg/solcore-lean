import Solcore.Abi.Keccak256
import Solcore.Abi.StaticWord
import Solcore.ContractRuntime.Internal.WorldStateDeltaLaws
import Solcore.ContractRuntime.Internal.BalancedLaws
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.ContractRuntime.WorldState

/-!
# Static Word ABI tests

Static Word ABI codecs, metadata, method tables and dispatchers, routing and finalization end to end,
and the Keccak helper.
-/

section
-- leanmerge: from Solcore.Test.AbiKeccak256
/-! Runtime known-answer tests for Ethereum-compatible Keccak-256. -/

set_option autoImplicit false

namespace Tests

open Solcore.Abi.V1
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def assertDigest
    (label : String) (input : Bytes) (expected : String) : IO Unit := do
  let digest := Keccak256.hash input
  assertTrue (digest.size == 32)
    (label ++ " must produce exactly 32 bytes")
  assertTrue (encodeBytesText digest == expected)
    (label ++ " must match its independent Keccak-256 vector")

private def assertTextDigest
    (text expected : String) : IO Unit :=
  assertDigest text text.toByteArray expected

private def sequentialBytes (count : Nat) : Bytes :=
  ((List.range count).map UInt8.ofNat).toByteArray

-- Compile-only consumers keep the total padding, absorption, and squeeze
-- boundaries usable outside the implementation module.
private example (input : Bytes) :
    Keccak256.paddedSize input =
      Keccak256.rateBytes * (input.size / Keccak256.rateBytes + 1) := by
  exact Keccak256.paddedSize_eq_rate_mul input

private example (input : Bytes) :
    Keccak256.paddedSize input % Keccak256.rateBytes = 0 := by
  exact Keccak256.paddedSize_mod_rateBytes_eq_zero input

private example
    (input : Bytes) (block lane index : Nat)
    (blockLt : block < Keccak256.paddedSize input / Keccak256.rateBytes)
    (laneLt : lane < 17)
    (indexLt : index < 8) :
    block * Keccak256.rateBytes + 8 * lane + index <
      Keccak256.paddedSize input := by
  exact Keccak256.absorbReadInBounds input block lane index
    blockLt laneLt indexLt

private example (input : Bytes) : (Keccak256.hash input).size = 32 := by
  exact Keccak256.hash_size input

def testAbiKeccak256 : IO Unit := do
  assertTextDigest ""
    "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
  assertTextDigest "abc"
    "0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

  -- Complete digests retain the selector as their first four bytes.
  assertTextDigest "f(uint256)"
    "0xb3de648b001c08ab857afe5a9633887e7a4e2a429d1d8d4231238c1ffaeb256f"
  assertTextDigest "foo(uint256)"
    "0x2fbebd3821c4e005fbe0a9002cc1bd25dc266d788dba1dbcb39cc66a07e7b38b"
  assertTextDigest "transfer(address,uint256)"
    "0xa9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b"

  -- Inputs are the octets 0x00 through 0x86, 0x87, or 0x88 respectively.
  -- These straddle the 136-byte Keccak rate and exercise both padding forms.
  assertDigest "135-byte rate predecessor" (sequentialBytes 135)
    "0xcbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62"
  assertDigest "136-byte full rate block" (sequentialBytes 136)
    "0x7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e"
  assertDigest "137-byte rate successor" (sequentialBytes 137)
    "0xac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db"

end Tests
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordEndToEndFixture
/-! Explicit ABI/world fixture for the first Static Word vertical execution. -/

set_option autoImplicit false

namespace Tests.AbiStaticWordEndToEndFixture

open Solcore.Core
open Solcore.ContractRuntime
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
  (StaticWordContract.validate methods).toOption

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
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordEndToEnd
/-! Executable vertical checks for Static Word ABI routing and finalization. -/

set_option autoImplicit false

namespace Tests.AbiStaticWordEndToEnd

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.BalancedTopLevelExecution
open Solcore.ContractRuntime.OneLevelNestedExecution
open Solcore.Abi.V1
open Tests.AbiStaticWordEndToEndFixture

private def storageAt?
    (world : WorldState) (slot : Word) : Option Word :=
  world.readStorage? target slot

private def terminal?
    {initial : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initial root invocation) :
    Option (TerminalResult initial root invocation) :=
  match result.view with
  | .rejected _ => none
  | .execution execution =>
      match execution.view with
      | .completed terminal => some terminal
      | .outOfFuel _ _ _ => none

/-- A proof-irrelevant projection used to compare dependent raw/convenience runs. -/
private structure TerminalObservation where
  outcome : FrameOutcome Word
  callerFinal : Option Word
  targetFinal : Option Word
  storedFinal : Option Word
  logs : List CheckedCoreWordLog
  committedLogs : List CheckedCoreWordLog
  storageEndpoints : Option Word × Option Word
  callerBalanceEndpoints : Option Word × Option Word
  targetBalanceEndpoints : Option Word × Option Word
  deriving BEq

private def observeTerminal?
    {initial : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initial root invocation) :
    Option TerminalObservation := do
  let terminal ← terminal? result
  some {
    outcome := terminal.outcome
    callerFinal := terminal.finalWorld.balance? caller
    targetFinal := terminal.finalWorld.balance? target
    storedFinal := storageAt? terminal.finalWorld storageSlot
    logs := terminal.workingJournal.logList
    committedLogs := terminal.committedJournal.logList
    storageEndpoints :=
      terminal.committedDelta.storageEndpoints target storageSlot
    callerBalanceEndpoints :=
      terminal.committedDelta.balanceEndpoints caller
    targetBalanceEndpoints :=
      terminal.committedDelta.balanceEndpoints target
  }

private def successChecksFor
    {initial : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initial root invocation) : Bool :=
  match terminal? result with
  | none => false
  | some terminal =>
      terminal.outcome == .returned (encodeResult argument) &&
        terminal.finalWorld.balance? caller == some callerBalanceAfter &&
        terminal.finalWorld.balance? target == some targetBalanceAfter &&
        storageAt? terminal.finalWorld storageSlot == some argument &&
        terminal.workingJournal.logList == [expectedLog] &&
        terminal.committedJournal.logList == [expectedLog] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.committedDelta.storageEndpoints target storageSlot ==
          (some Word.zero, some argument) &&
        terminal.committedDelta.slotChange? target storageSlot ==
          some (some Word.zero, some argument) &&
        terminal.committedDelta.balanceEndpoints caller ==
          (some callerBalance, some callerBalanceAfter) &&
        terminal.committedDelta.balanceEndpoints target ==
          (some targetBalance, some targetBalanceAfter)

private def canonicalAndSuffixCommit : Bool :=
  let canonical := runCanonical completionFuel
  let rawCanonical := runRaw canonicalInput completionFuel
  let suffixed := runRaw suffixedInput completionFuel
  successChecksFor canonical && successChecksFor rawCanonical &&
    successChecksFor suffixed &&
    observeTerminal? canonical == observeTerminal? rawCanonical &&
    observeTerminal? canonical == observeTerminal? suffixed

private def rollbackChecks
    (input : HostStorageDriver.InputData) (reason : Word) : Bool :=
  match terminal? (runRaw input completionFuel) with
  | none => false
  | some terminal =>
      let checkpoint :=
        terminal.terminalContext.context.values.checkpoint.state
      terminal.outcome == .reverted (encodeResult reason) &&
        terminal.finalWorld.balance? caller == some callerBalance &&
        terminal.finalWorld.balance? target == some targetBalance &&
        storageAt? terminal.finalWorld storageSlot == some Word.zero &&
        checkpoint.balance? caller == some callerBalance &&
        checkpoint.balance? target == some targetBalance &&
        storageAt? checkpoint storageSlot == some Word.zero &&
        terminal.terminalContext.context.values.checkpoint.effects.rollback.logList ==
          [] &&
        terminal.workingJournal.logList == [] &&
        terminal.committedJournal.logList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.committedDelta.storageEndpoints target storageSlot ==
          (some Word.zero, some Word.zero) &&
        terminal.committedDelta.slotChange? target storageSlot == none &&
        terminal.committedDelta.balanceEndpoints caller ==
          (some callerBalance, some callerBalance) &&
        terminal.committedDelta.balanceEndpoints target ==
          (some targetBalance, some targetBalance) &&
        terminal.committedDelta.balanceChange? caller == none &&
        terminal.committedDelta.balanceChange? target == none

private def routingRollback : Bool :=
  rollbackChecks shortInput malformedCalldataReason &&
    rollbackChecks unknownInput unknownSelectorReason

private structure InFlightObservation where
  callerWorking : Option Word
  targetWorking : Option Word
  storedWorking : Option Word
  logs : List CheckedCoreWordLog
  deriving BEq

private def observeRootOutOfFuel?
    {initial : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initial root invocation) :
    Option InFlightObservation :=
  match result.view with
  | .rejected _ => none
  | .execution execution =>
      match execution.view with
      | .completed _ => none
      | .outOfFuel _ (.root frame) _ =>
          let working := frame.context.context.values.working.1
          some {
            callerWorking := working.balance? caller
            targetWorking := working.balance? target
            storedWorking := storageAt? working storageSlot
            logs := frame.context.workingJournal.logList
          }
      | .outOfFuel _ (.child _) _ => none
      | .outOfFuel _ (.initializer _) _ => none

private def transferredBeforeMethod : InFlightObservation := {
  callerWorking := some callerBalanceAfter
  targetWorking := some targetBalanceAfter
  storedWorking := some Word.zero
  logs := []
}

private def afterSingleLog : InFlightObservation := {
  callerWorking := some callerBalanceAfter
  targetWorking := some targetBalanceAfter
  storedWorking := some argument
  logs := [expectedLog]
}

private def findSplit
    (expected : InFlightObservation) : Nat → Nat → Option Nat
  | _, 0 => none
  | fuel, remaining + 1 =>
      if observeRootOutOfFuel? (runCanonical fuel) == some expected then
        some fuel
      else
        findSplit expected (fuel + 1) remaining

private def zeroFuelIsGenuine : Bool :=
  (observeRootOutOfFuel? (runCanonical 0)).isSome

/-- Recognize the exact scheduler boundary after selector routing has entered
the selected method but before its first storage effect is handled.  The
result itself must be root fuel exhaustion; the retained Core control must be
ready to emit the fixture's first `storageWrite` suspension. -/
def beforeFirstMethodEffect (fuel : Nat) : Bool :=
  let result := runCanonical fuel
  match result.view with
  | .rejected _ => false
  | .execution execution =>
      match execution.view with
      | .completed _ => false
      | .outOfFuel _ (.root frame) _ =>
          match frame.state.control, frame.state.continuation,
              hostAdvance frame.state with
          | .ret (.pair (.word slot) (.word value)),
              .hostApply .storageWrite :: _,
              HostAdvanceResult.suspended suspension =>
              match suspension.request with
              | .storageWrite requestedSlot requestedValue =>
                  slot == storageSlot && value == argument &&
                    requestedSlot == storageSlot &&
                    requestedValue == argument &&
                    observeRootOutOfFuel? result ==
                      some transferredBeforeMethod
              | _ => false
          | _, _, _ => false
      | .outOfFuel _ (.child _) _ => false
      | .outOfFuel _ (.initializer _) _ => false

private def findBeforeFirstMethodEffect : Nat → Nat → Option Nat
  | _, 0 => none
  | fuel, remaining + 1 =>
      if beforeFirstMethodEffect fuel then
        some fuel
      else
        findBeforeFirstMethodEffect (fuel + 1) remaining

def beforeFirstMethodEffectFound : Bool :=
  match findBeforeFirstMethodEffect 1 512 with
  | some fuel => beforeFirstMethodEffect fuel
  | none => false

/-- Kernel-checkable evidence that the bounded fixture reaches precisely the
post-dispatch/pre-effect boundary, rather than merely sharing its world-state
observation with an earlier Core control point. -/
theorem beforeFirstMethodEffect_found_exact :
    beforeFirstMethodEffectFound = true := by
  native_decide

/-- The ABI wrapper consumes, without weakening, the balanced runner's exact
split-fuel equality.  In particular the value-transfer preflight and every
dispatcher or method effect occur exactly once. -/
theorem runCanonical_split_fuel (fuel additional : Nat) :
    BalancedTopLevelExecution.resumeWithFuel (runCanonical fuel) additional =
      runCanonical (fuel + additional) := by
  simpa [runCanonical, StaticWordContract.run, StaticWordContract.runRaw,
    StaticWordContract.callInvocation,
    Tests.AbiStaticWordEndToEndFixture.runRaw] using
    BalancedTopLevelExecution.resumeWithFuel_runWithEnvironment
      contract.checkedCore
      (StaticWordContract.callInvocation target caller callValue selected
        argument)
      installed environment fuel additional

private def resumedMatchesOneShot (splitFuel : Nat) : Bool :=
  let prefixRun := runCanonical splitFuel
  let resumed :=
    BalancedTopLevelExecution.resumeWithFuel prefixRun completionFuel
  let oneShot := runCanonical (splitFuel + completionFuel)
  successChecksFor resumed &&
    observeTerminal? resumed == observeTerminal? oneShot

private def dispatchAndLogResumption : Bool :=
  match findBeforeFirstMethodEffect 1 512,
      findSplit afterSingleLog 1 512 with
  | some dispatchFuel, some logFuel =>
      dispatchFuel < logFuel &&
        resumedMatchesOneShot dispatchFuel && resumedMatchesOneShot logFuel
  | _, _ => false

private def allChecks : Bool :=
  canonicalAndSuffixCommit && routingRollback && zeroFuelIsGenuine &&
    dispatchAndLogResumption

private theorem allChecks_exact : allChecks = true := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def testAbiStaticWordEndToEnd : IO Unit := do
  assertTrue canonicalAndSuffixCommit
    "canonical, suffixed, raw, or convenience ABI execution diverged"
  assertTrue routingRollback
    "malformed or unknown ABI routing did not roll value and state back"
  assertTrue zeroFuelIsGenuine
    "zero fuel did not retain a resumable ABI execution"
  assertTrue beforeFirstMethodEffectFound
    "ABI execution did not expose the exact post-dispatch/pre-effect boundary"
  assertTrue dispatchAndLogResumption
    "ABI resumption replayed dispatch, balance, storage, or the emitted log"

end Tests.AbiStaticWordEndToEnd
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordCodec
/-! External boundary consumers for the Static Word ABI byte codecs. -/
set_option autoImplicit false
namespace Tests
open Solcore
open Solcore.Abi.V1
open Solcore.ContractRuntime
private def fSelector : Selector :=
  ⟨#v[0xb3, 0xde, 0x64, 0x8b]⟩
private def argument : Core.Word :=
  ⟨0x123, by decide⟩
private def expectedCall : StaticWordCall :=
  ⟨fSelector, argument⟩
private def canonicalCalldata : Bytes :=
  ([0xb3, 0xde, 0x64, 0x8b] ++
    List.replicate 30 (0 : UInt8) ++ [0x01, 0x23]).toByteArray

private def calldata35 : Bytes :=
  canonicalCalldata.extract 0 35
private def calldata37 : Bytes :=
  canonicalCalldata.append [0xff].toByteArray
private def returndata31 : Bytes :=
  (List.replicate 31 (0 : UInt8)).toByteArray
private def returndata33 : Bytes :=
  (encodeResult argument).append [0xff].toByteArray

private theorem canonicalCalldata_eq :
    canonicalCalldata = encodeCall fSelector argument := by
  native_decide

private theorem compileTimeCallBoundaries :
    encodeCall fSelector argument = canonicalCalldata ∧
      decodeCall calldata35 = .error (.shortCalldata 35) ∧
      decodeCall canonicalCalldata = .ok expectedCall ∧
      decodeCall calldata37 = .ok expectedCall := by
  refine ⟨canonicalCalldata_eq.symm, ?_, ?_, ?_⟩
  · apply (decodeCall_eq_shortCalldata_iff calldata35).2
    native_decide
  · rw [canonicalCalldata_eq]
    exact decodeCall_encode fSelector argument
  · unfold calldata37
    rw [canonicalCalldata_eq]
    exact decodeCall_encode_append fSelector argument _

private theorem compileTimeResultBoundaries :
    decodeResult returndata31 = .error (.invalidLength 31) ∧
      decodeResult (encodeResult argument) = .ok argument ∧
      decodeResult returndata33 = .error (.invalidLength 33) := by
  refine ⟨?_, decodeResult_encode argument, ?_⟩
  · apply (decodeResult_eq_invalidLength_iff returndata31).2
    native_decide
  · have invalid := (decodeResult_eq_invalidLength_iff returndata33).2
      (by native_decide)
    simpa [returndata33, resultSize] using invalid

private theorem compileTimeCallFailureDisjoint :
    decodeCall calldata35 ≠ .ok expectedCall := by
  apply decodeCall_failure_ne_success calldata35 (.shortCalldata 35)
  exact compileTimeCallBoundaries.2.1

private theorem compileTimeResultFailureDisjoint :
    decodeResult returndata31 ≠ .ok argument := by
  apply decodeResult_failure_ne_success returndata31 (.invalidLength 31)
  exact compileTimeResultBoundaries.1

private def matchesCall (result : Except CallDecodeFailure StaticWordCall) : Bool :=
  match result with | .ok call => call == expectedCall | _ => false

private def matchesCallFailure (result : Except CallDecodeFailure StaticWordCall) : Bool :=
  match result with | .error (.shortCalldata size) => size == 35 | _ => false

private def matchesResult (result : Except ResultDecodeFailure Core.Word) : Bool :=
  match result with | .ok word => word == argument | _ => false

private def matchesResultFailure
    (size : Nat) (result : Except ResultDecodeFailure Core.Word) : Bool :=
  match result with | .error (.invalidLength actual) => actual == size | _ => false

def testAbiStaticWordCodec : IO Unit := do
  assertTrue (encodeCall fSelector argument == canonicalCalldata)
    "calldata must be the exact selector followed by one big-endian word"
  assertTrue (canonicalCalldata.size == 36)
    "canonical calldata must contain exactly 36 bytes"
  assertTrue (matchesCallFailure (decodeCall calldata35))
    "35-byte calldata must report its structured short-calldata failure"
  assertTrue (matchesCall (decodeCall canonicalCalldata))
    "36-byte calldata must round-trip its selector and argument"
  assertTrue (matchesCall (decodeCall calldata37))
    "a suffix after the 36-byte call prefix must be ignored"

  assertTrue (matchesResultFailure 31 (decodeResult returndata31))
    "31-byte returndata must fail strict result decoding"
  assertTrue (matchesResult (decodeResult (encodeResult argument)))
    "32-byte returndata must round-trip its word"
  assertTrue (matchesResultFailure 33 (decodeResult returndata33))
    "33-byte returndata must fail strict result decoding"

end Tests
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordContract
/-! Admission and balanced-entry consumers for Static Word ABI contracts. -/

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

private def identityMethod : Method := {
  metadata := .staticWord (name "identity" (by decide))
  implementation := identityImplementation
}

private def incrementMethod : Method := {
  metadata := .staticWord (name "increment" (by decide))
  implementation := incrementImplementation
}

private def methods : List Method := [identityMethod, incrementMethod]

private def target : Address := ⟨0x51, by decide⟩
private def caller : Address := ⟨0x52, by decide⟩
private def argument_variant : Word := ⟨0x123, by decide⟩

private def admissionAccepted : Bool :=
  match StaticWordContract.validate methods with
  | .error _ => false
  | .ok _ => true

private theorem admissionAccepted_exact : admissionAccepted = true := by
  native_decide

/-- A consumer can recover both sealed provenance equations after admission. -/
private theorem admittedCarriesExactProvenance
    (contract : StaticWordContract methods) :
    MethodTable.validate methods = .ok contract.table ∧
      contract.checkedCore = contract.table.generate :=
  ⟨contract.table_valid, contract.checkedCore_eq⟩

private def invocationBytesAgree : Bool :=
  match StaticWordContract.validate methods with
  | .error _ => false
  | .ok contract =>
      let selected := contract.firstMember
      let canonical := StaticWordContract.callInvocation
        target caller Word.zero selected argument_variant
      let raw := StaticWordContract.rawInvocation target caller Word.zero
        (selected.inputData argument_variant)
      raw.inputData.bytes == canonical.inputData.bytes &&
        canonical.inputData.bytes ==
          encodeCall selected.indexed.selector argument_variant

private theorem invocationBytesAgree_exact : invocationBytesAgree = true := by
  native_decide

private def accountFor
    (contract : StaticWordContract methods) : Account :=
  Account.empty.withCode contract.checkedCore.code

private def worldFor
    (contract : StaticWordContract methods) : WorldState :=
  WorldState.empty.putAccount target (accountFor contract)

/-- The installation witness retains the admitted dispatcher's exact type. -/
private def installedFor
    (contract : StaticWordContract methods) :
    InstalledCheckedCoreContract (worldFor contract) target
      contract.checkedCore := {
  account := accountFor contract
  account_present := by rfl
  code_present := by rfl
}

private def environment : ExecutionEnvironment :=
  .callsOnly { lookup := fun _ => none }

/-- The convenience entry is definitionally the raw balanced entry. -/
private theorem convenienceDelegatesExactly
    (contract : StaticWordContract methods)
    (selected : contract.Member)
    (fuel : Nat) :
    contract.run target caller Word.zero selected argument_variant
        (installedFor contract) environment fuel =
      contract.runRaw target caller Word.zero (selected.inputData argument_variant)
        (installedFor contract) environment fuel := by
  rfl

private def dependentEntriesRun : Bool :=
  match StaticWordContract.validate methods with
  | .error _ => false
  | .ok contract =>
      let selected := contract.firstMember
      let raw := contract.runRaw target caller Word.zero
        (selected.inputData argument_variant) (installedFor contract) environment 0
      let canonical := contract.run target caller Word.zero selected argument_variant
        (installedFor contract) environment 0
      match raw.view, canonical.view with
      | .execution _, .execution _ => true
      | _, _ => false

private theorem dependentEntriesRun_exact : dependentEntriesRun = true := by
  native_decide

def testAbiStaticWordContract : IO Unit := do
  assertTrue admissionAccepted
    "the identity/increment Static Word contract was not admitted"
  assertTrue invocationBytesAgree
    "raw and membership-sealed ABI invocations used different calldata"
  assertTrue dependentEntriesRun
    "the admitted contract did not enter both balanced execution adapters"

end Tests
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordDispatcher
/-! Compile-time and runtime consumers for checked Static Word dispatchers. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Abi.V1

private def fMetadata : MethodMetadata :=
  .staticWord (name "f" (by decide))

private def fooMetadata : MethodMetadata :=
  .staticWord (name "foo" (by decide))

private def methods_variant : List Method := [
  ⟨fMetadata, identityImplementation⟩,
  ⟨fooMetadata, incrementImplementation⟩
]

private def generated? : Option CheckedCoreContract :=
  match MethodTable.validate methods_variant with
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
  match MethodTable.validate methods_variant with
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

private def incremented : Word := ⟨0x124, by decide⟩

private def execute
    (inputData : HostStorageDriver.InputData) : Option HostDriverOutcome :=
  generated?.map fun contract =>
    (contract.code.runWithStorage context (inputs inputData) 256).outcome

private theorem compileTimeRuntimeRouting :
    execute shortInput = some (.done
      (revertedValue malformedCalldataReason) []) ∧
    execute (callInput unknownSelector argument_variant) = some (.done
      (revertedValue unknownSelectorReason) []) ∧
    execute (callInput fMetadata.selector argument_variant) = some (.done
      (returnedValue argument_variant) []) ∧
    execute (callInput fooMetadata.selector argument_variant) = some (.done
      (returnedValue incremented) []) := by
  native_decide

def testAbiStaticWordDispatcher : IO Unit := do
  assertTrue generated?.isSome
    "the validated Static Word table did not generate checked Core code"
  match MethodTable.validate methods_variant with
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
    (execute (callInput unknownSelector argument_variant) == some (.done
      (revertedValue unknownSelectorReason) []))
    "an unknown selector did not complete with reason one"
  assertTrue
    (execute (callInput fMetadata.selector argument_variant) == some (.done
      (returnedValue argument_variant) []))
    "the identity route did not receive the decoded ABI word"
  assertTrue
    (execute (callInput fooMetadata.selector argument_variant) == some (.done
      (returnedValue incremented) []))
    "the increment route did not execute its checked implementation"

end Tests
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordImplementation
/-! Admission regressions for checked Static Word method implementations. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Abi.V1

private def one : Word := ⟨1, by decide⟩

private theorem identityProgram_checked :
    identityProgram.checkHost = true := by
  decide

private def identityCode : CheckedHostCoreProgram :=
  ⟨identityProgram, identityProgram_checked⟩

example : ∃ implementation,
    WordImplementation.ofCode? identityCode = some implementation :=
  (WordImplementation.ofCode?_exists_iff identityCode).2 ⟨rfl, rfl⟩

private def arithmeticProgram : Program := {
  resultType := .function .word .word
  body :=
    .lambda .word .word
      (.binary .wordAdd (.var 0) (.word one))
}

private theorem arithmeticProgram_checked :
    arithmeticProgram.checkHost = true := by
  decide

private def arithmeticCode : CheckedHostCoreProgram :=
  ⟨arithmeticProgram, arithmeticProgram_checked⟩

example : ∃ implementation,
    WordImplementation.ofCode? arithmeticCode = some implementation :=
  (WordImplementation.ofCode?_exists_iff arithmeticCode).2 ⟨rfl, rfl⟩

/-- The method parameter shifts every fixed host capability by one slot. -/
private def storageReadProgram : Program := {
  resultType := .function .word .word
  body :=
    .lambda .word .word
      (.apply
        (.var (HostFunction.storageRead.index + 1))
        (.var 0))
}

private theorem storageReadProgram_checked :
    storageReadProgram.checkHost = true := by
  decide

private def storageReadCode : CheckedHostCoreProgram :=
  ⟨storageReadProgram, storageReadProgram_checked⟩

example : ∃ implementation,
    WordImplementation.ofCode? storageReadCode = some implementation :=
  (WordImplementation.ofCode?_exists_iff storageReadCode).2 ⟨rfl, rfl⟩

private def wrongResultProgram : Program := {
  resultType := .function .word .bool
  body := .lambda .word .bool (.bool true)
}

private theorem wrongResultProgram_checked :
    wrongResultProgram.checkHost = true := by
  decide

private def wrongResultCode : CheckedHostCoreProgram :=
  ⟨wrongResultProgram, wrongResultProgram_checked⟩

example : WordImplementation.ofCode? wrongResultCode = none := by
  apply (WordImplementation.ofCode?_eq_none_iff wrongResultCode).2
  left
  decide

private def namedDefinition : DataDefinition := {
  constructorPayloadTypes := []
}

private def nonemptyDefinitionsProgram : Program := {
  resultType := .function .word .word
  body := .lambda .word .word (.var 0)
  dataDefinitions := [namedDefinition]
}

private theorem nonemptyDefinitionsProgram_checked :
    nonemptyDefinitionsProgram.checkHost = true := by
  decide

private def nonemptyDefinitionsCode : CheckedHostCoreProgram :=
  ⟨nonemptyDefinitionsProgram, nonemptyDefinitionsProgram_checked⟩

example : WordImplementation.ofCode? nonemptyDefinitionsCode = none := by
  apply (WordImplementation.ofCode?_eq_none_iff
    nonemptyDefinitionsCode).2
  right
  decide

private def rejectedProgram : Program := {
  resultType := .function .word .word
  body := .lambda .word .word (.bool true)
}

private theorem rejectedProgram_rejected :
    rejectedProgram.checkHost = false := by
  decide

example : WordImplementation.ofProgram? rejectedProgram = none :=
  WordImplementation.ofProgram?_of_rejected
    rejectedProgram rejectedProgram_rejected

end Tests
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordMetadata
/-! External consumers for Static Word ABI names, metadata, and selectors. -/

set_option autoImplicit false

namespace Tests

open Solcore.Abi.V1

private def bytes (values : List UInt8) : ByteArray :=
  values.toByteArray

private def fName : MethodName :=
  ⟨"f", by decide⟩

private def fooName : MethodName :=
  ⟨"foo", by decide⟩

private def fMetadata_variant : MethodMetadata :=
  .staticWord fName

private def fooMetadata_variant : MethodMetadata :=
  .staticWord fooName

private def fSelectorBytes : ByteArray :=
  bytes [0xb3, 0xde, 0x64, 0x8b]

private def fooSelectorBytes : ByteArray :=
  bytes [0x2f, 0xbe, 0xbd, 0x38]

private def transferSelectorBytes : ByteArray :=
  bytes [0xa9, 0x05, 0x9c, 0xbb]

private theorem compileTimeCanonicalSignature :
    fMetadata_variant.canonicalSignatureBytes = "f(uint256)".toUTF8 := by
  native_decide

private theorem compileTimeCanonicalTypes :
    fMetadata_variant.inputType = .uint256 ∧
      fMetadata_variant.outputType = .uint256 := by
  decide

private theorem compileTimeSelectorPrefix :
    fMetadata_variant.selector.encode = fSelectorBytes := by
  native_decide

private theorem compileTimeAsciiBoundary :
    isValidMethodName "A_09z" = true ∧
      isValidMethodName "9bad" = false ∧
      isValidMethodName "aβ" = false := by
  native_decide

private def testMethodNames : IO Unit := do
  let accepted := ["f", "_", "A_09z", "snake_case2"]
  let rejected := ["", "9bad", "has-dash", "aβ", "é", "$bad"]
  assertTrue
    (accepted.all fun text => (validateMethodName? text).isSome)
    "Static Word method names must accept the complete ASCII identifier grammar"
  assertTrue
    (rejected.all fun text => (validateMethodName? text).isNone)
    "Static Word method names must reject empty, malformed, and non-ASCII spellings"

private def testCanonicalMetadata : IO Unit := do
  assertTrue
    (fMetadata_variant.canonicalSignatureText == "f(uint256)" &&
      fMetadata_variant.canonicalSignatureBytes == "f(uint256)".toUTF8)
    "canonical signatures must spell the explicit input type exactly"
  assertTrue
    (fMetadata_variant.inputType == .uint256 && fMetadata_variant.outputType == .uint256)
    "metadata must retain both the input and output types"

private def testKnownSelectors : IO Unit := do
  assertTrue (fMetadata_variant.selector.encode == fSelectorBytes)
    "f(uint256) must have selector b3de648b"
  assertTrue (fooMetadata_variant.selector.encode == fooSelectorBytes)
    "foo(uint256) must have selector 2fbebd38"
  assertTrue
    ((selectorFromSignatureBytes
      "transfer(address,uint256)".toUTF8).encode == transferSelectorBytes)
    "raw canonical signature bytes must produce transfer selector a9059cbb"
  assertTrue (fMetadata_variant.selector.toFin.val == 0xb3de648b)
    "the Fin (2^32) selector view must use big-endian byte order"

private def testSelectorCodec : IO Unit := do
  let selector := fMetadata_variant.selector
  assertTrue (Selector.decode? selector.encode == some selector)
    "an exact four-byte selector must round-trip"
  assertTrue ((Selector.decode? (bytes [0xb3, 0xde, 0x64])).isNone)
    "selector decoding must reject three bytes"
  assertTrue
    ((Selector.decode? (bytes [0xb3, 0xde, 0x64, 0x8b, 0])).isNone)
    "selector decoding must reject five bytes"

def testAbiStaticWordMetadata : IO Unit := do
  testMethodNames
  testCanonicalMetadata
  testKnownSelectors
  testSelectorCodec

end Tests
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordMetadataProperties
/-! External compile consumers for Static Word ABI metadata proof contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Abi.V1
open Solcore.ContractRuntime

private theorem compileTimeKeccakWidth (input : Bytes) :
    (Keccak256.hash input).size = 32 :=
  Keccak256.hash_size input

private theorem compileTimeValidatorSuccessIff (text : String) :
    (validateMethodName? text).isSome ↔
      isValidMethodName text = true :=
  validateMethodName?_isSome_iff text

private theorem compileTimeValidatorTextSeal
    {text : String} {name : MethodName}
    (success : validateMethodName? text = some name) :
    name.text = text :=
  validateMethodName?_success_text success

private theorem compileTimeValidatorConstructorIff
    (text : String) (name : MethodName) :
    validateMethodName? text = some name ↔ name.text = text :=
  validateMethodName?_eq_some_iff text name

private theorem compileTimeSelectorDecodeInverse
    {bytes : Bytes} {selector : Selector}
    (success : Selector.decode? bytes = some selector) :
    selector.encode = bytes :=
  Selector.encode_of_decode?_eq_some success

private theorem compileTimeSelectorCodecIff
    (bytes : Bytes) (selector : Selector) :
    Selector.decode? bytes = some selector ↔
      bytes = selector.encode :=
  Selector.decode?_eq_some_iff bytes selector

private theorem compileTimeSelectorDigestPrefix (signature : Bytes) :
    (selectorFromSignatureBytes signature).encode =
      (Keccak256.hash signature).extract 0 4 :=
  selectorFromSignatureBytes_encode signature

private theorem compileTimeSelectorBigEndian (selector : Selector) :
    selector.toUInt32 =
        ((selector.bytes[0].toUInt32 <<< 8 |||
            selector.bytes[1].toUInt32) <<< 8 |||
          selector.bytes[2].toUInt32) <<< 8 |||
        selector.bytes[3].toUInt32 ∧
      selector.toFin.val =
        (((selector.bytes[0].toUInt32 <<< 8 |||
            selector.bytes[1].toUInt32) <<< 8 |||
          selector.bytes[2].toUInt32) <<< 8 |||
        selector.bytes[3].toUInt32).toNat := by
  exact ⟨selector.toUInt32_eq_bigEndianBytes,
    selector.toFin_val_eq_bigEndianBytes⟩

/-- All checks in this module are elaboration-time proof consumers. -/
def testAbiStaticWordMetadataProperties : IO Unit :=
  pure ()

end Tests
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordMethodTable
/-! Consumers for deterministic Static Word method-table validation. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Abi.V1

private def identityCode_variant : CheckedHostCoreProgram :=
  ⟨identityProgram, by decide⟩

private def identityImplementation_variant : WordImplementation :=
  ⟨identityCode_variant, rfl, rfl⟩

private def method (methodName : MethodName) : Method where
  metadata := .staticWord methodName
  implementation := identityImplementation_variant

private def methodWith
    (methodName : MethodName) (implementation : WordImplementation) : Method where
  metadata := .staticWord methodName
  implementation := implementation

private def fMethod : Method := method (name "f" (by decide))
private def fIncrementMethod : Method :=
  methodWith (name "f" (by decide)) incrementImplementation
private def fooMethod : Method := method (name "foo" (by decide))
private def collisionLow : Method := method (name "f116643" (by decide))
private def collisionHigh : Method := method (name "f38491" (by decide))

private structure ErrorSummary where
  kind : Nat
  firstSignature : String
  secondSignature : String
  selector : Nat
  deriving BEq, DecidableEq

private def summarizeError : MethodTableError → ErrorSummary
  | .empty => ⟨0, "", "", 0⟩
  | .duplicateSignature _ _ signature =>
      ⟨1, signature, signature, 0⟩
  | .selectorCollision _ _ first second selector =>
      ⟨2, first, second, selector.toUInt32.toNat⟩

private def summarizeResult
    (result : Except MethodTableError MethodTable) : ErrorSummary :=
  match result with
  | .error error => summarizeError error
  | .ok _ => ⟨3, "", "", 0⟩

private def duplicateSummary : ErrorSummary :=
  ⟨1, "f(uint256)", "f(uint256)", 0⟩

private def collisionSummary : ErrorSummary :=
  ⟨2, "f116643(uint256)", "f38491(uint256)", 0x77dbd42e⟩

private theorem compileTimeEmptyRejected :
    summarizeResult (MethodTable.validate []) = ⟨0, "", "", 0⟩ := by
  native_decide

private theorem compileTimeDuplicateNormalized :
    summarizeResult (MethodTable.validate [fMethod, fIncrementMethod]) =
      duplicateSummary ∧
    summarizeResult (MethodTable.validate [fIncrementMethod, fMethod]) =
      duplicateSummary := by
  native_decide

private theorem compileTimeKnownCollision :
    collisionLow.metadata.selector.toUInt32.toNat = 0x77dbd42e ∧
      collisionHigh.metadata.selector.toUInt32.toNat = 0x77dbd42e := by
  native_decide

private theorem compileTimeCollisionNormalized :
    summarizeResult
        (MethodTable.validate [collisionHigh, collisionLow]) =
      collisionSummary ∧
    summarizeResult
        (MethodTable.validate [collisionLow, collisionHigh]) =
      collisionSummary := by
  native_decide

private def acceptedSignatures (methods : List Method) : Option (List String) :=
  match MethodTable.validate methods with
  | .error _ => none
  | .ok table => some (table.entries.map IndexedMethod.signature)

private theorem compileTimeDistinctAccepted :
    acceptedSignatures [fooMethod, fMethod] =
      some ["f(uint256)", "foo(uint256)"] := by
  native_decide

def testAbiStaticWordMethodTable : IO Unit := do
  assertTrue
    (summarizeResult (MethodTable.validate []) == ⟨0, "", "", 0⟩)
    "an empty Static Word method table must be rejected"
  let duplicateForward := summarizeResult
    (MethodTable.validate [fMethod, fIncrementMethod])
  let duplicateReverse := summarizeResult
    (MethodTable.validate [fIncrementMethod, fMethod])
  assertTrue
    (duplicateForward == duplicateSummary &&
      duplicateReverse == duplicateSummary)
    "duplicate signatures must produce one normalized error"
  let collisionForward := summarizeResult
    (MethodTable.validate [collisionHigh, collisionLow])
  let collisionReverse := summarizeResult
    (MethodTable.validate [collisionLow, collisionHigh])
  assertTrue
    (collisionForward == collisionSummary &&
      collisionReverse == collisionSummary)
    "selector collisions must retain their canonical signatures and selector"
  assertTrue
    (acceptedSignatures [fooMethod, fMethod] ==
      some ["f(uint256)", "foo(uint256)"])
    "distinct methods must produce a nonempty canonical table"

end Tests
end

section
-- leanmerge: from Solcore.Test.AbiStaticWordMethodTableProperties
/-! External compile consumers for Static Word ABI method-table contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Abi.V1

private theorem compileTimeDuplicateScanComplete
    (entries : List IndexedMethod) :
    firstDuplicateSignature? entries = none ↔
      entries.Pairwise fun left right => left.signature ≠ right.signature :=
  firstDuplicateSignature?_eq_none_iff entries

private theorem compileTimeSelectorScanComplete
    (entries : List IndexedMethod) :
    firstSelectorCollision? entries = none ↔
      entries.Pairwise fun left right => left.selector ≠ right.selector :=
  firstSelectorCollision?_eq_none_iff entries

private theorem compileTimeCanonicalProvenance
    {methods : List Method} {entry : IndexedMethod} :
    entry ∈ canonicalMethodEntries methods ↔
      ∃ method, method ∈ methods ∧ Method.index method = entry :=
  mem_canonicalMethodEntries_iff

private theorem compileTimeCanonicalPermutation (methods : List Method) :
    (canonicalMethodEntries methods).Perm (methods.map Method.index) :=
  canonicalMethodEntries_perm methods

private theorem compileTimeCanonicalSorted (methods : List Method) :
    (canonicalMethodEntries methods).Pairwise fun left right =>
      IndexedMethod.signatureLE left right = true :=
  canonicalMethodEntries_sorted methods

private theorem compileTimeAcceptedProvenance
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table)
    {entry : IndexedMethod} (member : entry ∈ table.entries) :
    ∃ method, method ∈ methods ∧ Method.index method = entry :=
  MethodTable.entries_provenance accepted member

private theorem compileTimeAcceptedNonempty (table : MethodTable) :
    table.entries ≠ [] :=
  MethodTable.entries_nonempty table

private theorem compileTimeAcceptedSignatureUnique (table : MethodTable) :
    table.entries.Pairwise fun left right =>
      left.signature ≠ right.signature :=
  MethodTable.signatures_pairwise table

private theorem compileTimeAcceptedSelectorUnique (table : MethodTable) :
    table.entries.Pairwise fun left right => left.selector ≠ right.selector :=
  MethodTable.selectors_pairwise table

private theorem compileTimeAcceptedSorted
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table) :
    table.entries.Pairwise fun left right =>
      IndexedMethod.signatureLE left right = true :=
  MethodTable.entries_sorted accepted

private theorem compileTimePermutationPreservesAcceptedEntries
    {firstMethods secondMethods : List Method}
    {firstTable secondTable : MethodTable}
    (permutation : firstMethods.Perm secondMethods)
    (firstAccepted : MethodTable.validate firstMethods = .ok firstTable)
    (secondAccepted : MethodTable.validate secondMethods = .ok secondTable) :
    firstTable.entries = secondTable.entries :=
  MethodTable.entries_eq_of_input_perm permutation
    firstAccepted secondAccepted

private theorem compileTimePermutationPreservesAcceptance
    {firstMethods secondMethods : List Method}
    (permutation : firstMethods.Perm secondMethods) :
    (∃ table, MethodTable.validate firstMethods = .ok table) ↔
      ∃ table, MethodTable.validate secondMethods = .ok table :=
  MethodTable.validate_accepts_iff_of_input_perm permutation

private theorem compileTimePermutationPreservesErrorKind
    {firstMethods secondMethods : List Method}
    {firstError secondError : MethodTableError}
    (permutation : firstMethods.Perm secondMethods)
    (firstRejected : MethodTable.validate firstMethods = .error firstError)
    (secondRejected : MethodTable.validate secondMethods = .error secondError) :
    MethodTable.ErrorKind.ofError firstError =
      MethodTable.ErrorKind.ofError secondError :=
  MethodTable.errorKind_eq_of_input_perm permutation
    firstRejected secondRejected

/-- All checks in this module are elaboration-time proof consumers. -/
def testAbiStaticWordMethodTableProperties : IO Unit :=
  pure ()

end Tests
end
