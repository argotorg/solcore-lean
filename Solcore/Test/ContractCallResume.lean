import Solcore.ContractRuntime.CallResumeExecution
import Solcore.Test.OneLevelNestedExecutionFixture

/-! Golden laws for the raw-bytes child convention and the call-and-resume
convention. Raw return data are the first bytes of the data Words up to the
length the length Word names, written out as hexadecimal text; a revert carries
one Word and a trap its reason, wrong annotations do not decode, and a raw
contract has no one-Word view, so a word call to it is unavailable.

A small parent runs through the composition: its call phase writes slot 0 and
returns the target, the selector `0x9507d39a`, the input as the argument and as
its one kept Word; a raw child writes slot 0 and returns 40 bytes, or reverts
with its argument when it is odd; the resume phase writes the status Word and
its input size to slots 1 and 2, returns the first data Word, or reverts with
it when the kept input has bit 1 set. A returned child commits, a reverted one
leaves the call phase's world and delivers its revert Word, a parent revert
commits nothing, a target that does not resolve fails with no data, and the
parent's code and every balance stay as they were. -/

set_option autoImplicit false

namespace Tests.ContractCallResume

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.CallResumeExecution

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def firstRamp : Word := w 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
private def secondRamp : Word := w 0x2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40

/-! Kernel-checked recognition facts. -/

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 1) (.sum .word .word)) =
      some (.rawBytesOutcomeV1 1) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 0) (.sum .word .word)) =
      some (.rawBytesOutcomeV1 0) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.product .word (.product .word .word)) (.sum .word .word)) =
      some (.wordTupleOutcomeV1 1) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.product .unit .word) (.sum .word .word)) = none := rfl

example : (CoreContractEntryProfile.rawBytesOutcomeV1 3).returnsOneWord = false := rfl

example (extraWords other : Nat) :
    (CoreContractEntryProfile.rawBytesOutcomeV1 extraWords).resultType ≠
      (CoreContractEntryProfile.wordTupleOutcomeV1 other).resultType := by
  intro equal
  cases CoreContractEntryProfile.resultType_injective equal

example : (CoreContractEntryProfile.rawBytesOutcomeV1 0).resultType ≠
    CoreContractEntryProfile.boundedBytesOutcomeV1.resultType := by
  intro equal
  cases CoreContractEntryProfile.resultType_injective equal

/-- The length Word names its length modulo the capacity plus one. -/
example : CoreContractEntryProfile.rawBytesLength 1 (w 0) = 0 := rfl
example : CoreContractEntryProfile.rawBytesLength 1 (w 64) = 64 := rfl
example : CoreContractEntryProfile.rawBytesLength 1 (w 65) = 0 := rfl
example : CoreContractEntryProfile.rawBytesLength 4 (w 161) = 0 := rfl

private def rawValue (length first second : Word) : Value :=
  .pair .unit (.pair (.word length) (.pair (.word first) (.word second)))

private def returnedRaw (payload : Value) : Option (FrameOutcome Word) :=
  CoreContractEntryProfile.decode? (.rawBytesOutcomeV1 1) (.inLeft (.sum .word .word) payload)

private def text (outcome : Option (FrameOutcome Word)) : Option String :=
  match outcome with
  | some (.returned bytes) => some (encodeBytesText bytes)
  | some (.reverted bytes) => some ("revert:" ++ encodeBytesText bytes)
  | _ => none

/-! The composed parent and child. -/

private def parentAddress : Address := ⟨0x10, by decide⟩
private def childAddress : Address := ⟨0x20, by decide⟩
private def missingAddress : Address := ⟨0x30, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩
private def getSelector : Nat := 0x9507d39a

private def readInput (locals offset : Nat) : Expr :=
  .caseE (.apply (.var (HostFunction.inputDataWordBE?.index + locals)) (.word (w offset)))
    (.word Word.zero) (.var 0)

private def storageWrite (locals slot : Nat) (value : Expr) : Expr :=
  .apply (.var (HostFunction.storageWrite.index + locals)) (.pair (.word (w slot)) value)

private def bitSet (value : Expr) (bit : Nat) : Expr :=
  .binary .wordEq (.binary .wordAnd value (.word (w bit))) (.word (w bit))

/-- The call phase: target and input from the calldata, slot 0 written, then
the request with the input kept. -/
def callProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 2).resultType
  body :=
    .letE (readInput 0 0)
      (.letE (readInput 1 32)
        (.letE (storageWrite 2 0 (.var 0))
          (.inLeft (.sum .word .word)
            (.pair (.var 2) (.pair (.word (w getSelector)) (.pair (.var 1) (.var 1)))))))
}

theorem callProgram_checked : callProgram.checkHost = true := by
  decide

def callContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨callProgram, callProgram_checked⟩ 2 rfl

/-- The raw child: slot 0 written with its argument, an odd argument reverted,
otherwise 40 bytes of the argument and its successor. -/
def childProgram : Program := {
  resultType := (CoreContractEntryProfile.rawBytesOutcomeV1 1).resultType
  body :=
    .letE (readInput 0 4)
      (.letE (storageWrite 1 0 (.var 0))
        (.ifE (bitSet (.var 1) 1)
          (.inRight (CoreContractEntryProfile.rawBytesType 1) (.inLeft .word (.var 1)))
          (.inLeft (.sum .word .word)
            (.pair .unit (.pair (.word (w 40))
              (.pair (.var 1) (.binary .wordAdd (.var 1) (.word (w 1)))))))))
}

theorem childProgram_checked : childProgram.checkHost = true := by
  decide

def childContract : CheckedCoreContract :=
  CheckedCoreContract.rawBytesOutcomeV1 ⟨childProgram, childProgram_checked⟩ 1 rfl

/-- The resume phase: the input size, the kept input, the status Word and the
first data Word, slots 1 and 2 written, then the first data Word returned or,
under the kept input's bit 1, reverted. -/
def resumeProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE (.apply (.var HostFunction.inputDataSize.index) .unit)
      (.letE (readInput 1 0)
        (.letE (readInput 2 32)
          (.letE (readInput 3 64)
            (.letE (storageWrite 4 1 (.var 1))
              (.letE (storageWrite 5 2 (.var 4))
                (.ifE (bitSet (.var 4) 2)
                  (.inRight .word (.inLeft .word (.var 2)))
                  (.inLeft (.sum .word .word) (.var 2))))))))
}

theorem resumeProgram_checked : resumeProgram.checkHost = true := by
  decide

def resumeContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 ⟨resumeProgram, resumeProgram_checked⟩ rfl

def parentContract : CallResumeParent := {
  call := callContract
  resume := resumeContract
  keptWords := 1
  call_entryProfile := rfl
  resume_entryProfile := rfl
}

private def balanceOf (value : Nat) : Account → Account := fun account => account.withBalance (w value)

private def initialWorld : WorldState :=
  WorldState.empty
    |>.putAccount callerAddress (balanceOf 9 Account.empty)
    |>.putAccount parentAddress (balanceOf 5 (Account.empty.withCode callContract.code))
    |>.putAccount childAddress (balanceOf 3 (Account.empty.withCode childContract.code))

private def registry : CheckedContractRegistry := {
  lookup := fun address => if address = childAddress then some childContract else none }

private def input (target : Word) (value : Nat) : HostStorageDriver.InputData := {
  bytes := encodeWordBytesBE target ++ encodeWordBytesBE (w value)
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

private def compose (target : Word) (value : Nat) : Result :=
  CallResumeExecution.run registry parentContract initialWorld parentAddress callerAddress
    (input target value) 4096

private def slot (world : WorldState) (address : Address) (index : Nat) : Word :=
  ((world.account? address).map fun account => account.storageRead (w index)).getD (w 0)

/-- The outcome, the parent's slots 0 to 2, the child's slot 0, the child's
status and delivered bytes. -/
private def summary : Result → Option (Option String × List Word × Word × Option (ChildStatus × String))
  | .completed outcome finalWorld _ child =>
      some (text (some outcome), [0, 1, 2].map (slot finalWorld parentAddress), slot finalWorld childAddress 0,
        child.map fun result => (result.status, encodeBytesText result.data))
  | _ => none

private def balancesAndCode : Result → Bool
  | .completed _ finalWorld _ _ =>
      [callerAddress, parentAddress, childAddress].all (fun address =>
        finalWorld.balance? address == initialWorld.balance? address) &&
      (match finalWorld.code? parentAddress with
        | some code => code.program == callContract.code.program
        | none => false)
  | _ => false

def testContractCallResume : IO Unit := do
  -- Raw return data are exactly the named bytes, with no padding.
  ensure (text (returnedRaw (rawValue (w 0) firstRamp secondRamp)) == some "0x")
    "a zero length did not return empty data"
  ensure (text (returnedRaw (rawValue (w 1) firstRamp secondRamp)) == some "0x01")
    "a one-byte value differs from its byte"
  ensure (text (returnedRaw (rawValue (w 31) firstRamp secondRamp)) ==
      some "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
    "a 31-byte value differs from its bytes"
  ensure (text (returnedRaw (rawValue (w 33) firstRamp secondRamp)) ==
      some "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021")
    "a 33-byte value differs from its bytes"
  ensure (text (returnedRaw (rawValue (w 64) firstRamp secondRamp)) ==
      some ("0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" ++
        "2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40"))
    "a 64-byte value differs from its two Words"
  ensure (text (returnedRaw (rawValue (w (2 ^ 256 - 1)) firstRamp secondRamp)) ==
      text (returnedRaw (rawValue (w ((2 ^ 256 - 1) % 65)) firstRamp secondRamp)))
    "the largest length Word does not name its residue"
  -- Revert and trap carry one Word under the exact raw annotation.
  ensure (text (CoreContractEntryProfile.decode? (.rawBytesOutcomeV1 1)
      (.inRight (CoreContractEntryProfile.rawBytesType 1) (.inLeft .word (.word (w 0x99))))) ==
        some ("revert:0x" ++ hexWord "99"))
    "a raw revert differs from its one Word"
  ensure (CoreContractEntryProfile.decode? (.rawBytesOutcomeV1 1)
      (.inRight (CoreContractEntryProfile.rawBytesType 1) (.inRight .word (.word (w 7)))) ==
        some (.trapped (w 7)))
    "a raw trap differs from its reason"
  -- Wrong annotations and payloads do not decode.
  ensure (CoreContractEntryProfile.decode? (.rawBytesOutcomeV1 1)
      (.inRight (CoreContractEntryProfile.rawBytesType 2) (.inLeft .word (.word (w 1))))).isNone
    "a revert with another capacity's annotation decoded"
  ensure (returnedRaw (.pair (.word (w 1)) (.pair (.word (w 40)) (.pair (.word firstRamp) (.word secondRamp))))).isNone
    "a value without the unit marker decoded"
  ensure (returnedRaw (.pair .unit (.pair (.word (w 40)) (.word firstRamp)))).isNone
    "a value with one data Word decoded under two"
  ensure (CoreContractEntryProfile.decodeWordOutcome? (.rawBytesOutcomeV1 1)
      (.inLeft (.sum .word .word) (rawValue (w 1) firstRamp secondRamp))).isNone
    "a raw value has a one-Word view"
  ensure ((CheckedCoreContract.ofCode? childContract.code).map (·.entryProfile) == some (.rawBytesOutcomeV1 1))
    "admission does not recognize the raw convention"
  -- A word call to a registered raw contract is unavailable: the child never
  -- runs and the root traps with the failure.
  let rawWordChild := CheckedCoreContract.rawBytesOutcomeV1 ⟨childProgram, childProgram_checked⟩ 1 rfl
  ensure ((match (OneLevelNestedExecutionFixture.runScenario
      (OneLevelNestedExecutionFixture.rootContract .commit OneLevelNestedExecutionFixture.childTargetWord)
      rawWordChild 512).view with
    | .completed terminal => some terminal.outcome
    | .outOfFuel _ _ _ => none) == some (.trapped ContractCallFailure.unavailable.code))
    "a word call reached a raw contract"
  -- The child's invocation: the parent as caller, zero value, 36 input bytes.
  let request : Request := ⟨addressToWord childAddress, w getSelector, w 4, [w 4]⟩
  ensure (encodeBytesText (childInvocation parentAddress childAddress request).inputData.bytes ==
      "0x9507d39a" ++ hexWord "4")
    "the child's input differs from the selector and argument"
  ensure ((childInvocation parentAddress childAddress request).caller == parentAddress &&
      (childInvocation parentAddress childAddress request).callValue == Word.zero)
    "the child's caller or value changed"
  -- A returned child commits; the resume phase reads 32 + 32 + 40 bytes.
  let child := addressToWord childAddress
  let delivered := "0x" ++ hexWord "4" ++ "0000000000000000"
  ensure (summary (compose child 4) ==
      some (some ("0x" ++ hexWord "4"), [w 4, w 1, w 104], w 4, some (.returned, delivered)))
    "a returned child's transaction differs"
  -- A reverted child leaves the call phase's world and delivers its revert Word.
  ensure (summary (compose child 5) ==
      some (some ("0x" ++ hexWord "5"), [w 5, w 0, w 96], w 0, some (.reverted, "0x" ++ hexWord "5")))
    "a reverted child's transaction differs"
  -- A parent revert after a returned child commits nothing.
  ensure (summary (compose child 6) ==
      some (some ("revert:0x" ++ hexWord "6"), [w 0, w 0, w 0], w 0, some (.returned, "0x" ++ hexWord "6" ++
        "0000000000000000")))
    "a parent revert committed a phase"
  -- Targets that do not resolve fail with no data, before any child runs.
  ensure (summary (compose (addressToWord missingAddress) 8) ==
      some (some ("0x" ++ hexWord "0"), [w 8, w 3, w 64], w 0, some (.failed, "0x")))
    "an unregistered target did not fail"
  ensure (summary (compose (w (2 ^ 160)) 8) ==
      some (some ("0x" ++ hexWord "0"), [w 8, w 3, w 64], w 0, some (.failed, "0x")))
    "a target beyond 160 bits did not fail"
  -- Every balance and the parent's code stay as they were.
  for value in [4, 5, 6, 8] do
    ensure (balancesAndCode (compose child value)) s!"input {value} changed a balance or the parent's code"
  -- A parent whose call phase is not installed does not run.
  ensure ((match CallResumeExecution.run registry parentContract initialWorld childAddress callerAddress
      (input child 4) 4096 with
    | .unresolved .call => true
    | _ => false))
    "a parent without its call phase ran"
  -- Fuel runs out in the call phase first.
  ensure ((match CallResumeExecution.run registry parentContract initialWorld parentAddress callerAddress
      (input child 4) 0 with
    | .outOfFuel .call => true
    | _ => false))
    "an exhausted call phase did not report its step"

end Tests.ContractCallResume
