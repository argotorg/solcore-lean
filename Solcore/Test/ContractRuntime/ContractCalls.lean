import Solcore.ContractRuntime.Internal.EntryOutcomeLaws
import Solcore.Test.ContractRuntime.NestedExecution
import Solcore.ContractRuntime.Internal.CallPhaseLaws
import Solcore.Core.Internal.HostPreservation
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.ContractRuntime.Internal.TopLevelLaws

/-!
# Contract call convention tests

Golden laws of the entry conventions for tuples, enums and bounded bytes, and of the call chain, choice
and resume conventions.
-/

section
-- leanmerge: from Solcore.Test.ContractBoundedBytesEntryProfile
/-! Golden laws for the bounded `bytes` entry convention. The expected return
data is written out as hexadecimal text: a returned value of length `L` is the
offset Word 32, the length Word and the first `L` data bytes, zero-padded to a
whole number of Words, even when the data Words carry nonzero bytes after the
length. A revert carries one Word and a trap its reason. Wrong annotations and
payloads do not decode, a bytes value has no one-Word view, and the nested
executor treats a registered bytes contract as unavailable to a word call and a
template with a bytes initializer as unavailable to creation, while a bytes
root returns its whole encoding. -/

set_option autoImplicit false

namespace Tests.ContractBoundedBytesEntryProfile

open Solcore.Core
open Solcore.ContractRuntime
open Tests.OneLevelNestedExecutionFixture

/-! Kernel-checked recognition and typing facts. -/

example : CoreContractEntryProfile.boundedBytesOutcomeV1.resultType =
    .sum (.sum .unit (.product .word (.product .word .word))) (.sum .word .word) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.sum .unit (.product .word (.product .word .word))) (.sum .word .word)) =
      some .boundedBytesOutcomeV1 := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.sum .unit (.product .word .word)) (.sum .word .word)) = none := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.sum .unit (.product .word (.product .word (.product .word .word)))) (.sum .word .word)) =
      none := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.sum .word (.product .word (.product .word .word))) (.sum .word .word)) = none := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.product .word (.product .word .word)) (.sum .word .word)) =
      some (.wordTupleOutcomeV1 1) := rfl

example : CoreContractEntryProfile.ofResultType? (.sum .word (.sum .word .word)) =
    some .wordOutcomeV1 := rfl

example : CoreContractEntryProfile.boundedBytesOutcomeV1.returnsOneWord = false := rfl

example (extraWords : Nat) :
    CoreContractEntryProfile.boundedBytesOutcomeV1.resultType ≠
      (CoreContractEntryProfile.wordTupleOutcomeV1 extraWords).resultType := by
  intro equal
  cases CoreContractEntryProfile.resultType_injective equal

/-- The tag names `tag mod 64 + 1`: the first and last lengths, and a wrap. -/
example : CoreContractEntryProfile.boundedBytesLength (Word.ofNatModulo 0) = 1 := rfl
example : CoreContractEntryProfile.boundedBytesLength (Word.ofNatModulo 63) = 64 := rfl
example : CoreContractEntryProfile.boundedBytesLength (Word.ofNatModulo 64) = 1 := rfl

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- One Word's 64 hexadecimal digits, written as the digits after a run of zeros. -/
private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

/-- Two data Words whose bytes are 1 to 32 and 33 to 64, so every byte after a
length is nonzero before encoding. -/
private def firstRamp : Word := w 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
private def secondRamp : Word := w 0x2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40

private def emptyValue : Value := .inLeft (.product .word (.product .word .word)) .unit

private def nonEmptyValue (tag first second : Word) : Value :=
  .inRight .unit (.pair (.word tag) (.pair (.word first) (.word second)))

private def returned (payload : Value) : Option (FrameOutcome Word) :=
  CoreContractEntryProfile.decode? .boundedBytesOutcomeV1 (.inLeft (.sum .word .word) payload)

/-- The returned value of `length` bytes from 1 to 64, tagged `length - 1`. -/
private def returnedLength (length : Nat) (first second : Word) : Option (FrameOutcome Word) :=
  returned (nonEmptyValue (w (length - 1)) first second)

private def returnedText (outcome : Option (FrameOutcome Word)) : Option String :=
  match outcome with
  | some (.returned bytes) => some (encodeBytesText bytes)
  | _ => none

/-- A registered child whose convention returns `bytes`, after writing the child
slot: 33 bytes of its payload and new value. -/
def bytesChildProgram : Program := {
  resultType := CoreContractEntryProfile.boundedBytesOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word childSlot) (.word childNewValue)))
      (.inLeft (.sum .word .word) (.inRight .unit
        (.pair (.word (w 32)) (.pair (.word childPayload) (.word childNewValue)))))
}

theorem bytesChildProgram_checked : bytesChildProgram.checkHost = true := by
  decide

def bytesChildContract : CheckedCoreContract :=
  CheckedCoreContract.boundedBytesOutcomeV1 ⟨bytesChildProgram, bytesChildProgram_checked⟩ rfl

/-- A creation template whose initializer returns an empty `bytes` value. -/
def bytesInitializerProgram : Program := {
  resultType := CoreContractEntryProfile.boundedBytesOutcomeV1.resultType
  body := .inLeft (.sum .word .word) (.inLeft (.product .word (.product .word .word)) .unit)
}

theorem bytesInitializerProgram_checked : bytesInitializerProgram.checkHost = true := by
  decide

def bytesInitializer : CheckedCoreContract :=
  CheckedCoreContract.boundedBytesOutcomeV1
    ⟨bytesInitializerProgram, bytesInitializerProgram_checked⟩ rfl

/-- The preflight fixture's environment with the bytes initializer in its template. -/
def bytesTemplateEnvironment : ExecutionEnvironment := {
  callRegistry := Adr0148CheckedCreationPreflightFixture.validCallRegistry
  creationTemplates := {
    lookup := fun identifier =>
      if identifier = Adr0148CheckedCreationPreflightFixture.templateId then
        some { initializer := bytesInitializer, runtime := Adr0148CheckedCreationPreflightFixture.runtime }
      else none }
  creationAddressPolicy := Adr0148CheckedCreationPreflightFixture.addressPolicy
}

private def completionFuel : Nat := 512

/-- The creating root's outcome, and the working creator nonce and created
account when it halts. -/
private def creationAt (environment : ExecutionEnvironment) :
    Option (FrameHaltKind × FrameOutcome Word × Option Word × Bool) :=
  match (OneLevelNestedExecution.runWithEnvironment Adr0148NestedCreationLifecycleFixture.rootContract
      Adr0148NestedCreationLifecycleFixture.rootInvocation Adr0148NestedCreationLifecycleFixture.rootInstalled
      environment completionFuel).view with
  | .completed terminal =>
      let working := terminal.terminalContext.context.values.working.1
      some (terminal.outcome.kind, terminal.outcome,
        working.nonce? Adr0148CheckedCreationPreflightFixture.creator,
        (working.account? Adr0148CheckedCreationPreflightFixture.created).isSome)
  | .outOfFuel _ _ _ => none

private def childAt {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : OneLevelNestedExecution.Result initialWorld root invocation) :
    Option (FrameOutcome Word × Option Word × Option Word) :=
  match result.view with
  | .completed terminal =>
      some (terminal.outcome, childStorageValue? terminal.terminalContext.context.values.working.1,
        childStorageValue? terminal.finalWorld)
  | .outOfFuel _ _ _ => none

def testContractBoundedBytesEntryProfile : IO Unit := do
  -- The empty value and lengths 1, 31, 32, 33 and 64 over the two ramps: only
  -- the first `L` bytes survive, and the rest of the last Word is zero.
  ensure (returnedText (returned emptyValue) == some ("0x" ++ hexWord "20" ++ hexWord ""))
    "an empty value differs from its offset and zero length"
  ensure (returnedText (returnedLength 1 firstRamp secondRamp) ==
      some ("0x" ++ hexWord "20" ++ hexWord "1" ++
        "0100000000000000000000000000000000000000000000000000000000000000"))
    "a one-byte value differs from its zero-padded byte"
  ensure (returnedText (returnedLength 31 firstRamp secondRamp) ==
      some ("0x" ++ hexWord "20" ++ hexWord "1f" ++
        "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f00"))
    "a 31-byte value differs from its zero-padded bytes"
  ensure (returnedText (returnedLength 32 firstRamp secondRamp) ==
      some ("0x" ++ hexWord "20" ++ hexWord "20" ++
        "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"))
    "a 32-byte value differs from its one Word"
  ensure (returnedText (returnedLength 33 firstRamp secondRamp) ==
      some ("0x" ++ hexWord "20" ++ hexWord "21" ++
        "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" ++
        "2100000000000000000000000000000000000000000000000000000000000000"))
    "a 33-byte value differs from its Word and zero-padded byte"
  ensure (returnedText (returnedLength 64 firstRamp secondRamp) ==
      some ("0x" ++ hexWord "20" ++ hexWord "40" ++
        "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" ++
        "2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40"))
    "a 64-byte value differs from its two Words"
  -- All-ones data Words lose every byte after the length.
  ensure (returnedText (returnedLength 33 (w (2 ^ 256 - 1)) (w (2 ^ 256 - 1))) ==
      some ("0x" ++ hexWord "20" ++ hexWord "21" ++ String.ofList (List.replicate 66 'f') ++
        String.ofList (List.replicate 62 '0')))
    "the bytes after a 33-byte value's length are not zero"
  -- A tag names its length modulo 64: `2^256 - 1` is 64 bytes and 64 is one byte.
  ensure (returnedText (returned (nonEmptyValue (w (2 ^ 256 - 1)) firstRamp secondRamp)) ==
      returnedText (returnedLength 64 firstRamp secondRamp))
    "the largest tag does not name 64 bytes"
  ensure (returnedText (returned (nonEmptyValue (w 64) firstRamp secondRamp)) ==
      returnedText (returnedLength 1 firstRamp secondRamp))
    "the tag 64 does not name one byte"
  -- The decoded size is the two head Words and the data rounded up to Words.
  for (length, size) in [(1, 96), (31, 96), (32, 96), (33, 128), (63, 128), (64, 128)] do
    match returnedLength length firstRamp secondRamp with
    | some (.returned bytes) => ensure (bytes.size == size) s!"a {length}-byte value has the wrong size"
    | _ => throw (IO.userError "a well-typed bytes value did not decode")
  match returned emptyValue with
  | some (.returned bytes) => ensure (bytes.size == 64) "an empty value has the wrong size"
  | _ => throw (IO.userError "the empty value did not decode")
  -- Revert and trap carry one Word, under the exact bytes annotation.
  ensure ((match CoreContractEntryProfile.decode? .boundedBytesOutcomeV1
      (.inRight CoreContractEntryProfile.boundedBytesType (.inLeft .word (.word (w 0x99)))) with
    | some (.reverted bytes) => some (encodeBytesText bytes)
    | _ => none) == some ("0x" ++ hexWord "99"))
    "a bytes revert differs from its one Word"
  ensure (CoreContractEntryProfile.decode? .boundedBytesOutcomeV1
      (.inRight (.sum .unit (.product .word (.product .word .word))) (.inRight .word (.word (w 7)))) ==
        some (.trapped (w 7)))
    "a bytes trap differs from its reason"
  -- A wrong annotation or payload does not decode.
  ensure (CoreContractEntryProfile.decode? .boundedBytesOutcomeV1
      (.inRight .word (.inLeft .word (.word (w 1))))).isNone
    "a revert with the one-Word annotation decoded"
  ensure (CoreContractEntryProfile.decode? .boundedBytesOutcomeV1
      (.inRight (.product .word (.product .word .word)) (.inLeft .word (.word (w 1))))).isNone
    "a revert with a tuple annotation decoded"
  ensure (returned (.inLeft (.product .word .word) .unit)).isNone
    "an empty value with another annotation decoded"
  ensure (returned (.inRight .word (.pair (.word (w 0)) (.pair (.word firstRamp) (.word secondRamp))))).isNone
    "a non-empty value with another annotation decoded"
  ensure (returned (.inRight .unit (.pair (.word (w 0)) (.word firstRamp)))).isNone
    "a non-empty value with one data Word decoded"
  ensure (returned (.inRight .unit (.pair (.bool true) (.pair (.word firstRamp) (.word secondRamp))))).isNone
    "a non-empty value with a Boolean tag decoded"
  ensure (returned (.pair (.word firstRamp) (.pair (.word secondRamp) (.word (w 1))))).isNone
    "a Word tuple decoded as bytes"
  ensure (CoreContractEntryProfile.decode? .boundedBytesOutcomeV1
      (.inLeft (.sum .word .bool) emptyValue)).isNone
    "a return with another annotation decoded"
  -- The other conventions are unchanged, and a bytes value has no one-Word view.
  ensure (CoreContractEntryProfile.decode? .wordOutcomeV1
      (.inLeft (.sum .word .word) (.word (w 3))) == some (.returned (encodeWordBytesBE (w 3))))
    "the one-Word outcome convention changed"
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 0)
      (.inLeft (.sum .word .word) (.pair (.word (w 1)) (.word (w 2)))) ==
        some (.returned (encodeWordBytesBE (w 1) ++ encodeWordBytesBE (w 2))))
    "the tuple convention changed"
  ensure (CoreContractEntryProfile.decodeWordOutcome? .boundedBytesOutcomeV1
      (.inLeft (.sum .word .word) emptyValue)).isNone
    "a bytes value has a one-Word view"
  ensure (CoreContractEntryProfile.wordOutcomeV1.returnsOneWord &&
      CoreContractEntryProfile.returnWord.returnsOneWord &&
      !CoreContractEntryProfile.boundedBytesOutcomeV1.returnsOneWord)
    "the one-Word predicate changed"
  -- Admission recognizes the bytes contract's exact convention.
  ensure ((CheckedCoreContract.ofCode? bytesChildContract.code).map (·.entryProfile) ==
      some .boundedBytesOutcomeV1)
    "admission does not recognize the bytes convention"
  -- A word call to a registered bytes contract is unavailable: the child never
  -- runs, its slot keeps the old value, and the root traps with the failure.
  ensure (childAt (runScenario (rootContract .commit childTargetWord) bytesChildContract completionFuel) ==
      some (.trapped ContractCallFailure.unavailable.code, some childOldValue, some childOldValue))
    "a word call reached a bytes contract"
  -- Creation from a template with a bytes initializer is unavailable before the
  -- creator's nonce advances; the one-Word initializer still deploys.
  ensure (creationAt bytesTemplateEnvironment ==
      some (.trapped, .trapped ContractCallFailure.unavailable.code,
        some Adr0148CheckedCreationPreflightFixture.oldNonce, false))
    "creation started a bytes initializer"
  ensure ((creationAt Adr0148CheckedCreationPreflightFixture.validEnvironment).map
      (fun (kind, _, nonce, present) => (kind, nonce, present)) ==
      some (.returned, some Adr0148CheckedCreationPreflightFixture.nextNonce, true))
    "the one-Word initializer no longer deploys"
  -- A bytes root returns its whole encoding through the nested executor: 33
  -- bytes of the payload Word and the new value's first byte, which is zero.
  ensure ((match childAt (runScenario bytesChildContract childReturnContract completionFuel) with
    | some (.returned bytes, working, final) => some (encodeBytesText bytes, working, final)
    | _ => none) ==
      some ("0x" ++ hexWord "20" ++ hexWord "21" ++ hexWord "71" ++ String.ofList (List.replicate 64 '0'),
        some childOldValue, some childOldValue))
    "a bytes root did not return its whole encoding"

end Tests.ContractBoundedBytesEntryProfile
end

section
-- leanmerge: from Solcore.Test.ContractCallChain
/-! Golden laws for the raw-outcome child convention and the call chain. Raw
return and revert data are the first bytes of the data Words up to the length
the length Word names, written out as hexadecimal text; a trap carries its
reason, wrong annotations do not decode, and a raw-outcome contract has no
one-Word view, so a word call to it is unavailable.

A small parent makes two calls through the chain: its call phase writes the
input to slot 0 and requests a call with the input as argument, keeping the
target and the input; a raw-outcome child writes its argument `x` to slot 0 and
counts its calls in slot 1, then returns `(x >> 1) & 63` bytes of
`x xor R1 ‖ x xor R2`, or reverts with them when `x` is odd; the middle phase
writes the status Word plus twice the data's size to slot 1 and requests a
call with `input + 3`, or reverts under the input's bit 8; the last phase
writes the same for the second call to slot 2 and returns the data's first
Word, or reverts with it under the input's bit 9. Each phase sees the latest
call's data only, a child revert leaves the world of the phase that requested
it, a phase revert commits nothing, and the parent's code and every balance
stay as they were. Without its middle phase the chain is the one-call
convention. -/

set_option autoImplicit false

namespace Tests.ContractCallChain

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.CallChainExecution

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def firstRamp : Word := w 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
private def secondRamp : Word := w 0x2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40

/-! Kernel-checked recognition facts. -/

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 1) (.sum (CoreContractEntryProfile.rawBytesType 1) .word)) =
      some (.rawOutcomeV1 1) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 2) (.sum (CoreContractEntryProfile.rawBytesType 2) .word)) =
      some (.rawOutcomeV1 2) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 1) (.sum (CoreContractEntryProfile.rawBytesType 2) .word)) =
      none := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 1) (.sum .word .word)) =
      some (.rawBytesOutcomeV1 1) := rfl

example : (CoreContractEntryProfile.rawOutcomeV1 2).returnsOneWord = false := rfl

example (extraWords other : Nat) :
    (CoreContractEntryProfile.rawOutcomeV1 extraWords).resultType ≠
      (CoreContractEntryProfile.rawBytesOutcomeV1 other).resultType := by
  intro equal
  cases CoreContractEntryProfile.resultType_injective equal

private def rawValue (length first second : Word) : Value :=
  .pair .unit (.pair (.word length) (.pair (.word first) (.word second)))

private def rawErrors : Ty := .sum (CoreContractEntryProfile.rawBytesType 1) .word

private def returnedRaw (payload : Value) : Option (FrameOutcome Word) :=
  CoreContractEntryProfile.decode? (.rawOutcomeV1 1) (.inLeft rawErrors payload)

private def revertedRaw (payload : Value) : Option (FrameOutcome Word) :=
  CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
    (.inRight (CoreContractEntryProfile.rawBytesType 1) (.inLeft .word payload))

private def text (outcome : Option (FrameOutcome Word)) : Option String :=
  match outcome with
  | some (.returned bytes) => some (encodeBytesText bytes)
  | some (.reverted bytes) => some ("revert:" ++ encodeBytesText bytes)
  | _ => none

/-! The chained parent and the raw-outcome child. -/

private def parentAddress : Address := ⟨0x10, by decide⟩
private def childAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩
private def getSelector : Nat := 0x9507d39a

private def readInput (locals offset : Nat) : Expr :=
  .caseE (.apply (.var (HostFunction.inputDataWordBE?.index + locals)) (.word (w offset)))
    (.word Word.zero) (.var 0)

private def inputSize (locals : Nat) : Expr :=
  .apply (.var (HostFunction.inputDataSize.index + locals)) .unit

private def storageRead (locals slot : Nat) : Expr :=
  .apply (.var (HostFunction.storageRead.index + locals)) (.word (w slot))

private def storageWrite (locals slot : Nat) (value : Expr) : Expr :=
  .apply (.var (HostFunction.storageWrite.index + locals)) (.pair (.word (w slot)) value)

private def bitSet (value : Expr) (bit : Nat) : Expr :=
  .binary .wordEq (.binary .wordAnd value (.word (w bit))) (.word (w bit))

/-- The status Word plus twice the data's size after the two kept Words and the
status Word. -/
private def statusAndSize (status size : Expr) : Expr :=
  .binary .wordAdd status (.binary .wordMul (.word (w 2)) (.binary .wordSub size (.word (w 96))))

/-- The call phase: target and input from the calldata, the input written to
slot 0, then the request keeping the target and the input. -/
def callProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 3).resultType
  body :=
    .letE (readInput 0 0)
      (.letE (readInput 1 32)
        (.letE (storageWrite 2 0 (.var 0))
          (.inLeft (.sum .word .word)
            (.pair (.var 2) (.pair (.word (w getSelector)) (.pair (.var 1) (.pair (.var 2) (.var 1))))))))
}

theorem callProgram_checked : callProgram.checkHost = true := by
  decide

def callContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨callProgram, callProgram_checked⟩ 3 rfl

/-- The raw-outcome child: its argument to slot 0, its call count to slot 1,
then `(x >> 1) & 63` bytes of `x xor R1 ‖ x xor R2`, reverted for an odd `x`. -/
def childProgram : Program := {
  resultType := (CoreContractEntryProfile.rawOutcomeV1 1).resultType
  body :=
    .letE (readInput 0 4)
      (.letE (storageWrite 1 0 (.var 0))
        (.letE (storageWrite 2 1 (.binary .wordAdd (storageRead 2 1) (.word (w 1))))
          (.letE (.binary .wordAnd (.binary .wordShr (.var 2) (.word (w 1))) (.word (w 63)))
            (.ifE (bitSet (.var 3) 1)
              (.inRight (CoreContractEntryProfile.rawBytesType 1) (.inLeft .word
                (.pair .unit (.pair (.var 0) (.pair (.binary .wordXor (.var 3) (.word firstRamp))
                  (.binary .wordXor (.var 3) (.word secondRamp)))))))
              (.inLeft rawErrors
                (.pair .unit (.pair (.var 0) (.pair (.binary .wordXor (.var 3) (.word firstRamp))
                  (.binary .wordXor (.var 3) (.word secondRamp))))))))))
}

theorem childProgram_checked : childProgram.checkHost = true := by
  decide

def childContract : CheckedCoreContract :=
  CheckedCoreContract.rawOutcomeV1 ⟨childProgram, childProgram_checked⟩ 1 rfl

/-- The middle phase: the status and size of the first call to slot 1, then the
request for `input + 3`, or a revert with the status Word under bit 8. -/
def middleProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 3).resultType
  body :=
    .letE (inputSize 0)
      (.letE (readInput 1 0)
        (.letE (readInput 2 32)
          (.letE (readInput 3 64)
            (.letE (storageWrite 4 1 (statusAndSize (.var 0) (.var 3)))
              (.ifE (bitSet (.var 2) 256)
                (.inRight (CoreContractEntryProfile.wordTupleType 4) (.inLeft .word (.var 1)))
                (.inLeft (.sum .word .word)
                  (.pair (.var 3) (.pair (.word (w getSelector))
                    (.pair (.binary .wordAdd (.var 2) (.word (w 3))) (.pair (.var 3) (.var 2)))))))))))
}

theorem middleProgram_checked : middleProgram.checkHost = true := by
  decide

def middleContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨middleProgram, middleProgram_checked⟩ 3 rfl

/-- The last phase: the status and size of the second call to slot 2, then its
data's first Word, reverted under bit 9. -/
def lastProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE (inputSize 0)
      (.letE (readInput 1 32)
        (.letE (readInput 2 64)
          (.letE (readInput 3 96)
            (.letE (storageWrite 4 2 (statusAndSize (.var 1) (.var 3)))
              (.ifE (bitSet (.var 3) 512)
                (.inRight .word (.inLeft .word (.var 1)))
                (.inLeft (.sum .word .word) (.var 1)))))))
}

theorem lastProgram_checked : lastProgram.checkHost = true := by
  decide

def lastContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 ⟨lastProgram, lastProgram_checked⟩ rfl

def parentContract : CallChainParent := {
  call := callContract
  middles := [middleContract]
  last := lastContract
  keptWords := 2
  call_entryProfile := rfl
  middles_entryProfile := by simp [middleContract, CheckedCoreContract.wordTupleOutcomeV1]
  last_entryProfile := rfl
}

/-- The same call and last phases as a one-call parent. -/
def oneCallParent : CallResumeParent := {
  call := callContract
  resume := lastContract
  keptWords := 2
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

private def input (value : Nat) : HostStorageDriver.InputData := {
  bytes := encodeWordBytesBE (addressToWord childAddress) ++ encodeWordBytesBE (w value)
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

private def chain (value : Nat) : Result :=
  CallChainExecution.run registry parentContract initialWorld parentAddress callerAddress (input value) 4096

private def slot (world : WorldState) (address : Address) (index : Nat) : Word :=
  ((world.account? address).map fun account => account.storageRead (w index)).getD (w 0)

/-- The outcome, the parent's slots 0 to 2, the child's slots 0 and 1, and each
call's argument, status and delivered bytes. -/
private def summary : Result → Option (Option String × List Word × List Word ×
    List (Word × CallResumeExecution.ChildStatus × String))
  | .completed outcome finalWorld calls =>
      some (text (some outcome), [0, 1, 2].map (slot finalWorld parentAddress),
        [0, 1].map (slot finalWorld childAddress),
        calls.map fun call => (call.request.argument, call.child.status, encodeBytesText call.child.data))
  | _ => none

private def balancesAndCode : Result → Bool
  | .completed _ finalWorld _ =>
      [callerAddress, parentAddress, childAddress].all (fun address =>
        finalWorld.balance? address == initialWorld.balance? address) &&
      (match finalWorld.code? parentAddress with
        | some code => code.program == callContract.code.program
        | none => false)
  | _ => false

private def xorWord (left right : Word) : Word := w (left.val ^^^ right.val)

/-- The first `count` bytes of `x xor R1 ‖ x xor R2` as hexadecimal text. -/
private def childData (x count : Nat) : String :=
  encodeBytesText ((encodeWordBytesBE (xorWord (w x) firstRamp) ++
    encodeWordBytesBE (xorWord (w x) secondRamp)).extract 0 count)

def testContractCallChain : IO Unit := do
  -- Raw return and revert data are exactly the named bytes, with no padding.
  ensure (text (returnedRaw (rawValue (w 0) firstRamp secondRamp)) == some "0x")
    "a zero length did not return empty data"
  ensure (text (revertedRaw (rawValue (w 0) firstRamp secondRamp)) == some "revert:0x")
    "a zero length did not revert with empty data"
  ensure (text (revertedRaw (rawValue (w 1) firstRamp secondRamp)) == some "revert:0x01")
    "a one-byte revert differs from its byte"
  ensure (text (revertedRaw (rawValue (w 33) firstRamp secondRamp)) ==
      some "revert:0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021")
    "a 33-byte revert differs from its bytes"
  ensure (text (returnedRaw (rawValue (w 64) firstRamp secondRamp)) ==
      some ("0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" ++
        "2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40"))
    "a 64-byte return differs from its two Words"
  ensure (text (revertedRaw (rawValue (w (2 ^ 256 - 1)) firstRamp secondRamp)) ==
      text (revertedRaw (rawValue (w ((2 ^ 256 - 1) % 65)) firstRamp secondRamp)))
    "the largest length Word does not name its residue in a revert"
  ensure (CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
      (.inRight (CoreContractEntryProfile.rawBytesType 1)
        (.inRight (CoreContractEntryProfile.rawBytesType 1) (.word (w 7)))) == some (.trapped (w 7)))
    "a raw-outcome trap differs from its reason"
  -- Wrong annotations and payloads do not decode.
  ensure (CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
      (.inLeft (.sum .word .word) (rawValue (w 1) firstRamp secondRamp))).isNone
    "a return with the one-Word revert annotation decoded"
  ensure (CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
      (.inRight (CoreContractEntryProfile.rawBytesType 2) (.inLeft .word (rawValue (w 1) firstRamp secondRamp)))).isNone
    "a revert with another capacity's annotation decoded"
  ensure (CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
      (.inRight (CoreContractEntryProfile.rawBytesType 1)
        (.inRight .word (.word (w 7))))).isNone
    "a trap with the one-Word revert annotation decoded"
  ensure (revertedRaw (.word (w 1))).isNone
    "a one-Word revert decoded as raw bytes"
  ensure (CoreContractEntryProfile.decodeWordOutcome? (.rawOutcomeV1 1)
      (.inLeft rawErrors (rawValue (w 1) firstRamp secondRamp))).isNone
    "a raw-outcome value has a one-Word view"
  ensure ((CheckedCoreContract.ofCode? childContract.code).map (·.entryProfile) == some (.rawOutcomeV1 1))
    "admission does not recognize the raw-outcome convention"
  -- A word call to a registered raw-outcome contract is unavailable.
  ensure ((match (OneLevelNestedExecutionFixture.runScenario
      (OneLevelNestedExecutionFixture.rootContract .commit OneLevelNestedExecutionFixture.childTargetWord)
      childContract 512).view with
    | .completed terminal => some terminal.outcome
    | .outOfFuel _ _ _ => none) == some (.trapped ContractCallFailure.unavailable.code))
    "a word call reached a raw-outcome contract"
  -- A returned call commits and a reverted one leaves the world its
  -- requesting phase left; each phase reads only the latest call's data.
  ensure (summary (chain 4) == some (some ("0x" ++ hexWord "0"), [w 4, w 5, w 6], [w 4, w 1],
      [(w 4, .returned, childData 4 2), (w 7, .reverted, childData 7 3)]))
    "a return then a revert differs"
  ensure (summary (chain 5) == some (some ("0x" ++ hexWord "0"), [w 5, w 4, w 9], [w 8, w 1],
      [(w 5, .reverted, childData 5 2), (w 8, .returned, childData 8 4)]))
    "a revert then a return differs"
  -- A long first call: the last phase reads the second call's first Word, not the first's.
  ensure (summary (chain 66) == some (some (encodeBytesText (encodeWordBytesBE (xorWord (w 69) firstRamp))),
      [w 66, w 67, w 68], [w 66, w 1], [(w 66, .returned, childData 66 33), (w 69, .reverted, childData 69 34)]))
    "a long return then a long revert differs"
  ensure (summary (chain 63) == some (some (encodeBytesText (encodeWordBytesBE (xorWord (w 66) firstRamp))),
      [w 63, w 62, w 67], [w 66, w 1], [(w 63, .reverted, childData 63 31), (w 66, .returned, childData 66 33)]))
    "a short revert then a long return differs"
  -- A middle or last phase revert commits nothing.
  ensure (summary (chain (4 + 256)) == some (some ("revert:0x" ++ hexWord "1"), [w 0, w 0, w 0], [w 0, w 0],
      [(w 260, .returned, childData 260 2)]))
    "a middle phase revert committed a phase or made a second call"
  ensure (summary (chain (4 + 512)) == some (some ("revert:0x" ++ hexWord "0"), [w 0, w 0, w 0], [w 0, w 0],
      [(w 516, .returned, childData 516 2), (w 519, .reverted, childData 519 3)]))
    "a last phase revert committed a phase"
  -- Every balance and the parent's code stay as they were.
  for value in [4, 5, 66, 63, 260, 516] do
    ensure (balancesAndCode (chain value)) s!"input {value} changed a balance or the parent's code"
  -- Without the middle phase the chain is the one-call convention.
  for value in [4, 5, 66, 516] do
    let chained := CallChainExecution.run registry (ofCallResume oneCallParent) initialWorld parentAddress
      callerAddress (input value) 4096
    let single := CallResumeExecution.run registry oneCallParent initialWorld parentAddress callerAddress
      (input value) 4096
    ensure ((match chained.toCallResume, single with
      | .completed outcome finalWorld request child, .completed outcome' finalWorld' request' child' =>
          outcome == outcome' && [0, 1, 2].all (fun index => slot finalWorld parentAddress index ==
            slot finalWorld' parentAddress index) && request.map (·.argument) == request'.map (·.argument) &&
            child.map (fun child => (child.status, encodeBytesText child.data)) ==
              child'.map (fun child => (child.status, encodeBytesText child.data))
      | _, _ => false))
      s!"input {value}: the chain without middle phases differs from the one-call convention"
  -- A parent whose call phase is not installed does not run, and fuel runs out
  -- in the call phase first.
  ensure ((match CallChainExecution.run registry parentContract initialWorld childAddress callerAddress
      (input 4) 4096 with
    | .unresolved .call => true
    | _ => false))
    "a parent without its call phase ran"
  ensure ((match CallChainExecution.run registry parentContract initialWorld parentAddress callerAddress
      (input 4) 0 with
    | .outOfFuel .call => true
    | _ => false))
    "an exhausted call phase did not report its step"

end Tests.ContractCallChain
end

section
-- leanmerge: from Solcore.Test.ContractCallChoice
/-! Golden laws for the choice chain. A small parent chooses its own number of
calls: its call phase writes the input to slot 0 and, for the requested count
`r = (input >> 8) & 3`, finishes with the input when `r` is zero, and otherwise
requests a call with the input as argument, keeping the target, the input and
the calls made. One resume program follows every call: it writes the status
Word plus twice the data's size to slot `calls + 1`, then requests the next
call with `input + calls` while fewer than `r` calls are made, and otherwise
finishes with the data's first Word plus the calls made, or reverts with the
status Word under the input's bit 10. The child is the call chain test's
raw-outcome child: it writes its argument `x` to slot 0, counts its calls in
slot 1, and returns `(x >> 1) & 63` bytes of `x xor R1 ‖ x xor R2`, or reverts
with them when `x` is odd.

Zero to three calls follow from the input. Each phase reads only the latest
call's data, a child revert leaves the world of the phase that requested it, a
phase revert commits nothing, a request with no phase left stops the
transaction, and the parent's code and every balance stay as they were. The
call chain's parent runs alike through `ofChain`. -/

set_option autoImplicit false

namespace Tests.ContractCallChoice

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.CallChoiceExecution

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def firstRamp : Word := w 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
private def secondRamp : Word := w 0x2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40

private def parentAddress : Address := ⟨0x10, by decide⟩
private def childAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩
private def getSelector : Nat := 0x9507d39a

private def readInput (locals offset : Nat) : Expr :=
  .caseE (.apply (.var (HostFunction.inputDataWordBE?.index + locals)) (.word (w offset)))
    (.word Word.zero) (.var 0)

private def inputSize (locals : Nat) : Expr :=
  .apply (.var (HostFunction.inputDataSize.index + locals)) .unit

private def storageWrite (locals : Nat) (slot value : Expr) : Expr :=
  .apply (.var (HostFunction.storageWrite.index + locals)) (.pair slot value)

private def bitSet (value : Expr) (bit : Nat) : Expr :=
  .binary .wordEq (.binary .wordAnd value (.word (w bit))) (.word (w bit))

/-- The requested count, the input's bits 8 and 9. -/
private def requestedOf (input : Expr) : Expr :=
  .binary .wordAnd (.binary .wordShr input (.word (w 8))) (.word (w 3))

/-- A returned tuple of seven Words. -/
private def returned (first second third fourth fifth sixth seventh : Expr) : Expr :=
  .inLeft (.sum .word .word)
    (.pair first (.pair second (.pair third (.pair fourth (.pair fifth (.pair sixth seventh))))))

private def zero : Expr := .word Word.zero

/-- The call phase: target and input from the calldata, the input written to
slot 0, then a finish with the input or the first request. -/
def callProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 5).resultType
  body :=
    .letE (readInput 0 0)
      (.letE (readInput 1 32)
        (.letE (storageWrite 2 (.word (w 0)) (.var 0))
          (.letE (requestedOf (.var 1))
            (.ifE (.binary .wordEq (.var 0) zero)
              (returned zero (.var 2) zero zero zero zero zero)
              (returned (.word (w 1)) (.var 3) (.word (w getSelector)) (.var 2) (.var 3) (.var 2) zero)))))
}

theorem callProgram_checked : callProgram.checkHost = true := by
  decide

def callContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨callProgram, callProgram_checked⟩ 5 rfl

/-- The resume phase after every call: the kept target, input and calls made,
the status Word and the data from byte 128. -/
def resumeProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 5).resultType
  body :=
    .letE (inputSize 0)
      (.letE (readInput 1 0)
        (.letE (readInput 2 32)
          (.letE (readInput 3 64)
            (.letE (readInput 4 96)
              (.letE (readInput 5 128)
                (.letE (.binary .wordAdd (.var 2) (.word (w 1)))
                  (.letE (storageWrite 7 (.var 0)
                      (.binary .wordAdd (.var 2) (.binary .wordMul (.word (w 2)) (.binary .wordSub (.var 6) (.word (w 128))))))
                    (.letE (requestedOf (.var 5))
                      (.ifE (bitSet (.var 6) 1024)
                        (.inRight (CoreContractEntryProfile.wordTupleType 6) (.inLeft .word (.var 4)))
                        (.ifE (.binary .wordGt (.var 0) (.var 2))
                          (returned (.word (w 1)) (.var 7) (.word (w getSelector)) (.binary .wordAdd (.var 6) (.var 2))
                            (.var 7) (.var 6) (.var 2))
                          (returned zero (.binary .wordAdd (.var 3) (.var 2)) zero zero zero zero zero)))))))))))
}

theorem resumeProgram_checked : resumeProgram.checkHost = true := by
  decide

def resumeContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨resumeProgram, resumeProgram_checked⟩ 5 rfl

/-- The choosing parent with `count` resume phases, all the same program. -/
def choiceParent (count : Nat) : CallChoiceParent := {
  call := ⟨callContract, .choose⟩
  resumes := List.replicate count ⟨resumeContract, .choose⟩
  keptWords := 3
  call_entryProfile := rfl
  resumes_entryProfile := by
    intro phase member
    rw [List.eq_of_mem_replicate member]
    rfl
}

private def child : CheckedCoreContract := Tests.ContractCallChain.childContract

private def balanceOf (value : Nat) : Account → Account := fun account => account.withBalance (w value)

private def worldWith (code : CheckedHostCoreProgram) : WorldState :=
  WorldState.empty
    |>.putAccount callerAddress (balanceOf 9 Account.empty)
    |>.putAccount parentAddress (balanceOf 5 (Account.empty.withCode code))
    |>.putAccount childAddress (balanceOf 3 (Account.empty.withCode child.code))

private def initialWorld : WorldState := worldWith callContract.code

private def registry : CheckedContractRegistry := {
  lookup := fun address => if address = childAddress then some child else none }

private def input (value : Nat) : HostStorageDriver.InputData := {
  bytes := encodeWordBytesBE (addressToWord childAddress) ++ encodeWordBytesBE (w value)
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

private def choice (resumes value : Nat) : Result :=
  run registry (choiceParent resumes) initialWorld parentAddress callerAddress (input value) 4096

private def slot (world : WorldState) (address : Address) (index : Nat) : Word :=
  ((world.account? address).map fun account => account.storageRead (w index)).getD (w 0)

private def text (outcome : FrameOutcome Word) : String :=
  match outcome with
  | .returned bytes => encodeBytesText bytes
  | .reverted bytes => "revert:" ++ encodeBytesText bytes
  | .trapped reason => "trap:" ++ toString reason.val

/-- The outcome, the parent's slots 0 to 3, the child's slots 0 and 1, and each
call's argument, status and delivered bytes. -/
private def summary : Result → Option (String × List Word × List Word ×
    List (Word × CallResumeExecution.ChildStatus × String))
  | .completed outcome finalWorld calls =>
      some (text outcome, [0, 1, 2, 3].map (slot finalWorld parentAddress),
        [0, 1].map (slot finalWorld childAddress),
        calls.map fun call => (call.request.argument, call.child.status, encodeBytesText call.child.data))
  | _ => none

private def balancesAndCode (world : WorldState) (code : CheckedHostCoreProgram) : Result → Bool
  | .completed _ finalWorld _ =>
      [callerAddress, parentAddress, childAddress].all (fun address =>
        finalWorld.balance? address == world.balance? address) &&
      (match finalWorld.code? parentAddress with
        | some installed => installed.program == code.program
        | none => false)
  | _ => false

private def xorWord (left right : Word) : Word := w (left.val ^^^ right.val)

/-- The first `count` bytes of `x xor R1 ‖ x xor R2` as hexadecimal text. -/
private def childData (x count : Nat) : String :=
  encodeBytesText ((encodeWordBytesBE (xorWord (w x) firstRamp) ++
    encodeWordBytesBE (xorWord (w x) secondRamp)).extract 0 count)

private def wordText (value : Word) : String := encodeBytesText (encodeWordBytesBE value)

def testContractCallChoice : IO Unit := do
  -- A zero count finishes in the call phase without a call.
  ensure (summary (choice 3 4) == some (wordText (w 4), [w 4, w 0, w 0, w 0], [w 0, w 0], []))
    "a zero count made a call or did not finish with the input"
  -- One call: the resume phase reads its status and size, then finishes.
  ensure (summary (choice 3 260) == some (wordText (w 1), [w 260, w 5, w 0, w 0], [w 260, w 1],
      [(w 260, .returned, childData 260 2)]))
    "one call differs"
  -- Two calls, a return then a revert: the revert leaves the first call's world.
  ensure (summary (choice 3 516) == some (wordText (w 2), [w 516, w 5, w 4, w 0], [w 516, w 1],
      [(w 516, .returned, childData 516 2), (w 517, .reverted, childData 517 2)]))
    "a return then a revert differs"
  -- Three calls through the same resume program.
  ensure (summary (choice 3 772) == some (wordText (w 3), [w 772, w 5, w 4, w 7], [w 774, w 2],
      [(w 772, .returned, childData 772 2), (w 773, .reverted, childData 773 2),
        (w 774, .returned, childData 774 3)]))
    "three calls differ"
  -- A long call: the finishing phase reads that call's first Word.
  ensure (summary (choice 3 322) == some (wordText (w ((xorWord (w 322) firstRamp).val + 1)),
      [w 322, w 67, w 0, w 0], [w 322, w 1], [(w 322, .returned, childData 322 33)]))
    "a long call differs"
  -- A resume phase revert commits nothing.
  ensure (summary (choice 3 1284) == some ("revert:0x" ++ hexWord "1", [w 0, w 0, w 0, w 0], [w 0, w 0],
      [(w 1284, .returned, childData 1284 2)]))
    "a resume phase revert committed a phase"
  -- A request with no phase left stops the transaction.
  ensure ((match choice 2 772 with
    | .callLimit 2 => true
    | _ => false))
    "a third request without a third resume phase did not stop at call 2"
  ensure ((match choice 0 260 with
    | .callLimit 0 => true
    | _ => false))
    "a request without resume phases did not stop at call 0"
  -- Every balance and the parent's code stay as they were.
  for value in [4, 260, 516, 772, 322, 1284] do
    ensure (balancesAndCode initialWorld callContract.code (choice 3 value))
      s!"input {value} changed a balance or the parent's code"
  -- Fuel runs out in the call phase first, and a parent without its call phase
  -- installed does not run.
  ensure ((match run registry (choiceParent 3) initialWorld parentAddress callerAddress (input 260) 0 with
    | .outOfFuel .call => true
    | _ => false))
    "an exhausted call phase did not report its step"
  ensure ((match run registry (choiceParent 3) initialWorld childAddress callerAddress (input 260) 4096 with
    | .unresolved .call => true
    | _ => false))
    "a parent without its call phase ran"
  -- The call chain's parent runs alike as request phases and a finish phase.
  let chainWorld := worldWith Tests.ContractCallChain.callContract.code
  for value in [4, 5, 66, 63, 260, 516] do
    let viaChoice := run registry (ofChain Tests.ContractCallChain.parentContract) chainWorld parentAddress
      callerAddress (input value) 4096
    let viaChain := (CallChainExecution.run registry Tests.ContractCallChain.parentContract chainWorld parentAddress
      callerAddress (input value) 4096).toChoice
    ensure (summary viaChoice == summary viaChain && (summary viaChoice).isSome)
      s!"input {value}: the call chain through ofChain differs"
    ensure (balancesAndCode chainWorld Tests.ContractCallChain.callContract.code viaChoice)
      s!"input {value}: the call chain through ofChain changed a balance or the parent's code"

end Tests.ContractCallChoice
end

section
-- leanmerge: from Solcore.Test.ContractCallResume
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
end

section
-- leanmerge: from Solcore.Test.ContractCallWordBoundary
/-! Focused regressions for the low-level checked contract-word call boundary. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def target : Word := ⟨0x1234, by decide⟩
private def input : Word :=
  ⟨0x0102030405060708090a0b0c0d0e0f10, by decide⟩
private def payload : Word := ⟨0xa5, by decide⟩
private def trapReason : Word := ⟨0xb6, by decide⟩
private def failureReason : Word := ⟨0xc7, by decide⟩

private def returned : ContractCallWordResult := .returned payload
private def reverted : ContractCallWordResult := .reverted payload
private def trapped : ContractCallWordResult := .trapped trapReason
private def failed : ContractCallWordResult := .failed failureReason

private def canonicalResponses : List ContractCallWordResult :=
  [returned, reverted, trapped, failed]

private def canonicalRoundTrips : Bool :=
  canonicalResponses.all fun response =>
    ContractCallWordResult.ofValue? response.value == some response

private def canonicalValuesDisjoint : Bool :=
  returned.value != reverted.value &&
    returned.value != trapped.value &&
    returned.value != failed.value &&
    reverted.value != trapped.value &&
    reverted.value != failed.value &&
    trapped.value != failed.value

private theorem compileTimeCanonicalRoundTrips :
    canonicalRoundTrips = true := by
  native_decide

private theorem compileTimeCanonicalValuesDisjoint :
    canonicalValuesDisjoint = true := by
  native_decide

private theorem compileTimeCanonicalValuesTyped :
    returned.value.type = ContractCallWordResult.resultType ∧
      reverted.value.type = ContractCallWordResult.resultType ∧
      trapped.value.type = ContractCallWordResult.resultType ∧
      failed.value.type = ContractCallWordResult.resultType := by
  simp [returned, reverted, trapped, failed]

private def invalidAddressCode : Word := ⟨0, by decide⟩
private def unavailableCode : Word := ⟨1, by decide⟩
private def depthExceededCode : Word := ⟨2, by decide⟩

private def failureCodesExactAndDistinct : Bool :=
  ContractCallFailure.invalidAddress.code == invalidAddressCode &&
    ContractCallFailure.unavailable.code == unavailableCode &&
    ContractCallFailure.depthExceeded.code == depthExceededCode &&
    ContractCallFailure.invalidAddress.code !=
      ContractCallFailure.unavailable.code &&
    ContractCallFailure.invalidAddress.code !=
      ContractCallFailure.depthExceeded.code &&
    ContractCallFailure.unavailable.code !=
      ContractCallFailure.depthExceeded.code

private theorem compileTimeFailureCodes :
    failureCodesExactAndDistinct = true := by
  native_decide

private theorem compileTimeFailureBranches :
    ContractCallFailure.invalidAddress.result = .failed invalidAddressCode ∧
      ContractCallFailure.unavailable.result = .failed unavailableCode ∧
      ContractCallFailure.depthExceeded.result = .failed depthExceededCode := by
  native_decide

private def canonicalInput : HostStorageDriver.InputData :=
  HostStorageDriver.InputData.ofWord input

private def canonicalInputExact : Bool :=
  canonicalInput.bytes.size == 32 &&
    canonicalInput.bytes == encodeWordBytesBE input &&
    canonicalInput.sizeWord.val == 32 &&
    canonicalInput.wordBE? Word.zero == some input

private theorem compileTimeCanonicalInputExact :
    canonicalInputExact = true := by
  native_decide

private theorem compileTimeCanonicalInputWordBE :
    canonicalInput.wordBE? Word.zero = some input := by
  exact HostStorageDriver.InputData.ofWord_wordBE?_zero input

/-- A checker-accepted Core program that emits the new typed host request. -/
private def callProgram : Program := {
  resultType := ContractCallWordResult.resultType
  body :=
    .apply
      (.var HostFunction.callContractWord.index)
      (.pair (.word target) (.word input))
}

private theorem callProgramHostChecked :
    callProgram.checkHost = true := by
  decide

private def callCode : CheckedHostCoreProgram :=
  ⟨callProgram, callProgramHostChecked⟩

/-- Observe emission and feed a request-indexed response back to Core. -/
private def checkedCallEmitsAndResumes : Bool :=
  match callCode.program.runHostStateful 32 with
  | .suspended
      ⟨.callContractWord actualTarget actualInput, continuation, store⟩
      remainingFuel =>
      actualTarget == target && actualInput == input &&
        let suspension : HostSuspension :=
          ⟨.callContractWord actualTarget actualInput, continuation, store⟩
        match hostRun remainingFuel
            (suspension.resume (ContractCallWordResult.returned payload)) with
        | .done value finalStore =>
            value == returned.value && finalStore == []
        | _ => false
  | _ => false

private theorem compileTimeCheckedCallEmitsAndResumes :
    checkedCallEmitsAndResumes = true := by
  native_decide

private def storageAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x30, by decide⟩
private def storageSlot : Word := ⟨0x40, by decide⟩
private def storageValue : Word := ⟨0x50, by decide⟩

private def storageAccount : Account :=
  Account.empty.storageWrite storageSlot storageValue

private def world : WorldState :=
  WorldState.empty.putAccount storageAddress storageAccount

private def context : HostStorageDriver.Context Nat (List Nat) :=
  ⟨⟨storageAddress,
      ⟨⟨world, ⟨7, [8]⟩⟩, (world, ⟨9, [10, 11]⟩)⟩⟩,
    storageAccount,
    by rfl⟩

private def executionInputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := storageAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := canonicalInput
  currentAddress := storageAddress
}

private def flatHandled :
    HostStorageDriver.Context Nat (List Nat) × ContractCallWordResult :=
  HostStorageDriver.handleRequest executionInputs context
    (.callContractWord target input)

private theorem compileTimeFlatHandlerExact :
    flatHandled =
      (context, ContractCallFailure.depthExceeded.result) := by
  rfl

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

private def flatHandlerPreservesObservableContext : Bool :=
  flatHandled.2 == ContractCallFailure.depthExceeded.result &&
    flatHandled.1.context.storageAddress == storageAddress &&
    flatHandled.1.storageAccount.storageRead storageSlot == storageValue &&
    storageValueAt? flatHandled.1.context.values.checkpoint.state
      storageAddress storageSlot == some storageValue &&
    storageValueAt? flatHandled.1.context.values.working.1
      storageAddress storageSlot == some storageValue &&
    flatHandled.1.context.values.checkpoint.effects.rollback == 7 &&
    flatHandled.1.context.values.checkpoint.effects.trace == [8] &&
    flatHandled.1.context.values.working.2.rollback == 9 &&
    flatHandled.1.context.values.working.2.trace == [10, 11]

private theorem compileTimeFlatHandlerPreservesContext :
    flatHandlerPreservesObservableContext = true := by
  native_decide

/-- Runtime counterpart to the compile-time boundary assertions above. -/
def testContractCallWordBoundary : IO Unit := do
  assertTrue canonicalRoundTrips
    "contract-call response values did not round-trip canonically"
  assertTrue canonicalValuesDisjoint
    "contract-call response constructors shared a Core value"
  assertTrue failureCodesExactAndDistinct
    "contract-call dispatch failure codes changed or collided"
  assertTrue canonicalInputExact
    "contract-word input was not the exact 32-byte big-endian encoding"
  assertTrue checkedCallEmitsAndResumes
    "checked Core call did not emit and resume with its typed response"
  assertTrue flatHandlerPreservesObservableContext
    "flat handler did not reject recursion without changing its context"

end Tests
end

section
-- leanmerge: from Solcore.Test.ContractEnumEntryProfile
/-! Golden laws for the enum entry convention. The expected return data is
written out as hexadecimal text. A static enum is the constructor's tag Word,
its fields, then zero Words up to the widest constructor. A dynamic enum, one
with a `bytes` constructor, is the offset Word 32, then that body; a `bytes`
field's head is its offset from the body's start, and its tail is the length
Word and the zero-padded data. A revert carries one Word and a trap its reason.
Wrong annotations and fields do not decode, an enum value has no one-Word view,
and the nested executor treats a registered enum contract as unavailable to a
word call and a template with an enum initializer as unavailable to creation,
while an enum root returns its whole encoding. -/

set_option autoImplicit false

namespace Tests.ContractEnumEntryProfile

open Solcore.Core
open Solcore.ContractRuntime
open Tests.OneLevelNestedExecutionFixture

/-! Kernel-checked recognition facts. -/

example : (CoreContractEntryProfile.enumOutcomeV1 .noWords .oneWord []).resultType =
    .sum (.sum (.product .word .unit) (.product .word .word)) (.sum .word .word) := rfl

example : (CoreContractEntryProfile.enumOutcomeV1 .twoWords .boundedBytes [.noWords]).resultType =
    .sum (.sum (.product .word (.product .word .word))
      (.sum (.product .word (.sum .unit (.product .word (.product .word .word))))
        (.product .word .unit))) (.sum .word .word) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.sum (.product .word .unit) (.sum (.product .word .word) (.product .word .unit)))
      (.sum .word .word)) =
      some (.enumOutcomeV1 .noWords .oneWord [.noWords]) := rfl

/-- A sum of untagged Words, a three-Word constructor and a lone constructor are
not enums; the existing conventions keep their types. -/
example : CoreContractEntryProfile.ofResultType? (.sum (.sum .word .word) (.sum .word .word)) = none :=
  rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.sum (.product .word .unit) (.product .word (.product .word (.product .word .word))))
      (.sum .word .word)) = none := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.product .word .unit) (.sum .word .word)) = none := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.product .word .word) (.sum .word .word)) = some (.wordTupleOutcomeV1 0) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.sum .unit (.product .word (.product .word .word))) (.sum .word .word)) =
      some .boundedBytesOutcomeV1 := rfl

example (first second : EnumPayload) (rest : List EnumPayload) :
    (CoreContractEntryProfile.enumOutcomeV1 first second rest).resultType ≠
      CoreContractEntryProfile.boundedBytesOutcomeV1.resultType := by
  intro equal
  cases CoreContractEntryProfile.resultType_injective equal

example (first second : EnumPayload) (rest : List EnumPayload) :
    CoreContractEntryProfile.ofResultType?
        (CoreContractEntryProfile.enumOutcomeV1 first second rest).resultType =
      some (.enumOutcomeV1 first second rest) :=
  CoreContractEntryProfile.ofResultType?_resultType _

/-- The body's head is the tag and the widest fields; only `bytes` makes an
enum dynamic. -/
example : CoreContractEntryProfile.enumBodyHeadSize [.noWords, .oneWord] = 64 := rfl
example : CoreContractEntryProfile.enumBodyHeadSize [.noWords, .twoWords, .boundedBytes] = 96 := rfl
example : CoreContractEntryProfile.enumBodyHeadSize [.noWords, .noWords] = 32 := rfl
example : CoreContractEntryProfile.enumIsStatic [.noWords, .oneWord, .twoWords] = true := rfl
example : CoreContractEntryProfile.enumIsStatic [.oneWord, .boundedBytes] = false := rfl

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- One Word's 64 hexadecimal digits, written as the digits after a run of zeros. -/
private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def zeros (bytes : Nat) : String := String.ofList (List.replicate (2 * bytes) '0')

/-- Two data Words whose bytes are 1 to 32 and 33 to 64. -/
private def firstRamp : Word := w 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
private def secondRamp : Word := w 0x2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40
private def firstHex : String := "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
private def secondHex : String := "2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40"

private def tagged (tag : Word) (fields : Value) : Value := .pair (.word tag) fields

/-- The bounded `bytes` value of `length` bytes of the two ramps. -/
private def bytesValue (length : Nat) : Value :=
  if length = 0 then .inLeft (.product .word (.product .word .word)) .unit
  else .inRight .unit (.pair (.word (w (length - 1))) (.pair (.word firstRamp) (.word secondRamp)))

/-- The value of constructor `index`, with every annotation exact. -/
private def inject : List EnumPayload → Nat → Value → Value
  | _ :: next :: rest, 0, value => .inLeft (CoreContractEntryProfile.enumType next rest) value
  | payload :: next :: rest, index + 1, value =>
      .inRight (CoreContractEntryProfile.enumPayloadType payload) (inject (next :: rest) index value)
  | _, _, value => value

private def returned (payloads : List EnumPayload) (value : Value) : Option (FrameOutcome Word) :=
  match payloads with
  | first :: second :: rest =>
      CoreContractEntryProfile.decode? (.enumOutcomeV1 first second rest) (.inLeft (.sum .word .word) value)
  | _ => none

private def returnedText (outcome : Option (FrameOutcome Word)) : Option String :=
  match outcome with
  | some (.returned bytes) => some (encodeBytesText bytes)
  | _ => none

private def text (payloads : List EnumPayload) (index : Nat) (value : Value) : Option String :=
  returnedText (returned payloads (inject payloads index value))

/-- `A() | B(uint256)`, static: the narrower constructor leaves one zero Word. -/
private def staticPair : List EnumPayload := [.noWords, .oneWord]
/-- `A(uint256, uint256) | B() | C(uint256) | D()`, static, three Words each. -/
private def staticWide : List EnumPayload := [.twoWords, .noWords, .oneWord, .noWords]
/-- `A() | B()`, static: the tag alone. -/
private def staticTags : List EnumPayload := [.noWords, .noWords]
/-- `A(uint256) | B(bytes) | C()`, dynamic with a two-Word body head. -/
private def dynamicNarrow : List EnumPayload := [.oneWord, .boundedBytes, .noWords]
/-- `A() | B(uint256) | C(uint256, uint256) | D(bytes)`, dynamic with a
three-Word body head, so a `bytes` field leaves one zero Word before its tail. -/
private def dynamicWide : List EnumPayload := [.noWords, .oneWord, .twoWords, .boundedBytes]
/-- `A(bytes) | B(uint256)`, dynamic, with `bytes` first. -/
private def dynamicFirst : List EnumPayload := [.boundedBytes, .oneWord]

/-- The tail of `length` ramp bytes: the length Word, then the data zero-padded. -/
private def tailHex (length : Nat) : String :=
  let data := (firstHex ++ secondHex).take (2 * length)
  hexWord (String.ofList (Nat.toDigits 16 length)) ++ data ++ zeros ((32 - length % 32) % 32)

/-- A registered child returning `A(uint256) | B(bytes)`'s `bytes` constructor,
33 bytes of its payload and new value, after writing the child slot. -/
def enumChildProgram : Program := {
  resultType := (CoreContractEntryProfile.enumOutcomeV1 .oneWord .boundedBytes []).resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word childSlot) (.word childNewValue)))
      (.inLeft (.sum .word .word) (.inRight (.product .word .word)
        (.pair (.word (w 0xb1)) (.inRight .unit
          (.pair (.word (w 32)) (.pair (.word childPayload) (.word childNewValue)))))))
}

theorem enumChildProgram_checked : enumChildProgram.checkHost = true := by
  decide

def enumChildContract : CheckedCoreContract :=
  CheckedCoreContract.enumOutcomeV1 ⟨enumChildProgram, enumChildProgram_checked⟩
    .oneWord .boundedBytes [] rfl

/-- A creation template whose initializer returns `A()` of `A() | B(uint256)`. -/
def enumInitializerProgram : Program := {
  resultType := (CoreContractEntryProfile.enumOutcomeV1 .noWords .oneWord []).resultType
  body := .inLeft (.sum .word .word) (.inLeft (.product .word .word) (.pair (.word (w 0xa0)) .unit))
}

theorem enumInitializerProgram_checked : enumInitializerProgram.checkHost = true := by
  decide

def enumInitializer : CheckedCoreContract :=
  CheckedCoreContract.enumOutcomeV1 ⟨enumInitializerProgram, enumInitializerProgram_checked⟩
    .noWords .oneWord [] rfl

/-- The preflight fixture's environment with the enum initializer in its template. -/
def enumTemplateEnvironment : ExecutionEnvironment := {
  callRegistry := Adr0148CheckedCreationPreflightFixture.validCallRegistry
  creationTemplates := {
    lookup := fun identifier =>
      if identifier = Adr0148CheckedCreationPreflightFixture.templateId then
        some { initializer := enumInitializer, runtime := Adr0148CheckedCreationPreflightFixture.runtime }
      else none }
  creationAddressPolicy := Adr0148CheckedCreationPreflightFixture.addressPolicy
}

private def completionFuel : Nat := 512

/-- The creating root's outcome, and the working creator nonce and created
account when it halts. -/
private def creationAt (environment : ExecutionEnvironment) :
    Option (FrameHaltKind × FrameOutcome Word × Option Word × Bool) :=
  match (OneLevelNestedExecution.runWithEnvironment Adr0148NestedCreationLifecycleFixture.rootContract
      Adr0148NestedCreationLifecycleFixture.rootInvocation Adr0148NestedCreationLifecycleFixture.rootInstalled
      environment completionFuel).view with
  | .completed terminal =>
      let working := terminal.terminalContext.context.values.working.1
      some (terminal.outcome.kind, terminal.outcome,
        working.nonce? Adr0148CheckedCreationPreflightFixture.creator,
        (working.account? Adr0148CheckedCreationPreflightFixture.created).isSome)
  | .outOfFuel _ _ _ => none

private def childAt {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : OneLevelNestedExecution.Result initialWorld root invocation) :
    Option (FrameOutcome Word × Option Word × Option Word) :=
  match result.view with
  | .completed terminal =>
      some (terminal.outcome, childStorageValue? terminal.terminalContext.context.values.working.1,
        childStorageValue? terminal.finalWorld)
  | .outOfFuel _ _ _ => none

def testContractEnumEntryProfile : IO Unit := do
  -- A static enum is inline: the tag, the fields and zero Words up to the
  -- widest constructor.
  ensure (text staticPair 0 (tagged (w 0xa0) .unit) == some ("0x" ++ hexWord "a0" ++ zeros 32))
    "a static field-less constructor differs from its tag and zero Word"
  ensure (text staticPair 1 (tagged (w 0xb1) (.word firstRamp)) == some ("0x" ++ hexWord "b1" ++ firstHex))
    "a static one-Word constructor differs from its tag and Word"
  ensure (text staticWide 0 (tagged (w 0xa0) (.pair (.word firstRamp) (.word secondRamp))) ==
      some ("0x" ++ hexWord "a0" ++ firstHex ++ secondHex))
    "a static two-Word constructor differs from its tag and Words"
  ensure (text staticWide 1 (tagged (w 0xb1) .unit) == some ("0x" ++ hexWord "b1" ++ zeros 64))
    "a static field-less constructor differs from its tag and two zero Words"
  ensure (text staticWide 2 (tagged (w 0xc2) (.word firstRamp)) ==
      some ("0x" ++ hexWord "c2" ++ firstHex ++ zeros 32))
    "a static one-Word constructor differs from its tag, Word and zero Word"
  ensure (text staticWide 3 (tagged (w 0xd3) .unit) == some ("0x" ++ hexWord "d3" ++ zeros 64))
    "the last static constructor differs from its tag and two zero Words"
  ensure (text staticTags 0 (tagged (w 0xa0) .unit) == some ("0x" ++ hexWord "a0") &&
      text staticTags 1 (tagged (w 0xb1) .unit) == some ("0x" ++ hexWord "b1"))
    "an enum of field-less constructors differs from its one tag Word"
  -- A dynamic enum is the offset 32 to its body; a `bytes` field's head is its
  -- offset from the body's start.
  ensure (text dynamicNarrow 0 (tagged (w 0xa0) (.word firstRamp)) ==
      some ("0x" ++ hexWord "20" ++ hexWord "a0" ++ firstHex))
    "a dynamic enum's one-Word constructor differs from its offset, tag and Word"
  ensure (text dynamicNarrow 2 (tagged (w 0xc2) .unit) ==
      some ("0x" ++ hexWord "20" ++ hexWord "c2" ++ zeros 32))
    "a dynamic enum's field-less constructor differs from its offset, tag and zero Word"
  for length in [0, 1, 31, 32, 33, 64] do
    ensure (text dynamicNarrow 1 (tagged (w 0xb1) (bytesValue length)) ==
        some ("0x" ++ hexWord "20" ++ hexWord "b1" ++ hexWord "40" ++ tailHex length))
      s!"a {length}-byte constructor of a two-Word body differs from its encoding"
    ensure (text dynamicWide 3 (tagged (w 0xd3) (bytesValue length)) ==
        some ("0x" ++ hexWord "20" ++ hexWord "d3" ++ hexWord "60" ++ zeros 32 ++ tailHex length))
      s!"a {length}-byte constructor of a three-Word body differs from its encoding"
    ensure (text dynamicFirst 0 (tagged (w 0xa0) (bytesValue length)) ==
        some ("0x" ++ hexWord "20" ++ hexWord "a0" ++ hexWord "40" ++ tailHex length))
      s!"a {length}-byte first constructor differs from its encoding"
  -- The hand-written tails of the bank's ends.
  ensure (tailHex 0 == hexWord "" && tailHex 1 == hexWord "1" ++ "01" ++ zeros 31 &&
      tailHex 33 == hexWord "21" ++ firstHex ++ "21" ++ zeros 31 &&
      tailHex 64 == hexWord "40" ++ firstHex ++ secondHex)
    "the expected bytes tails are not the zero-padded ramps"
  ensure (text dynamicWide 0 (tagged (w 0xa0) .unit) ==
      some ("0x" ++ hexWord "20" ++ hexWord "a0" ++ zeros 64) &&
    text dynamicWide 1 (tagged (w 0xb1) (.word firstRamp)) ==
      some ("0x" ++ hexWord "20" ++ hexWord "b1" ++ firstHex ++ zeros 32) &&
    text dynamicWide 2 (tagged (w 0xc2) (.pair (.word firstRamp) (.word secondRamp))) ==
      some ("0x" ++ hexWord "20" ++ hexWord "c2" ++ firstHex ++ secondHex))
    "a dynamic enum's static constructors differ from their padded bodies"
  -- All-ones data lose every byte after the length, as for bounded `bytes`.
  ensure (text dynamicNarrow 1 (tagged (w 0xb1) (.inRight .unit
      (.pair (.word (w 32)) (.pair (.word (w (2 ^ 256 - 1))) (.word (w (2 ^ 256 - 1))))))) ==
      some ("0x" ++ hexWord "20" ++ hexWord "b1" ++ hexWord "40" ++ hexWord "21" ++
        String.ofList (List.replicate 66 'f') ++ zeros 31))
    "the bytes after a 33-byte field's length are not zero"
  -- Sizes: the body's head for a static enum; the offset, head and tail Words
  -- for a dynamic one.
  for (payloads, index, value, size) in [
      (staticPair, 0, tagged (w 1) .unit, 64), (staticWide, 3, tagged (w 1) .unit, 96),
      (staticTags, 1, tagged (w 1) .unit, 32), (dynamicNarrow, 2, tagged (w 1) .unit, 96),
      (dynamicNarrow, 1, tagged (w 1) (bytesValue 0), 128),
      (dynamicNarrow, 1, tagged (w 1) (bytesValue 33), 192),
      (dynamicWide, 3, tagged (w 1) (bytesValue 64), 224)] do
    match returned payloads (inject payloads index value) with
    | some (.returned bytes) => ensure (bytes.size == size) s!"an enum value has {bytes.size} bytes, not {size}"
    | _ => throw (IO.userError "a well-typed enum value did not decode")
  -- Revert and trap carry one Word, under the exact enum annotation.
  ensure ((match CoreContractEntryProfile.decode? (.enumOutcomeV1 .noWords .oneWord [])
      (.inRight (CoreContractEntryProfile.enumType .noWords [.oneWord]) (.inLeft .word (.word (w 0x99)))) with
    | some (.reverted bytes) => some (encodeBytesText bytes)
    | _ => none) == some ("0x" ++ hexWord "99"))
    "an enum revert differs from its one Word"
  ensure (CoreContractEntryProfile.decode? (.enumOutcomeV1 .noWords .oneWord [])
      (.inRight (.sum (.product .word .unit) (.product .word .word)) (.inRight .word (.word (w 7)))) ==
        some (.trapped (w 7)))
    "an enum trap differs from its reason"
  -- A wrong annotation or wrong fields do not decode.
  ensure (CoreContractEntryProfile.decode? (.enumOutcomeV1 .noWords .oneWord [])
      (.inRight (.sum (.product .word .word) (.product .word .unit)) (.inLeft .word (.word (w 1))))).isNone
    "a revert under another enum's annotation decoded"
  ensure (returned staticPair (.inLeft (.product .word .unit) (tagged (w 1) .unit))).isNone
    "a constructor injected with the wrong remaining type decoded"
  ensure (returned staticPair (.inRight (.product .word .word) (tagged (w 1) (.word firstRamp)))).isNone
    "a constructor injected past the wrong constructor type decoded"
  ensure (returned staticPair (inject staticPair 0 (tagged (w 1) (.word firstRamp)))).isNone
    "a field-less constructor with a Word decoded"
  ensure (returned staticPair (inject staticPair 1 (tagged (w 1) .unit))).isNone
    "a one-Word constructor without its Word decoded"
  ensure (returned staticPair (inject staticPair 1 (.pair (.bool true) (.word firstRamp)))).isNone
    "a constructor with a Boolean tag decoded"
  ensure (returned dynamicNarrow (inject dynamicNarrow 1 (tagged (w 1)
      (.inRight .unit (.pair (.word (w 0)) (.word firstRamp)))))).isNone
    "a bytes field with one data Word decoded"
  ensure (returned staticPair (.word firstRamp)).isNone
    "a bare Word decoded as an enum"
  ensure (CoreContractEntryProfile.decode? (.enumOutcomeV1 .noWords .oneWord [])
      (.inLeft (.sum .word .bool) (inject staticPair 0 (tagged (w 1) .unit)))).isNone
    "a return with another annotation decoded"
  -- The other conventions are unchanged, and an enum value has no one-Word view.
  ensure (CoreContractEntryProfile.decode? .wordOutcomeV1
      (.inLeft (.sum .word .word) (.word (w 3))) == some (.returned (encodeWordBytesBE (w 3))))
    "the one-Word outcome convention changed"
  ensure (CoreContractEntryProfile.decode? .boundedBytesOutcomeV1
      (.inLeft (.sum .word .word) (.inLeft (.product .word (.product .word .word)) .unit)) ==
        some (.returned (encodeWordBytesBE (w 32) ++ encodeWordBytesBE (w 0))))
    "the bounded bytes convention changed"
  ensure (CoreContractEntryProfile.decodeWordOutcome? (.enumOutcomeV1 .noWords .noWords [])
      (.inLeft (.sum .word .word) (inject staticTags 0 (tagged (w 1) .unit)))).isNone
    "an enum value has a one-Word view"
  ensure (CoreContractEntryProfile.wordOutcomeV1.returnsOneWord &&
      CoreContractEntryProfile.returnWord.returnsOneWord &&
      !(CoreContractEntryProfile.enumOutcomeV1 .noWords .noWords []).returnsOneWord)
    "the one-Word predicate changed"
  -- Admission recognizes the enum contract's exact convention.
  ensure ((CheckedCoreContract.ofCode? enumChildContract.code).map (·.entryProfile) ==
      some (.enumOutcomeV1 .oneWord .boundedBytes []))
    "admission does not recognize the enum convention"
  -- A word call to a registered enum contract is unavailable: the child never
  -- runs, its slot keeps the old value, and the root traps with the failure.
  ensure (childAt (runScenario (rootContract .commit childTargetWord) enumChildContract completionFuel) ==
      some (.trapped ContractCallFailure.unavailable.code, some childOldValue, some childOldValue))
    "a word call reached an enum contract"
  -- Creation from a template with an enum initializer is unavailable before the
  -- creator's nonce advances; the one-Word initializer still deploys.
  ensure (creationAt enumTemplateEnvironment ==
      some (.trapped, .trapped ContractCallFailure.unavailable.code,
        some Adr0148CheckedCreationPreflightFixture.oldNonce, false))
    "creation started an enum initializer"
  ensure ((creationAt Adr0148CheckedCreationPreflightFixture.validEnvironment).map
      (fun (kind, _, nonce, present) => (kind, nonce, present)) ==
      some (.returned, some Adr0148CheckedCreationPreflightFixture.nextNonce, true))
    "the one-Word initializer no longer deploys"
  -- An enum root returns its whole encoding through the nested executor: the
  -- offset, the tag, the field's offset and 33 bytes of the payload Word and the
  -- new value's first byte, which is zero.
  ensure ((match childAt (runScenario enumChildContract childReturnContract completionFuel) with
    | some (.returned bytes, working, final) => some (encodeBytesText bytes, working, final)
    | _ => none) ==
      some ("0x" ++ hexWord "20" ++ hexWord "b1" ++ hexWord "40" ++ hexWord "21" ++ hexWord "71" ++
        zeros 32, some childOldValue, some childOldValue))
    "an enum root did not return its whole encoding"

end Tests.ContractEnumEntryProfile
end

section
-- leanmerge: from Solcore.Test.ContractLanguageResult
/-! An ordinary sum failure after actual storage and log requests rolls back
through the existing top-level finalizer. Fuel exhaustion retains its checkpoint. -/

set_option autoImplicit false

namespace Tests.ContractLanguageResult

open Solcore.Core
open Solcore.ContractRuntime

private def word (value : Nat) : Word := Word.ofNatModulo value
private def target : Address := ⟨17, by decide⟩
private def caller : Address := ⟨19, by decide⟩
private def slot : Word := word 3
private def oldValue : Word := word 5
private def writtenValue : Word := word 7
private def topic : Word := word 11
private def payload : Word := word 13
private def reason : Word := word 23

private def account : Account := Account.empty.storageWrite slot oldValue
private def initialWorld : WorldState := WorldState.empty.putAccount target account
private theorem present : initialWorld.account? target = some account :=
  WorldState.account?_putAccount_same _ _ _

private def context : TransactionHostStorageDriver.Context :=
  ⟨⟨target, TopLevelExecution.initialTransactionValues initialWorld⟩, account, present⟩

private def invocation : TopLevelInvocation := {
  target := target
  caller := caller
  callValue := Word.zero
  inputData := { bytes := ByteArray.empty, size_lt_wordModulus := by decide }
}

private def failureBody : Expr := LanguageResult.failure .word (.word reason)
private def afterWrite : Expr := .letE
  (.apply (.var (HostFunction.emitLogWord.index + 1)) (.pair (.word topic) (.word payload)))
  failureBody

private def program : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE
    (.apply (.var HostFunction.storageWrite.index) (.pair (.word slot) (.word writtenValue)))
    afterWrite
}

private theorem program_checked : program.checkHost = true := by decide

private def initialState : State := State.initial program.body hostEnvironment

private def raw (fuel : Nat) : HostDriverResult TransactionHostStorageDriver.Context :=
  TransactionHostStorageDriver.run context invocation.executionInputs fuel initialState

/-- The caller's total entry decoder is supplied unchanged to the adapter. -/
private def successCodec (_ : TransactionHostStorageDriver.Context)
    (value : Value) (_ : Store) : FrameOutcome Word :=
  (CoreContractEntryProfile.returnWord.decode? value).getD (.trapped Word.zero)

private def adapted (fuel : Nat) : CoreLanguageResult.Result TransactionHostStorageDriver.Context :=
  CoreLanguageResult.decode successCodec (raw fuel)

private theorem adapted_typed (fuel : Nat) : (adapted fuel).outcome.HasType .word :=
  CoreLanguageResult.decode_hasType successCodec _
    (TransactionHostStorageDriver.run_hasType context invocation.executionInputs fuel initialState
      (.eval .nil (hostEnvironment_hasTypes [] [])
        (Program.checkHost_sound program_checked) .nil))

private theorem invalid_impossible (fuel : Nat) (value : Value) (store : Store) :
    (adapted fuel).outcome ≠ .invalidCarrier value store := by
  intro invalid
  have typed := adapted_typed fuel
  rw [invalid] at typed
  exact typed

private theorem internal_fault_impossible (fuel : Nat) (error : MachineFault) (state : State) :
    (adapted fuel).outcome ≠ .fault error state := by
  intro fault
  have typed := adapted_typed fuel
  rw [fault] at typed
  exact typed

private def expectedLog : CheckedCoreWordLog := {
  emitter := target
  topic := topic
  payload := payload
}

private def writeSuspension : HostSuspension :=
  ⟨.storageWrite slot writtenValue, [.letBody afterWrite hostEnvironment], []⟩

private def writeHandled :=
  TransactionHostStorageDriver.handleSuspension invocation.executionInputs context writeSuspension

private def logSuspension : HostSuspension :=
  ⟨.emitLogWord topic payload, [.letBody failureBody (.unit :: hostEnvironment)], []⟩

private def effectsHandled := TransactionHostStorageDriver.handleSuspension
  invocation.executionInputs writeHandled.1 logSuspension

private theorem raw_after_effects (fuel : Nat) :
    raw (fuel + 21) = TransactionHostStorageDriver.run effectsHandled.1
      invocation.executionInputs fuel effectsHandled.2 := by
  unfold raw
  rw [TransactionHostStorageDriver.run_of_suspended context invocation.executionInputs
    (fuel + 21) (fuel + 11) initialState writeSuspension (by rfl)]
  change TransactionHostStorageDriver.run writeHandled.1 invocation.executionInputs
    (fuel + 11) writeHandled.2 = _
  rw [TransactionHostStorageDriver.run_of_suspended writeHandled.1 invocation.executionInputs
    (fuel + 11) fuel writeHandled.2 logSuspension (by rfl)]
  rfl

private theorem raw_done : raw 40 =
    ⟨effectsHandled.1, .done (.inLeft .word (.word reason)) []⟩ := by
  rw [show 40 = 19 + 21 from rfl, raw_after_effects]
  exact TransactionHostStorageDriver.run_of_done _ _ _ _ _ _ (by rfl)

private theorem raw_checkpoint : raw 21 = ⟨effectsHandled.1, .outOfFuel effectsHandled.2⟩ := by
  rw [show 21 = 0 + 21 from rfl, raw_after_effects]
  exact TransactionHostStorageDriver.run_of_outOfFuel _ _ _ _ _ (by rfl)

private theorem adapted_trap : (adapted 40).outcome =
      .completed (.inLeft .word (.word reason)) [] (.trapped reason) := by
  simp only [adapted, raw_done]
  rfl

private theorem storage_written :
    (adapted 40).context.storageAccount.storageRead slot = writtenValue := by
  simp only [adapted, raw_done]
  rfl

private theorem log_recorded :
    (adapted 40).context.workingJournal.logList = [expectedLog] := by
  simp only [adapted, raw_done]
  rfl

private theorem checkpoint_retained (fuel : Nat) :
    (adapted fuel).context.context.values.checkpoint = context.context.values.checkpoint :=
  TransactionHostStorageDriver.run_checkpoint context invocation.executionInputs fuel initialState

/-- This is the same state-delta obligation used by the existing finalizer. -/
private def delta (fuel : Nat) : TopLevelStorageDelta initialWorld
    (adapted fuel).context.context.values.working.1 target where
  initialAccount := account
  finalAccount := (raw fuel).context.storageAccount
  initialAccount_present := present
  finalAccount_present := by
    have retained := TransactionHostStorageDriver.run_storageAddress context
      invocation.executionInputs fuel initialState
    have finalPresent := (raw fuel).context.storageAccount_present
    change (raw fuel).context.context.storageAddress = target at retained
    rw [retained] at finalPresent
    exact finalPresent
  code_preserved := by
    have finalPresent := (raw fuel).context.storageAccount_present
    have retained := TransactionHostStorageDriver.run_storageAddress context
      invocation.executionInputs fuel initialState
    change (raw fuel).context.context.storageAddress = target at retained
    have finalPresent' : (raw fuel).context.context.values.working.1.account? target =
        some (raw fuel).context.storageAccount := by
      rw [retained] at finalPresent
      exact finalPresent
    have preserved := TransactionHostStorageDriver.run_workingCode? context
      invocation.executionInputs fuel initialState target
    change (raw fuel).context.context.values.working.1.code? target =
      initialWorld.code? target at preserved
    simpa [WorldState.code?, finalPresent', present] using preserved
  otherAccounts_preserved := by
    intro address different
    exact TransactionHostStorageDriver.run_workingAccount?_of_ne_storageAddress
      context invocation.executionInputs fuel initialState address different

private theorem checkpoint_empty (fuel : Nat) :
    (adapted fuel).context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty := by
  rw [checkpoint_retained]
  rfl

private def finalized (fuel : Nat) : Option (TopLevelTerminalResult initialWorld target) :=
  (adapted fuel).finalize? invocation account present (delta fuel) (checkpoint_empty fuel)

private theorem failure_rolls_back :
    (finalized 40).map (·.finalWorld) = some initialWorld ∧
      (finalized 40).map (·.committedJournal) = some TransactionJournal.empty ∧
      (finalized 40).map (·.workingJournal.logList) = some [expectedLog] := by
  have final_eq : finalized 40 = some (TopLevelExecution.finalize invocation account present
      (adapted 40).context (.inLeft .word (.word reason)) [] (.trapped reason)
      (delta 40) (checkpoint_empty 40)) := by
    unfold finalized CoreLanguageResult.Result.finalize?
    rw [adapted_trap]
  rw [final_eq]
  exact ⟨rfl, congrArg some (checkpoint_empty 40), congrArg some log_recorded⟩

private theorem fuel_preserves_effects_without_finalizing :
    (adapted 21).outcome = .outOfFuel effectsHandled.2 ∧
      (adapted 21).context.storageAccount.storageRead slot = writtenValue ∧
      (adapted 21).context.workingJournal.logList = [expectedLog] ∧
      finalized 21 = none := by
  have exhausted : (adapted 21).outcome = .outOfFuel effectsHandled.2 := by
    simp only [adapted, raw_checkpoint]
    rfl
  refine ⟨exhausted, ?_, ?_, ?_⟩
  · simp only [adapted, raw_checkpoint]
    rfl
  · simp only [adapted, raw_checkpoint]
    rfl
  · unfold finalized CoreLanguageResult.Result.finalize?
    rw [exhausted]
    rfl

/-- A successful outer carrier hands the payload to the exact existing codec. -/
private theorem success_uses_existing_codec :
    CoreLanguageResult.decodeDone? successCodec context (.inRight .word (.word payload)) [] =
      CoreContractEntryProfile.returnWord.decode? (.word payload) := rfl

private theorem malformed_is_distinct :
    (CoreLanguageResult.decode successCodec ⟨context, .done .unit []⟩).outcome =
      .invalidCarrier .unit [] := rfl

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def test : IO Unit := do
  match (adapted 40).outcome with
  | .completed carrier store frame =>
      assertTrue (carrier == .inLeft .word (.word reason) && store == [] && frame == .trapped reason)
        "a returned language failure must retain its carrier and decode to the exact frame trap"
  | _ => throw (IO.userError "the checked language failure must complete after its host requests")
  assertTrue ((adapted 40).context.storageAccount.storageRead slot == writtenValue &&
      (adapted 40).context.workingJournal.logList == [expectedLog])
    "storage and log requests before the language failure must occur"
  match finalized 40 with
  | some result =>
      assertTrue ((result.finalWorld.account? target).map (·.storageRead slot) == some oldValue &&
          result.committedJournal.logList == [] && result.workingJournal.logList == [expectedLog])
        "the existing trap finalizer must roll back storage and committed logs while retaining working evidence"
  | none => throw (IO.userError "the completed language failure must have a terminal result")
  match (adapted 21).outcome with
  | .outOfFuel state =>
      assertTrue (state == effectsHandled.2 &&
          (adapted 21).context.storageAccount.storageRead slot == writtenValue &&
          (adapted 21).context.workingJournal.logList == [expectedLog])
        "fuel exhaustion must retain the exact post-effect Core state and host context"
  | _ => throw (IO.userError "21 fuel must stop before the language result completes")
  assertTrue (finalized 21 |>.isNone)
    "fuel exhaustion must not be finalized as a language failure or a completed frame"
  assertTrue (CoreLanguageResult.decodeDone? successCodec context
      (.inRight .word (.word payload)) [] == CoreContractEntryProfile.returnWord.decode? (.word payload))
    "the success branch must delegate to the existing entry codec unchanged"

end Tests.ContractLanguageResult
end

section
-- leanmerge: from Solcore.Test.ContractTupleEntryProfile
/-! Golden laws for the static Word-tuple entry convention. The expected return
data is written out by hand as hexadecimal text: a returned tuple of two, three
or four Words is the concatenation of their 32-byte big-endian encodings, a
revert carries one Word and a trap its reason. Wrong annotations, arities and
payloads do not decode, a tuple has no one-Word view, and the nested executor
treats a registered tuple contract as unavailable to a word call and a template
with a tuple initializer as unavailable to creation, while a tuple root
returns its whole tuple. -/

set_option autoImplicit false

namespace Tests.ContractTupleEntryProfile

open Solcore.Core
open Solcore.ContractRuntime
open Tests.OneLevelNestedExecutionFixture

/-! Kernel-checked recognition and typing facts. -/

example : (CoreContractEntryProfile.wordTupleOutcomeV1 0).resultType =
    .sum (.product .word .word) (.sum .word .word) := rfl

example : (CoreContractEntryProfile.wordTupleOutcomeV1 2).resultType =
    .sum (.product .word (.product .word (.product .word .word))) (.sum .word .word) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.product .word (.product .word .word)) (.sum .word .word)) =
      some (.wordTupleOutcomeV1 1) := rfl

example : CoreContractEntryProfile.ofResultType? (.sum .word (.sum .word .word)) =
    some .wordOutcomeV1 := rfl

example : CoreContractEntryProfile.ofResultType? (.sum (.product .word .bool) (.sum .word .word)) =
    none := rfl

example : CoreContractEntryProfile.ofResultType? (.sum (.product (.product .word .word) .word)
    (.sum .word .word)) = none := rfl

example : CoreContractEntryProfile.ofResultType? (.product .word .word) = none := rfl

example : (CoreContractEntryProfile.wordTupleOutcomeV1 1).returnsOneWord = false := rfl

example (extraWords : Nat) :
    CoreContractEntryProfile.ofResultType?
        (CoreContractEntryProfile.wordTupleOutcomeV1 extraWords).resultType =
      some (.wordTupleOutcomeV1 extraWords) :=
  CoreContractEntryProfile.ofResultType?_resultType _

example (left right : Nat) (equal :
    (CoreContractEntryProfile.wordTupleOutcomeV1 left).resultType =
      (CoreContractEntryProfile.wordTupleOutcomeV1 right).resultType) : left = right := by
  have profiles := CoreContractEntryProfile.resultType_injective equal
  cases profiles
  rfl

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- One Word's 64 hexadecimal digits, written as the digits after a run of zeros. -/
private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def tupleValue : List Word → Value
  | [] => .unit
  | [last] => .word last
  | head :: rest => .pair (.word head) (tupleValue rest)

private def returned (extraWords : Nat) (words : List Word) :
    Option (FrameOutcome Word) :=
  CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 extraWords)
    (.inLeft (.sum .word .word) (tupleValue words))

private def returnedText (outcome : Option (FrameOutcome Word)) : Option String :=
  match outcome with
  | some (.returned bytes) => some (encodeBytesText bytes)
  | _ => none

/-- A registered child whose convention returns two Words, after writing the
child slot. -/
def tupleChildProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 0).resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word childSlot) (.word childNewValue)))
      (.inLeft (.sum .word .word) (.pair (.word childPayload) (.word childNewValue)))
}

theorem tupleChildProgram_checked : tupleChildProgram.checkHost = true := by
  decide

def tupleChildContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1
    ⟨tupleChildProgram, tupleChildProgram_checked⟩ 0 rfl

/-- A creation template whose initializer returns two Words. -/
def tupleInitializerProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 0).resultType
  body := .inLeft (.sum .word .word)
    (.pair (.word Adr0148CheckedCreationPreflightFixture.initializerPayload)
      (.word Adr0148CheckedCreationPreflightFixture.initializerPayload))
}

theorem tupleInitializerProgram_checked : tupleInitializerProgram.checkHost = true := by
  decide

def tupleInitializer : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1
    ⟨tupleInitializerProgram, tupleInitializerProgram_checked⟩ 0 rfl

/-- The preflight fixture's environment with the tuple initializer in its template. -/
def tupleTemplateEnvironment : ExecutionEnvironment := {
  callRegistry := Adr0148CheckedCreationPreflightFixture.validCallRegistry
  creationTemplates := {
    lookup := fun identifier =>
      if identifier = Adr0148CheckedCreationPreflightFixture.templateId then
        some { initializer := tupleInitializer, runtime := Adr0148CheckedCreationPreflightFixture.runtime }
      else none }
  creationAddressPolicy := Adr0148CheckedCreationPreflightFixture.addressPolicy
}

private def completionFuel : Nat := 512

/-- The creating root's outcome, and the working creator nonce and created
account when it halts. -/
private def creationAt (environment : ExecutionEnvironment) :
    Option (FrameHaltKind × FrameOutcome Word × Option Word × Bool) :=
  match (OneLevelNestedExecution.runWithEnvironment Adr0148NestedCreationLifecycleFixture.rootContract
      Adr0148NestedCreationLifecycleFixture.rootInvocation Adr0148NestedCreationLifecycleFixture.rootInstalled
      environment completionFuel).view with
  | .completed terminal =>
      let working := terminal.terminalContext.context.values.working.1
      some (terminal.outcome.kind, terminal.outcome,
        working.nonce? Adr0148CheckedCreationPreflightFixture.creator,
        (working.account? Adr0148CheckedCreationPreflightFixture.created).isSome)
  | .outOfFuel _ _ _ => none

private def childAt {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : OneLevelNestedExecution.Result initialWorld root invocation) :
    Option (FrameOutcome Word × Option Word × Option Word) :=
  match result.view with
  | .completed terminal =>
      some (terminal.outcome, childStorageValue? terminal.terminalContext.context.values.working.1,
        childStorageValue? terminal.finalWorld)
  | .outOfFuel _ _ _ => none

def testContractTupleEntryProfile : IO Unit := do
  -- Returned tuples of two, three and four Words, including both extremes.
  ensure (returnedText (returned 0 [w 1, w 2]) ==
      some ("0x" ++ hexWord "1" ++ hexWord "2"))
    "a returned pair differs from its two concatenated Words"
  ensure (returnedText (returned 1 [w 0, w (2 ^ 255), w (2 ^ 256 - 1)]) ==
      some ("0x" ++ hexWord "" ++ hexWord ("8" ++ String.ofList (List.replicate 63 '0')) ++
        String.ofList (List.replicate 64 'f')))
    "a returned triple differs from its three concatenated Words"
  ensure (returnedText (returned 2 [w 0x11, w 0x2222, w 0x333333, w 0x44444444]) ==
      some ("0x" ++ hexWord "11" ++ hexWord "2222" ++ hexWord "333333" ++ hexWord "44444444"))
    "a returned quadruple differs from its four concatenated Words"
  -- The decoded size is exactly 32 bytes per Word.
  for (extraWords, words) in [(0, [w 5, w 6]), (1, [w 5, w 6, w 7]), (2, [w 5, w 6, w 7, w 8])] do
    match returned extraWords words with
    | some (.returned bytes) => ensure (bytes.size == 32 * (extraWords + 2)) "a tuple has the wrong size"
    | _ => throw (IO.userError "a well-typed tuple did not decode")
  -- Revert and trap carry one Word, under the exact tuple annotation.
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 1)
      (.inRight (.product .word (.product .word .word)) (.inLeft .word (.word (w 0x99)))) ==
        some (.reverted (encodeWordBytesBE (w 0x99))))
    "a tuple revert differs from its one Word"
  ensure ((match CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 1)
      (.inRight (.product .word (.product .word .word)) (.inLeft .word (.word (w 0x99)))) with
    | some (.reverted bytes) => some (encodeBytesText bytes)
    | _ => none) == some ("0x" ++ hexWord "99"))
    "a tuple revert's bytes differ"
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 2)
      (.inRight (.product .word (.product .word (.product .word .word)))
        (.inRight .word (.word (w 7)))) == some (.trapped (w 7)))
    "a tuple trap differs from its reason"
  -- A wrong annotation, arity or payload does not decode.
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 1)
      (.inRight .word (.inLeft .word (.word (w 1))))).isNone
    "a revert with another annotation decoded"
  ensure (returned 0 [w 1, w 2, w 3]).isNone "a triple decoded as a pair"
  ensure (returned 1 [w 1, w 2]).isNone "a pair decoded as a triple"
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 0)
      (.inLeft (.sum .word .word) (.pair (.word (w 1)) (.bool true)))).isNone
    "a pair with a Boolean decoded"
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 0)
      (.inLeft (.sum .word .bool) (tupleValue [w 1, w 2]))).isNone
    "a return with another annotation decoded"
  -- One-Word conventions are unchanged, and a tuple has no one-Word view.
  ensure (CoreContractEntryProfile.decode? .wordOutcomeV1
      (.inLeft (.sum .word .word) (.word (w 3))) == some (.returned (encodeWordBytesBE (w 3))))
    "the one-Word outcome convention changed"
  ensure (CoreContractEntryProfile.decodeWordOutcome? (.wordTupleOutcomeV1 0)
      (.inLeft (.sum .word .word) (tupleValue [w 1, w 2]))).isNone
    "a tuple has a one-Word view"
  ensure (CoreContractEntryProfile.wordOutcomeV1.returnsOneWord &&
      CoreContractEntryProfile.returnWord.returnsOneWord &&
      !(CoreContractEntryProfile.wordTupleOutcomeV1 0).returnsOneWord)
    "the one-Word predicate changed"
  -- Admission recognizes the tuple contract's exact convention.
  ensure ((CheckedCoreContract.ofCode? tupleChildContract.code).map (·.entryProfile) ==
      some (.wordTupleOutcomeV1 0))
    "admission does not recognize the tuple convention"
  -- A word call to a registered tuple contract is unavailable: the child never
  -- runs, its slot keeps the old value, and the root traps with the failure.
  ensure (childAt (runScenario (rootContract .commit childTargetWord) tupleChildContract completionFuel) ==
      some (.trapped ContractCallFailure.unavailable.code, some childOldValue, some childOldValue))
    "a word call reached a tuple contract"
  -- Creation from a template with a tuple initializer is unavailable before
  -- the creator's nonce advances; the one-Word initializer still deploys.
  ensure (creationAt tupleTemplateEnvironment ==
      some (.trapped, .trapped ContractCallFailure.unavailable.code,
        some Adr0148CheckedCreationPreflightFixture.oldNonce, false))
    "creation started a tuple initializer"
  ensure ((creationAt Adr0148CheckedCreationPreflightFixture.validEnvironment).map
      (fun (kind, _, nonce, present) => (kind, nonce, present)) ==
      some (.returned, some Adr0148CheckedCreationPreflightFixture.nextNonce, true))
    "the one-Word initializer no longer deploys"
  -- A tuple root returns its whole tuple through the nested executor.
  ensure (childAt (runScenario tupleChildContract childReturnContract completionFuel) ==
      some (.returned (encodeWordBytesBE childPayload ++ encodeWordBytesBE childNewValue),
        some childOldValue, some childOldValue))
    "a tuple root did not return its whole tuple"

end Tests.ContractTupleEntryProfile
end
