import Solcore.ContractRuntime.CheckedCoreWordOutcome
import Solcore.Test.Adr0148NestedCreationLifecycleFixture
import Solcore.Test.OneLevelNestedExecutionFixture

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
