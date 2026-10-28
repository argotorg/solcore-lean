import Solcore.ContractRuntime.CheckedCoreWordOutcome
import Solcore.Test.Adr0148NestedCreationLifecycleFixture
import Solcore.Test.OneLevelNestedExecutionFixture

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
