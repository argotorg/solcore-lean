import Solcore.Core.HostSafety
import Solcore.ContractRuntime.FrameOutcome
import Solcore.ContractRuntime.RuntimeScalars

/-! Typed completion conventions for syntax-independent checked Core contracts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Initial checked-Core entry conventions understood by the top-level runner. -/
inductive CoreContractEntryProfile where
  | returnWord
  | wordOutcomeV1
  /-- A returned static tuple of `extraWords + 2` Words, or a reverted Word, or
  a trap reason. -/
  | wordTupleOutcomeV1 (extraWords : Nat)
  /-- A returned `bytes` value of at most 64 bytes, or a reverted Word, or a
  trap reason. -/
  | boundedBytesOutcomeV1
  deriving Repr, BEq, DecidableEq

namespace CoreContractEntryProfile

/-- The right-nested product of `count + 1` Words. -/
def wordTupleType : Nat → Core.Ty
  | 0 => .word
  | count + 1 => .product .word (wordTupleType count)

/-- Recognize a right-nested product of Words, returning one less than its
Word count. -/
def ofWordTupleType? : Core.Ty → Option Nat
  | .word => some 0
  | .product .word rest => (ofWordTupleType? rest).map (· + 1)
  | _ => none

@[simp] theorem ofWordTupleType?_wordTupleType (count : Nat) :
    ofWordTupleType? (wordTupleType count) = some count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [wordTupleType, ofWordTupleType?, ih]

@[simp] theorem wordTupleType_inj {left right : Nat} :
    wordTupleType left = wordTupleType right ↔ left = right := by
  constructor
  · intro equal
    simpa using congrArg ofWordTupleType? equal
  · intro equal
    rw [equal]

/-- The longest returned `bytes` value of the bounded convention: two Words. -/
def boundedBytesLimit : Nat := 64

/-- The returned side of the bounded `bytes` convention: the empty value, or a
length tag and two data Words. -/
def boundedBytesType : Core.Ty := .sum .unit (.product .word (.product .word .word))

/-- The length a non-empty value's tag names, `tag mod 64 + 1`: every Word
names one of the lengths 1 to 64. -/
def boundedBytesLength (tag : Core.Word) : Nat := tag.val % boundedBytesLimit + 1

/-- std's ABI encoding of one returned `bytes` value made of the first `length`
bytes of `data`: the offset Word 32, the length Word, those bytes, then zero
bytes up to a whole number of Words. -/
def encodeBoundedBytes (length : Nat) (data : Bytes) : Bytes :=
  encodeWordBytesBE (Core.Word.ofNatModulo 32) ++ encodeWordBytesBE (Core.Word.ofNatModulo length) ++
    data.extract 0 length ++ ⟨Array.replicate ((32 - length % 32) % 32) 0⟩

/-- The Core result type required by one entry convention. -/
def resultType : CoreContractEntryProfile → Core.Ty
  | .returnWord => .word
  | .wordOutcomeV1 => .sum .word (.sum .word .word)
  | .wordTupleOutcomeV1 extraWords =>
      .sum (wordTupleType (extraWords + 1)) (.sum .word .word)
  | .boundedBytesOutcomeV1 => .sum boundedBytesType (.sum .word .word)

/-- Recognize exactly the result types supported by the contract ABI. -/
def ofResultType? : Core.Ty → Option CoreContractEntryProfile
  | .word => some .returnWord
  | .sum returned (.sum .word .word) =>
      match ofWordTupleType? returned with
      | some 0 => some .wordOutcomeV1
      | some (extraWords + 1) => some (.wordTupleOutcomeV1 extraWords)
      | none => if returned = boundedBytesType then some .boundedBytesOutcomeV1 else none
  | _ => none

/--
Whether every completion of the convention carries exactly one Word. Nested
word calls and creation initializers require it.
-/
def returnsOneWord : CoreContractEntryProfile → Bool
  | .returnWord => true
  | .wordOutcomeV1 => true
  | .wordTupleOutcomeV1 _ => false
  | .boundedBytesOutcomeV1 => false

/-- The concatenated big-endian Words of a right-nested tuple of `count + 1`
Words: the static ABI encoding of the tuple. -/
def decodeWordTuple? : Nat → Core.Value → Option Bytes
  | 0, .word word => some (encodeWordBytesBE word)
  | count + 1, .pair (.word word) rest =>
      (decodeWordTuple? count rest).map (encodeWordBytesBE word ++ ·)
  | _, _ => none

/-- The returned bytes of the bounded convention: the empty value, or the first
`boundedBytesLength tag` bytes of two big-endian data Words. Both carry std's
canonical encoding, so the data bytes after the length are zeroed. -/
def decodeBoundedBytes? : Core.Value → Option Bytes
  | .inLeft (.product .word (.product .word .word)) .unit =>
      some (encodeBoundedBytes 0 ByteArray.empty)
  | .inRight .unit (.pair (.word tag) (.pair (.word first) (.word second))) =>
      some (encodeBoundedBytes (boundedBytesLength tag)
        (encodeWordBytesBE first ++ encodeWordBytesBE second))
  | _ => none

/-- Decode one runtime value according to its contract-owned entry convention. -/
def decode?
    (profile : CoreContractEntryProfile)
    (value : Core.Value) : Option (FrameOutcome Core.Word) :=
  match profile, value with
  | .returnWord, .word word =>
      some (.returned (encodeWordBytesBE word))
  | .wordOutcomeV1, .inLeft (.sum .word .word) (.word word) =>
      some (.returned (encodeWordBytesBE word))
  | .wordOutcomeV1, .inRight .word (.inLeft .word (.word word)) =>
      some (.reverted (encodeWordBytesBE word))
  | .wordOutcomeV1, .inRight .word (.inRight .word (.word reason)) =>
      some (.trapped reason)
  | .wordTupleOutcomeV1 extraWords, .inLeft (.sum .word .word) tuple =>
      (decodeWordTuple? (extraWords + 1) tuple).map .returned
  | .wordTupleOutcomeV1 extraWords,
      .inRight returned (.inLeft .word (.word word)) =>
      if returned = wordTupleType (extraWords + 1) then
        some (.reverted (encodeWordBytesBE word))
      else none
  | .wordTupleOutcomeV1 extraWords,
      .inRight returned (.inRight .word (.word reason)) =>
      if returned = wordTupleType (extraWords + 1) then
        some (.trapped reason)
      else none
  | .boundedBytesOutcomeV1, .inLeft (.sum .word .word) payload =>
      (decodeBoundedBytes? payload).map .returned
  | .boundedBytesOutcomeV1, .inRight returned (.inLeft .word (.word word)) =>
      if returned = boundedBytesType then
        some (.reverted (encodeWordBytesBE word))
      else none
  | .boundedBytesOutcomeV1, .inRight returned (.inRight .word (.word reason)) =>
      if returned = boundedBytesType then
        some (.trapped reason)
      else none
  | _, _ => none

/-- A host-runtime value of a Word tuple's type always decodes. -/
theorem decodeWordTuple?_ne_none_of_hasType
    (count : Nat)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value (wordTupleType count) definitions) :
    decodeWordTuple? count value ≠ none := by
  induction count generalizing value with
  | zero =>
      change Core.HostRuntimeValueHasType world value .word definitions at typing
      cases typing with
      | word => simp [decodeWordTuple?]
  | succ count ih =>
      change Core.HostRuntimeValueHasType world value
        (.product .word (wordTupleType count)) definitions at typing
      cases typing with
      | pair leftTyping restTyping =>
          cases leftTyping with
          | word =>
              have rest := ih restTyping
              simp only [decodeWordTuple?, ne_eq, Option.map_eq_none_iff]
              exact rest

/-- A host-runtime value of the profile's result type always decodes. -/
theorem decode?_ne_none_of_hasType
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    profile.decode? value ≠ none := by
  cases profile with
  | returnWord =>
      cases typing with
      | word => simp [decode?]
  | wordOutcomeV1 =>
      cases typing with
      | inLeft payloadTyping =>
          cases payloadTyping with
          | word => simp [decode?]
      | inRight payloadTyping =>
          cases payloadTyping with
          | inLeft innerTyping =>
              cases innerTyping with
              | word => simp [decode?]
          | inRight innerTyping =>
              cases innerTyping with
              | word => simp [decode?]
  | wordTupleOutcomeV1 extraWords =>
      cases typing with
      | inLeft payloadTyping =>
          have tuple :=
            decodeWordTuple?_ne_none_of_hasType (extraWords + 1) payloadTyping
          simp only [decode?, ne_eq, Option.map_eq_none_iff]
          exact tuple
      | inRight payloadTyping =>
          cases payloadTyping with
          | inLeft innerTyping =>
              cases innerTyping with
              | word => simp [decode?]
          | inRight innerTyping =>
              cases innerTyping with
              | word => simp [decode?]
  | boundedBytesOutcomeV1 =>
      cases typing with
      | inLeft payloadTyping =>
          cases payloadTyping with
          | inLeft emptyTyping =>
              cases emptyTyping
              simp [decode?, decodeBoundedBytes?]
          | inRight dataTyping =>
              cases dataTyping with
              | pair tagTyping wordsTyping =>
                  cases tagTyping
                  cases wordsTyping with
                  | pair firstTyping secondTyping =>
                      cases firstTyping
                      cases secondTyping
                      simp [decode?, decodeBoundedBytes?]
      | inRight payloadTyping =>
          cases payloadTyping with
          | inLeft innerTyping =>
              cases innerTyping with
              | word => simp [decode?]
          | inRight innerTyping =>
              cases innerTyping with
              | word => simp [decode?]

/-- The typed decoder's executable option is always populated. -/
theorem decode?_isSome_of_hasType
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    (profile.decode? value).isSome = true :=
  Option.isSome_iff_ne_none.mpr
    (profile.decode?_ne_none_of_hasType typing)

/-- Decode a well-typed completion without an invalid-value fallback branch. -/
def decodeTyped
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    FrameOutcome Core.Word :=
  (profile.decode? value).get
    (profile.decode?_isSome_of_hasType typing)

end CoreContractEntryProfile

end Solcore.ContractRuntime
