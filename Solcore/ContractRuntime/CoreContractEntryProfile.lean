import Solcore.Core.HostSafety
import Solcore.ContractRuntime.FrameOutcome
import Solcore.ContractRuntime.RuntimeScalars

/-! Typed completion conventions for syntax-independent checked Core contracts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- The fields of one constructor of a returned enum. -/
inductive EnumPayload where
  | noWords
  | oneWord
  | twoWords
  /-- One `bytes` value of at most 64 bytes. -/
  | boundedBytes
  deriving Repr, BEq, DecidableEq

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
  /-- A returned value of an enum whose constructors, in declaration order,
  have the fields `first`, `second`, then `rest`, or a reverted Word, or a
  trap reason. Each constructor's value carries its own tag Word. -/
  | enumOutcomeV1 (first second : EnumPayload) (rest : List EnumPayload)
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

/-- A constructor's value: its tag Word paired with its fields, which are unit,
one Word, two Words or a bounded `bytes` value. -/
def enumPayloadType : EnumPayload → Core.Ty
  | .noWords => .product .word .unit
  | .oneWord => .product .word .word
  | .twoWords => .product .word (.product .word .word)
  | .boundedBytes => .product .word boundedBytesType

/-- Recognize exactly the four constructor types. -/
def ofEnumPayloadType? (type : Core.Ty) : Option EnumPayload :=
  if type = enumPayloadType .noWords then some .noWords
  else if type = enumPayloadType .oneWord then some .oneWord
  else if type = enumPayloadType .twoWords then some .twoWords
  else if type = enumPayloadType .boundedBytes then some .boundedBytes
  else none

@[simp] theorem ofEnumPayloadType?_enumPayloadType (payload : EnumPayload) :
    ofEnumPayloadType? (enumPayloadType payload) = some payload := by
  cases payload <;> rfl

@[simp] theorem enumPayloadType_inj {payload other : EnumPayload} :
    enumPayloadType payload = enumPayloadType other ↔ payload = other := by
  constructor
  · intro equal
    simpa using congrArg ofEnumPayloadType? equal
  · rintro rfl
    rfl

/-- Every constructor's value is a product, never the unit of an empty `bytes`
value. -/
@[simp] theorem enumPayloadType_ne_unit (payload : EnumPayload) :
    enumPayloadType payload ≠ .unit := by
  cases payload <;> simp [enumPayloadType]

@[simp] theorem unit_ne_enumPayloadType (payload : EnumPayload) :
    Core.Ty.unit ≠ enumPayloadType payload :=
  (enumPayloadType_ne_unit payload).symm

/-- The right-nested sum of an enum's constructor values, in declaration order. -/
def enumType (first : EnumPayload) : List EnumPayload → Core.Ty
  | [] => enumPayloadType first
  | next :: rest => .sum (enumPayloadType first) (enumType next rest)

/-- Recognize a right-nested sum of constructor types as its first fields and
the remaining ones; a lone constructor type has none remaining. -/
def ofEnumType? : Core.Ty → Option (EnumPayload × List EnumPayload)
  | .sum left right => do
      let first ← ofEnumPayloadType? left
      let (next, rest) ← ofEnumType? right
      return (first, next :: rest)
  | type => (ofEnumPayloadType? type).map (·, [])

@[simp] theorem ofEnumType?_enumType (first : EnumPayload) (rest : List EnumPayload) :
    ofEnumType? (enumType first rest) = some (first, rest) := by
  induction rest generalizing first with
  | nil => cases first <;> rfl
  | cons next rest ih => simp [enumType, ofEnumType?, ih]

@[simp] theorem enumType_inj {first other : EnumPayload} {rest others : List EnumPayload} :
    enumType first rest = enumType other others ↔ first = other ∧ rest = others := by
  constructor
  · intro equal
    simpa using congrArg ofEnumType? equal
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The bytes a constructor's fields take in the head of the enum's body: a
`bytes` value takes its offset Word. -/
def enumPayloadHeadSize : EnumPayload → Nat
  | .noWords => 0
  | .oneWord => 32
  | .twoWords => 64
  | .boundedBytes => 32

/-- The head of an enum's body: the tag Word and the widest constructor's
fields. std reserves it whichever constructor is encoded. -/
def enumBodyHeadSize (payloads : List EnumPayload) : Nat :=
  32 + payloads.foldr (fun payload widest => max (enumPayloadHeadSize payload) widest) 0

/-- An enum is static when no constructor carries `bytes`. -/
def enumIsStatic (payloads : List EnumPayload) : Bool :=
  payloads.all (· != .boundedBytes)

/-- The Core result type required by one entry convention. -/
def resultType : CoreContractEntryProfile → Core.Ty
  | .returnWord => .word
  | .wordOutcomeV1 => .sum .word (.sum .word .word)
  | .wordTupleOutcomeV1 extraWords =>
      .sum (wordTupleType (extraWords + 1)) (.sum .word .word)
  | .boundedBytesOutcomeV1 => .sum boundedBytesType (.sum .word .word)
  | .enumOutcomeV1 first second rest => .sum (enumType first (second :: rest)) (.sum .word .word)

/-- Recognize exactly the result types supported by the contract ABI. -/
def ofResultType? : Core.Ty → Option CoreContractEntryProfile
  | .word => some .returnWord
  | .sum returned (.sum .word .word) =>
      match ofWordTupleType? returned with
      | some 0 => some .wordOutcomeV1
      | some (extraWords + 1) => some (.wordTupleOutcomeV1 extraWords)
      | none =>
          if returned = boundedBytesType then some .boundedBytesOutcomeV1
          else match ofEnumType? returned with
            | some (first, second :: rest) => some (.enumOutcomeV1 first second rest)
            | _ => none
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
  | .enumOutcomeV1 _ _ _ => false

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

/-- std's encoding of a `bytes` value after its offset: the length Word, the
first `length` bytes of `data`, then zero bytes up to a whole number of Words. -/
def encodeBytesTail (length : Nat) (data : Bytes) : Bytes :=
  encodeWordBytesBE (Core.Word.ofNatModulo length) ++ data.extract 0 length ++
    ⟨Array.replicate ((32 - length % 32) % 32) 0⟩

/-- A bounded `bytes` value's length and its two data Words, read exactly as
`decodeBoundedBytes?` reads them. -/
def boundedBytesValue? : Core.Value → Option (Nat × Bytes)
  | .inLeft (.product .word (.product .word .word)) .unit => some (0, ByteArray.empty)
  | .inRight .unit (.pair (.word tag) (.pair (.word first) (.word second))) =>
      some (boundedBytesLength tag, encodeWordBytesBE first ++ encodeWordBytesBE second)
  | _ => none

/-- One constructor value's tag Word, its fields' head and their tail. A
`bytes` field's head is its offset `bodyHead` from the start of the body, and
its tail is the encoded value. -/
def decodeEnumFields? (bodyHead : Nat) :
    EnumPayload → Core.Value → Option (Core.Word × Bytes × Bytes)
  | .noWords, .pair (.word tag) .unit => some (tag, ByteArray.empty, ByteArray.empty)
  | .oneWord, .pair (.word tag) (.word value) =>
      some (tag, encodeWordBytesBE value, ByteArray.empty)
  | .twoWords, .pair (.word tag) (.pair (.word first) (.word second)) =>
      some (tag, encodeWordBytesBE first ++ encodeWordBytesBE second, ByteArray.empty)
  | .boundedBytes, .pair (.word tag) value =>
      (boundedBytesValue? value).map fun (length, data) =>
        (tag, encodeWordBytesBE (Core.Word.ofNatModulo bodyHead), encodeBytesTail length data)
  | _, _ => none

/-- The constructor a right-nested enum value injects, and that constructor's
value. Every injection's annotation must be the exact remaining type. -/
def selectEnumVariant? (first : EnumPayload) :
    List EnumPayload → Core.Value → Option (EnumPayload × Core.Value)
  | [], value => some (first, value)
  | next :: rest, .inLeft right value =>
      if right = enumType next rest then some (first, value) else none
  | next :: rest, .inRight left value =>
      if left = enumPayloadType first then selectEnumVariant? next rest value else none
  | _ :: _, _ => none

/-- std's encoding of one returned enum value. The body is the tag Word, the
fields' head, zero bytes up to the body's head, then a `bytes` field's tail. A
static enum is its body inline; a dynamic one is the offset Word 32, then the
body. -/
def decodeEnum? (first : EnumPayload) (rest : List EnumPayload) (value : Core.Value) :
    Option Bytes := do
  let (payload, constructed) ← selectEnumVariant? first rest value
  let bodyHead := enumBodyHeadSize (first :: rest)
  let (tag, head, tail) ← decodeEnumFields? bodyHead payload constructed
  let body := encodeWordBytesBE tag ++ head ++
    ⟨Array.replicate (bodyHead - 32 - enumPayloadHeadSize payload) 0⟩ ++ tail
  return if enumIsStatic (first :: rest) then body
    else encodeWordBytesBE (Core.Word.ofNatModulo 32) ++ body

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
  | .enumOutcomeV1 first second rest, .inLeft (.sum .word .word) payload =>
      (decodeEnum? first (second :: rest) payload).map .returned
  | .enumOutcomeV1 first second rest, .inRight returned (.inLeft .word (.word word)) =>
      if returned = enumType first (second :: rest) then
        some (.reverted (encodeWordBytesBE word))
      else none
  | .enumOutcomeV1 first second rest, .inRight returned (.inRight .word (.word reason)) =>
      if returned = enumType first (second :: rest) then
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

/-- A host-runtime value of the bounded `bytes` type always has a length and data. -/
theorem boundedBytesValue?_ne_none_of_hasType
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing : Core.HostRuntimeValueHasType world value boundedBytesType definitions) :
    boundedBytesValue? value ≠ none := by
  cases typing with
  | inLeft emptyTyping =>
      cases emptyTyping
      simp [boundedBytesValue?]
  | inRight dataTyping =>
      cases dataTyping with
      | pair tagTyping wordsTyping =>
          cases tagTyping
          cases wordsTyping with
          | pair firstTyping secondTyping =>
              cases firstTyping
              cases secondTyping
              simp [boundedBytesValue?]

/-- A host-runtime value of a constructor's type always has its fields. -/
theorem decodeEnumFields?_ne_none_of_hasType
    (bodyHead : Nat) (payload : EnumPayload)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing : Core.HostRuntimeValueHasType world value (enumPayloadType payload) definitions) :
    decodeEnumFields? bodyHead payload value ≠ none := by
  cases payload with
  | noWords =>
      cases typing with
      | pair tagTyping unitTyping =>
          cases tagTyping
          cases unitTyping
          simp [decodeEnumFields?]
  | oneWord =>
      cases typing with
      | pair tagTyping wordTyping =>
          cases tagTyping
          cases wordTyping
          simp [decodeEnumFields?]
  | twoWords =>
      cases typing with
      | pair tagTyping wordsTyping =>
          cases tagTyping
          cases wordsTyping with
          | pair firstTyping secondTyping =>
              cases firstTyping
              cases secondTyping
              simp [decodeEnumFields?]
  | boundedBytes =>
      cases typing with
      | pair tagTyping bytesTyping =>
          cases tagTyping
          have bytes := boundedBytesValue?_ne_none_of_hasType bytesTyping
          simp only [decodeEnumFields?, ne_eq, Option.map_eq_none_iff]
          exact bytes

/-- A host-runtime value of an enum's type injects one constructor, whose value
has that constructor's type. -/
theorem selectEnumVariant?_of_hasType
    (first : EnumPayload) (rest : List EnumPayload)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing : Core.HostRuntimeValueHasType world value (enumType first rest) definitions) :
    ∃ payload constructed, selectEnumVariant? first rest value = some (payload, constructed) ∧
      Core.HostRuntimeValueHasType world constructed (enumPayloadType payload) definitions := by
  induction rest generalizing first value with
  | nil => exact ⟨first, value, rfl, typing⟩
  | cons next rest ih =>
      cases typing with
      | inLeft payloadTyping =>
          exact ⟨first, _, by simp [selectEnumVariant?], payloadTyping⟩
      | inRight restTyping =>
          obtain ⟨payload, constructed, selected, typed⟩ := ih next restTyping
          exact ⟨payload, constructed, by simp [selectEnumVariant?, selected], typed⟩

/-- A host-runtime value of an enum's type always decodes. -/
theorem decodeEnum?_ne_none_of_hasType
    (first : EnumPayload) (rest : List EnumPayload)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing : Core.HostRuntimeValueHasType world value (enumType first rest) definitions) :
    decodeEnum? first rest value ≠ none := by
  obtain ⟨payload, constructed, selected, typed⟩ := selectEnumVariant?_of_hasType first rest typing
  have fields := decodeEnumFields?_ne_none_of_hasType (enumBodyHeadSize (first :: rest)) payload typed
  cases decoded : decodeEnumFields? (enumBodyHeadSize (first :: rest)) payload constructed with
  | none => exact absurd decoded fields
  | some triple =>
      obtain ⟨tag, head, tail⟩ := triple
      simp [decodeEnum?, selected, decoded]

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
  | enumOutcomeV1 first second rest =>
      cases typing with
      | inLeft payloadTyping =>
          have decoded := decodeEnum?_ne_none_of_hasType first (second :: rest) payloadTyping
          simp only [decode?, ne_eq, Option.map_eq_none_iff]
          exact decoded
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
