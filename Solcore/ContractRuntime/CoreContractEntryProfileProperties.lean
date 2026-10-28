import Solcore.ContractRuntime.CheckedCoreContract

/-! Exact recognition and decoding laws for checked Core contract entries. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace CoreContractEntryProfile

@[simp] theorem ofResultType?_resultType
    (profile : CoreContractEntryProfile) :
    ofResultType? profile.resultType = some profile := by
  cases profile with
  | returnWord => rfl
  | wordOutcomeV1 => rfl
  | wordTupleOutcomeV1 extraWords =>
      simp [resultType, ofResultType?]
  | boundedBytesOutcomeV1 => rfl
  | enumOutcomeV1 first second rest =>
      simp [resultType, ofResultType?, enumType, ofWordTupleType?, ofEnumType?, boundedBytesType]

theorem resultType_injective :
    Function.Injective CoreContractEntryProfile.resultType := by
  intro left right equal
  simpa using congrArg ofResultType? equal

@[simp] theorem decode?_returnWord
    (word : Core.Word) :
    decode? .returnWord (.word word) =
      some (.returned (encodeWordBytesBE word)) := by
  rfl

@[simp] theorem decode?_wordOutcomeV1_returned
    (word : Core.Word) :
    decode? .wordOutcomeV1
        (.inLeft (.sum .word .word) (.word word)) =
      some (.returned (encodeWordBytesBE word)) := by
  rfl

@[simp] theorem decode?_wordOutcomeV1_reverted
    (word : Core.Word) :
    decode? .wordOutcomeV1
        (.inRight .word (.inLeft .word (.word word))) =
      some (.reverted (encodeWordBytesBE word)) := by
  rfl

@[simp] theorem decode?_wordOutcomeV1_trapped
    (reason : Core.Word) :
    decode? .wordOutcomeV1
        (.inRight .word (.inRight .word (.word reason))) =
      some (.trapped reason) := by
  rfl

@[simp] theorem decodeWordTuple?_zero (word : Core.Word) :
    decodeWordTuple? 0 (.word word) = some (encodeWordBytesBE word) :=
  rfl

@[simp] theorem decodeWordTuple?_succ
    (count : Nat) (word : Core.Word) (rest : Core.Value) :
    decodeWordTuple? (count + 1) (.pair (.word word) rest) =
      (decodeWordTuple? count rest).map (encodeWordBytesBE word ++ ·) :=
  rfl

/-- A decoded tuple of `count + 1` Words has exactly `32 (count + 1)` bytes. -/
theorem decodeWordTuple?_size
    {count : Nat} {value : Core.Value} {bytes : Bytes}
    (decoded : decodeWordTuple? count value = some bytes) :
    bytes.size = 32 * (count + 1) := by
  induction count generalizing value bytes with
  | zero =>
      match value, decoded with
      | .word word, decoded =>
          cases decoded
          simp
  | succ count ih =>
      match value, decoded with
      | .pair (.word word) rest, decoded =>
          simp only [decodeWordTuple?_succ] at decoded
          cases restEq : decodeWordTuple? count rest with
          | none => simp [restEq] at decoded
          | some restBytes =>
              simp only [restEq, Option.map_some, Option.some.injEq] at decoded
              cases decoded
              simp [ByteArray.size_append, ih restEq]
              omega

@[simp] theorem decode?_wordTupleOutcomeV1_returned
    (extraWords : Nat) (tuple : Core.Value) :
    decode? (.wordTupleOutcomeV1 extraWords)
        (.inLeft (.sum .word .word) tuple) =
      (decodeWordTuple? (extraWords + 1) tuple).map .returned := by
  rfl

@[simp] theorem decode?_wordTupleOutcomeV1_reverted
    (extraWords : Nat) (word : Core.Word) :
    decode? (.wordTupleOutcomeV1 extraWords)
        (.inRight (wordTupleType (extraWords + 1)) (.inLeft .word (.word word))) =
      some (.reverted (encodeWordBytesBE word)) := by
  simp [decode?]

@[simp] theorem decode?_wordTupleOutcomeV1_trapped
    (extraWords : Nat) (reason : Core.Word) :
    decode? (.wordTupleOutcomeV1 extraWords)
        (.inRight (wordTupleType (extraWords + 1)) (.inRight .word (.word reason))) =
      some (.trapped reason) := by
  simp [decode?]

/-- Every tag names a length from 1 to 64. -/
theorem boundedBytesLength_pos (tag : Core.Word) : 0 < boundedBytesLength tag := by
  simp [boundedBytesLength]

theorem boundedBytesLength_le (tag : Core.Word) :
    boundedBytesLength tag ≤ boundedBytesLimit := by
  have bound := Nat.mod_lt tag.val (show 0 < boundedBytesLimit by decide)
  simp only [boundedBytesLength]
  omega

/-- The tag `length - 1` names each length from 1 to 64. -/
theorem boundedBytesLength_ofNatModulo
    {length : Nat} (positive : 0 < length) (bounded : length ≤ boundedBytesLimit) :
    boundedBytesLength (Core.Word.ofNatModulo (length - 1)) = length := by
  have small : length - 1 < Core.wordModulus := by
    simp only [boundedBytesLimit] at bounded
    simp only [Core.wordModulus]
    omega
  simp only [boundedBytesLength, Core.Word.ofNatModulo, Nat.mod_eq_of_lt small]
  simp only [boundedBytesLimit] at bounded ⊢
  omega

/-- The encoding has the two head Words and the data padded to whole Words. -/
theorem encodeBoundedBytes_size
    (length : Nat) (data : Bytes) (fits : length ≤ data.size) :
    (encodeBoundedBytes length data).size = 64 + 32 * ((length + 31) / 32) := by
  have padding : (⟨Array.replicate ((32 - length % 32) % 32) 0⟩ : ByteArray).size =
      (32 - length % 32) % 32 := by
    simp [ByteArray.size]
  simp only [encodeBoundedBytes, ByteArray.size_append, encodeWordBytesBE_size,
    ByteArray.size_extract, padding]
  omega

@[simp] theorem decodeBoundedBytes?_empty :
    decodeBoundedBytes? (.inLeft (.product .word (.product .word .word)) .unit) =
      some (encodeBoundedBytes 0 ByteArray.empty) :=
  rfl

@[simp] theorem decodeBoundedBytes?_nonEmpty (tag first second : Core.Word) :
    decodeBoundedBytes?
        (.inRight .unit (.pair (.word tag) (.pair (.word first) (.word second)))) =
      some (encodeBoundedBytes (boundedBytesLength tag)
        (encodeWordBytesBE first ++ encodeWordBytesBE second)) :=
  rfl

/-- A decoded value has the two head Words and at most two data Words. -/
theorem decodeBoundedBytes?_size
    {value : Core.Value} {bytes : Bytes}
    (decoded : decodeBoundedBytes? value = some bytes) :
    ∃ length, length ≤ boundedBytesLimit ∧
      bytes.size = 64 + 32 * ((length + 31) / 32) := by
  match value, decoded with
  | .inLeft (.product .word (.product .word .word)) .unit, decoded =>
      cases decoded
      exact ⟨0, by decide, encodeBoundedBytes_size 0 _ (by simp)⟩
  | .inRight .unit (.pair (.word tag) (.pair (.word first) (.word second))), decoded =>
      cases decoded
      refine ⟨boundedBytesLength tag, boundedBytesLength_le tag, ?_⟩
      apply encodeBoundedBytes_size
      have bounded := boundedBytesLength_le tag
      simp only [boundedBytesLimit] at bounded
      simp only [ByteArray.size_append, encodeWordBytesBE_size]
      omega

@[simp] theorem decode?_boundedBytesOutcomeV1_returned (payload : Core.Value) :
    decode? .boundedBytesOutcomeV1 (.inLeft (.sum .word .word) payload) =
      (decodeBoundedBytes? payload).map .returned := by
  rfl

@[simp] theorem decode?_boundedBytesOutcomeV1_reverted (word : Core.Word) :
    decode? .boundedBytesOutcomeV1
        (.inRight boundedBytesType (.inLeft .word (.word word))) =
      some (.reverted (encodeWordBytesBE word)) := by
  simp [decode?]

@[simp] theorem decode?_boundedBytesOutcomeV1_trapped (reason : Core.Word) :
    decode? .boundedBytesOutcomeV1
        (.inRight boundedBytesType (.inRight .word (.word reason))) =
      some (.trapped reason) := by
  simp [decode?]

/-- The bounded encoding is the offset Word 32 before std's `bytes` tail. -/
theorem encodeBoundedBytes_eq_encodeBytesTail (length : Nat) (data : Bytes) :
    encodeBoundedBytes length data =
      encodeWordBytesBE (Core.Word.ofNatModulo 32) ++ encodeBytesTail length data := by
  simp only [encodeBoundedBytes, encodeBytesTail, ByteArray.append_assoc]

/-- The tail is the length Word and the data padded to whole Words. -/
theorem encodeBytesTail_size
    (length : Nat) (data : Bytes) (fits : length ≤ data.size) :
    (encodeBytesTail length data).size = 32 + 32 * ((length + 31) / 32) := by
  have padding : (⟨Array.replicate ((32 - length % 32) % 32) 0⟩ : ByteArray).size =
      (32 - length % 32) % 32 := by
    simp [ByteArray.size]
  simp only [encodeBytesTail, ByteArray.size_append, encodeWordBytesBE_size,
    ByteArray.size_extract, padding]
  omega

/-- A bounded `bytes` value has at most 64 bytes of two data Words. -/
theorem boundedBytesValue?_bounds
    {value : Core.Value} {length : Nat} {data : Bytes}
    (decoded : boundedBytesValue? value = some (length, data)) :
    length ≤ boundedBytesLimit ∧ length ≤ data.size := by
  match value, decoded with
  | .inLeft (.product .word (.product .word .word)) .unit, decoded =>
      cases decoded
      exact ⟨by decide, by simp⟩
  | .inRight .unit (.pair (.word tag) (.pair (.word first) (.word second))), decoded =>
      cases decoded
      have bounded := boundedBytesLength_le tag
      refine ⟨bounded, ?_⟩
      simp only [boundedBytesLimit] at bounded
      simp only [ByteArray.size_append, encodeWordBytesBE_size]
      omega

/-- A constructor's fields fill exactly their head, and only a `bytes` field has
a tail, of at most three Words. -/
theorem decodeEnumFields?_size
    {bodyHead : Nat} {payload : EnumPayload} {constructed : Core.Value}
    {tag : Core.Word} {head tail : Bytes}
    (decoded : decodeEnumFields? bodyHead payload constructed = some (tag, head, tail)) :
    head.size = enumPayloadHeadSize payload ∧ ∃ tailWords, tailWords ≤ 3 ∧
      (payload ≠ .boundedBytes → tailWords = 0) ∧ tail.size = 32 * tailWords := by
  match payload, constructed, decoded with
  | .noWords, .pair (.word _) .unit, decoded =>
      cases decoded
      exact ⟨rfl, 0, by decide, fun _ => rfl, rfl⟩
  | .oneWord, .pair (.word _) (.word _), decoded =>
      cases decoded
      exact ⟨encodeWordBytesBE_size _, 0, by decide, fun _ => rfl, rfl⟩
  | .twoWords, .pair (.word _) (.pair (.word _) (.word _)), decoded =>
      cases decoded
      refine ⟨?_, 0, by decide, fun _ => rfl, rfl⟩
      simp [ByteArray.size_append, encodeWordBytesBE_size, enumPayloadHeadSize]
  | .boundedBytes, .pair (.word _) bytes, decoded =>
      simp only [decodeEnumFields?] at decoded
      cases value : boundedBytesValue? bytes with
      | none => simp [value] at decoded
      | some pair =>
          obtain ⟨length, data⟩ := pair
          simp only [value, Option.map_some, Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨_, rfl, rfl⟩ := decoded
          obtain ⟨bounded, fits⟩ := boundedBytesValue?_bounds value
          simp only [boundedBytesLimit] at bounded
          refine ⟨encodeWordBytesBE_size _, 1 + (length + 31) / 32, by omega,
            fun absurd => absurd rfl |>.elim, ?_⟩
          rw [encodeBytesTail_size length data fits]
          omega

/-- The injected constructor is one of the enum's constructors. -/
theorem selectEnumVariant?_mem
    {first : EnumPayload} {rest : List EnumPayload} {value constructed : Core.Value}
    {payload : EnumPayload}
    (selected : selectEnumVariant? first rest value = some (payload, constructed)) :
    payload ∈ first :: rest := by
  induction rest generalizing first value with
  | nil =>
      simp only [selectEnumVariant?, Option.some.injEq, Prod.mk.injEq] at selected
      simp [selected.1]
  | cons next rest ih =>
      match value, selected with
      | .inLeft right value, selected =>
          simp only [selectEnumVariant?] at selected
          split at selected
          · simp only [Option.some.injEq, Prod.mk.injEq] at selected
            simp [selected.1]
          · cases selected
      | .inRight left value, selected =>
          simp only [selectEnumVariant?] at selected
          split at selected
          · exact List.mem_cons_of_mem _ (ih selected)
          · cases selected

/-- Every constructor's fields fit in the body's head after the tag. -/
theorem enumPayloadHeadSize_le
    {payload : EnumPayload} {payloads : List EnumPayload} (member : payload ∈ payloads) :
    enumPayloadHeadSize payload + 32 ≤ enumBodyHeadSize payloads := by
  induction payloads with
  | nil => cases member
  | cons head rest ih =>
      simp only [enumBodyHeadSize, List.foldr_cons] at ih ⊢
      cases member with
      | head => omega
      | tail _ member =>
          have := ih member
          omega

/-- A decoded enum value is the body's head and at most three tail Words, after
the offset Word when the enum is dynamic; a static enum has no tail. -/
theorem decodeEnum?_size
    {first : EnumPayload} {rest : List EnumPayload} {value : Core.Value} {bytes : Bytes}
    (decoded : decodeEnum? first rest value = some bytes) :
    ∃ tailWords, tailWords ≤ 3 ∧ (enumIsStatic (first :: rest) = true → tailWords = 0) ∧
      bytes.size = (if enumIsStatic (first :: rest) then 0 else 32) +
        enumBodyHeadSize (first :: rest) + 32 * tailWords := by
  cases selected : selectEnumVariant? first rest value with
  | none => simp [decodeEnum?, selected] at decoded
  | some pair =>
      obtain ⟨payload, constructed⟩ := pair
      cases fields : decodeEnumFields? (enumBodyHeadSize (first :: rest)) payload constructed with
      | none => simp [decodeEnum?, selected, fields] at decoded
      | some triple =>
          obtain ⟨tag, head, tail⟩ := triple
          simp only [decodeEnum?, selected, fields, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq] at decoded
          have member := selectEnumVariant?_mem selected
          have fits := enumPayloadHeadSize_le member
          obtain ⟨headSize, tailWords, bounded, onlyBytes, tailSize⟩ := decodeEnumFields?_size fields
          have padding : (⟨Array.replicate (enumBodyHeadSize (first :: rest) - 32 -
              enumPayloadHeadSize payload) 0⟩ : ByteArray).size =
              enumBodyHeadSize (first :: rest) - 32 - enumPayloadHeadSize payload := by
            simp [ByteArray.size]
          have staticTail : enumIsStatic (first :: rest) = true → tailWords = 0 := by
            intro static
            apply onlyBytes
            intro isBytes
            subst isBytes
            exact absurd (List.all_eq_true.mp static _ member) (by decide)
          refine ⟨tailWords, bounded, staticTail, ?_⟩
          subst decoded
          split <;>
            simp only [ByteArray.size_append, encodeWordBytesBE_size, headSize, padding,
              tailSize] <;>
            omega

@[simp] theorem decode?_enumOutcomeV1_returned
    (first second : EnumPayload) (rest : List EnumPayload) (payload : Core.Value) :
    decode? (.enumOutcomeV1 first second rest) (.inLeft (.sum .word .word) payload) =
      (decodeEnum? first (second :: rest) payload).map .returned := by
  rfl

@[simp] theorem decode?_enumOutcomeV1_reverted
    (first second : EnumPayload) (rest : List EnumPayload) (word : Core.Word) :
    decode? (.enumOutcomeV1 first second rest)
        (.inRight (enumType first (second :: rest)) (.inLeft .word (.word word))) =
      some (.reverted (encodeWordBytesBE word)) := by
  simp [decode?]

@[simp] theorem decode?_enumOutcomeV1_trapped
    (first second : EnumPayload) (rest : List EnumPayload) (reason : Core.Word) :
    decode? (.enumOutcomeV1 first second rest)
        (.inRight (enumType first (second :: rest)) (.inRight .word (.word reason))) =
      some (.trapped reason) := by
  simp [decode?]

@[simp] theorem returnsOneWord_returnWord :
    returnsOneWord .returnWord = true :=
  rfl

@[simp] theorem returnsOneWord_wordOutcomeV1 :
    returnsOneWord .wordOutcomeV1 = true :=
  rfl

@[simp] theorem returnsOneWord_wordTupleOutcomeV1 (extraWords : Nat) :
    returnsOneWord (.wordTupleOutcomeV1 extraWords) = false :=
  rfl

@[simp] theorem returnsOneWord_boundedBytesOutcomeV1 :
    returnsOneWord .boundedBytesOutcomeV1 = false :=
  rfl

@[simp] theorem returnsOneWord_enumOutcomeV1
    (first second : EnumPayload) (rest : List EnumPayload) :
    returnsOneWord (.enumOutcomeV1 first second rest) = false :=
  rfl

end CoreContractEntryProfile

namespace CheckedCoreContract

theorem ofCode?_of_resultType
    (code : CheckedHostCoreProgram)
    (profile : CoreContractEntryProfile)
    (resultType_eq : code.program.resultType = profile.resultType) :
    ofCode? code = some ⟨code, profile, resultType_eq⟩ := by
  simp [ofCode?, resultType_eq]

theorem decodeCompletion?_eq_some_decodeCompletion
    (contract : CheckedCoreContract)
    {world : Core.StoreTyping}
    {value : Core.Value}
    (typing :
      Core.HostRuntimeValueHasType world value
        contract.code.program.resultType
        contract.code.program.dataDefinitions) :
    contract.decodeCompletion? value =
      some (contract.decodeCompletion typing) := by
  have populated : contract.decodeCompletion? value ≠ none := by
    apply contract.entryProfile.decode?_ne_none_of_hasType
    rw [← contract.resultType_eq]
    exact typing
  cases decoded : contract.decodeCompletion? value with
  | none => exact False.elim (populated decoded)
  | some outcome =>
      simp [decodeCompletion, decoded]

end CheckedCoreContract

end Solcore.ContractRuntime
