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
