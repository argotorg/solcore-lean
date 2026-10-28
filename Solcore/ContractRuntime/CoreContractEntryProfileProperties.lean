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

@[simp] theorem returnsOneWord_returnWord :
    returnsOneWord .returnWord = true :=
  rfl

@[simp] theorem returnsOneWord_wordOutcomeV1 :
    returnsOneWord .wordOutcomeV1 = true :=
  rfl

@[simp] theorem returnsOneWord_wordTupleOutcomeV1 (extraWords : Nat) :
    returnsOneWord (.wordTupleOutcomeV1 extraWords) = false :=
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
