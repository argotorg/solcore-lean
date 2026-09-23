import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.RuntimeScalars.WordBytesProperties

/-! Bounded raw input bytes shared by one handled execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

/-- Immutable input bytes whose exact length is representable by a Core Word. -/
structure InputData where
  bytes : Bytes
  size_lt_wordModulus : bytes.size < Core.wordModulus

namespace InputData

/-- Exact byte length, represented without truncation as a Core Word. -/
def sizeWord (input : InputData) : Core.Word :=
  ⟨input.bytes.size, input.size_lt_wordModulus⟩

/-- Read one byte at the exact natural index represented by `offset`. -/
def byte? (input : InputData) (offset : Core.Word) : Option Core.Word :=
  match input.bytes.data[offset.val]? with
  | none => none
  | some byte =>
      some ⟨byte.toNat,
        Nat.lt_trans byte.toFin.isLt (by decide)⟩

/-- Decode one complete 32-byte big-endian window at an exact natural offset. -/
def wordBE? (input : InputData) (offset : Core.Word) : Option Core.Word :=
  if offset.val + 32 ≤ input.bytes.size then
    decodeWordBytesBE?
      (input.bytes.extract offset.val (offset.val + 32))
  else
    none

end InputData

end Solcore.ContractRuntime.HostStorageDriver

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageInputDataProperties`
-/

/-! Exact length and byte-lookup laws for bounded raw input data. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

namespace InputData

@[simp] theorem mk_bytes
    (bytes : Bytes) (size_lt_wordModulus : bytes.size < Core.wordModulus) :
    (InputData.mk bytes size_lt_wordModulus).bytes = bytes :=
  rfl

@[simp] theorem mk_size_lt_wordModulus
    (bytes : Bytes) (size_lt_wordModulus : bytes.size < Core.wordModulus) :
    (InputData.mk bytes size_lt_wordModulus).size_lt_wordModulus =
      size_lt_wordModulus :=
  rfl

/-- Every position in the bounded byte sequence has an exact Core Word index. -/
theorem exists_word_offset_of_lt_size
    (input : InputData) (index : Nat)
    (inBounds : index < input.bytes.size) :
    ∃ offset : Core.Word, offset.val = index :=
  ⟨⟨index, Nat.lt_trans inBounds input.size_lt_wordModulus⟩, rfl⟩

@[simp] theorem sizeWord_val (input : InputData) :
    input.sizeWord.val = input.bytes.size :=
  rfl

@[simp] theorem mk_sizeWord
    (bytes : Bytes) (size_lt_wordModulus : bytes.size < Core.wordModulus) :
    (InputData.mk bytes size_lt_wordModulus).sizeWord =
      ⟨bytes.size, size_lt_wordModulus⟩ :=
  rfl

theorem byte?_eq_some_iff
    (input : InputData) (offset result : Core.Word) :
    input.byte? offset = some result ↔
      ∃ byte,
        input.bytes.data[offset.val]? = some byte ∧
          result.val = byte.toNat := by
  cases lookup : input.bytes.data[offset.val]? with
  | none => simp [byte?, lookup]
  | some byte =>
      constructor
      · intro observed
        have resultEq :
            result = ⟨byte.toNat,
              Nat.lt_trans byte.toFin.isLt (by decide)⟩ := by
          exact (Option.some.inj
            (by simpa [byte?, lookup] using observed)).symm
        exact ⟨byte, rfl, congrArg Fin.val resultEq⟩
      · rintro ⟨found, foundLookup, valueEq⟩
        have foundEq : found = byte := by
          exact (Option.some.inj foundLookup).symm
        subst found
        have resultEq :
            result = ⟨byte.toNat,
              Nat.lt_trans byte.toFin.isLt (by decide)⟩ :=
          Fin.ext valueEq
        subst result
        simp [byte?, lookup]

@[simp] theorem byte?_eq_none_iff
    (input : InputData) (offset : Core.Word) :
    input.byte? offset = none ↔
      input.bytes.data[offset.val]? = none := by
  cases lookup : input.bytes.data[offset.val]? <;>
    simp [byte?, lookup]

theorem byte?_result_lt_256
    (input : InputData) (offset result : Core.Word)
    (read : input.byte? offset = some result) :
    result.val < 256 := by
  obtain ⟨byte, _, resultValue⟩ :=
    (byte?_eq_some_iff input offset result).mp read
  rw [resultValue]
  exact byte.toFin.isLt

@[simp] theorem byte?_eq_some_zero_of_lookup_zero
    (input : InputData) (offset : Core.Word)
    (lookup : input.bytes.data[offset.val]? = some 0) :
    input.byte? offset = some Core.Word.zero := by
  apply (byte?_eq_some_iff input offset Core.Word.zero).2
  exact ⟨0, lookup, rfl⟩

@[simp] theorem byte?_eq_none_of_size_le
    (input : InputData) (offset : Core.Word)
    (outOfBounds : input.bytes.size ≤ offset.val) :
    input.byte? offset = none := by
  rw [byte?_eq_none_iff]
  apply Array.getElem?_eq_none
  simpa only [ByteArray.size_data] using outOfBounds

theorem byte?_eq_some_of_lt_size
    (input : InputData) (offset : Core.Word)
    (inBounds : offset.val < input.bytes.size) :
    ∃ result,
      input.byte? offset = some result ∧
        result.val =
          (input.bytes.data[offset.val]'(by
            simpa only [ByteArray.size_data] using inBounds)).toNat := by
  let byte := input.bytes.data[offset.val]'(by
    simpa only [ByteArray.size_data] using inBounds)
  have lookup : input.bytes.data[offset.val]? = some byte := by
    apply Array.getElem?_eq_some_iff.mpr
    exact ⟨by simpa only [ByteArray.size_data] using inBounds, rfl⟩
  let result : Core.Word :=
    ⟨byte.toNat, Nat.lt_trans byte.toFin.isLt (by decide)⟩
  refine ⟨result, ?_, rfl⟩
  exact (byte?_eq_some_iff input offset result).2
    ⟨byte, lookup, rfl⟩

theorem exists_byte?_eq_some_iff_lt_sizeWord
    (input : InputData) (offset : Core.Word) :
    (∃ result, input.byte? offset = some result) ↔
      offset.val < input.sizeWord.val := by
  constructor
  · rintro ⟨result, present⟩
    obtain ⟨byte, lookup, _⟩ :=
      (byte?_eq_some_iff input offset result).1 present
    have inBounds : offset.val < input.bytes.data.size :=
      (Array.getElem?_eq_some_iff.mp lookup).1
    simpa only [sizeWord_val, ByteArray.size_data] using inBounds
  · intro inBounds
    obtain ⟨result, present, _⟩ :=
      byte?_eq_some_of_lt_size input offset (by simpa using inBounds)
    exact ⟨result, present⟩

theorem byte?_eq_none_iff_sizeWord_le
    (input : InputData) (offset : Core.Word) :
    input.byte? offset = none ↔ input.sizeWord.val ≤ offset.val := by
  constructor
  · intro absent
    exact Nat.le_of_not_gt fun inBounds => by
      obtain ⟨result, present⟩ :=
        (exists_byte?_eq_some_iff_lt_sizeWord input offset).2 inBounds
      rw [present] at absent
      cases absent
  · intro outOfBounds
    exact byte?_eq_none_of_size_le input offset (by simpa using outOfBounds)

@[simp] theorem byte?_sizeWord (input : InputData) :
    input.byte? input.sizeWord = none :=
  (byte?_eq_none_iff_sizeWord_le input input.sizeWord).2 (Nat.le_refl _)

/-- The strict Word decoder succeeds exactly on 32-byte inputs. -/
theorem exists_decodeWordBytesBE?_eq_some_iff_size_eq_32
    (bytes : Bytes) :
    (∃ word, decodeWordBytesBE? bytes = some word) ↔ bytes.size = 32 := by
  unfold decodeWordBytesBE? RuntimeScalar.Internal.wordDigitsOfBytes?
  split
  next lengthEq =>
    simp [lengthEq]
  next lengthNe =>
    simp [lengthNe]

/-- A fully bounded half-open Word window has exactly 32 bytes. -/
theorem extract_wordBE_window_size
    (input : InputData) (offset : Core.Word)
    (full : offset.val + 32 ≤ input.bytes.size) :
    (input.bytes.extract offset.val (offset.val + 32)).size = 32 := by
  simp only [ByteArray.size_extract]
  rw [Nat.min_eq_left full]
  omega

/-- A returned Word is precisely the canonical decoding of the selected window. -/
theorem wordBE?_eq_some_iff
    (input : InputData) (offset word : Core.Word) :
    input.wordBE? offset = some word ↔
      offset.val + 32 ≤ input.sizeWord.val ∧
        input.bytes.extract offset.val (offset.val + 32) =
          encodeWordBytesBE word := by
  unfold wordBE?
  split
  next full =>
    constructor
    · intro success
      refine ⟨by simpa using full, ?_⟩
      exact (encodeWordBytesBE_of_decodeWordBytesBE?_eq_some
        _ word success).symm
    · rintro ⟨_, selected⟩
      rw [selected]
      simp
  next incomplete =>
    constructor
    · intro impossible
      contradiction
    · rintro ⟨full, _⟩
      exact (incomplete (by simpa using full)).elim

/-- Word observation succeeds exactly when the complete natural-number window exists. -/
theorem exists_wordBE?_eq_some_iff_full_window
    (input : InputData) (offset : Core.Word) :
    (∃ word, input.wordBE? offset = some word) ↔
      offset.val + 32 ≤ input.sizeWord.val := by
  constructor
  · rintro ⟨word, success⟩
    exact (wordBE?_eq_some_iff input offset word).1 success |>.1
  · intro full
    have extractedSize :
        (input.bytes.extract offset.val (offset.val + 32)).size = 32 :=
      extract_wordBE_window_size input offset (by simpa using full)
    obtain ⟨word, decoded⟩ :=
      (exists_decodeWordBytesBE?_eq_some_iff_size_eq_32
        (input.bytes.extract offset.val (offset.val + 32))).2 extractedSize
    refine ⟨word, ?_⟩
    unfold wordBE?
    rw [if_pos (by simpa using full)]
    exact decoded

/-- Absence means exactly that fewer than 32 bytes remain at the exact offset. -/
@[simp] theorem wordBE?_eq_none_iff
    (input : InputData) (offset : Core.Word) :
    input.wordBE? offset = none ↔
      input.sizeWord.val < offset.val + 32 := by
  constructor
  · intro absent
    apply Nat.lt_of_not_ge
    intro full
    obtain ⟨word, present⟩ :=
      (exists_wordBE?_eq_some_iff_full_window input offset).2 full
    rw [present] at absent
    contradiction
  · intro incomplete
    unfold wordBE?
    rw [if_neg]
    exact Nat.not_le_of_gt (by simpa using incomplete)

/-- Every successful observation selected an exact 32-byte carrier. -/
theorem wordBE?_extract_size_of_eq_some
    (input : InputData) (offset word : Core.Word)
    (success : input.wordBE? offset = some word) :
    (input.bytes.extract offset.val (offset.val + 32)).size = 32 := by
  apply extract_wordBE_window_size input offset
  simpa using (wordBE?_eq_some_iff input offset word).1 success |>.1

/-- Every byte in a successful window remains below the exact input size. -/
theorem wordBE?_position_lt_sizeWord
    (input : InputData) (offset word : Core.Word)
    (success : input.wordBE? offset = some word) (index : Fin 32) :
    offset.val + index.val < input.sizeWord.val := by
  have full := (wordBE?_eq_some_iff input offset word).1 success |>.1
  omega

/-- Each successful-window position has a lossless Core Word representation. -/
theorem exists_word_offset_of_wordBE?_eq_some
    (input : InputData) (offset word : Core.Word)
    (success : input.wordBE? offset = some word) (index : Fin 32) :
    ∃ position : Core.Word, position.val = offset.val + index.val := by
  apply exists_word_offset_of_lt_size input
  simpa using wordBE?_position_lt_sizeWord input offset word success index

/-- Single-byte observation agrees with the corresponding encoded Word byte. -/
theorem wordBE?_byte?_eq_encoded_byte
    (input : InputData) (offset word position : Core.Word)
    (success : input.wordBE? offset = some word) (index : Fin 32)
    (positionEq : position.val = offset.val + index.val) :
    input.byte? position =
      some (Core.Word.ofNatModulo
        ((encodeWordBytesBE word)[index.val]'(by simp)).toNat) := by
  have full := (wordBE?_eq_some_iff input offset word).1 success |>.1
  have windowEq := (wordBE?_eq_some_iff input offset word).1 success |>.2
  let byte := (encodeWordBytesBE word)[index.val]'(by simp)
  have selectedLookup :
      (input.bytes.extract offset.val (offset.val + 32)).data[index.val]? =
        some byte := by
    rw [windowEq]
    apply Array.getElem?_eq_some_iff.mpr
    exact ⟨by simp, rfl⟩
  have extractIndex :
      index.val <
        min (offset.val + 32) input.bytes.data.size - offset.val := by
    rw [ByteArray.size_data]
    rw [Nat.min_eq_left (by simpa using full)]
    omega
  have sourceLookup :
      input.bytes.data[offset.val + index.val]? = some byte := by
    simpa only [ByteArray.data_extract, Array.getElem?_extract,
      if_pos extractIndex] using selectedLookup
  have lookup : input.bytes.data[position.val]? = some byte := by
    simpa only [positionEq] using sourceLookup
  apply (byte?_eq_some_iff input position _).2
  refine ⟨byte, lookup, ?_⟩
  simp only [Core.Word.ofNatModulo]
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_trans byte.toFin.isLt (by decide)

/-- Single-byte observation agrees with Core's big-endian `Word.byteAt`. -/
theorem wordBE?_byte?_eq_byteAt
    (input : InputData) (offset word position : Core.Word)
    (success : input.wordBE? offset = some word) (index : Fin 32)
    (positionEq : position.val = offset.val + index.val) :
    input.byte? position =
      some ((Core.Word.ofNatModulo index.val).byteAt word) := by
  rw [← encodeWordBytesBE_getElem_byteAt word index]
  exact wordBE?_byte?_eq_encoded_byte
    input offset word position success index positionEq

end InputData

end Solcore.ContractRuntime.HostStorageDriver
