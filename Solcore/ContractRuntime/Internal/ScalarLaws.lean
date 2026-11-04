import Solcore.ContractRuntime.RuntimeScalars
import Solcore.Core.Internal.ByteSelection

/-!
# Laws of scalars

Word bytes against their encoding, and the bridge between addresses and words.
-/

section
-- leanmerge: from Solcore.ContractRuntime.AddressWordBridge
/-! Lossless internal conversion between runtime addresses and Core words. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.AddressWordBridgeProperties`
-/

/-! Focused laws for the strict internal address and word bridge. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

theorem wordToAddress?_eq_some_iff
    (word : Core.Word) (address : Address) :
    wordToAddress? word = some address ↔ word.val = address.val := by
  unfold wordToAddress?
  split
  next inRange =>
    constructor
    · intro equal
      have payloadEqual : (⟨word.val, inRange⟩ : Address) = address :=
        Option.some.inj equal
      exact congrArg Fin.val payloadEqual
    · intro valuesEqual
      apply congrArg some
      exact Fin.ext valuesEqual
  next outOfRange =>
    constructor
    · intro impossible
      cases impossible
    · intro valuesEqual
      have inRange : word.val < addressModulus :=
        Eq.mp
          (congrArg (fun value => value < addressModulus) valuesEqual.symm)
          address.isLt
      exact (outOfRange inRange).elim

theorem wordToAddress?_success_iff (word : Core.Word) :
    (∃ address : Address, wordToAddress? word = some address) ↔
      word.val < addressModulus := by
  constructor
  · rintro ⟨address, success⟩
    have valuesEqual :=
      (wordToAddress?_eq_some_iff word address).mp success
    exact Eq.mp
      (congrArg (fun value => value < addressModulus) valuesEqual.symm)
      address.isLt
  · intro inRange
    let address : Address := ⟨word.val, inRange⟩
    exact ⟨address, (wordToAddress?_eq_some_iff word address).mpr rfl⟩

@[simp] theorem wordToAddress?_failure_iff (word : Core.Word) :
    wordToAddress? word = none ↔ addressModulus ≤ word.val := by
  unfold wordToAddress?
  split
  next inRange =>
    constructor
    · intro impossible
      cases impossible
    · intro outOfRange
      exact (Nat.not_lt_of_ge outOfRange inRange).elim
  next outOfRange =>
    constructor
    · intro _
      exact Nat.le_of_not_gt outOfRange
    · intro _
      rfl

@[simp] theorem wordToAddress?_addressToWord (address : Address) :
    wordToAddress? (addressToWord address) = some address := by
  unfold wordToAddress? addressToWord
  split
  next inRange =>
    apply congrArg some
    exact Fin.ext rfl
  next outOfRange =>
    exact (outOfRange address.isLt).elim

theorem addressToWord_of_wordToAddress?_eq_some
    {word : Core.Word} {address : Address}
    (success : wordToAddress? word = some address) :
    addressToWord address = word := by
  apply Fin.ext
  exact ((wordToAddress?_eq_some_iff word address).mp success).symm

theorem addressToWord_injective : Function.Injective addressToWord := by
  intro left right equal
  apply Fin.ext
  change left.val = right.val
  exact congrArg (fun word : Core.Word => word.val) equal

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.RuntimeScalars.WordBytesProperties
set_option autoImplicit false

namespace Solcore.ContractRuntime

open Solcore.Util

private theorem bytesOfWordDigits_size
    (digits : FixedRadix.Digits 256 32) :
    (RuntimeScalar.Internal.bytesOfWordDigits digits).size = 32 := by
  change (digits.toArray.map UInt8.ofFin).size = 32
  rw [Array.size_map]
  exact digits.size_toArray

@[simp] theorem encodeWordBytesBE_size (value : Core.Word) :
    (encodeWordBytesBE value).size = 32 := by
  exact bytesOfWordDigits_size (RuntimeScalar.Internal.wordByteDigits value)

private theorem wordOfByteValue_wordByteValue (value : Core.Word) :
    RuntimeScalar.Internal.wordOfByteValue
        (RuntimeScalar.Internal.wordByteValue value) = value := by
  apply Fin.ext
  rfl

private theorem wordByteValue_wordOfByteValue
    (value : FixedRadix.Value 256 32) :
    RuntimeScalar.Internal.wordByteValue
        (RuntimeScalar.Internal.wordOfByteValue value) = value := by
  apply Fin.ext
  rfl

@[simp] private theorem wordDigitsOfBytes?_bytesOfWordDigits
    (digits : FixedRadix.Digits 256 32) :
    RuntimeScalar.Internal.wordDigitsOfBytes?
        (RuntimeScalar.Internal.bytesOfWordDigits digits) = some digits := by
  unfold RuntimeScalar.Internal.wordDigitsOfBytes?
  rw [dif_pos (bytesOfWordDigits_size digits)]
  congr 1
  apply Vector.toArray_inj.mp
  simp only [RuntimeScalar.Internal.bytesOfWordDigits, Array.map_map]
  rw [show (UInt8.toFin ∘ UInt8.ofFin) = id by
    funext digit
    simp]
  exact Array.map_id _

private theorem bytesOfWordDigits_of_wordDigitsOfBytes?_eq_some
    (bytes : ByteArray) (digits : FixedRadix.Digits 256 32)
    (success : RuntimeScalar.Internal.wordDigitsOfBytes? bytes = some digits) :
    RuntimeScalar.Internal.bytesOfWordDigits digits = bytes := by
  simp only [RuntimeScalar.Internal.wordDigitsOfBytes?] at success
  split at success
  next _ =>
    have vectorEq := Option.some.inj success
    have arrayEq := congrArg Vector.toArray vectorEq
    apply ByteArray.ext
    simp only [RuntimeScalar.Internal.bytesOfWordDigits]
    rw [← arrayEq]
    rw [Array.map_map]
    rw [show (UInt8.ofFin ∘ UInt8.toFin) = id by
      funext byte
      simp]
    exact Array.map_id _
  next _ =>
    contradiction

@[simp] theorem decodeWordBytesBE?_encodeWordBytesBE (value : Core.Word) :
    decodeWordBytesBE? (encodeWordBytesBE value) = some value := by
  simp [decodeWordBytesBE?, encodeWordBytesBE,
    RuntimeScalar.Internal.wordByteDigits, wordOfByteValue_wordByteValue]

private theorem wordByteDigits_wordOfByteValue_decode
    (digits : FixedRadix.Digits 256 32) :
    RuntimeScalar.Internal.wordByteDigits
        (RuntimeScalar.Internal.wordOfByteValue (FixedRadix.decode digits)) =
      digits := by
  unfold RuntimeScalar.Internal.wordByteDigits
  rw [wordByteValue_wordOfByteValue]
  exact FixedRadix.encode_decode (by decide) digits

theorem encodeWordBytesBE_of_decodeWordBytesBE?_eq_some
    (bytes : ByteArray) (value : Core.Word)
    (success : decodeWordBytesBE? bytes = some value) :
    encodeWordBytesBE value = bytes := by
  simp only [decodeWordBytesBE?] at success
  cases digitsResult : RuntimeScalar.Internal.wordDigitsOfBytes? bytes with
  | none => simp [digitsResult] at success
  | some digits =>
      simp [digitsResult] at success
      rw [← success]
      rw [encodeWordBytesBE, wordByteDigits_wordOfByteValue_decode]
      exact bytesOfWordDigits_of_wordDigitsOfBytes?_eq_some
        bytes digits digitsResult

private theorem encodeWordBytesBE_getElem_toFin
    (value : Core.Word) (index : Fin 32) :
    ((encodeWordBytesBE value)[index.val]'(by simp)).toFin =
      (RuntimeScalar.Internal.wordByteDigits value).get index := by
  unfold encodeWordBytesBE RuntimeScalar.Internal.bytesOfWordDigits
  simp [ByteArray.getElem_eq_getElem_data, Vector.get]

private theorem pow256_eq_pow2 (power : Nat) :
    256 ^ power = 2 ^ (8 * power) := by
  exact (Nat.pow_mul 2 8 power).symm

private theorem encodeWordBytesBE_getElem_toNat
    (value : Core.Word) (index : Fin 32) :
    ((encodeWordBytesBE value)[index.val]'(by simp)).toNat =
      (value.val / 2 ^ (8 * (31 - index.val))) % 256 := by
  change
    ((encodeWordBytesBE value)[index.val]'(by simp)).toFin.val = _
  rw [encodeWordBytesBE_getElem_toFin]
  unfold RuntimeScalar.Internal.wordByteDigits
  rw [FixedRadix.encode_get]
  simp only [RuntimeScalar.Internal.wordByteValue, Fin.val_cast]
  rw [show 32 - 1 - index.val = 31 - index.val by omega]
  rw [pow256_eq_pow2]

private theorem wordIndex_value (index : Fin 32) :
    (Core.Word.ofNatModulo index.val).val = index.val := by
  have inRange : index.val < Core.wordModulus :=
    Nat.lt_trans index.isLt (by decide)
  simp [Core.Word.ofNatModulo, Nat.mod_eq_of_lt inRange]

theorem encodeWordBytesBE_getElem_byteAt
    (value : Core.Word) (index : Fin 32) :
    Core.Word.ofNatModulo
        ((encodeWordBytesBE value)[index.val]'(by simp)).toNat =
      (Core.Word.ofNatModulo index.val).byteAt value := by
  have indexValue := wordIndex_value index
  have small : (Core.Word.ofNatModulo index.val).val < 32 := by
    rw [indexValue]
    exact index.isLt
  rw [Core.Word.byteAt_of_lt_32 _ _ small]
  rw [indexValue]
  rw [encodeWordBytesBE_getElem_toNat]

end Solcore.ContractRuntime
end
