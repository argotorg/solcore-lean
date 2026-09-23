import Solcore.ContractRuntime.RuntimeScalars.TextProperties
import Solcore.ContractRuntime.AddressBytesBEProperties

/-! Private radix bridge for Address text and exact-byte coherence. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

open Solcore.Foundation
open RuntimeScalar.Internal

@[simp] private theorem addressEncodeByteDigits_length (byte : UInt8) :
    (encodeByteDigits byte).length = 2 := by
  simp [encodeByteDigits]

private theorem addressEncodeBytesDigits_length (bytes : List UInt8) :
    (encodeBytesDigits bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      simp [encodeBytesDigits, ih]
      omega

private theorem addressEncodeByteDigits_get
    (byte : UInt8) (index : Fin 2) :
    ((encodeByteDigits byte)[index.val]'(by simp)).val =
      (byte.toNat / 16 ^ (1 - index.val)) % 16 := by
  simpa [encodeByteDigits, Vector.get, byteHexValue] using
    FixedRadix.encode_get 16 2 (by decide) (byteHexValue byte) index

private theorem addressEncodeBytesDigits_get_even
    (bytes : List UInt8) (index : Nat) (indexLt : index < bytes.length) :
    ((encodeBytesDigits bytes)[2 * index]'(by
      rw [addressEncodeBytesDigits_length]
      omega)).val =
      ((encodeByteDigits bytes[index])[0]'(by simp)).val := by
  induction bytes generalizing index with
  | nil => simp at indexLt
  | cons byte bytes ih =>
      cases index with
      | zero =>
          simp [encodeBytesDigits]
      | succ index =>
          have indexLt' : index < bytes.length := by simpa using indexLt
          simp only [encodeBytesDigits]
          rw [List.getElem_append_right (by
            rw [addressEncodeByteDigits_length]
            omega)]
          have shifted :
              2 * (index + 1) - 2 =
                2 * index := by
            omega
          simpa [shifted] using ih index indexLt'

private theorem addressEncodeBytesDigits_get_odd
    (bytes : List UInt8) (index : Nat) (indexLt : index < bytes.length) :
    ((encodeBytesDigits bytes)[2 * index + 1]'(by
      rw [addressEncodeBytesDigits_length]
      omega)).val =
      ((encodeByteDigits bytes[index])[1]'(by simp)).val := by
  induction bytes generalizing index with
  | nil => simp at indexLt
  | cons byte bytes ih =>
      cases index with
      | zero =>
          simp [encodeBytesDigits]
      | succ index =>
          have indexLt' : index < bytes.length := by simpa using indexLt
          simp only [encodeBytesDigits]
          rw [List.getElem_append_right (by
            rw [addressEncodeByteDigits_length]
            omega)]
          have shifted :
              2 * (index + 1) + 1 - 2 =
                2 * index + 1 := by
            omega
          simpa [shifted] using ih index indexLt'

private theorem addressBytePower (power : Nat) :
    256 ^ power = 16 ^ (2 * power) := by
  rw [show 256 = 16 ^ 2 by decide]
  exact (Nat.pow_mul 16 2 power).symm

private theorem addressHighNibble (value power : Nat) :
    (((value / 256 ^ power) % 256) / 16) % 16 =
      (value / 16 ^ (2 * power + 1)) % 16 := by
  rw [addressBytePower]
  rw [show 256 = 16 * 16 by decide]
  rw [Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod]
  rw [Nat.div_div_eq_div_mul]
  rw [← Nat.pow_succ]

private theorem addressLowNibble (value power : Nat) :
    ((value / 256 ^ power) % 256) % 16 =
      (value / 16 ^ (2 * power)) % 16 := by
  rw [addressBytePower]
  rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 256)]

private theorem addressByteModulus : addressModulus = 256 ^ 20 := by
  decide

private theorem addressBytesGetElemToFin
    (value : Address) (index : Fin 20) :
    ((encodeAddressBytesBE value)[index.val]'(by simp)).toFin =
      (FixedRadix.encode 256 20 (by decide)
        (Fin.cast addressByteModulus value)).get index := by
  unfold encodeAddressBytesBE
  simp [ByteArray.getElem_eq_getElem_data, Vector.get]

private theorem addressBytesGetElemToNat
    (value : Address) (index : Fin 20) :
    ((encodeAddressBytesBE value)[index.val]'(by simp)).toNat =
      (value.val / 256 ^ (19 - index.val)) % 256 := by
  change
    ((encodeAddressBytesBE value)[index.val]'(by simp)).toFin.val = _
  rw [addressBytesGetElemToFin]
  rw [FixedRadix.encode_get]
  simp only [Fin.val_cast]

private theorem addressBytesListGetElemToNat
    (value : Address) (index : Fin 20) :
    ((encodeAddressBytesBE value).data.toList[index.val]'(by
      simp [ByteArray.size_data])).toNat =
      (value.val / 256 ^ (19 - index.val)) % 256 := by
  change
    ((encodeAddressBytesBE value)[index.val]'(by simp)).toNat = _
  exact addressBytesGetElemToNat value index

private theorem addressDigitEven
    (value : Address) (index : Fin 20) :
    ((encodeBytesDigits (encodeAddressBytesBE value).data.toList)[2 * index.val]'(by
          rw [addressEncodeBytesDigits_length]
          have sizeEq :
              (encodeAddressBytesBE value).data.toList.length = 20 := by
            simp [ByteArray.size_data]
          rw [sizeEq]
          omega
          )).val =
      ((FixedRadix.encode 16 40 (by decide) (addressHexValue value)).get
        ⟨2 * index.val, by omega⟩).val := by
  have indexLt :
      index.val < (encodeAddressBytesBE value).data.toList.length := by
    simp [ByteArray.size_data]
  rw [addressEncodeBytesDigits_get_even _ index.val indexLt]
  rw [addressEncodeByteDigits_get _ ⟨0, by decide⟩]
  rw [addressBytesListGetElemToNat]
  rw [FixedRadix.encode_get]
  simp only [addressHexValue, Fin.val_cast]
  rw [addressHighNibble]
  congr 3
  omega

private theorem addressDigitOdd
    (value : Address) (index : Fin 20) :
    ((encodeBytesDigits (encodeAddressBytesBE value).data.toList)[2 * index.val + 1]'(by
          rw [addressEncodeBytesDigits_length]
          have sizeEq :
              (encodeAddressBytesBE value).data.toList.length = 20 := by
            simp [ByteArray.size_data]
          rw [sizeEq]
          omega
          )).val =
      ((FixedRadix.encode 16 40 (by decide) (addressHexValue value)).get
        ⟨2 * index.val + 1, by omega⟩).val := by
  have indexLt :
      index.val < (encodeAddressBytesBE value).data.toList.length := by
    simp [ByteArray.size_data]
  rw [addressEncodeBytesDigits_get_odd _ index.val indexLt]
  rw [addressEncodeByteDigits_get _ ⟨1, by decide⟩]
  simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
  rw [addressBytesListGetElemToNat]
  rw [FixedRadix.encode_get]
  simp only [addressHexValue, Fin.val_cast]
  rw [addressLowNibble]
  congr 3
  omega

private theorem addressDigitListsEqual (value : Address) :
    encodeBytesDigits (encodeAddressBytesBE value).data.toList =
      (FixedRadix.encode 16 40 (by decide) (addressHexValue value)).toList := by
  apply List.ext_getElem
  · rw [addressEncodeBytesDigits_length]
    have bytesSize :
        (encodeAddressBytesBE value).data.toList.length = 20 := by
      simp [ByteArray.size_data]
    rw [bytesSize]
    simp
  · intro position leftBound rightBound
    have leftLength :
        (encodeBytesDigits
          (encodeAddressBytesBE value).data.toList).length = 40 := by
      rw [addressEncodeBytesDigits_length]
      have bytesSize :
          (encodeAddressBytesBE value).data.toList.length = 20 := by
        simp [ByteArray.size_data]
      rw [bytesSize]
    have quotientBound : position / 2 < 20 := by
      rw [leftLength] at leftBound
      omega
    let index : Fin 20 := ⟨position / 2, quotientBound⟩
    apply Fin.ext
    change
      ((encodeBytesDigits (encodeAddressBytesBE value).data.toList)[position]'leftBound).val =
      ((FixedRadix.encode 16 40 (by decide) (addressHexValue value)).get
        ⟨position, by simpa using rightBound⟩).val
    have reconstruction := Nat.mod_add_div position 2
    rcases Nat.mod_two_eq_zero_or_one position with even | odd
    · have positionEq : position = 2 * index.val := by
        simp only [index]
        omega
      simpa [positionEq] using addressDigitEven value index
    · have positionEq : position = 2 * index.val + 1 := by
        simp only [index]
        omega
      simpa [positionEq] using addressDigitOdd value index

theorem encodeBytesText_encodeAddressBytesBE (value : Address) :
    encodeBytesText (encodeAddressBytesBE value) = encodeAddressText value := by
  unfold encodeBytesText encodeAddressText FixedHex.encodeText
  rw [addressDigitListsEqual]

@[simp] theorem decodeBytesText?_encodeAddressText (value : Address) :
    decodeBytesText? (encodeAddressText value) =
      some (encodeAddressBytesBE value) := by
  rw [← encodeBytesText_encodeAddressBytesBE]
  exact decodeBytesText?_encodeBytesText _

theorem decodeAddressText?_encodeBytesText (bytes : ByteArray) :
    decodeAddressText? (encodeBytesText bytes) =
      decodeAddressBytesBE? bytes := by
  cases decodedBytes : decodeAddressBytesBE? bytes with
  | some value =>
      have bytesEqual :=
        encodeAddressBytesBE_of_decodeAddressBytesBE?_eq_some
          bytes value decodedBytes
      rw [← bytesEqual, encodeBytesText_encodeAddressBytesBE]
      exact decodeAddressText?_encodeAddressText value
  | none =>
      cases decodedText : decodeAddressText? (encodeBytesText bytes) with
      | none => rfl
      | some value =>
          have textEqual :=
            encodeAddressText_of_decodeAddressText?_eq_some
              (encodeBytesText bytes) value decodedText
          rw [← encodeBytesText_encodeAddressBytesBE] at textEqual
          have bytesEqual := encodeBytesText_injective textEqual
          have roundTrip := decodeAddressBytesBE?_encodeAddressBytesBE value
          rw [bytesEqual, decodedBytes] at roundTrip
          contradiction

theorem decodeAddressText?_eq_decodeBytesText?_bind (text : String) :
    decodeAddressText? text =
      (decodeBytesText? text).bind decodeAddressBytesBE? := by
  cases decodedBytes : decodeBytesText? text with
  | some bytes =>
      have textEqual :=
        encodeBytesText_of_decodeBytesText?_eq_some text bytes decodedBytes
      rw [← textEqual]
      rw [decodeAddressText?_encodeBytesText]
      simp
  | none =>
      cases decodedAddress : decodeAddressText? text with
      | none => rfl
      | some value =>
          have textEqual :=
            encodeAddressText_of_decodeAddressText?_eq_some
              text value decodedAddress
          rw [← textEqual] at decodedBytes
          rw [← encodeBytesText_encodeAddressBytesBE] at decodedBytes
          simp at decodedBytes

end Solcore.ContractRuntime
