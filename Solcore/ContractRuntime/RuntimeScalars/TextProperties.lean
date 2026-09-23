import Solcore.ContractRuntime.RuntimeScalars

set_option autoImplicit false

namespace Solcore.ContractRuntime

open Solcore.Foundation
open RuntimeScalar.Internal

@[simp] private theorem encodeByteDigits_length (byte : UInt8) :
    (encodeByteDigits byte).length = 2 := by
  simp [encodeByteDigits]

private theorem encodeByteDigits_pair (byte : UInt8) :
    ∃ high low, encodeByteDigits byte = [high, low] ∧
      decodeByteDigits high low = byte := by
  let digits := FixedRadix.encode 16 2 (by decide) (byteHexValue byte)
  have lengthEq : digits.toList.length = 2 := Vector.length_toList
  have encodedEq : encodeByteDigits byte = digits.toList := rfl
  cases listEq : digits.toList with
  | nil => simp [listEq] at lengthEq
  | cons high tail =>
      cases tail with
      | nil => simp [listEq] at lengthEq
      | cons low rest =>
          cases rest with
          | nil =>
              refine ⟨high, low, by simp [encodedEq, listEq], ?_⟩
              have digitsEq : (#v[high, low] : FixedHex.Digits 2) = digits := by
                apply Vector.toList_inj.mp
                simp [listEq]
              simp [decodeByteDigits, digitsEq, digits, byteHexValue]
          | cons extra rest => simp [listEq] at lengthEq

@[simp] private theorem encodeByteDigits_decodeByteDigits
    (high low : FixedHex.Digit) :
    encodeByteDigits (decodeByteDigits high low) = [high, low] := by
  simp [encodeByteDigits, decodeByteDigits, byteHexValue]

private theorem encodeBytesDigits_length (bytes : List UInt8) :
    (encodeBytesDigits bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      simp [encodeBytesDigits, ih]
      omega

@[simp] private theorem decodeBytesDigits?_encodeBytesDigits
    (bytes : List UInt8) :
    decodeBytesDigits? (encodeBytesDigits bytes) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      obtain ⟨high, low, encoded, decoded⟩ := encodeByteDigits_pair byte
      simp [encodeBytesDigits, encoded, decodeBytesDigits?, decoded, ih]

private theorem encodeBytesDigits_of_decodeBytesDigits?_eq_some :
    ∀ (digits : List FixedHex.Digit) (bytes : List UInt8),
      decodeBytesDigits? digits = some bytes → encodeBytesDigits bytes = digits
  | [], bytes, success => by
      simp [decodeBytesDigits?] at success
      subst bytes
      rfl
  | [_], _, success => by simp [decodeBytesDigits?] at success
  | high :: low :: digits, bytes, success => by
      cases tailResult : decodeBytesDigits? digits with
      | none => simp [decodeBytesDigits?, tailResult] at success
      | some tail =>
          simp [decodeBytesDigits?, tailResult] at success
          subst bytes
          rw [encodeBytesDigits, encodeByteDigits_decodeByteDigits,
            encodeBytesDigits_of_decodeBytesDigits?_eq_some digits tail tailResult]
          rfl

private theorem dataToList_toByteArray (value : ByteArray) :
    value.data.toList.toByteArray = value := by
  apply ByteArray.ext
  simp

private theorem addressOfHexValue_addressHexValue (value : Address) :
    addressOfHexValue (addressHexValue value) = value := by
  apply Fin.ext
  rfl

private theorem addressHexValue_addressOfHexValue
    (value : FixedHex.Value 40) :
    addressHexValue (addressOfHexValue value) = value := by
  apply Fin.ext
  rfl

private theorem wordOfHexValue_wordHexValue (value : Core.Word) :
    wordOfHexValue (wordHexValue value) = value := by
  apply Fin.ext
  rfl

private theorem wordHexValue_wordOfHexValue (value : FixedHex.Value 64) :
    wordHexValue (wordOfHexValue value) = value := by
  apply Fin.ext
  rfl

theorem encodeBytesText_length (value : Bytes) :
    (encodeBytesText value).length = 2 + 2 * value.size := by
  simp [encodeBytesText, encodeBytesDigits_length, ByteArray.size_data]
  omega

@[simp] theorem decodeBytesText?_encodeBytesText (value : Bytes) :
    decodeBytesText? (encodeBytesText value) = some value := by
  simp [decodeBytesText?, encodeBytesText, dataToList_toByteArray]

theorem encodeBytesText_of_decodeBytesText?_eq_some
    (text : String) (value : Bytes)
    (success : decodeBytesText? text = some value) :
    encodeBytesText value = text := by
  simp only [decodeBytesText?] at success
  cases digitsResult : FixedHex.decodeDigitsText? text with
  | none => simp [digitsResult] at success
  | some digits =>
      cases bytesResult : decodeBytesDigits? digits with
      | none => simp [digitsResult, bytesResult] at success
      | some bytes =>
          simp [digitsResult, bytesResult] at success
          subst value
          rw [encodeBytesText, List.toList_data_toByteArray]
          rw [encodeBytesDigits_of_decodeBytesDigits?_eq_some digits bytes bytesResult]
          exact FixedHex.encodeDigitsText_of_decodeDigitsText?_eq_some
            text digits digitsResult

theorem encodeBytesText_injective : Function.Injective encodeBytesText := by
  intro left right equal
  have decoded := congrArg decodeBytesText? equal
  simpa using decoded

theorem encodeAddressText_length (value : Address) :
    (encodeAddressText value).length = 42 := by
  simp [encodeAddressText]

@[simp] theorem decodeAddressText?_encodeAddressText (value : Address) :
    decodeAddressText? (encodeAddressText value) = some value := by
  simp [decodeAddressText?, encodeAddressText,
    addressOfHexValue_addressHexValue]

theorem encodeAddressText_of_decodeAddressText?_eq_some
    (text : String) (value : Address)
    (success : decodeAddressText? text = some value) :
    encodeAddressText value = text := by
  simp only [decodeAddressText?] at success
  cases decodedResult : FixedHex.decodeText? 40 text with
  | none => simp [decodedResult] at success
  | some decoded =>
      simp [decodedResult] at success
      subst value
      rw [encodeAddressText, addressHexValue_addressOfHexValue]
      exact FixedHex.encodeText_of_decodeText?_eq_some
        40 text decoded decodedResult

theorem encodeAddressText_injective : Function.Injective encodeAddressText := by
  intro left right equal
  have decoded := congrArg decodeAddressText? equal
  simpa using decoded

theorem encodeWordText_length (value : Core.Word) :
    (encodeWordText value).length = 66 := by
  simp [encodeWordText]

@[simp] theorem decodeWordText?_encodeWordText (value : Core.Word) :
    decodeWordText? (encodeWordText value) = some value := by
  simp [decodeWordText?, encodeWordText, wordOfHexValue_wordHexValue]

theorem encodeWordText_of_decodeWordText?_eq_some
    (text : String) (value : Core.Word)
    (success : decodeWordText? text = some value) :
    encodeWordText value = text := by
  simp only [decodeWordText?] at success
  cases decodedResult : FixedHex.decodeText? 64 text with
  | none => simp [decodedResult] at success
  | some decoded =>
      simp [decodedResult] at success
      subst value
      rw [encodeWordText, wordHexValue_wordOfHexValue]
      exact FixedHex.encodeText_of_decodeText?_eq_some
        64 text decoded decodedResult

theorem encodeWordText_injective : Function.Injective encodeWordText := by
  intro left right equal
  have decoded := congrArg decodeWordText? equal
  simpa using decoded

end Solcore.ContractRuntime
