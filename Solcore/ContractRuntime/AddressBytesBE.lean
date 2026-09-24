import Solcore.ContractRuntime.RuntimeScalars
import Solcore.Core.ByteSelection
import Solcore.ContractRuntime.AddressWordBridge

/-! Exact-width, big-endian bytes for internal runtime addresses. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

open Solcore.Util

private theorem addressByteModulus : addressModulus = 256 ^ 20 := by
  decide

/-- Encode an address as exactly 20 most-significant-byte-first octets. -/
def encodeAddressBytesBE (value : Address) : ByteArray :=
  let digits := FixedRadix.encode 256 20 (by decide)
    (Fin.cast addressByteModulus value)
  ⟨digits.toArray.map UInt8.ofFin⟩

/-- Decode an address only from an exact 20-byte big-endian representation. -/
def decodeAddressBytesBE? (bytes : ByteArray) : Option Address :=
  if lengthEq : bytes.size = 20 then
    let digits : FixedRadix.Digits 256 20 :=
      ⟨bytes.data.map UInt8.toFin, by simpa using lengthEq⟩
    some (Fin.cast addressByteModulus.symm (FixedRadix.decode digits))
  else
    none

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.AddressBytesBEProperties`
-/

/-! Focused laws for exact-width, big-endian runtime address bytes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

open Solcore.Util

private theorem addressByteModulusProperties : addressModulus = 256 ^ 20 := by
  decide

@[simp] theorem encodeAddressBytesBE_size (value : Address) :
    (encodeAddressBytesBE value).size = 20 := by
  change
    ((FixedRadix.encode 256 20 (by decide)
      (Fin.cast addressByteModulusProperties value)).toArray.map UInt8.ofFin).size = 20
  rw [Array.size_map]
  exact (FixedRadix.encode 256 20 (by decide)
    (Fin.cast addressByteModulusProperties value)).size_toArray

@[simp] theorem decodeAddressBytesBE?_encodeAddressBytesBE (value : Address) :
    decodeAddressBytesBE? (encodeAddressBytesBE value) = some value := by
  unfold decodeAddressBytesBE?
  rw [dif_pos (encodeAddressBytesBE_size value)]
  let decodedDigits : FixedRadix.Digits 256 20 :=
    ⟨(encodeAddressBytesBE value).data.map UInt8.toFin, by simp⟩
  have digitsEqual :
      decodedDigits =
        FixedRadix.encode 256 20 (by decide)
          (Fin.cast addressByteModulusProperties value) := by
    apply Vector.toArray_inj.mp
    unfold decodedDigits encodeAddressBytesBE
    simp only
    rw [Array.map_map]
    rw [show (UInt8.toFin ∘ UInt8.ofFin) = id by
      funext digit
      simp]
    exact Array.map_id _
  change
    some (Fin.cast addressByteModulusProperties.symm
      (FixedRadix.decode decodedDigits)) = some value
  apply congrArg some
  rw [digitsEqual, FixedRadix.decode_encode]
  apply Fin.ext
  rfl

theorem encodeAddressBytesBE_of_decodeAddressBytesBE?_eq_some
    (bytes : ByteArray) (value : Address)
    (success : decodeAddressBytesBE? bytes = some value) :
    encodeAddressBytesBE value = bytes := by
  unfold decodeAddressBytesBE? at success
  split at success
  next lengthEq =>
    let digits : FixedRadix.Digits 256 20 :=
      ⟨bytes.data.map UInt8.toFin, by simpa using lengthEq⟩
    have addressEqual :
        Fin.cast addressByteModulusProperties.symm (FixedRadix.decode digits) = value :=
      Option.some.inj success
    rw [← addressEqual]
    have castEqual :
        Fin.cast addressByteModulusProperties
          (Fin.cast addressByteModulusProperties.symm (FixedRadix.decode digits)) =
            FixedRadix.decode digits := by
      apply Fin.ext
      rfl
    apply ByteArray.ext
    change
      (FixedRadix.encode 256 20 (by decide)
        (Fin.cast addressByteModulusProperties
          (Fin.cast addressByteModulusProperties.symm
            (FixedRadix.decode digits)))).toArray.map UInt8.ofFin = bytes.data
    rw [castEqual, FixedRadix.encode_decode]
    unfold digits
    rw [Array.map_map]
    rw [show (UInt8.ofFin ∘ UInt8.toFin) = id by
      funext byte
      simp]
    exact Array.map_id _
  next _ =>
    contradiction

theorem decodeAddressBytesBE?_success_iff (bytes : ByteArray) :
    (∃ value : Address, decodeAddressBytesBE? bytes = some value) ↔
      bytes.size = 20 := by
  constructor
  · rintro ⟨value, success⟩
    unfold decodeAddressBytesBE? at success
    split at success
    next lengthEq => exact lengthEq
    next _ => contradiction
  · intro lengthEq
    unfold decodeAddressBytesBE?
    rw [dif_pos lengthEq]
    exact ⟨_, rfl⟩

theorem encodeAddressBytesBE_injective :
    Function.Injective encodeAddressBytesBE := by
  intro left right equal
  have leftRoundtrip := decodeAddressBytesBE?_encodeAddressBytesBE left
  have rightRoundtrip := decodeAddressBytesBE?_encodeAddressBytesBE right
  rw [equal] at leftRoundtrip
  rw [rightRoundtrip] at leftRoundtrip
  exact Option.some.inj leftRoundtrip.symm

private theorem encodeAddressBytesBE_getElem_toFin
    (value : Address) (index : Fin 20) :
    ((encodeAddressBytesBE value)[index.val]'(by simp)).toFin =
      (FixedRadix.encode 256 20 (by decide)
        (Fin.cast addressByteModulusProperties value)).get index := by
  unfold encodeAddressBytesBE
  simp [ByteArray.getElem_eq_getElem_data, Vector.get]

private theorem encodeAddressBytesBE_getElem_toNat
    (value : Address) (index : Fin 20) :
    ((encodeAddressBytesBE value)[index.val]'(by simp)).toNat =
      (value.val / 2 ^ (8 * (19 - index.val))) % 256 := by
  change
    ((encodeAddressBytesBE value)[index.val]'(by simp)).toFin.val = _
  rw [encodeAddressBytesBE_getElem_toFin]
  rw [FixedRadix.encode_get]
  simp only [Fin.val_cast]
  rw [show 20 - 1 - index.val = 19 - index.val by omega]
  rw [(Nat.pow_mul 2 8 (19 - index.val)).symm]

theorem encodeAddressBytesBE_getElem_byteAt
    (value : Address) (index : Fin 20) :
    Core.Word.ofNatModulo
        ((encodeAddressBytesBE value)[index.val]'(by simp)).toNat =
      (Core.Word.ofNatModulo (index.val + 12)).byteAt
        (addressToWord value) := by
  have wordIndexValue :
      (Core.Word.ofNatModulo (index.val + 12)).val = index.val + 12 := by
    have belowWordWidth : index.val + 12 < 32 := by omega
    have wordWidthBelowModulus : 32 < Core.wordModulus := by decide
    have inRange : index.val + 12 < Core.wordModulus :=
      Nat.lt_trans belowWordWidth wordWidthBelowModulus
    simp [Core.Word.ofNatModulo, Nat.mod_eq_of_lt inRange]
  have small : (Core.Word.ofNatModulo (index.val + 12)).val < 32 := by
    rw [wordIndexValue]
    omega
  rw [Core.Word.byteAt_of_lt_32 _ _ small]
  rw [wordIndexValue]
  rw [encodeAddressBytesBE_getElem_toNat]
  have exponentEqual :
      31 - (index.val + 12) = 19 - index.val := by omega
  rw [exponentEqual]
  rfl

end Solcore.ContractRuntime
