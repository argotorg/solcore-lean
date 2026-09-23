import Solcore.Abi.StaticWordMetadata

/-! Proof contracts for Static Word ABI metadata and selectors. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.ContractRuntime

theorem validateMethodName?_isSome_iff (text : String) :
    (validateMethodName? text).isSome ↔ isValidMethodName text = true := by
  unfold validateMethodName?
  split <;> simp_all

theorem validateMethodName?_eq_some_iff
    (text : String) (name : MethodName) :
    validateMethodName? text = some name ↔ name.text = text := by
  constructor
  · intro success
    unfold validateMethodName? at success
    split at success
    · cases success
      rfl
    · contradiction
  · intro textEq
    rcases name with ⟨nameText, valid⟩
    simp only at textEq
    subst nameText
    unfold validateMethodName?
    rw [dif_pos valid]

theorem validateMethodName?_success_text
    {text : String} {name : MethodName}
    (success : validateMethodName? text = some name) :
    name.text = text :=
  (validateMethodName?_eq_some_iff text name).mp success

theorem Selector.encode_of_decode?_eq_some
    {bytes : Bytes} {selector : Selector}
    (success : Selector.decode? bytes = some selector) :
    selector.encode = bytes := by
  unfold Selector.decode? at success
  split at success
  · cases success
    rfl
  · contradiction

theorem Selector.decode?_eq_some_iff
    (bytes : Bytes) (selector : Selector) :
    Selector.decode? bytes = some selector ↔ bytes = selector.encode := by
  constructor
  · intro success
    exact (Selector.encode_of_decode?_eq_some success).symm
  · intro encoded
    subst bytes
    exact selector.decode_encode

/-- The numeric selector view consumes its four bytes from most to least
significant, with one eight-bit shift per byte. -/
theorem Selector.toUInt32_eq_bigEndianBytes (selector : Selector) :
    selector.toUInt32 =
      ((selector.bytes[0].toUInt32 <<< 8 |||
          selector.bytes[1].toUInt32) <<< 8 |||
        selector.bytes[2].toUInt32) <<< 8 |||
      selector.bytes[3].toUInt32 := by
  rcases selector with ⟨⟨⟨items⟩, sizeEq⟩⟩
  cases items with
  | nil => simp at sizeEq
  | cons first rest =>
      cases rest with
      | nil => simp at sizeEq
      | cons second rest =>
          cases rest with
          | nil => simp at sizeEq
          | cons third rest =>
              cases rest with
              | nil => simp at sizeEq
              | cons fourth rest =>
                  cases rest with
                  | nil => simp [Selector.toUInt32]
                  | cons fifth rest => simp at sizeEq

/-- The bounded numeric view carries the same big-endian value. -/
theorem Selector.toFin_val_eq_bigEndianBytes (selector : Selector) :
    selector.toFin.val =
      (((selector.bytes[0].toUInt32 <<< 8 |||
          selector.bytes[1].toUInt32) <<< 8 |||
        selector.bytes[2].toUInt32) <<< 8 |||
      selector.bytes[3].toUInt32).toNat := by
  change selector.toUInt32.toNat = _
  rw [selector.toUInt32_eq_bigEndianBytes]

private theorem selectorOfFirstFourBytes_encode
    (bytes : Bytes) (width : 4 ≤ bytes.size) :
    (⟨Vector.ofFn (fun index => bytes.get! index.val)⟩ : Selector).encode =
      bytes.extract 0 4 := by
  apply ByteArray.ext
  apply Array.ext
  · simp [Selector.encode, Nat.min_eq_left width]
  · intro index leftLt rightLt
    have indexLtFour : index < 4 := by
      simpa [Selector.encode] using leftLt
    have indexLtBytes : index < bytes.data.size := by
      exact Nat.lt_of_lt_of_le indexLtFour width
    simp [Selector.encode, ByteArray.data_extract]
    change bytes.data[index]! = bytes.data[index]
    exact getElem!_pos bytes.data index indexLtBytes

theorem selectorFromSignatureBytes_encode (signature : Bytes) :
    (selectorFromSignatureBytes signature).encode =
      (Keccak256.hash signature).extract 0 4 := by
  unfold selectorFromSignatureBytes
  apply selectorOfFirstFourBytes_encode
  rw [Keccak256.hash_size]
  omega

end Solcore.Abi.V1
