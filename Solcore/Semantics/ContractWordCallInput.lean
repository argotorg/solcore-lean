import Solcore.Semantics.HostStorageInputDataProperties

/-! Exact fixed-width input derivation for the internal contract-word call. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver.InputData

/-- Represent one call input Word by its exact canonical 32-byte encoding. -/
def ofWord (word : Core.Word) : InputData := {
  bytes := encodeWordBytesBE word
  size_lt_wordModulus := by
    rw [encodeWordBytesBE_size]
    decide
}

@[simp] theorem ofWord_bytes (word : Core.Word) :
    (ofWord word).bytes = encodeWordBytesBE word :=
  rfl

@[simp] theorem ofWord_sizeWord_val (word : Core.Word) :
    (ofWord word).sizeWord.val = 32 := by
  simp [ofWord]

@[simp] theorem ofWord_wordBE?_zero (word : Core.Word) :
    (ofWord word).wordBE? Core.Word.zero = some word := by
  rw [wordBE?_eq_some_iff]
  constructor
  · simp [Core.Word.zero, ofWord]
  · change (encodeWordBytesBE word).extract 0 32 = encodeWordBytesBE word
    rw [← encodeWordBytesBE_size word]
    exact ByteArray.extract_zero_size

end Solcore.Semantics.HostStorageDriver.InputData
