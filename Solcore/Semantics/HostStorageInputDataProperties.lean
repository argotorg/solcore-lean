import Solcore.Semantics.HostStorageInputData

/-! Exact length and byte-lookup laws for bounded raw input data. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

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

end InputData

end Solcore.Semantics.HostStorageDriver
