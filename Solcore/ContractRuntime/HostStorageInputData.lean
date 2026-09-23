import Solcore.ContractRuntime.RuntimeScalars

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
