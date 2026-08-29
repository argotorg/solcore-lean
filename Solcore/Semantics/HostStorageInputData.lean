import Solcore.Semantics.RuntimeScalars

/-! Bounded raw input bytes shared by one handled execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

/-- Immutable input bytes whose exact length is representable by a Core Word. -/
structure InputData where
  bytes : Bytes
  size_lt_wordModulus : bytes.size < Core.wordModulus

namespace InputData

/-- Read one byte at the exact natural index represented by `offset`. -/
def byte? (input : InputData) (offset : Core.Word) : Option Core.Word :=
  match input.bytes.data[offset.val]? with
  | none => none
  | some byte =>
      some ⟨byte.toNat,
        Nat.lt_trans byte.toFin.isLt (by decide)⟩

end InputData

end Solcore.Semantics.HostStorageDriver
