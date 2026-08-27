import Solcore.Semantics.RuntimeScalars

/-! Exact-width, big-endian bytes for internal runtime addresses. -/

set_option autoImplicit false

namespace Solcore.Semantics

open Solcore.Foundation

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

end Solcore.Semantics
