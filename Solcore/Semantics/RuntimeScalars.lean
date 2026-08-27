import Solcore.Core.Syntax
import Solcore.Foundation.FixedHex
import Solcore.Foundation.FixedRadix

set_option autoImplicit false

namespace Solcore.Semantics

/-- An ordered runtime sequence of octets. -/
abbrev Bytes := ByteArray

/-- The number of distinct unsigned runtime addresses. -/
def addressModulus : Nat := 2 ^ 160

/-- An unsigned 160-bit runtime address. -/
abbrev Address := Fin addressModulus

namespace RuntimeScalar.Internal

open Solcore.Foundation

private theorem addressHexModulus : addressModulus = 16 ^ 40 := by decide

def addressHexValue (value : Address) : FixedHex.Value 40 :=
  Fin.cast addressHexModulus value

def addressOfHexValue (value : FixedHex.Value 40) : Address :=
  Fin.cast addressHexModulus.symm value

private theorem wordHexModulus : Core.wordModulus = 16 ^ 64 := by decide

def wordHexValue (value : Core.Word) : FixedHex.Value 64 :=
  Fin.cast wordHexModulus value

def wordOfHexValue (value : FixedHex.Value 64) : Core.Word :=
  Fin.cast wordHexModulus.symm value

/-- View one octet as the fixed-width pair of hexadecimal digits it owns. -/
def byteHexValue (byte : UInt8) : FixedHex.Value 2 :=
  byte.toFin

def encodeByteDigits (byte : UInt8) : List FixedHex.Digit :=
  (FixedRadix.encode 16 2 (by decide) (byteHexValue byte)).toList

def decodeByteDigits (high low : FixedHex.Digit) : UInt8 :=
  let digits : FixedHex.Digits 2 := #v[high, low]
  UInt8.ofFin (FixedRadix.decode digits)

def encodeBytesDigits : List UInt8 → List FixedHex.Digit
  | [] => []
  | byte :: bytes => encodeByteDigits byte ++ encodeBytesDigits bytes

def decodeBytesDigits? : List FixedHex.Digit → Option (List UInt8)
  | [] => some []
  | [_] => none
  | high :: low :: digits => do
      let bytes ← decodeBytesDigits? digits
      some (decodeByteDigits high low :: bytes)

private theorem wordByteModulus : Core.wordModulus = 256 ^ 32 := by decide

def wordByteValue (value : Core.Word) : FixedRadix.Value 256 32 :=
  Fin.cast wordByteModulus value

def wordOfByteValue (value : FixedRadix.Value 256 32) : Core.Word :=
  Fin.cast wordByteModulus.symm value

def wordByteDigits (value : Core.Word) : FixedRadix.Digits 256 32 :=
  FixedRadix.encode 256 32 (by decide) (wordByteValue value)

def bytesOfWordDigits (digits : FixedRadix.Digits 256 32) : ByteArray :=
  ⟨digits.toArray.map UInt8.ofFin⟩

def wordDigitsOfBytes? (bytes : ByteArray) :
    Option (FixedRadix.Digits 256 32) :=
  if lengthEq : bytes.size = 32 then
    some ⟨bytes.data.map UInt8.toFin, by simpa using lengthEq⟩
  else
    none

end RuntimeScalar.Internal

open Solcore.Foundation

/-- Encode bytes with a strict `0x` prefix and two lowercase digits per byte. -/
def encodeBytesText (value : Bytes) : String :=
  FixedHex.encodeDigitsText
    (RuntimeScalar.Internal.encodeBytesDigits value.data.toList)

/-- Decode only the canonical prefixed, lowercase, even-width byte spelling. -/
def decodeBytesText? (text : String) : Option Bytes := do
  let digits ← FixedHex.decodeDigitsText? text
  let bytes ← RuntimeScalar.Internal.decodeBytesDigits? digits
  some bytes.toByteArray

/-- Encode an address as exactly 40 lowercase hexadecimal digits after `0x`. -/
def encodeAddressText (value : Address) : String :=
  FixedHex.encodeText (RuntimeScalar.Internal.addressHexValue value)

/-- Decode only the canonical fixed-width address spelling. -/
def decodeAddressText? (text : String) : Option Address :=
  (FixedHex.decodeText? 40 text).map RuntimeScalar.Internal.addressOfHexValue

/-- Encode a Core word as exactly 64 lowercase hexadecimal digits after `0x`. -/
def encodeWordText (value : Core.Word) : String :=
  FixedHex.encodeText (RuntimeScalar.Internal.wordHexValue value)

/-- Decode only the canonical fixed-width Core word spelling. -/
def decodeWordText? (text : String) : Option Core.Word :=
  (FixedHex.decodeText? 64 text).map RuntimeScalar.Internal.wordOfHexValue

/-- Encode a Core word as exactly 32 most-significant-byte-first octets. -/
def encodeWordBytesBE (value : Core.Word) : ByteArray :=
  RuntimeScalar.Internal.bytesOfWordDigits
    (RuntimeScalar.Internal.wordByteDigits value)

/-- Decode a Core word only from an exact 32-byte big-endian representation. -/
def decodeWordBytesBE? (bytes : ByteArray) : Option Core.Word := do
  let digits ← RuntimeScalar.Internal.wordDigitsOfBytes? bytes
  some (RuntimeScalar.Internal.wordOfByteValue (FixedRadix.decode digits))

end Solcore.Semantics
