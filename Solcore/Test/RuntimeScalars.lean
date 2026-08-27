import Solcore.Core.Primitive
import Solcore.Core.Wire
import Solcore.Core.Wire.V2
import Solcore.Semantics.RuntimeScalars

/-! Executable boundary tests for canonical runtime scalar encodings. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def bytes (values : List UInt8) : ByteArray :=
  values.toByteArray

private def repeated (count : Nat) (digit : Char) : String :=
  String.ofList (List.replicate count digit)

private def acceptedCanonical {α : Type}
    (decode : String → Option α) (encode : α → String) (text : String) : Bool :=
  match decode text with
  | some value => encode value == text
  | none => false

private def addressMaximum : Address :=
  ⟨addressModulus - 1, by decide⟩

private def word (value : Nat) : Word :=
  Word.ofNatModulo value

private def testBytesText : IO Unit := do
  let empty := bytes []
  let zero := bytes [0]
  let maximum := bytes [0xff]
  let multiple := bytes [0x12, 0x34, 0xab]
  let padded := bytes [0, 0x12, 0]
  let cases := [empty, zero, maximum, multiple, padded]
  assertTrue (encodeBytesText empty == "0x")
    "empty bytes must encode as the prefix alone"
  assertTrue
    (encodeBytesText zero == "0x00" &&
      encodeBytesText maximum == "0xff")
    "byte endpoint encodings must use two lowercase digits"
  assertTrue (encodeBytesText multiple == "0x1234ab")
    "multiple bytes must retain their order in hexadecimal text"
  assertTrue (encodeBytesText padded == "0x001200")
    "byte text must retain leading and trailing zero octets"
  assertTrue
    (cases.all fun value => decodeBytesText? (encodeBytesText value) == some value)
    "canonical byte text must round-trip every representative value"
  assertTrue
    (acceptedCanonical decodeBytesText? encodeBytesText "0x0012ff00")
    "accepted byte text must re-encode to its identical canonical spelling"
  let rejected := ["00", "0X00", "0xFF", "0x0g", "0x0"]
  assertTrue (rejected.all fun text => (decodeBytesText? text).isNone)
    "byte text must reject missing or altered prefixes, uppercase, non-hex, and odd width"

private def testAddressText : IO Unit := do
  let zero : Address := ⟨0, by decide⟩
  let one : Address := ⟨1, by decide⟩
  let values := [zero, one, addressMaximum]
  let zeros := repeated 40 '0'
  let maximum := repeated 40 'f'
  assertTrue (encodeAddressText zero == "0x" ++ zeros)
    "zero address must encode as exactly forty zero digits"
  assertTrue (encodeAddressText one == "0x" ++ repeated 39 '0' ++ "1")
    "address one must be left-padded to forty digits"
  assertTrue (encodeAddressText addressMaximum == "0x" ++ maximum)
    "maximum address must encode as forty lowercase f digits"
  assertTrue
    (values.all fun value => decodeAddressText? (encodeAddressText value) == some value)
    "canonical address text must round-trip endpoint values"
  assertTrue
    (acceptedCanonical decodeAddressText? encodeAddressText
      ("0x" ++ repeated 38 '0' ++ "12"))
    "accepted address text must re-encode to its identical canonical spelling"
  let wrongWidths := ["0x" ++ repeated 39 '0', "0x" ++ repeated 41 '0']
  assertTrue (wrongWidths.all fun text => (decodeAddressText? text).isNone)
    "address text must reject both thirty-nine and forty-one digits"
  let malformed := [
    zeros,
    "0X" ++ zeros,
    "0x" ++ repeated 39 '0' ++ "F",
    "0x" ++ repeated 39 '0' ++ "g"
  ]
  assertTrue (malformed.all fun text => (decodeAddressText? text).isNone)
    "address text must reject missing or altered prefixes, uppercase, and non-hex digits"

private def testWordText : IO Unit := do
  let zero := Word.zero
  let one := word 1
  let values := [zero, one, Word.maximum]
  let zeros := repeated 64 '0'
  let maximum := repeated 64 'f'
  assertTrue (encodeWordText zero == "0x" ++ zeros)
    "zero word must encode as exactly sixty-four zero digits"
  assertTrue (encodeWordText one == "0x" ++ repeated 63 '0' ++ "1")
    "word one must be left-padded to sixty-four digits"
  assertTrue (encodeWordText Word.maximum == "0x" ++ maximum)
    "maximum word must encode as sixty-four lowercase f digits"
  assertTrue
    (values.all fun value => decodeWordText? (encodeWordText value) == some value)
    "canonical word text must round-trip endpoint values"
  assertTrue
    (acceptedCanonical decodeWordText? encodeWordText
      ("0x" ++ repeated 62 '0' ++ "12"))
    "accepted word text must re-encode to its identical canonical spelling"
  let wrongWidths := ["0x" ++ repeated 63 '0', "0x" ++ repeated 65 '0']
  assertTrue (wrongWidths.all fun text => (decodeWordText? text).isNone)
    "word text must reject both sixty-three and sixty-five digits"
  let malformed := [
    zeros,
    "0X" ++ zeros,
    "0x" ++ repeated 63 '0' ++ "F",
    "0x" ++ repeated 63 '0' ++ "g"
  ]
  assertTrue (malformed.all fun text => (decodeWordText? text).isNone)
    "word text must reject missing or altered prefixes, uppercase, and non-hex digits"

private def testWordBytesBE : IO Unit := do
  let marker := word (0xaa * 2 ^ 248 + 0x1122)
  let encoded := encodeWordBytesBE marker
  let expected := bytes ([0xaa] ++ List.replicate 29 0 ++ [0x11, 0x22])
  assertTrue (encoded.size == 32)
    "big-endian word encoding must contain exactly thirty-two bytes"
  assertTrue (encoded == expected)
    "big-endian word encoding must match the complete independent byte fixture"
  assertTrue
    (encoded.data[0]? == some (0xaa : UInt8) &&
      encoded.data[30]? == some (0x11 : UInt8) &&
      encoded.data[31]? == some (0x22 : UInt8))
    "big-endian word encoding must place the most significant and final bytes correctly"
  assertTrue
    (encoded.data[0]?.map (fun byte => word byte.toNat) == some ((word 0).byteAt marker) &&
      encoded.data[30]?.map (fun byte => word byte.toNat) == some ((word 30).byteAt marker) &&
      encoded.data[31]?.map (fun byte => word byte.toNat) == some ((word 31).byteAt marker))
    "big-endian byte positions must agree directly with executable word byte selection"
  assertTrue
    (match decodeWordBytesBE? expected with
    | some value => encodeWordBytesBE value == expected
    | none => false)
    "accepted big-endian bytes must re-encode to their identical canonical sequence"
  let values := [Word.zero, word 1, marker, Word.maximum]
  assertTrue
    (values.all fun value =>
      decodeWordBytesBE? (encodeWordBytesBE value) == some value)
    "big-endian word bytes must round-trip representative values"
  let wrongWidths := [
    bytes (List.replicate 31 0),
    bytes (List.replicate 33 0)
  ]
  assertTrue (wrongWidths.all fun value => (decodeWordBytesBE? value).isNone)
    "big-endian word decoding must reject both thirty-one and thirty-three bytes"

private def testFrozenWireCompatibility : IO Unit := do
  let values := [Word.zero, word 1, word 0x1122, Word.maximum]
  assertTrue
    (values.all fun value =>
      Solcore.Core.Wire.V1.encodeWordText value == encodeWordText value)
    "runtime word text must match frozen Wire V1 for zero, one, 0x1122, and maximum"
  assertTrue
    (values.all fun value =>
      Solcore.Core.Wire.V2.encodeWordText value == encodeWordText value)
    "runtime word text must match frozen Wire V2 for zero, one, 0x1122, and maximum"

def testRuntimeScalars : IO Unit := do
  testBytesText
  testAddressText
  testWordText
  testWordBytesBE
  testFrozenWireCompatibility

end Tests
