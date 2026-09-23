import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.AddressBytesBE

/-! Executable coherence tests for canonical address text and exact bytes. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def bytes (values : List UInt8) : ByteArray :=
  values.toByteArray

private def addressZero : Address := ⟨0, by decide⟩
private def addressOne : Address := ⟨1, by decide⟩
private def addressMiddle : Address := ⟨0x123456789abcdef, by decide⟩
private def addressMaximum : Address := ⟨addressModulus - 1, by decide⟩

private def nineteenBytes : ByteArray :=
  bytes ([0x12] ++ List.replicate 17 0 ++ [0x34])

private def twentyBytes : ByteArray :=
  bytes ([0x12] ++ List.replicate 18 0 ++ [0x34])

private def twentyOneBytes : ByteArray :=
  bytes ([0x12] ++ List.replicate 19 0 ++ [0x34])

private def directAndByteMediated (text : String) : Option Address × Option Address :=
  (decodeAddressText? text, (decodeBytesText? text).bind decodeAddressBytesBE?)

private def canonicalByteTextAgrees (value : ByteArray) : Bool :=
  let text := encodeBytesText value
  decodeAddressText? text == decodeAddressBytesBE? value

private def decoderFixtures : List (String × String) :=
  [ ("canonical zero", encodeAddressText addressZero)
  , ("canonical middle", encodeAddressText addressMiddle)
  , ("uppercase", "0x00000000000000000000000000000000000000AB")
  , ("odd width", "0x0")
  , ("wrong width", "0x000000000000000000000000000000000000000")
  ]

private def firstDecoderMismatch? : Option String :=
  (decoderFixtures.find? fun fixture =>
    let paths := directAndByteMediated fixture.2
    paths.1 != paths.2).map Prod.fst

def testAddressCodecCoherence : IO Unit := do
  assertTrue
    (encodeBytesText (encodeAddressBytesBE addressZero) == encodeAddressText addressZero)
    "zero address text must equal the text of its exact byte encoding"
  assertTrue
    (encodeBytesText (encodeAddressBytesBE addressOne) == encodeAddressText addressOne)
    "address one text must preserve leading zeros across the byte codec"
  assertTrue
    (encodeBytesText (encodeAddressBytesBE addressMiddle) == encodeAddressText addressMiddle)
    "middle address text must equal the text of its exact byte encoding"
  assertTrue
    (encodeBytesText (encodeAddressBytesBE addressMaximum) == encodeAddressText addressMaximum)
    "maximum address text must equal the text of its exact byte encoding"
  assertTrue (canonicalByteTextAgrees nineteenBytes)
    "canonical text for an independent nineteen-byte value must agree on rejection"
  assertTrue (canonicalByteTextAgrees twentyBytes)
    "canonical text for an independent twenty-byte value must agree on decoding"
  assertTrue (canonicalByteTextAgrees twentyOneBytes)
    "canonical text for an independent twenty-one-byte value must agree on rejection"
  assertTrue firstDecoderMismatch?.isNone
    s!"direct and byte-mediated address decoding disagree for {firstDecoderMismatch?.getD "unknown fixture"}"

end Tests
