import Solcore.Semantics.AddressBytesBE
import Solcore.Semantics.AddressWordBridge

/-! Executable boundary tests for exact 20-byte big-endian addresses. -/

set_option autoImplicit false

namespace Tests

open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def bytes (values : List UInt8) : ByteArray :=
  values.toByteArray

private def addressZero : Address := ⟨0, by decide⟩
private def addressOne : Address := ⟨1, by decide⟩
private def addressMiddle : Address := ⟨0x123456789abcdef, by decide⟩
private def addressMaximum : Address := ⟨addressModulus - 1, by decide⟩

private def representativeAddresses : List Address :=
  [addressZero, addressOne, addressMiddle, addressMaximum]

private def zeroBytes : ByteArray :=
  bytes (List.replicate 20 0)

private def oneBytes : ByteArray :=
  bytes (List.replicate 19 0 ++ [1])

private def maximumBytes : ByteArray :=
  bytes (List.replicate 20 0xff)

private def nineteenBytes : ByteArray :=
  bytes (List.replicate 19 0)

private def twentyOneBytes : ByteArray :=
  bytes (List.replicate 21 0)

def testAddressBytesBE : IO Unit := do
  assertTrue (encodeAddressBytesBE addressZero == zeroBytes)
    "zero address encoding must contain exactly twenty zero octets"
  assertTrue (encodeAddressBytesBE addressOne == oneBytes)
    "address one encoding must preserve nineteen leading zero octets"
  assertTrue (encodeAddressBytesBE addressMaximum == maximumBytes)
    "maximum address encoding must contain exactly twenty 0xff octets"
  assertTrue (decodeAddressBytesBE? zeroBytes == some addressZero)
    "twenty zero octets must decode as the zero address"
  assertTrue (decodeAddressBytesBE? oneBytes == some addressOne)
    "nineteen zero octets followed by one must decode as address one"
  assertTrue (decodeAddressBytesBE? maximumBytes == some addressMaximum)
    "twenty 0xff octets must decode as the maximum address"
  assertTrue (decodeAddressBytesBE? nineteenBytes == none)
    "strict address decoding must reject nineteen bytes"
  assertTrue (decodeAddressBytesBE? twentyOneBytes == none)
    "strict address decoding must reject twenty-one bytes"
  assertTrue
    (representativeAddresses.all fun address =>
      decodeAddressBytesBE? (encodeAddressBytesBE address) == some address)
    "zero, one, a middle address, and the maximum must round-trip through exact bytes"
  assertTrue
    (representativeAddresses.all fun address =>
      let addressBytes := encodeAddressBytesBE address
      let wordBytes := encodeWordBytesBE (addressToWord address)
      addressBytes.size == 20 && wordBytes.size == 32 &&
        (List.range 20).all (fun index =>
          addressBytes.data[index]? == wordBytes.data[index + 12]?))
    "every representative address byte must match its widened word at offset twelve"

end Tests
