import Solcore.Abi.Keccak256

/-! Runtime known-answer tests for Ethereum-compatible Keccak-256. -/

set_option autoImplicit false

namespace Tests

open Solcore.Abi.V1
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def assertDigest
    (label : String) (input : Bytes) (expected : String) : IO Unit := do
  let digest := Keccak256.hash input
  assertTrue (digest.size == 32)
    (label ++ " must produce exactly 32 bytes")
  assertTrue (encodeBytesText digest == expected)
    (label ++ " must match its independent Keccak-256 vector")

private def assertTextDigest
    (text expected : String) : IO Unit :=
  assertDigest text text.toByteArray expected

private def sequentialBytes (count : Nat) : Bytes :=
  ((List.range count).map UInt8.ofNat).toByteArray

def testAbiKeccak256 : IO Unit := do
  assertTextDigest ""
    "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
  assertTextDigest "abc"
    "0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

  -- Complete digests retain the selector as their first four bytes.
  assertTextDigest "f(uint256)"
    "0xb3de648b001c08ab857afe5a9633887e7a4e2a429d1d8d4231238c1ffaeb256f"
  assertTextDigest "foo(uint256)"
    "0x2fbebd3821c4e005fbe0a9002cc1bd25dc266d788dba1dbcb39cc66a07e7b38b"
  assertTextDigest "transfer(address,uint256)"
    "0xa9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b"

  -- Inputs are the octets 0x00 through 0x86, 0x87, or 0x88 respectively.
  -- These straddle the 136-byte Keccak rate and exercise both padding forms.
  assertDigest "135-byte rate predecessor" (sequentialBytes 135)
    "0xcbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62"
  assertDigest "136-byte full rate block" (sequentialBytes 136)
    "0x7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e"
  assertDigest "137-byte rate successor" (sequentialBytes 137)
    "0xac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db"

end Tests
