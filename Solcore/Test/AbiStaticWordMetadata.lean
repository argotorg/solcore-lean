import Solcore.Abi.StaticWordMetadata

/-! External consumers for Static Word ABI names, metadata, and selectors. -/

set_option autoImplicit false

namespace Tests

open Solcore.Abi.V1

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def bytes (values : List UInt8) : ByteArray :=
  values.toByteArray

private def fName : MethodName :=
  ⟨"f", by decide⟩

private def fooName : MethodName :=
  ⟨"foo", by decide⟩

private def fMetadata : MethodMetadata :=
  .staticWord fName

private def fooMetadata : MethodMetadata :=
  .staticWord fooName

private def fSelectorBytes : ByteArray :=
  bytes [0xb3, 0xde, 0x64, 0x8b]

private def fooSelectorBytes : ByteArray :=
  bytes [0x2f, 0xbe, 0xbd, 0x38]

private def transferSelectorBytes : ByteArray :=
  bytes [0xa9, 0x05, 0x9c, 0xbb]

private theorem compileTimeCanonicalSignature :
    fMetadata.canonicalSignatureBytes = "f(uint256)".toUTF8 := by
  native_decide

private theorem compileTimeCanonicalTypes :
    fMetadata.inputType = .uint256 ∧
      fMetadata.outputType = .uint256 := by
  decide

private theorem compileTimeSelectorPrefix :
    fMetadata.selector.encode = fSelectorBytes := by
  native_decide

private theorem compileTimeAsciiBoundary :
    isValidMethodName "A_09z" = true ∧
      isValidMethodName "9bad" = false ∧
      isValidMethodName "aβ" = false := by
  native_decide

private def testMethodNames : IO Unit := do
  let accepted := ["f", "_", "A_09z", "snake_case2"]
  let rejected := ["", "9bad", "has-dash", "aβ", "é", "$bad"]
  assertTrue
    (accepted.all fun text => (validateMethodName? text).isSome)
    "Static Word method names must accept the complete ASCII identifier grammar"
  assertTrue
    (rejected.all fun text => (validateMethodName? text).isNone)
    "Static Word method names must reject empty, malformed, and non-ASCII spellings"

private def testCanonicalMetadata : IO Unit := do
  assertTrue
    (fMetadata.canonicalSignatureText == "f(uint256)" &&
      fMetadata.canonicalSignatureBytes == "f(uint256)".toUTF8)
    "canonical signatures must spell the explicit input type exactly"
  assertTrue
    (fMetadata.inputType == .uint256 && fMetadata.outputType == .uint256)
    "metadata must retain both the input and output types"

private def testKnownSelectors : IO Unit := do
  assertTrue (fMetadata.selector.encode == fSelectorBytes)
    "f(uint256) must have selector b3de648b"
  assertTrue (fooMetadata.selector.encode == fooSelectorBytes)
    "foo(uint256) must have selector 2fbebd38"
  assertTrue
    ((selectorFromSignatureBytes
      "transfer(address,uint256)".toUTF8).encode == transferSelectorBytes)
    "raw canonical signature bytes must produce transfer selector a9059cbb"
  assertTrue (fMetadata.selector.toFin.val == 0xb3de648b)
    "the Fin (2^32) selector view must use big-endian byte order"

private def testSelectorCodec : IO Unit := do
  let selector := fMetadata.selector
  assertTrue (Selector.decode? selector.encode == some selector)
    "an exact four-byte selector must round-trip"
  assertTrue ((Selector.decode? (bytes [0xb3, 0xde, 0x64])).isNone)
    "selector decoding must reject three bytes"
  assertTrue
    ((Selector.decode? (bytes [0xb3, 0xde, 0x64, 0x8b, 0])).isNone)
    "selector decoding must reject five bytes"

def testAbiStaticWordMetadata : IO Unit := do
  testMethodNames
  testCanonicalMetadata
  testKnownSelectors
  testSelectorCodec

end Tests
