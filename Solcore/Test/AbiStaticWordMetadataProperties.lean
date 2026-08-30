import Solcore.Abi.StaticWordMetadataProperties

/-! External compile consumers for Static Word ABI metadata proof contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Abi.V1
open Solcore.Semantics

private theorem compileTimeKeccakWidth (input : Bytes) :
    (Keccak256.hash input).size = 32 :=
  Keccak256.hash_size input

private theorem compileTimeValidatorSuccessIff (text : String) :
    (validateMethodName? text).isSome ↔
      isValidMethodName text = true :=
  validateMethodName?_isSome_iff text

private theorem compileTimeValidatorTextSeal
    {text : String} {name : MethodName}
    (success : validateMethodName? text = some name) :
    name.text = text :=
  validateMethodName?_success_text success

private theorem compileTimeValidatorConstructorIff
    (text : String) (name : MethodName) :
    validateMethodName? text = some name ↔ name.text = text :=
  validateMethodName?_eq_some_iff text name

private theorem compileTimeSelectorDecodeInverse
    {bytes : Bytes} {selector : Selector}
    (success : Selector.decode? bytes = some selector) :
    selector.encode = bytes :=
  Selector.encode_of_decode?_eq_some success

private theorem compileTimeSelectorCodecIff
    (bytes : Bytes) (selector : Selector) :
    Selector.decode? bytes = some selector ↔
      bytes = selector.encode :=
  Selector.decode?_eq_some_iff bytes selector

private theorem compileTimeSelectorDigestPrefix (signature : Bytes) :
    (selectorFromSignatureBytes signature).encode =
      (Keccak256.hash signature).extract 0 4 :=
  selectorFromSignatureBytes_encode signature

private theorem compileTimeSelectorBigEndian (selector : Selector) :
    selector.toUInt32 =
        ((selector.bytes[0].toUInt32 <<< 8 |||
            selector.bytes[1].toUInt32) <<< 8 |||
          selector.bytes[2].toUInt32) <<< 8 |||
        selector.bytes[3].toUInt32 ∧
      selector.toFin.val =
        (((selector.bytes[0].toUInt32 <<< 8 |||
            selector.bytes[1].toUInt32) <<< 8 |||
          selector.bytes[2].toUInt32) <<< 8 |||
        selector.bytes[3].toUInt32).toNat := by
  exact ⟨selector.toUInt32_eq_bigEndianBytes,
    selector.toFin_val_eq_bigEndianBytes⟩

/-- All checks in this module are elaboration-time proof consumers. -/
def testAbiStaticWordMetadataProperties : IO Unit :=
  pure ()

end Tests
