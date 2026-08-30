import Solcore.Abi.StaticWordCodec
/-! External boundary consumers for the Static Word ABI byte codecs. -/
set_option autoImplicit false
namespace Tests
open Solcore
open Solcore.Abi.V1
open Solcore.Semantics
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def fSelector : Selector :=
  ⟨#v[0xb3, 0xde, 0x64, 0x8b]⟩
private def argument : Core.Word :=
  ⟨0x123, by decide⟩
private def expectedCall : StaticWordCall :=
  ⟨fSelector, argument⟩
private def canonicalCalldata : Bytes :=
  ([0xb3, 0xde, 0x64, 0x8b] ++
    List.replicate 30 (0 : UInt8) ++ [0x01, 0x23]).toByteArray

private def calldata35 : Bytes :=
  canonicalCalldata.extract 0 35
private def calldata37 : Bytes :=
  canonicalCalldata.append [0xff].toByteArray
private def returndata31 : Bytes :=
  (List.replicate 31 (0 : UInt8)).toByteArray
private def returndata33 : Bytes :=
  (encodeResult argument).append [0xff].toByteArray

private theorem canonicalCalldata_eq :
    canonicalCalldata = encodeCall fSelector argument := by
  native_decide

private theorem compileTimeCallBoundaries :
    encodeCall fSelector argument = canonicalCalldata ∧
      decodeCall calldata35 = .error (.shortCalldata 35) ∧
      decodeCall canonicalCalldata = .ok expectedCall ∧
      decodeCall calldata37 = .ok expectedCall := by
  refine ⟨canonicalCalldata_eq.symm, ?_, ?_, ?_⟩
  · apply (decodeCall_eq_shortCalldata_iff calldata35).2
    native_decide
  · rw [canonicalCalldata_eq]
    exact decodeCall_encode fSelector argument
  · unfold calldata37
    rw [canonicalCalldata_eq]
    exact decodeCall_encode_append fSelector argument _

private theorem compileTimeResultBoundaries :
    decodeResult returndata31 = .error (.invalidLength 31) ∧
      decodeResult (encodeResult argument) = .ok argument ∧
      decodeResult returndata33 = .error (.invalidLength 33) := by
  refine ⟨?_, decodeResult_encode argument, ?_⟩
  · apply (decodeResult_eq_invalidLength_iff returndata31).2
    native_decide
  · have invalid := (decodeResult_eq_invalidLength_iff returndata33).2
      (by native_decide)
    simpa [returndata33, resultSize] using invalid

private theorem compileTimeCallFailureDisjoint :
    decodeCall calldata35 ≠ .ok expectedCall := by
  apply decodeCall_failure_ne_success calldata35 (.shortCalldata 35)
  exact compileTimeCallBoundaries.2.1

private theorem compileTimeResultFailureDisjoint :
    decodeResult returndata31 ≠ .ok argument := by
  apply decodeResult_failure_ne_success returndata31 (.invalidLength 31)
  exact compileTimeResultBoundaries.1

private def matchesCall (result : Except CallDecodeFailure StaticWordCall) : Bool :=
  match result with | .ok call => call == expectedCall | _ => false

private def matchesCallFailure (result : Except CallDecodeFailure StaticWordCall) : Bool :=
  match result with | .error (.shortCalldata size) => size == 35 | _ => false

private def matchesResult (result : Except ResultDecodeFailure Core.Word) : Bool :=
  match result with | .ok word => word == argument | _ => false

private def matchesResultFailure
    (size : Nat) (result : Except ResultDecodeFailure Core.Word) : Bool :=
  match result with | .error (.invalidLength actual) => actual == size | _ => false

def testAbiStaticWordCodec : IO Unit := do
  assertTrue (encodeCall fSelector argument == canonicalCalldata)
    "calldata must be the exact selector followed by one big-endian word"
  assertTrue (canonicalCalldata.size == 36)
    "canonical calldata must contain exactly 36 bytes"
  assertTrue (matchesCallFailure (decodeCall calldata35))
    "35-byte calldata must report its structured short-calldata failure"
  assertTrue (matchesCall (decodeCall canonicalCalldata))
    "36-byte calldata must round-trip its selector and argument"
  assertTrue (matchesCall (decodeCall calldata37))
    "a suffix after the 36-byte call prefix must be ignored"

  assertTrue (matchesResultFailure 31 (decodeResult returndata31))
    "31-byte returndata must fail strict result decoding"
  assertTrue (matchesResult (decodeResult (encodeResult argument)))
    "32-byte returndata must round-trip its word"
  assertTrue (matchesResultFailure 33 (decodeResult returndata33))
    "33-byte returndata must fail strict result decoding"

end Tests
