import Solcore.Abi.StaticWordMetadata
import Solcore.ContractRuntime.RuntimeScalars.WordBytesProperties

/-! Exact calldata and returndata codecs for the Static Word ABI profile. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Foundation
open Solcore.ContractRuntime

/-- A decoded `uint256 -> uint256` call, before selector admission. -/
structure StaticWordCall where
  selector : Selector
  argument : Core.Word
  deriving Repr, BEq, DecidableEq

/-- The sole low-level call decoding failure: the fixed prefix is incomplete. -/
inductive CallDecodeFailure where
  | shortCalldata (actualSize : Nat)
  deriving Repr, BEq, DecidableEq

/-- Strict returndata rejects every width other than one ABI word. -/
inductive ResultDecodeFailure where
  | invalidLength (actualSize : Nat)
  deriving Repr, BEq, DecidableEq

def callSize : Nat := 36

def resultSize : Nat := 32

/-- Canonical calldata is the exact selector followed by one big-endian word. -/
def encodeCall (selector : Selector) (argument : Core.Word) : Bytes :=
  selector.encode.append (encodeWordBytesBE argument)

/-- Canonical returndata is one exact big-endian word. -/
def encodeResult (result : Core.Word) : Bytes :=
  encodeWordBytesBE result

private def selectorOfExactBytes
    (bytes : Bytes) (width : bytes.size = 4) : Selector :=
  ⟨⟨bytes.data, by simpa using width⟩⟩

private def wordOfExactBytes
    (bytes : Bytes) (width : bytes.size = 32) : Core.Word :=
  RuntimeScalar.Internal.wordOfByteValue
    (FixedRadix.decode
      ⟨bytes.data.map UInt8.toFin, by simpa using width⟩)

private theorem selectorOfExactBytes_encode (selector : Selector) :
    selectorOfExactBytes selector.encode selector.encode_size = selector := by
  cases selector
  rfl

private theorem selectorOfExactBytes_eq_of_eq
    (bytes : Bytes) (width : bytes.size = 4) (selector : Selector)
    (selected : bytes = selector.encode) :
    selectorOfExactBytes bytes width = selector := by
  subst bytes
  exact selectorOfExactBytes_encode selector

private theorem decodeWordBytesBE?_wordOfExactBytes
    (bytes : Bytes) (width : bytes.size = 32) :
    decodeWordBytesBE? bytes = some (wordOfExactBytes bytes width) := by
  unfold decodeWordBytesBE? RuntimeScalar.Internal.wordDigitsOfBytes?
  rw [dif_pos width]
  rfl

private theorem wordOfExactBytes_encode (word : Core.Word) :
    wordOfExactBytes (encodeWordBytesBE word) (encodeWordBytesBE_size word) =
      word := by
  have decoded := decodeWordBytesBE?_wordOfExactBytes
    (encodeWordBytesBE word) (encodeWordBytesBE_size word)
  rw [decodeWordBytesBE?_encodeWordBytesBE] at decoded
  exact Option.some.inj decoded |>.symm

private theorem wordOfExactBytes_eq_of_eq
    (bytes : Bytes) (width : bytes.size = 32) (word : Core.Word)
    (selected : bytes = encodeWordBytesBE word) :
    wordOfExactBytes bytes width = word := by
  subst bytes
  exact wordOfExactBytes_encode word

/-- Decode the fixed 36-byte prefix and deliberately ignore any suffix. -/
def decodeCall (calldata : Bytes) :
    Except CallDecodeFailure StaticWordCall :=
  if short : calldata.size < callSize then
    .error (.shortCalldata calldata.size)
  else
    let selectorBytes := calldata.extract 0 4
    let argumentBytes := calldata.extract 4 36
    have selectorWidth : selectorBytes.size = 4 := by
      simp only [selectorBytes, ByteArray.size_extract, callSize] at short ⊢
      omega
    have argumentWidth : argumentBytes.size = 32 := by
      simp only [argumentBytes, ByteArray.size_extract, callSize] at short ⊢
      omega
    .ok {
      selector := selectorOfExactBytes selectorBytes selectorWidth
      argument := wordOfExactBytes argumentBytes argumentWidth
    }

/-- Decode returndata only at the exact one-word width. -/
def decodeResult (returndata : Bytes) :
    Except ResultDecodeFailure Core.Word :=
  if width : returndata.size = resultSize then
    .ok (wordOfExactBytes returndata width)
  else
    .error (.invalidLength returndata.size)

@[simp] theorem encodeCall_size (selector : Selector) (argument : Core.Word) :
    (encodeCall selector argument).size = callSize := by
  simp [encodeCall, callSize]

@[simp] theorem encodeResult_size (result : Core.Word) :
    (encodeResult result).size = resultSize := by
  simp [encodeResult, resultSize]

@[simp] theorem decodeCall_encode
    (selector : Selector) (argument : Core.Word) :
    decodeCall (encodeCall selector argument) =
      .ok ⟨selector, argument⟩ := by
  simp [decodeCall, encodeCall, callSize,
    ByteArray.extract_append_eq_left,
    ByteArray.extract_append_eq_right,
    selectorOfExactBytes_encode, wordOfExactBytes_encode]

/-- Additional calldata does not change the decoded fixed call prefix. -/
@[simp] theorem decodeCall_encode_append
    (selector : Selector) (argument : Core.Word) (suffix : Bytes) :
    decodeCall ((encodeCall selector argument).append suffix) =
      .ok ⟨selector, argument⟩ := by
  have selectorExtract :
      ((encodeCall selector argument).append suffix).extract 0 4 =
        selector.encode := by
    unfold encodeCall
    rw [show
      (selector.encode.append (encodeWordBytesBE argument)).append suffix =
        selector.encode.append ((encodeWordBytesBE argument).append suffix) from
      ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left selector.encode_size.symm
  have argumentExtract :
      ((encodeCall selector argument).append suffix).extract 4 36 =
        encodeWordBytesBE argument := by
    unfold encodeCall
    rw [show
      (selector.encode.append (encodeWordBytesBE argument)).append suffix =
        selector.encode.append ((encodeWordBytesBE argument).append suffix) from
      ByteArray.append_assoc]
    calc
      _ = ((encodeWordBytesBE argument).append suffix).extract 0 32 := by
        simpa using
          (ByteArray.extract_append_size_add
            (a := selector.encode)
            (b := (encodeWordBytesBE argument).append suffix)
            (i := 0) (j := 32))
      _ = encodeWordBytesBE argument :=
        ByteArray.extract_append_eq_left
          (encodeWordBytesBE_size argument).symm
  unfold decodeCall
  rw [dif_neg (by simp [encodeCall, callSize])]
  dsimp only
  rw [selectorOfExactBytes_eq_of_eq _ _ _ selectorExtract,
    wordOfExactBytes_eq_of_eq _ _ _ argumentExtract]

@[simp] theorem decodeResult_encode (result : Core.Word) :
    decodeResult (encodeResult result) = .ok result := by
  simp [decodeResult, encodeResult, resultSize, wordOfExactBytes_encode]

theorem decodeCall_eq_shortCalldata_iff (calldata : Bytes) :
    decodeCall calldata = .error (.shortCalldata calldata.size) ↔
      calldata.size < callSize := by
  unfold decodeCall
  split <;> simp_all

theorem decodeResult_eq_invalidLength_iff (returndata : Bytes) :
    decodeResult returndata = .error (.invalidLength returndata.size) ↔
      returndata.size ≠ resultSize := by
  unfold decodeResult
  split <;> simp_all

theorem decodeCall_failure_ne_success
    (calldata : Bytes) (failure : CallDecodeFailure) (call : StaticWordCall)
    (failed : decodeCall calldata = .error failure) :
    decodeCall calldata ≠ .ok call := by
  rw [failed]
  simp

theorem decodeResult_failure_ne_success
    (returndata : Bytes) (failure : ResultDecodeFailure) (result : Core.Word)
    (failed : decodeResult returndata = .error failure) :
    decodeResult returndata ≠ .ok result := by
  rw [failed]
  simp

end Solcore.Abi.V1
