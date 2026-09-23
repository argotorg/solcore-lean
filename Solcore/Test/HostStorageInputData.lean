import Solcore.Core.Primitive
import Solcore.ContractRuntime.HostStorageInputData

/-! Executable boundary tests for bounded run input bytes. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.HostStorageDriver

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def word (value : Nat) : Word :=
  Word.ofNatModulo value

private def emptyInput : InputData := {
  bytes := [].toByteArray
  size_lt_wordModulus := by decide
}

private def representativeInput : InputData := {
  bytes := [0x12, 0x00, 0xab, 0xff].toByteArray
  size_lt_wordModulus := by decide
}

private def singletonInput : InputData := {
  bytes := [0x7f].toByteArray
  size_lt_wordModulus := by decide
}

private def zeroTailInput : InputData := {
  bytes := [0x11, 0x00].toByteArray
  size_lt_wordModulus := by decide
}

private def shortWordInput : InputData := {
  bytes := (List.replicate 31 (0xa5 : UInt8)).toByteArray
  size_lt_wordModulus := by decide
}

private def exactWordInput : InputData := {
  bytes := ((List.range 32).map UInt8.ofNat).toByteArray
  size_lt_wordModulus := by decide
}

private def slidingWordInput : InputData := {
  bytes := ((List.range 34).map UInt8.ofNat).toByteArray
  size_lt_wordModulus := by decide
}

private def zeroWordInput : InputData := {
  bytes := (List.replicate 32 (0 : UInt8)).toByteArray
  size_lt_wordModulus := by decide
}

private def sequentialWord0 : Word :=
  ⟨0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f,
    by decide⟩

private def sequentialWord1 : Word :=
  ⟨0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20,
    by decide⟩

private def sequentialWord2 : Word :=
  ⟨0x02030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021,
    by decide⟩

/-- An exact natural index beyond machine-word range whose low bits name byte two. -/
private def beyondMachineIndex : Word :=
  ⟨2 ^ 64 + 2, by decide⟩

private theorem observed_byte_lt_256
    (offset result : Word)
    (read : representativeInput.byte? offset = some result) :
    result.val < 256 :=
  InputData.byte?_result_lt_256 representativeInput offset result read

private def allWordBytesCoherent
    (input : InputData) (offset expected : Word) : Bool :=
  (List.range 32).all fun index =>
    input.byte? (word (offset.val + index)) ==
      some ((word index).byteAt expected)

def testHostStorageInputData : IO Unit := do
  assertTrue (emptyInput.sizeWord == word 0)
    "empty input must have exact size zero"
  assertTrue (representativeInput.sizeWord == word 4)
    "the nonempty input size must be represented exactly"
  assertTrue (singletonInput.sizeWord == word 1)
    "a one-byte input must have exact size one"
  assertTrue (zeroTailInput.byte? (word 1) == some Word.zero)
    "a zero byte immediately below the size boundary must remain present"
  assertTrue (zeroTailInput.byte? zeroTailInput.sizeWord == none)
    "the exact size boundary must be absent"
  assertTrue (emptyInput.byte? (word 0) == none)
    "empty input must have no byte at offset zero"
  assertTrue (representativeInput.byte? (word 0) == some (word 0x12))
    "the first input byte must widen exactly to a Core Word"
  assertTrue (representativeInput.byte? (word 2) == some (word 0xab))
    "a middle input byte must be selected by its exact natural offset"
  assertTrue (representativeInput.byte? (word 3) == some (word 0xff))
    "the final input byte must remain addressable"
  assertTrue (representativeInput.byte? (word 4) == none)
    "the offset immediately after the final byte must be absent"
  assertTrue (representativeInput.byte? Word.maximum == none)
    "the maximum Core Word offset must be absent"
  assertTrue (representativeInput.byte? beyondMachineIndex == none)
    "input indexing must not narrow a large natural offset to machine width"
  assertTrue
    ((representativeInput.byte? (word 3)).isSome ==
      decide ((word 3).val < representativeInput.sizeWord.val))
    "the final byte must agree with the exact observed size"
  assertTrue
    ((representativeInput.byte? (word 4)).isSome ==
      decide ((word 4).val < representativeInput.sizeWord.val))
    "the first absent byte must agree with the exact observed size"
  assertTrue
    ((representativeInput.byte? Word.maximum).isSome ==
      decide (Word.maximum.val < representativeInput.sizeWord.val))
    "the maximum Word boundary must agree with the exact observed size"
  let presentZero := representativeInput.byte? (word 1)
  assertTrue (presentZero == some Word.zero)
    "a present zero byte must produce some zero"
  assertTrue (presentZero != none)
    "a present zero byte must remain distinct from an absent byte"
  assertTrue (emptyInput.wordBE? (word 0) == none)
    "empty input must not contain a complete Word window"
  assertTrue (singletonInput.wordBE? (word 0) == none)
    "a one-byte input must not be padded into a Word"
  assertTrue (shortWordInput.wordBE? (word 0) == none)
    "a 31-byte input must not be padded into a Word"
  assertTrue (exactWordInput.wordBE? (word 0) == some sequentialWord0)
    "an exact 32-byte input must decode as the known big-endian Word"
  assertTrue (slidingWordInput.wordBE? (word 0) == some sequentialWord0)
    "the first complete window must decode exactly"
  assertTrue (slidingWordInput.wordBE? (word 1) == some sequentialWord1)
    "a middle complete window must decode exactly"
  assertTrue (slidingWordInput.wordBE? (word 2) == some sequentialWord2)
    "the final complete window must decode exactly"
  assertTrue (slidingWordInput.wordBE? (word 3) == none)
    "the partial window immediately after the final complete one must fail"
  assertTrue (slidingWordInput.wordBE? Word.maximum == none)
    "the maximum Core Word offset must fail without wrapping"
  assertTrue (slidingWordInput.wordBE? beyondMachineIndex == none)
    "large exact natural offsets must not narrow to machine width"
  assertTrue (zeroWordInput.wordBE? (word 0) == some Word.zero)
    "32 zero bytes must remain present as some zero"
  assertTrue (zeroWordInput.wordBE? (word 0) != none)
    "a zero Word must remain distinct from an absent window"
  assertTrue
    (slidingWordInput.bytes.extract 1 33 == encodeWordBytesBE sequentialWord1)
    "encoding a loaded Word must recover its exact selected window"
  assertTrue (allWordBytesCoherent slidingWordInput (word 1) sequentialWord1)
    "all 32 selected bytes must agree with big-endian Word.byteAt"
  match representativeInput.byte? (word 3) with
  | none =>
      throw (IO.userError "the final representative byte unexpectedly disappeared")
  | some result =>
      assertTrue (decide (result.val < 256))
        "every successfully observed byte must remain below 256"

end Tests
