import Solcore.Core.Primitive
import Solcore.Semantics.HostStorageInputDataProperties

/-! Executable boundary tests for bounded run input bytes. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open Solcore.Semantics.HostStorageDriver

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

/-- An exact natural index beyond machine-word range whose low bits name byte two. -/
private def beyondMachineIndex : Word :=
  ⟨2 ^ 64 + 2, by decide⟩

private theorem observed_byte_lt_256
    (offset result : Word)
    (read : representativeInput.byte? offset = some result) :
    result.val < 256 :=
  InputData.byte?_result_lt_256 representativeInput offset result read

def testHostStorageInputData : IO Unit := do
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
  let presentZero := representativeInput.byte? (word 1)
  assertTrue (presentZero == some Word.zero)
    "a present zero byte must produce some zero"
  assertTrue (presentZero != none)
    "a present zero byte must remain distinct from an absent byte"
  match representativeInput.byte? (word 3) with
  | none =>
      throw (IO.userError "the final representative byte unexpectedly disappeared")
  | some result =>
      assertTrue (decide (result.val < 256))
        "every successfully observed byte must remain below 256"

end Tests
