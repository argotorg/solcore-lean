import Solcore.Core.Wire.V3

/-! The public Wire v3 umbrella exposes conversion, checking, and JSON APIs. -/

set_option autoImplicit false

namespace Tests

namespace CoreWireV3Public

open Solcore.Core.Wire.V3

private def program : Program := {
  resultType := .word
  dataDefinitions := []
  body := .word Solcore.Core.Word.zero
}

example : program.toCore.resultType = .word := by rfl

example : program.check = true := by native_decide

example : Host.functions.length = 14 := by decide

def testCoreWireV3Public : IO Unit := do
  match decodeProgram (encodeProgram program) with
  | .ok decoded =>
      unless encodeProgram decoded == encodeProgram program do
        throw (IO.userError "public Wire v3 codec did not round-trip")
  | .error _ =>
      throw (IO.userError "public Wire v3 umbrella failed to decode its Program")

end CoreWireV3Public

end Tests
