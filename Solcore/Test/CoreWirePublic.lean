import Solcore.Core.Wire

/-! The public Wire umbrella exposes conversion, checking, and JSON APIs. -/

set_option autoImplicit false

namespace Tests

namespace CoreWirePublic

open Solcore.Core.Wire

private def program : Program := {
  resultType := .word
  dataDefinitions := []
  body := .word Solcore.Core.Word.zero
}

example : program.toCore.resultType = .word := by rfl

example : program.check = true := by native_decide

example : Host.functions.length = 14 := by decide

def testCoreWirePublic : IO Unit := do
  match decodeProgram (encodeProgram program) with
  | .ok decoded =>
      unless encodeProgram decoded == encodeProgram program do
        throw (IO.userError "public Wire codec did not round-trip")
  | .error _ =>
      throw (IO.userError "public Wire umbrella failed to decode its Program")

end CoreWirePublic

end Tests
