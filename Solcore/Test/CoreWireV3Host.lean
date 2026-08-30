import Solcore.Core.Wire.V3.Host

/-! Focused regressions for the frozen Semantic Core Wire v3 host boundary. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Core.Wire.V3

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def storageReadProgram : Solcore.Core.Program := {
  resultType := .word
  body :=
    .apply (.var HostFunction.storageRead.index) (.word Word.zero)
}

private def shiftedStorageReadProgram : Solcore.Core.Program := {
  resultType := .word
  body :=
    .letE .unit
      (.apply (.var (HostFunction.storageRead.index + 1)) (.word Word.zero))
}

private def unshiftedStorageReadProgram : Solcore.Core.Program := {
  resultType := .word
  body :=
    .letE .unit
      (.apply (.var HostFunction.storageRead.index) (.word Word.zero))
}

private def firstUnboundProgram : Solcore.Core.Program := {
  resultType := .word
  body := .var 14
}

private def wireStorageReadProgram : Solcore.Core.Wire.V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (.var 0) (.word Word.zero)
}

private def wireFirstUnboundProgram : Solcore.Core.Wire.V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .var 14
}

example : Host.functions =
    [.storageRead, .storageWrite, .storageAddress, .codeAddress,
      .callValue, .callerAddress, .inputDataByte?, .inputDataSize,
      .inputDataWordBE?, .currentAddress, .callContractWord,
      .callContractWordWithValue, .createContractWord, .emitLogWord] :=
  rfl

example : Host.context[13]? =
    some (HostFunction.functionType .emitLogWord) :=
  Host.context_lookup .emitLogWord

example : Host.environment[13]? =
    some (.hostFunction .emitLogWord) :=
  Host.environment_lookup .emitLogWord

example : Host.check storageReadProgram = true := by
  decide

example : Host.checkDetailed storageReadProgram = .ok .word := by
  rfl

example : Host.check shiftedStorageReadProgram = true := by
  decide

example : Host.check unshiftedStorageReadProgram = false := by
  decide

example : Host.check firstUnboundProgram = false := by
  decide

example : storageReadProgram.checkHost = true :=
  Host.check_promotes_current (by decide)

example : wireStorageReadProgram.check = true := by
  native_decide

example : wireStorageReadProgram.checkDetailed = .ok .word := by
  apply Solcore.Core.Wire.V3.Program.checkDetailed_iff_check.mpr
  native_decide

example : wireFirstUnboundProgram.check = false := by
  native_decide

example : wireStorageReadProgram.toCore.checkHost = true :=
  Solcore.Core.Wire.V3.Program.check_promotes_current (by native_decide)

def testCoreWireV3Host : IO Unit := do
  assertTrue (Host.functions.length == 14)
    "Semantic Core Wire v3 must expose exactly fourteen host functions"
  assertTrue
    (Host.context == hostContext &&
      Host.environment == hostEnvironment)
    "the frozen v3 host entries must match the current internal prefix"
  assertTrue (Host.check storageReadProgram)
    "the frozen checker rejected a root host consumer"
  assertTrue (Host.check shiftedStorageReadProgram)
    "a local binder did not shift the frozen host context"
  assertTrue (!Host.check unshiftedStorageReadProgram)
    "an unshifted host index resolved through a local binder"
  assertTrue (!Host.check firstUnboundProgram)
    "the frozen checker accepted the first unbound root index"
  assertTrue wireStorageReadProgram.check
    "the Wire v3 checker rejected its projected host consumer"
  assertTrue (!wireFirstUnboundProgram.check)
    "the Wire v3 checker accepted the first unbound root index"
  match Host.checkDetailed storageReadProgram with
  | .ok .word => pure ()
  | result =>
      throw (IO.userError
        s!"the frozen detailed checker returned {reprStr result}")

end Tests
