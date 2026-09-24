import Solcore.Core.HostProgress
import Solcore.Core.HostRunner

/-! Executable and proof-contract checks for the append-only log boundary. -/

set_option autoImplicit false

namespace Tests.Adr0149EmitLogWordBoundary

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

example := HostFunction.parameterType_emitLogWord
example := HostFunction.resultType_emitLogWord
example := HostFunction.index_emitLogWord
example := hostContext_emitLogWord
example := hostEnvironment_emitLogWord
example := HostRequest.responseType_emitLogWord
example := HostRequest.responseValue_emitLogWord
example := HostSuspension.resume_emitLogWord
example := hostAdvance_begin_emitLogWord
example := hostAdvance_suspend_emitLogWord
example := hostAdvance_invalid_emitLogWord_argument
example := @typed_emitLogWord_emits

private def topic : Word := ⟨0x149, by decide⟩
private def payload : Word := ⟨0xfeed, by decide⟩

private def emitProgram : Program := {
  resultType := .unit
  body :=
    .apply
      (.var HostFunction.emitLogWord.index)
      (.pair (.word topic) (.word payload))
}

private theorem emitProgram_checked : emitProgram.checkHost = true := by
  decide

private def illTypedEmitProgram : Program := {
  resultType := .unit
  body :=
    .apply
      (.var HostFunction.emitLogWord.index)
      (.pair (.word topic) (.bool true))
}

private theorem illTypedEmitProgram_rejected :
    illTypedEmitProgram.checkHost = false := by
  decide

private def emitsExactRequestAndResumes : Bool :=
  match emitProgram.runHostStateful 32 with
  | .suspended
      ⟨.emitLogWord actualTopic actualPayload, continuation, store⟩
      remainingFuel =>
      actualTopic == topic && actualPayload == payload &&
        match hostRun remainingFuel
            ((HostSuspension.mk
              (.emitLogWord actualTopic actualPayload)
              continuation store).resume ()) with
        | .done returned finalStore =>
            returned == .unit && finalStore == []
        | _ => false
  | _ => false

private def appendOnlyRegistryExact : Bool :=
  HostFunction.emitLogWord.index == 13 &&
    HostFunction.all.length == 14 &&
    HostFunction.all[13]? == some .emitLogWord &&
    hostContext[13]? == some (HostFunction.functionType .emitLogWord) &&
    hostEnvironment[13]? == some (.hostFunction .emitLogWord) &&
    hostContext[14]? == none && hostEnvironment[14]? == none

private theorem compileTimeBoundaryExact :
    emitsExactRequestAndResumes && appendOnlyRegistryExact = true := by
  native_decide

def testAdr0149EmitLogWordBoundary : IO Unit := do
  assertTrue emitsExactRequestAndResumes
    "checked emit-log did not preserve topic/payload order and unit resumption"
  assertTrue appendOnlyRegistryExact
    "emit-log did not occupy the append-only host index 13"

end Tests.Adr0149EmitLogWordBoundary
