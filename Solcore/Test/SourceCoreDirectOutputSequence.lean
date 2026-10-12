import Solcore.Test.SourceCoreDirectIssuedSequence
import Solcore.Test.SourceCoreCapturedDirectSequence

/-! A direct named factory call exports a second capture, which is then reused
through its actual returned session alongside the original capture. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectOutput
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreCapturedReuse

structure ObservedFunctionInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    extends Tests.SourceCoreDirectIssued.ObservedInvocation session handle (.word secondSeed) where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) :
    IO (ObservedFunctionInvocation session handle) := do
  let call ← Tests.SourceCoreDirectIssued.observeInvocation session handle (.word secondSeed)
  match returned : call.completion.value with
  | .function exported => pure ⟨call, exported, returned⟩
  | _ => throw (IO.userError "direct factory did not return a function")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  named : Tests.SourceCoreDirectIssued.ObservedNamed first.completion.session observed.makeRow.row.key
  second : ObservedFunctionInvocation named.completion.session named.handle
  distinct : first.handle ≠ second.handle
  invokeFirst : Tests.SourceCoreCapturedDirect.ObservedInvocation second.completion.session first.handle
  firstValue : invokeFirst.completion.value = .word seed
  invokeSecond : Tests.SourceCoreCapturedDirect.ObservedInvocation invokeFirst.completion.session second.handle
  secondValue : invokeSecond.completion.value = .word secondSeed
  invokeFirstAgain : Tests.SourceCoreCapturedDirect.ObservedInvocation invokeSecond.completion.session first.handle
  firstValueAgain : invokeFirstAgain.completion.value = .word seed

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let named ← Tests.SourceCoreDirectIssued.observeNamed first.completion.session observed.makeRow.row.key
  let second ← observeFunctionInvocation named.completion.session named.handle
  let ⟨distinct⟩ ← confirm (first.handle ≠ second.handle) "direct factory reused the original captured handle"
  let invokeFirst ← Tests.SourceCoreCapturedDirect.observeInvocation second.completion.session first.handle
  let ⟨firstValue⟩ ← confirm (invokeFirst.completion.value = .word seed) "original capture did not return 10"
  let invokeSecond ← Tests.SourceCoreCapturedDirect.observeInvocation invokeFirst.completion.session second.handle
  let ⟨secondValue⟩ ← confirm (invokeSecond.completion.value = .word secondSeed) "direct factory capture did not return 20"
  let invokeFirstAgain ← Tests.SourceCoreCapturedDirect.observeInvocation invokeSecond.completion.session first.handle
  let ⟨firstValueAgain⟩ ← confirm (invokeFirstAgain.completion.value = .word seed) "original capture changed after reuse"
  pure ⟨first, named, second, distinct, invokeFirst, firstValue, invokeSecond, secondValue,
    invokeFirstAgain, firstValueAgain⟩

end Tests.SourceCoreDirectOutput
