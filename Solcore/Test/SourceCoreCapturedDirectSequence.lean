import Solcore.Test.SourceCoreCapturedReuseSequence

/-! Actual direct public invocations retain each original checkpoint and receipt.
Separate closures are called after later factory allocations and prior invocations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedDirect
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreCapturedReuse

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle .unit runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) :
    IO (ObservedInvocation session handle) := do
  match started : session.startHandlePacked handle .unit runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.invokePackedWithReceipt handle .unit runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "direct captured call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "direct captured call exhausted")
    | .ok (.succeeded completion) =>
      return ⟨checkpoint, started, completion, result ▸ executed.property⟩

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  invokeFirst : ObservedInvocation second.completion.session first.handle
  firstValue : invokeFirst.completion.value = .word seed
  intervening : ObservedFunctionCall invokeFirst.completion.session observed.makeRow.row.key [.word interveningSeed]
  invokeSecond : ObservedInvocation intervening.completion.session second.handle
  secondValue : invokeSecond.completion.value = .word secondSeed
  invokeFirstAgain : ObservedInvocation invokeSecond.completion.session first.handle
  firstValueAgain : invokeFirstAgain.completion.value = .word seed

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let second ← observeFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  let ⟨distinct⟩ ← confirm (first.handle ≠ second.handle) "distinct direct closures reused the same handle"
  let invokeFirst ← observeInvocation second.completion.session first.handle
  let ⟨firstValue⟩ ← confirm (invokeFirst.completion.value = .word seed) "first direct capture did not return 10"
  let intervening ← observeFunctionCall invokeFirst.completion.session observed.makeRow.row.key [.word interveningSeed]
  let invokeSecond ← observeInvocation intervening.completion.session second.handle
  let ⟨secondValue⟩ ← confirm (invokeSecond.completion.value = .word secondSeed) "second direct capture did not return 20"
  let invokeFirstAgain ← observeInvocation invokeSecond.completion.session first.handle
  let ⟨firstValueAgain⟩ ← confirm (invokeFirstAgain.completion.value = .word seed) "first direct capture changed after intervening calls"
  pure ⟨first, second, distinct, invokeFirst, firstValue, intervening, invokeSecond, secondValue,
    invokeFirstAgain, firstValueAgain⟩

end Tests.SourceCoreCapturedDirect
