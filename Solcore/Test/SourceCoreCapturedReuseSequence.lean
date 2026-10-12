import Solcore.Test.SourceCoreCapturedReuseFixture

/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20
def interveningSeed : Core.Word := Core.Word.ofNatModulo 30

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))

def observeCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedCall session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "captured reuse public call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "captured reuse public call exhausted")
    | .ok (.succeeded completion) =>
      return ⟨checkpoint, started, completion, result ▸ executed.property⟩

structure ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) extends ObservedCall session key arguments where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFunctionCall session key arguments) := do
  let call ← observeCall session key arguments
  match returned : call.completion.value with
  | .function handle => return ⟨call, handle, returned⟩
  | _ => throw (IO.userError "captured reuse expected a function export")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  readFirst : ObservedCall second.completion.session observed.readRow.row.key [.function first.handle]
  firstValue : readFirst.completion.value = .word seed
  intervening : ObservedFunctionCall readFirst.completion.session observed.makeRow.row.key [.word interveningSeed]
  readSecond : ObservedCall intervening.completion.session observed.readRow.row.key [.function second.handle]
  secondValue : readSecond.completion.value = .word secondSeed
  readFirstAgain : ObservedCall readSecond.completion.session observed.readRow.row.key [.function first.handle]
  firstValueAgain : readFirstAgain.completion.value = .word seed

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let second ← observeFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  let ⟨distinct⟩ ← confirm (first.handle ≠ second.handle) "distinct captured closures reused the same handle"
  let readFirst ← observeCall second.completion.session observed.readRow.row.key [.function first.handle]
  let ⟨firstValue⟩ ← confirm (readFirst.completion.value = .word seed) "first capture did not return 10"
  let intervening ← observeFunctionCall readFirst.completion.session observed.makeRow.row.key [.word interveningSeed]
  let readSecond ← observeCall intervening.completion.session observed.readRow.row.key [.function second.handle]
  let ⟨secondValue⟩ ← confirm (readSecond.completion.value = .word secondSeed) "second capture did not return 20"
  let readFirstAgain ← observeCall readSecond.completion.session observed.readRow.row.key [.function first.handle]
  let ⟨firstValueAgain⟩ ← confirm (readFirstAgain.completion.value = .word seed) "first capture changed after intervening calls"
  pure ⟨first, second, distinct, readFirst, firstValue, intervening, readSecond, secondValue,
    readFirstAgain, firstValueAgain⟩

end Tests.SourceCoreCapturedReuse
