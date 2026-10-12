import Solcore.Test.SourceCoreCapturedMatchFixture

/-! Actual public calls retain each returned session and opaque handle.
Interleaving a fresh allocation separates the two mutable captured cells. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def seed : Core.Word := Core.Word.ofNatModulo 10

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observePublicRun (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        match returned : completion.value with
        | .function handle =>
          return ⟨opened.val, opened.property, fresh.val, fresh.property, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
        | _ => throw (IO.userError "factory output was not a function handle")

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : Core.Word) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle (.word argument) runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : Core.Word) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle (.word argument) runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "packed captured call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "packed captured call exhausted")
  | .ok (.succeeded completion) => return ⟨completion, result ▸ executed.property⟩

structure ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceSpecialization.SpecializationKey)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceSpecialization.SpecializationKey)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFunctionCall session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "match factory call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "match factory call exhausted")
    | .ok (.succeeded completion) =>
      match returned : completion.value with
      | .function handle => return ⟨checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
      | _ => throw (IO.userError "match factory result was not a function")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  first : ObservedPublicRun fixture observed
  second : ObservedFunctionCall first.completion.session observed.row.key [.word (Core.Word.ofNatModulo 20)]
  distinct : first.handle ≠ second.handle
  firstCall : ObservedInvocation second.completion.session first.handle (Core.Word.ofNatModulo 11)
  firstValue : firstCall.completion.value = .word (Core.Word.ofNatModulo 10)
  third : ObservedFunctionCall firstCall.completion.session observed.row.key [.word (Core.Word.ofNatModulo 30)]
  secondCall : ObservedInvocation third.completion.session second.handle (Core.Word.ofNatModulo 21)
  secondValue : secondCall.completion.value = .word (Core.Word.ofNatModulo 20)
  firstAgain : ObservedInvocation secondCall.completion.session first.handle (Core.Word.ofNatModulo 12)
  finalValue : firstAgain.completion.value = .word (Core.Word.ofNatModulo 11)

private def observeWord {artifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion artifact) (expected : Core.Word) :
    IO (PLift (completion.value = .word expected)) :=
  if actual : completion.value = .word expected then pure ⟨actual⟩
  else throw (IO.userError "match returned wrong previous value")

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed
  let second ← observeFunctionCall first.completion.session observed.row.key [.word (Core.Word.ofNatModulo 20)]
  let distinct ← if distinct : first.handle ≠ second.handle then pure (PLift.up distinct)
    else throw (IO.userError "distinct match captures reused the same handle")
  let firstCall ← observeInvocation second.completion.session first.handle (Core.Word.ofNatModulo 11)
  let ⟨firstValue⟩ ← observeWord firstCall.completion (Core.Word.ofNatModulo 10)
  let third ← observeFunctionCall firstCall.completion.session observed.row.key [.word (Core.Word.ofNatModulo 30)]
  let secondCall ← observeInvocation third.completion.session second.handle (Core.Word.ofNatModulo 21)
  let ⟨secondValue⟩ ← observeWord secondCall.completion (Core.Word.ofNatModulo 20)
  let firstAgain ← observeInvocation secondCall.completion.session first.handle (Core.Word.ofNatModulo 12)
  let ⟨finalValue⟩ ← observeWord firstAgain.completion (Core.Word.ofNatModulo 11)
  return ⟨first, second, distinct.down, firstCall, firstValue, third, secondCall, secondValue, firstAgain, finalValue⟩

end Tests.SourceCoreCapturedMatch
