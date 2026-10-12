import Solcore.Test.SourceCoreCapturedMappingForward

/-! Each direct call resumes the returned checkpoint twice with positive fuel
before finishing. The original checkpoint is never executed a second time. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMappingResumption
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedMapping

structure ResumedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.startHandlePacked handle (publicArgument argument)
    runOptions.inputValidationFuel = .ok checkpoint
  first : SourceCoreExecution.Checkpoint artifact
  firstExhausted : checkpoint.ResumeAt 1 0 (.outOfFuel first)
  second : SourceCoreExecution.Checkpoint artifact
  secondExhausted : first.ResumeAt 1 0 (.outOfFuel second)
  completion : SourceCoreExecution.Completion artifact
  finished : second.ResumeAt (runOptions.executionFuel - 2) runOptions.outputValidationFuel
    (.succeeded completion)

theorem ResumedInvocation.chain {artifact : SourceCoreExecution.Artifact}
    {session : SourceCoreExecution.Session artifact} {handle : SourceCorePublicValues.Handle}
    {argument : List (Core.Word × Core.Word)} (call : ResumedInvocation session handle argument) :
    call.checkpoint.ResumeChain runOptions.executionFuel runOptions.outputValidationFuel
      (.succeeded call.completion) := by
  have chain := SourceCoreExecution.Checkpoint.ResumeChain.more call.firstExhausted
    (.more call.secondExhausted (.single call.finished))
  simpa only [runOptions] using chain

def ResumedInvocation.observed {artifact : SourceCoreExecution.Artifact}
    {session : SourceCoreExecution.Session artifact} {handle : SourceCorePublicValues.Handle}
    {argument : List (Core.Word × Core.Word)} (call : ResumedInvocation session handle argument) :
    ObservedInvocation session handle argument :=
  ⟨call.completion, call.checkpoint, call.started, call.chain.collapse⟩

def observeResumedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) : IO (ResumedInvocation session handle argument) := do
  match started : session.startHandlePacked handle (publicArgument argument)
      runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let first ← checkpoint.resumeWithReceipt 1 0
    match firstResult : first.val with
    | .outOfFuel firstCheckpoint =>
      let second ← firstCheckpoint.resumeWithReceipt 1 0
      match secondResult : second.val with
      | .outOfFuel secondCheckpoint =>
        let final ← secondCheckpoint.resumeWithReceipt (runOptions.executionFuel - 2)
          runOptions.outputValidationFuel
        match finalResult : final.val with
        | .succeeded completion =>
          return ⟨checkpoint, started, firstCheckpoint, firstResult ▸ first.property,
            secondCheckpoint, secondResult ▸ second.property,
            completion, finalResult ▸ final.property⟩
        | .failed _ _ => throw (IO.userError "resumed captured call failed")
        | .exportError error _ => throw (IO.userError (reprStr error))
        | .outOfFuel _ => throw (IO.userError "final captured-call resume exhausted")
      | _ => throw (IO.userError "second positive-fuel resume did not exhaust")
    | _ => throw (IO.userError "first positive-fuel resume did not exhaust")

structure ResumedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  factory : ObservedPublicRun fixture observed
  first : ResumedInvocation factory.completion.session factory.handle firstArgument
  firstValue : first.completion.value = .word seed
  second : ResumedInvocation first.completion.session factory.handle secondArgument
  secondValue : second.completion.value = .word seed

def ResumedSequence.observed {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (sequence : ResumedSequence fixture observed) : ObservedSequence fixture observed :=
  ⟨sequence.factory, sequence.first.observed, sequence.firstValue,
    sequence.second.observed, sequence.secondValue⟩

def observeResumedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ResumedSequence fixture observed) := do
  let factory ← observePublicRun fixture observed
  let first ← observeResumedInvocation factory.completion.session factory.handle firstArgument
  if firstValue : first.completion.value = .word seed then
    let second ← observeResumedInvocation first.completion.session factory.handle secondArgument
    if secondValue : second.completion.value = .word seed then
      return ⟨factory, first, firstValue, second, secondValue⟩
    else throw (IO.userError "second resumed call changed captured seed")
  else throw (IO.userError "first resumed call changed captured seed")

end Tests.SourceCoreCapturedMappingResumption
