import Solcore.Test.SourceCoreEvidenceClosureFixture

/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20

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

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle argument runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "direct issued call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "direct issued call exhausted")
  | .ok (.succeeded completion) => pure ⟨completion, result ▸ executed.property⟩


structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.wordRow.toObservedRow
  second : ObservedFunctionCall first.completion.session observed.boolRow.row.key
    [.bool false, .word (Core.Word.ofNatModulo 22)]
  firstRead : ObservedInvocation second.completion.session first.handle .unit
  firstValue : firstRead.completion.value = .word seed
  third : ObservedFunctionCall firstRead.completion.session observed.wordRow.row.key
    [.word (Core.Word.ofNatModulo 33), .bool false]
  firstSecond : first.handle ≠ second.handle
  firstThird : first.handle ≠ third.handle
  secondThird : second.handle ≠ third.handle
  secondRead : ObservedInvocation third.completion.session second.handle .unit
  secondValue : secondRead.completion.value = .bool false
  repeatedRead : ObservedInvocation secondRead.completion.session first.handle .unit
  repeatedValue : repeatedRead.completion.value = .word seed
  thirdRead : ObservedInvocation repeatedRead.completion.session third.handle .unit
  thirdValue : thirdRead.completion.value = .word (Core.Word.ofNatModulo 33)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.wordRow.toObservedRow
  let second ← observeFunctionCall first.completion.session observed.boolRow.row.key
    [.bool false, .word (Core.Word.ofNatModulo 22)]
  let firstRead ← observeInvocation second.completion.session first.handle .unit
  if firstValue : firstRead.completion.value = .word seed then
    let third ← observeFunctionCall firstRead.completion.session observed.wordRow.row.key
      [.word (Core.Word.ofNatModulo 33), .bool false]
    if firstSecond : first.handle ≠ second.handle then
      if firstThird : first.handle ≠ third.handle then
        if secondThird : second.handle ≠ third.handle then
          let secondRead ← observeInvocation third.completion.session second.handle .unit
          if secondValue : secondRead.completion.value = .bool false then
            let repeatedRead ← observeInvocation secondRead.completion.session first.handle .unit
            if repeatedValue : repeatedRead.completion.value = .word seed then
              let thirdRead ← observeInvocation repeatedRead.completion.session third.handle .unit
              if thirdValue : thirdRead.completion.value = .word (Core.Word.ofNatModulo 33) then
                return {
                  first := first
                  second := second
                  firstRead := firstRead
                  firstValue := firstValue
                  third := third
                  firstSecond := firstSecond
                  firstThird := firstThird
                  secondThird := secondThird
                  secondRead := secondRead
                  secondValue := secondValue
                  repeatedRead := repeatedRead
                  repeatedValue := repeatedValue
                  thirdRead := thirdRead
                  thirdValue := thirdValue
                }
              else throw (IO.userError "third Word closure capture changed")
            else throw (IO.userError "first Word closure capture changed on reuse")
          else throw (IO.userError "Bool closure capture changed")
        else throw (IO.userError "second and third exports alias")
      else throw (IO.userError "first and third exports alias")
    else throw (IO.userError "first and second exports alias")
  else throw (IO.userError "first Word closure capture changed")
end Tests.SourceCoreEvidenceClosure
