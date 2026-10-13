import Solcore.Test.SourceCoreNestedFormationFixture

/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
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


structure ObservedFormation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (parent : SourceCorePublicValues.Handle)
    extends ObservedInvocation session parent .unit where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFormation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (parent : SourceCorePublicValues.Handle) :
    IO (ObservedFormation session parent) := do
  let call ← observeInvocation session parent .unit
  match returned : call.completion.value with
  | .function handle => pure ⟨call, handle, returned⟩
  | _ => throw (IO.userError "nested formation expected inner function")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  firstFormation : ObservedFormation first.completion.session first.handle
  second : ObservedFunctionCall firstFormation.completion.session observed.makeRow.row.key [.word secondSeed]
  secondFormation : ObservedFormation second.completion.session second.handle
  distinctOuter : first.handle ≠ second.handle
  distinctInner : firstFormation.handle ≠ secondFormation.handle
  firstRead : ObservedInvocation secondFormation.completion.session firstFormation.handle .unit
  firstValue : firstRead.completion.value = .word seed
  secondRead : ObservedInvocation firstRead.completion.session secondFormation.handle .unit
  secondValue : secondRead.completion.value = .word secondSeed
  repeatedRead : ObservedInvocation secondRead.completion.session firstFormation.handle .unit
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let firstFormation ← observeFormation first.completion.session first.handle
  let second ← observeFunctionCall firstFormation.completion.session observed.makeRow.row.key [.word secondSeed]
  let secondFormation ← observeFormation second.completion.session second.handle
  if distinctOuter : first.handle ≠ second.handle then
    if distinctInner : firstFormation.handle ≠ secondFormation.handle then
      let firstRead ← observeInvocation secondFormation.completion.session firstFormation.handle .unit
      if firstValue : firstRead.completion.value = .word seed then
        let secondRead ← observeInvocation firstRead.completion.session secondFormation.handle .unit
        if secondValue : secondRead.completion.value = .word secondSeed then
          let repeatedRead ← observeInvocation secondRead.completion.session firstFormation.handle .unit
          if repeatedValue : repeatedRead.completion.value = .word seed then
            return {
              first := first
              firstFormation := firstFormation
              second := second
              secondFormation := secondFormation
              distinctOuter := distinctOuter
              distinctInner := distinctInner
              firstRead := firstRead
              firstValue := firstValue
              secondRead := secondRead
              secondValue := secondValue
              repeatedRead := repeatedRead
              repeatedValue := repeatedValue
            }
          else throw (IO.userError "retained first inner capture changed")
        else throw (IO.userError "second inner capture not20")
      else throw (IO.userError "first inner capture not10")
    else throw (IO.userError "nested formation lost distinct inner captures")
  else throw (IO.userError "nested formation lost distinct outer captures")

end Tests.SourceCoreNestedFormation
