import Solcore.Test.SourceCoreEvidenceMethodFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))
  returned : completion.value = expected

def observeCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (ObservedCall session key arguments expected) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "generic direct call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "generic direct call exhausted")
    | .ok (.succeeded completion) =>
      if returned : completion.value = expected then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "generic direct call output changed")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.wordRow.toObservedRow
  second : ObservedCall first.completion.session observed.boolRow.row.key
    [.bool false] (.bool false)
  third : ObservedCall second.completion.session observed.wordRow.row.key
    [.word (Core.Word.ofNatModulo 33)] (.word (Core.Word.ofNatModulo 33))
  fourth : ObservedCall third.completion.session observed.boolRow.row.key
    [.bool true] (.bool true)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.wordRow.toObservedRow
  let second ← observeCall first.completion.session observed.boolRow.row.key
    [.bool false] (.bool false)
  let third ← observeCall second.completion.session observed.wordRow.row.key
    [.word (Core.Word.ofNatModulo 33)] (.word (Core.Word.ofNatModulo 33))
  let fourth ← observeCall third.completion.session observed.boolRow.row.key
    [.bool true] (.bool true)
  pure ⟨first, second, third, fourth⟩
end Tests.SourceCoreEvidenceMethod
