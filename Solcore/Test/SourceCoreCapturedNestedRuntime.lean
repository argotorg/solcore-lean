import Solcore.Test.SourceCoreCapturedNestedFixture

/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedNested
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

def issuanceFuel : Nat := 1024

structure ObservedNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.NamedIssuedAt key issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

def observeNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamed session key) := do
  match ← session.namedWithReceipt key issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "named issuance did not return a function")

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


def mappingArgument (first second third : SourceCorePublicValues.Handle) : SourceCorePublicValues.Value :=
  .mapping .word (.function .unit .word)
    [(.word (Core.Word.ofNatModulo 1), .function first),
     (.word (Core.Word.ofNatModulo 1), .function second),
     (.word (Core.Word.ofNatModulo 2), .function third)]

structure ObservedEcho {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle first second : SourceCorePublicValues.Handle)
    extends ObservedInvocation session handle (mappingArgument first second first) where
  firstOutput : SourceCorePublicValues.Handle
  secondOutput : SourceCorePublicValues.Handle
  repeatedOutput : SourceCorePublicValues.Handle
  returned : completion.value = mappingArgument firstOutput secondOutput repeatedOutput
  firstSame : firstOutput = first
  secondSame : secondOutput = second
  repeatedSame : repeatedOutput = first

def observeEcho {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle first second : SourceCorePublicValues.Handle) :
    IO (ObservedEcho session handle first second) := do
  let call ← observeInvocation session handle (mappingArgument first second first)
  match call.completion.value with
  | .mapping _ _ [(_, .function firstOutput), (_, .function secondOutput), (_, .function repeatedOutput)] =>
    if returned : call.completion.value = mappingArgument firstOutput secondOutput repeatedOutput then
      if firstSame : firstOutput = first then
        if secondSame : secondOutput = second then
          if repeatedSame : repeatedOutput = first then
            return ⟨call, firstOutput, secondOutput, repeatedOutput, returned, firstSame, secondSame, repeatedSame⟩
          else throw (IO.userError "nested output changed repeated handle")
        else throw (IO.userError "nested output changed second handle")
      else throw (IO.userError "nested output changed first handle")
    else throw (IO.userError "nested output changed ordered mapping rows")
  | _ => throw (IO.userError "nested output expected three function rows")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  named : ObservedNamed second.completion.session observed.readRow.row.key
  echo : ObservedEcho named.completion.session named.handle first.handle second.handle
  firstRead : ObservedInvocation echo.completion.session echo.firstOutput .unit
  firstValue : firstRead.completion.value = .word seed
  intervening : ObservedFunctionCall firstRead.completion.session observed.makeRow.row.key [.word interveningSeed]
  secondRead : ObservedInvocation intervening.completion.session echo.secondOutput .unit
  secondValue : secondRead.completion.value = .word secondSeed
  repeatedRead : ObservedInvocation secondRead.completion.session echo.repeatedOutput .unit
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let second ← observeFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  if distinct : first.handle ≠ second.handle then
    let named ← observeNamed second.completion.session observed.readRow.row.key
    let echo ← observeEcho named.completion.session named.handle first.handle second.handle
    let firstRead ← observeInvocation echo.completion.session echo.firstOutput .unit
    if firstValue : firstRead.completion.value = .word seed then
      let intervening ← observeFunctionCall firstRead.completion.session observed.makeRow.row.key [.word interveningSeed]
      let secondRead ← observeInvocation intervening.completion.session echo.secondOutput .unit
      if secondValue : secondRead.completion.value = .word secondSeed then
        let repeatedRead ← observeInvocation secondRead.completion.session echo.repeatedOutput .unit
        if repeatedValue : repeatedRead.completion.value = .word seed then
          return ⟨first, second, distinct, named, echo, firstRead, firstValue, intervening,
            secondRead, secondValue, repeatedRead, repeatedValue⟩
        else throw (IO.userError "repeated collected capture did not remain 10")
      else throw (IO.userError "second collected capture did not remain 20")
    else throw (IO.userError "first collected capture did not remain 10")
  else throw (IO.userError "independent captured outputs shared a handle")

end Tests.SourceCoreCapturedNested
