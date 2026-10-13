import Solcore.Test.SourceCoreRecursiveIndexFixture
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState

/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20
def interveningSeed : Core.Word := Core.Word.ofNatModulo 30

abbrev ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) :=
  CoreLowering.RecursiveNamedPublicPhysicalSessionState.Call session key arguments runOptions

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
      return ⟨⟨checkpoint, started⟩, completion, result ▸ executed.property⟩

abbrev ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) :=
  CoreLowering.RecursiveNamedPublicPhysicalSessionState.FunctionCall session key arguments runOptions

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


def firstKey : Core.Word := Core.Word.ofNatModulo 1
def secondKey : Core.Word := Core.Word.ofNatModulo 2
def missingKey : Core.Word := Core.Word.ofNatModulo 3

def table (first second : SourceCorePublicValues.Handle) : SourceCorePublicValues.Value :=
  .mapping .word closureType [(.word firstKey, .function first), (.word secondKey, .function second)]

structure ObservedFailure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  reason : Core.Word
  returned : SourceCoreExecution.Session artifact
  executed : session.RunAt key arguments runOptions (.ok (.failed reason returned))
  diagnostic : SourceCoreFaultSites.Diagnostic
  decoded : checkpoint.diagnostic reason = .ok (some diagnostic)

def observeFailure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFailure session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .ok (.failed reason returned) =>
      match decoded : checkpoint.diagnostic reason with
      | .ok (some diagnostic) => return ⟨checkpoint, started, reason, returned, result ▸ executed.property, diagnostic, decoded⟩
      | _ => throw (IO.userError "missing-key failure had no actual diagnostic")
    | _ => throw (IO.userError "missing-key call unexpectedly succeeded")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  firstSelect : ObservedFunctionCall second.completion.session observed.selectRow.row.key [table first.handle second.handle, .word firstKey]
  firstSame : firstSelect.handle = first.handle
  firstRead : ObservedInvocation firstSelect.completion.session firstSelect.handle .unit
  firstValue : firstRead.completion.value = .word seed
  intervening : ObservedFunctionCall firstRead.completion.session observed.makeRow.row.key [.word interveningSeed]
  secondSelect : ObservedFunctionCall intervening.completion.session observed.selectRow.row.key [table first.handle second.handle, .word secondKey]
  secondSame : secondSelect.handle = second.handle
  secondRead : ObservedInvocation secondSelect.completion.session secondSelect.handle .unit
  secondValue : secondRead.completion.value = .word secondSeed
  failed : ObservedFailure secondRead.completion.session observed.selectRow.row.key [table first.handle second.handle, .word missingKey]
  missingDiagnostic : failed.diagnostic = {
    error := .typeMismatch closureType none
    site := .occurrence observed.selectShape.value.node.id.occurrence
    span := some observed.selectShape.value.node.span }
  repeatedRead : ObservedInvocation failed.returned first.handle .unit
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let second ← observeFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  if distinct : first.handle ≠ second.handle then
    let firstSelect ← observeFunctionCall second.completion.session observed.selectRow.row.key [table first.handle second.handle, .word firstKey]
    if firstSame : firstSelect.handle = first.handle then
      let firstRead ← observeInvocation firstSelect.completion.session firstSelect.handle .unit
      if firstValue : firstRead.completion.value = .word seed then
        let intervening ← observeFunctionCall firstRead.completion.session observed.makeRow.row.key [.word interveningSeed]
        let secondSelect ← observeFunctionCall intervening.completion.session observed.selectRow.row.key [table first.handle second.handle, .word secondKey]
        if secondSame : secondSelect.handle = second.handle then
          let secondRead ← observeInvocation secondSelect.completion.session secondSelect.handle .unit
          if secondValue : secondRead.completion.value = .word secondSeed then
            let failed ← observeFailure secondRead.completion.session observed.selectRow.row.key [table first.handle second.handle, .word missingKey]
            if missingDiagnostic : failed.diagnostic = {
                error := .typeMismatch closureType none
                site := .occurrence observed.selectShape.value.node.id.occurrence
                span := some observed.selectShape.value.node.span } then
              let repeatedRead ← observeInvocation failed.returned first.handle .unit
              if repeatedValue : repeatedRead.completion.value = .word seed then
                return ⟨first, second, distinct, firstSelect, firstSame, firstRead, firstValue,
                  intervening, secondSelect, secondSame, secondRead, secondValue, failed, missingDiagnostic, repeatedRead, repeatedValue⟩
              else throw (IO.userError "old handle changed after missing-key failure")
            else throw (IO.userError "missing-key diagnostic did not name the original index occurrence")
          else throw (IO.userError "second selected capture not20")
        else throw (IO.userError "second key selected the wrong handle")
      else throw (IO.userError "first selected capture not10")
    else throw (IO.userError "first key selected the wrong handle")
  else throw (IO.userError "initial exports lost distinct captures")

end Tests.SourceCoreRecursiveIndex
