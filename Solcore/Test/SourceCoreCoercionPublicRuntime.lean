import Solcore.Test.SourceCoreCoercionPublicFixture
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState

/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics

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

/-- Every use is an original compiled Source indirect call, reached through a
public named entry with the previously exported handle as its actual input. -/
structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow.toObservedRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.bool false]
  secondType : second.handle.sourceType = closureType .word
  firstRead : ObservedCall second.completion.session observed.useRow.row.key [.function first.handle]
  firstValue : firstRead.completion.value = .word (Core.Word.ofNatModulo 41)
  third : ObservedFunctionCall firstRead.completion.session observed.makeRow.row.key [.bool false]
  thirdType : third.handle.sourceType = closureType .word
  firstSecond : first.handle ≠ second.handle
  firstThird : first.handle ≠ third.handle
  secondThird : second.handle ≠ third.handle
  secondRead : ObservedCall third.completion.session observed.useRow.row.key [.function second.handle]
  secondValue : secondRead.completion.value = .word (Core.Word.ofNatModulo 7)
  repeatedRead : ObservedCall secondRead.completion.session observed.useRow.row.key [.function first.handle]
  repeatedValue : repeatedRead.completion.value = .word (Core.Word.ofNatModulo 41)
  thirdRead : ObservedCall repeatedRead.completion.session observed.useRow.row.key [.function third.handle]
  thirdValue : thirdRead.completion.value = .word (Core.Word.ofNatModulo 7)
  heapSizes : [first.session.heapSize, first.completion.session.heapSize, second.completion.session.heapSize,
    firstRead.completion.session.heapSize, third.completion.session.heapSize, secondRead.completion.session.heapSize,
    repeatedRead.completion.session.heapSize, thirdRead.completion.session.heapSize] = [5,8,11,20,23,32,41,50]

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeSequence (fixture : CompiledFixture) (program : ObservedProgram fixture) :
    IO (ObservedSequence fixture program) := do
  let first ← observePublicRun fixture program.makeRow.toObservedRow
  let second ← observeFunctionCall first.completion.session program.makeRow.row.key [.bool false]
  let ⟨secondType⟩ ← observed (second.handle.sourceType = closureType .word) "second public handle type"
  let firstRead ← observeCall second.completion.session program.useRow.row.key [.function first.handle]
  let ⟨firstValue⟩ ← observed (firstRead.completion.value = .word (Core.Word.ofNatModulo 41)) "first compiled indirect output"
  let third ← observeFunctionCall firstRead.completion.session program.makeRow.row.key [.bool false]
  let ⟨thirdType⟩ ← observed (third.handle.sourceType = closureType .word) "third public handle type"
  let ⟨firstSecond⟩ ← observed (first.handle ≠ second.handle) "first/second handles distinct"
  let ⟨firstThird⟩ ← observed (first.handle ≠ third.handle) "first/third handles distinct"
  let ⟨secondThird⟩ ← observed (second.handle ≠ third.handle) "second/third handles distinct"
  let secondRead ← observeCall third.completion.session program.useRow.row.key [.function second.handle]
  let ⟨secondValue⟩ ← observed (secondRead.completion.value = .word (Core.Word.ofNatModulo 7)) "second compiled indirect output"
  let repeatedRead ← observeCall secondRead.completion.session program.useRow.row.key [.function first.handle]
  let ⟨repeatedValue⟩ ← observed (repeatedRead.completion.value = .word (Core.Word.ofNatModulo 41)) "retained first compiled indirect output"
  let thirdRead ← observeCall repeatedRead.completion.session program.useRow.row.key [.function third.handle]
  let ⟨thirdValue⟩ ← observed (thirdRead.completion.value = .word (Core.Word.ofNatModulo 7)) "third compiled indirect output"
  let ⟨heapSizes⟩ ← observed ([first.session.heapSize, first.completion.session.heapSize, second.completion.session.heapSize,
    firstRead.completion.session.heapSize, third.completion.session.heapSize, secondRead.completion.session.heapSize,
    repeatedRead.completion.session.heapSize, thirdRead.completion.session.heapSize] = [5,8,11,20,23,32,41,50]) "exact seven-session heap sequence"
  return {first, second, secondType, firstRead, firstValue, third, thirdType, firstSecond, firstThird, secondThird, secondRead, secondValue, repeatedRead, repeatedValue, thirdRead, thirdValue, heapSizes}
end Tests.SourceCoreCoercionPublic
