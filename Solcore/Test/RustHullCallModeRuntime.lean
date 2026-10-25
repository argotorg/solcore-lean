import Solcore.Test.RustHullCallModeCorrespondence

/-! Public CALLCODE and DELEGATECALL preserve the invoking storage address.
Returned observations and shared checkpoints agree with the source derivations. -/
set_option autoImplicit false
namespace Tests.RustHullCallModeRuntime
open Solcore Solcore.Frontend.RustHull RustHullCallModeCorrespondence

private abbrev w := Core.Word.ofNatModulo

private def expectedBytes : Scenario → List UInt8
  | .callCode => [1, 4, 0, 0, 5, 187, 170]
  | .delegated => [1, 4, 0, 55, 7, 187, 170]
  | .reverted => [0, 4, 0, 55, 7, 187, 170]

private def expectedEvents (scenario : Scenario) : List Logs.Event :=
  if scenario = .reverted then [] else [⟨w 0, [], [187]⟩]

private def expectedStorage (scenario : Scenario) : List (Core.Word × Core.Word) :=
  [(w 7, w 42)] ++ if scenario = .reverted then [] else [(w 8, w 99)]

private def checkWorld (label : String) (scenario : Scenario)
    (world : List AccountState.Account) : IO Unit := do
  let some parent := world.find? (·.address == w 0) |
    throw (IO.userError s!"{label}: missing parent")
  let some child := world.find? (·.address == w 100) |
    throw (IO.userError s!"{label}: missing code account")
  unless world.length == 2 && parent.storage == expectedStorage scenario && child.storage.isEmpty &&
      parent.transient.isEmpty && child.transient.isEmpty && child.code == some childBytes do
    throw (IO.userError s!"{label}: wrong mode checkpoint for {reprStr scenario}: {reprStr world}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"call mode: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"call mode: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"call mode: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 4000000,
      Contract.resumeWithReceipt checkpoint 4000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes scenario && storage == expectedStorage scenario &&
            receipt.logs == expectedEvents scenario && receipt.balances == [(w 0, w 100)] do
          throw (IO.userError s!"call mode: wrong result for {reprStr scenario}: {reprStr receipt}")
        checkWorld "receipt" scenario receipt.world
    | outcome => throw (IO.userError s!"call mode: expected return for {reprStr scenario}: {reprStr outcome}")
  match Core.runStateful 4000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words &&
          storage == Core.WordMapping.encode (expectedStorage scenario) &&
          logs == Core.WordMapping.encode expected.runtime.runtime.runtime.words &&
          cursor == .word expected.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode [(w 0, w 100)] &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset &&
          count == .word runtime.storage.returnSize do
        throw (IO.userError s!"call mode: snapshot differs from source for {reprStr scenario}")
      let accounts ← match AccountState.decode world with
        | .ok accounts => pure accounts
        | .error error => throw (IO.userError s!"call mode: bad world snapshot: {error}")
      checkWorld "Core snapshot" scenario accounts
  | outcome => throw (IO.userError s!"call mode: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.callCode, .delegated, .reverted] do
    check scenario

end Tests.RustHullCallModeRuntime
