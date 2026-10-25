import Solcore.Test.RustHullNestedChildCallCorrespondence

/-! Public execution and resumptions observe the same nested checkpoints as
the independent source derivations, including retained revert data. -/
set_option autoImplicit false
namespace Tests.RustHullNestedChildCallRuntime
open Solcore Solcore.Frontend.RustHull RustHullNestedChildCallCorrespondence

private abbrev w := Core.Word.ofNatModulo

private def expectedBytes : Scenario → List UInt8
  | .committed => [1, 4, 1, 1, 204, 187, 170]
  | .grandchildReverted => [1, 4, 0, 1, 204, 187, 170]
  | .childReverted => [0, 4, 1, 1, 204, 187, 170]

private def expectedEvents (scenario : Scenario) : List Logs.Event :=
  [⟨w 0, [], [170]⟩] ++
    (if scenario = .childReverted then [] else [⟨w 100, [], [187]⟩]) ++
    (if scenario = .committed then [⟨w 200, [], [204]⟩] else [])

private def checkWorld (label : String) (scenario : Scenario)
    (world : List AccountState.Account) : IO Unit := do
  let some parent := world.find? (·.address == w 0) |
    throw (IO.userError s!"{label}: missing parent")
  let some child := world.find? (·.address == w 100) |
    throw (IO.userError s!"{label}: missing child")
  let some grandchild := world.find? (·.address == w 200) |
    throw (IO.userError s!"{label}: missing grandchild")
  let childStorage := if scenario = .childReverted then [] else [(w 8, w 99)]
  let grandchildStorage := if scenario = .committed then [(w 9, w 77)] else []
  unless world.length == 3 && parent.storage == [(w 7, w 42)] &&
      child.storage == childStorage && grandchild.storage == grandchildStorage &&
      parent.transient.isEmpty && child.transient.isEmpty && grandchild.transient.isEmpty &&
      child.code == image .child && grandchild.code == image .grandchild do
    throw (IO.userError s!"{label}: wrong nested checkpoint for {reprStr scenario}: {reprStr world}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"nested call: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"nested call: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"nested call: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 4000000,
      Contract.resumeWithReceipt checkpoint 4000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes scenario && storage == [(w 7, w 42)] &&
            receipt.logs == expectedEvents scenario && receipt.balances == [(w 0, w 0)] do
          throw (IO.userError s!"nested call: wrong result for {reprStr scenario}: {reprStr receipt}")
        checkWorld "receipt" scenario receipt.world
    | outcome => throw (IO.userError s!"nested call: expected return for {reprStr scenario}: {reprStr outcome}")
  match Core.runStateful 4000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words &&
          storage == Core.WordMapping.encode [(w 7, w 42)] &&
          logs == Core.WordMapping.encode expected.runtime.runtime.runtime.words &&
          cursor == .word expected.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode [(w 0, w 0)] &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset &&
          count == .word runtime.storage.returnSize do
        throw (IO.userError s!"nested call: snapshot differs from source for {reprStr scenario}")
      let accounts ← match AccountState.decode world with
        | .ok accounts => pure accounts
        | .error error => throw (IO.userError s!"nested call: bad world snapshot: {error}")
      checkWorld "Core snapshot" scenario accounts
  | outcome => throw (IO.userError s!"nested call: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.committed, .grandchildReverted, .childReverted] do
    check scenario

end Tests.RustHullNestedChildCallRuntime
