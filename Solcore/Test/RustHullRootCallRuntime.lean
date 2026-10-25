import Solcore.Test.RustHullRootCallCorrespondence

/-! Reentry invokes the root closure with fresh calldata and memory while
sharing storage. Parent revert suppresses the complete transaction receipt. -/
set_option autoImplicit false
namespace Tests.RustHullRootCallRuntime
open Solcore Solcore.Frontend.RustHull RustHullRootCallCorrespondence

private abbrev w := Core.Word.ofNatModulo

private def expectedBytes : List UInt8 := [1, 1, 0, 187, 99, 0, 170]
private def expectedStorage : Core.WordMapping.Entries := [(w 7, w 42), (w 8, w 99)]
private def expectedBalances : Core.WordMapping.Entries :=
  Core.WordMapping.insertEntries context.address context.balance context.accounts

private def checkWorld (label : String) (world : List AccountState.Account) : IO Unit := do
  let some root := world.find? (·.address == w 100) |
    throw (IO.userError s!"root reentry {label}: missing root account")
  unless world.length == 1 && root.storage == expectedStorage && root.transient.isEmpty &&
      root.code == some rootBytes do
    throw (IO.userError s!"root reentry {label}: incorrect shared state: {reprStr world}")

private def checkReceipt (scenario : Scenario) (receipt : Contract.Receipt) : IO Unit := do
  match scenario, receipt.outcome with
  | .success, .returned bytes storage =>
      unless bytes == expectedBytes && storage == expectedStorage && receipt.logs.isEmpty &&
          receipt.balances == expectedBalances do
        throw (IO.userError s!"root reentry: incorrect successful receipt: {reprStr receipt}")
      checkWorld "receipt" receipt.world
  | .parentReverted, .reverted bytes =>
      unless bytes == expectedBytes && receipt.logs.isEmpty && receipt.world.isEmpty && receipt.balances.isEmpty do
        throw (IO.userError s!"root reentry: parent revert exported transaction changes: {reprStr receipt}")
  | _, outcome =>
      throw (IO.userError s!"root reentry: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Root"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"root reentry: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let mut checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"root reentry: zero fuel completed: {reprStr outcome}")
  for fuel in [19, 173, 997] do
    checkpoint ← match (Contract.resumeWithReceipt checkpoint fuel).outcome with
      | .outOfFuel next => pure next
      | outcome => throw (IO.userError s!"root reentry: short resumption completed: {reprStr outcome}")
  checkReceipt scenario (Contract.runWithReceipt prepared 4000000)
  checkReceipt scenario (Contract.resumeWithReceipt checkpoint 4000000)
  match Core.runStateful 4000000 (Core.State.initial prepared.expression) with
  | .done (.pair status (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words &&
          storage == Core.WordMapping.encode expectedStorage &&
          logs == Core.WordMapping.encode expected.runtime.runtime.runtime.words &&
          cursor == .word expected.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode expectedBalances &&
          status == .inLeft .unit (.word Core.Word.maximum) &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset &&
          count == .word runtime.storage.returnSize do
        throw (IO.userError s!"root reentry: Core snapshot differs from source for {reprStr scenario}")
      let accounts ← match AccountState.decode world with
        | .ok accounts => pure accounts
        | .error error => throw (IO.userError s!"root reentry: invalid world snapshot: {error}")
      checkWorld "Core snapshot" accounts
  | outcome => throw (IO.userError s!"root reentry: Core execution failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.success, .parentReverted] do
    check scenario

end Tests.RustHullRootCallRuntime
