import Solcore.Test.RustHullLifecycleCorrespondence

/-! Child destruction transfers balances immediately. The public transaction
removes created accounts on success and withholds effects after a parent revert. -/
set_option autoImplicit false
namespace Tests.RustHullLifecycleRuntime
open Solcore Solcore.Frontend.RustHull RustHullLifecycleCorrespondence
private abbrev w := Core.Word.ofNatModulo

private def expectedStorage : StorageSemantics.Words := [(w 7, w 42)]
private def expectedEvents : List Logs.Event := [⟨w 100, [], [187]⟩]
private def expectedBytes : List UInt8 := [1, 2, 170]

private def checkWorld (label : String) (scenario : Scenario) (finalized : Bool)
    (world : List AccountState.Account) : IO Unit := do
  let some parent := world.find? (·.address == w 0) |
    throw (IO.userError s!"{label}: missing parent")
  unless parent.storage == expectedStorage && parent.transient.isEmpty && !parent.created && !parent.destroyed do
    throw (IO.userError s!"{label}: parent was changed by child destruction")
  if finalized && created scenario then
    unless world.length == 1 && (world.find? (·.address == w 100)).isNone do
      throw (IO.userError s!"{label}: created account was not removed")
  else
    let some child := world.find? (·.address == w 100) |
      throw (IO.userError s!"{label}: missing retained child")
    unless world.length == 2 && child.storage == [(w 8, w 99)] && child.code == some childBytes &&
        child.nonce == w 1 && child.transient.isEmpty &&
        child.created == (!finalized && created scenario) && child.destroyed == (!finalized && created scenario) do
      throw (IO.userError s!"{label}: wrong retained account for {reprStr scenario}: {reprStr child}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"lifecycle: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"lifecycle: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"lifecycle: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 4000000, Contract.resumeWithReceipt checkpoint 4000000] do
    if reverts scenario then
      match receipt.outcome with
      | .reverted bytes =>
          unless bytes == expectedBytes && receipt.logs.isEmpty && receipt.balances.isEmpty && receipt.world.isEmpty do
            throw (IO.userError s!"lifecycle: parent revert published child effects: {reprStr receipt}")
      | outcome => throw (IO.userError s!"lifecycle: expected parent revert: {reprStr outcome}")
    else
      match receipt.outcome with
      | .returned bytes storage =>
          unless bytes == expectedBytes && storage == expectedStorage && receipt.logs == expectedEvents &&
              receipt.balances == destroyedBalances do
            throw (IO.userError s!"lifecycle: wrong result for {reprStr scenario}: {reprStr receipt}")
          checkWorld "receipt" scenario true receipt.world
      | outcome => throw (IO.userError s!"lifecycle: expected return for {reprStr scenario}: {reprStr outcome}")
  match Core.runStateful 4000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world))))))))) _ =>
      let expected := finalState object scenario
      let state := runtime expected
      unless memory == Core.WordMapping.encode state.memory.words &&
          storage == Core.WordMapping.encode expectedStorage &&
          logs == Core.WordMapping.encode expected.external.runtime.runtime.runtime.words &&
          cursor == .word expected.external.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode destroyedBalances &&
          exit == .word state.storage.exit && offset == .word state.storage.returnOffset && count == .word state.storage.returnSize do
        throw (IO.userError s!"lifecycle: snapshot differs from source for {reprStr scenario}")
      let accounts ← match AccountState.decode world with
        | .ok accounts => pure accounts
        | .error error => throw (IO.userError s!"lifecycle: bad world snapshot: {error}")
      let sourceWorld := if reverts scenario then state.storage.world else
        (StorageSemantics.finalize state.storage.world expected.external.runtime.runtime.balances).1
      unless StorageCorrespondence.world (accounts.map (fun account => (account, 0))) ==
          StorageCorrespondence.world (sourceWorld.map (fun account => (account, 0))) do
        throw (IO.userError s!"lifecycle: finalized world differs from source for {reprStr scenario}")
      checkWorld "Core snapshot" scenario (!reverts scenario) accounts
  | outcome => throw (IO.userError s!"lifecycle: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.existing, .created, .parentReverted] do check scenario

end Tests.RustHullLifecycleRuntime
