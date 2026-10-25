import Solcore.Frontend.RustHull.AccountLifecycleSemantics
import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics

/-! Account destruction updates shared accounts and balances before completing
its frame. Failed lookups and overflowing credits retain the initial state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLifecycleSemantics
open Core

abbrev State := RuntimeCallEffectsSemantics.State

def updated (state : State) (world : StorageSemantics.World) (balances : StorageSemantics.Words) : State :=
  RuntimeCallEffectsSemantics.withShared state
    {RuntimeCallEffectsSemantics.shared state with world := world, balances := balances}

def terminate (state : State) (kind : Nat) : Semantics.Result Semantics.Value × State :=
  let stopped := TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime kind Word.zero Word.zero
  (stopped.1, {state with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.runtime stopped.2})

inductive Destroy (beneficiary : Word) : State → Semantics.Result Semantics.Value → State → Prop where
  | staticFrame (state : State)
      (isStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = true) :
      Destroy beneficiary state (terminate state 3).1 (terminate state 3).2
  | rejected (state : State) (reason : Word)
      (notStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (destroyed : AccountLifecycleSemantics.destroy state.runtime.runtime.runtime.runtime.runtime.storage.world
        state.runtime.runtime.balances state.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
        state.runtime.runtime.runtime.runtime.runtime.storage.complete = .error reason) :
      Destroy beneficiary state (.fault (.language reason)) state
  | completed (state : State) (world : StorageSemantics.World) (balances : StorageSemantics.Words)
      (notStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (destroyed : AccountLifecycleSemantics.destroy state.runtime.runtime.runtime.runtime.runtime.storage.world
        state.runtime.runtime.balances state.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
        state.runtime.runtime.runtime.runtime.runtime.storage.complete = .ok (world, balances)) :
      Destroy beneficiary state (terminate (updated state world balances) 1).1
        (terminate (updated state world balances) 1).2

end Solcore.Frontend.RustHull.RuntimeLifecycleSemantics
