import Solcore.Frontend.RustHull.AccountCallSemantics
import Solcore.Frontend.RustHull.RuntimeReturnDataEffectsSemantics

/-! A caller adds its message depth to the established source state. Shared
account resources and frame-local return data are projections of that state,
so nested calls do not introduce duplicate memory, balance, or log fields. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics

structure State where
  runtime : RuntimeReturnDataEffectsSemantics.State := {}
  callDepth : Core.Word := Core.Word.zero

def shared (state : State) : AccountCallSemantics.Shared :=
  let runtime := state.runtime.runtime.runtime.runtime.runtime
  {world := runtime.storage.world, balances := state.runtime.runtime.balances
   logs := state.runtime.runtime.runtime.words, logSize := state.runtime.runtime.runtime.cursor
   complete := runtime.storage.complete}

def withShared (state : State) (shared : AccountCallSemantics.Shared) : State :=
  let account := state.runtime.runtime
  let logs := account.runtime
  let environment := logs.runtime
  let runtime := environment.runtime
  let updated := {runtime with storage := {runtime.storage with world := shared.world, complete := shared.complete}}
  let logs := {logs with runtime := {environment with runtime := updated}, words := shared.logs, cursor := shared.logSize}
  {state with runtime := {state.runtime with runtime := {account with runtime := logs, balances := shared.balances}}}

def withReturned (state : State) (memory : MemorySemantics.State)
    (data : MemorySemantics.Entries) (size : Core.Word) : State :=
  let account := state.runtime.runtime
  let logs := account.runtime
  let environment := logs.runtime
  let runtime := {environment.runtime with memory := memory}
  let observations := environment.environment
  let observations := {observations with direct := fun operation =>
    if operation = .returnDataSize then size else observations.direct operation}
  let logs := {logs with runtime := {environment with runtime := runtime, environment := observations}}
  {state with runtime := {runtime := {account with runtime := logs}, returnData := data}}

theorem shared_withShared (state : State) (value : AccountCallSemantics.Shared) : shared (withShared state value) = value := by
  cases value
  rfl

theorem shared_withReturned (state : State) (memory : MemorySemantics.State)
    (data : MemorySemantics.Entries) (size : Core.Word) : shared (withReturned state memory data size) = shared state := rfl

end Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
