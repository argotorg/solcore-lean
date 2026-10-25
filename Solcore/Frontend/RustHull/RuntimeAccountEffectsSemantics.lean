import Solcore.Frontend.RustHull.RuntimeHashEffectsSemantics
import Solcore.Frontend.RustHull.AccountObservationSemantics

/-! Account observations share the running memory, world and message context.
The independent balance ledger records the existing runtime balance cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeAccountEffectsSemantics

structure State where
  runtime : RuntimeHashEffectsSemantics.State := {}
  balances : StorageSemantics.Words := []

def withMemory (state : State) (memory : MemorySemantics.State) : State :=
  {state with runtime := RuntimeCopyEffectsSemantics.withMemory state.runtime memory}

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeHashEffectsSemantics.Builtin name type arguments state.runtime result final) :
      Builtin name type arguments state result {state with runtime := final}
  | observation {name type arguments state result final}
      (computed : AccountObservationSemantics.Builtin state.runtime.runtime.runtime.storage.world
        state.runtime.runtime.runtime.storage.complete state.balances state.runtime.runtime.runtime.storage.address
        name type arguments state.runtime.runtime.runtime.memory result final) :
      Builtin name type arguments state result (withMemory state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeAccountEffectsSemantics
