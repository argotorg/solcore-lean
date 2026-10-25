import Solcore.Frontend.RustHull.RuntimeFullEffectsSemantics
import Solcore.Frontend.RustHull.MemoryCopySemantics

/-! Copy operations use the same memory and immutable calldata observations
as the surrounding source execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCopyEffectsSemantics

abbrev State := RuntimeFullEffectsSemantics.State

def withMemory (state : State) (memory : MemorySemantics.State) : State :=
  {state with runtime := {state.runtime with runtime := {state.runtime.runtime with memory := memory}}}

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeFullEffectsSemantics.Builtin name type arguments state result final) :
      Builtin name type arguments state result final
  | copy {name type arguments state result final}
      (computed : MemoryCopySemantics.Builtin state.runtime.environment.calldata name type arguments
        state.runtime.runtime.memory result final) :
      Builtin name type arguments state result (withMemory state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeCopyEffectsSemantics
