import Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsSemantics
import Solcore.Frontend.RustHull.LogsSemantics

/-! Memory, storage, environment observations and event capture share one
runtime state. Only the event stream and cursor add new source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLogEffectsSemantics

structure State where
  runtime : RuntimeEnvironmentEffectsSemantics.State := {}
  words : LogsSemantics.Words := []
  cursor : Core.Word := Core.Word.zero

def logsState (state : State) : LogsSemantics.State :=
  ⟨state.runtime.runtime.memory, state.words, state.cursor, state.runtime.runtime.storage.address,
    state.runtime.runtime.storage.isStatic, state.runtime.runtime.storage.exit,
    state.runtime.runtime.storage.returnOffset, state.runtime.runtime.storage.returnSize⟩

def withLogs (state : State) (logs : LogsSemantics.State) : State where
  runtime := {state.runtime with runtime := {
    memory := logs.memory
    storage := {state.runtime.runtime.storage with address := logs.address, isStatic := logs.isStatic, exit := logs.exit, returnOffset := logs.returnOffset, returnSize := logs.returnSize}}}
  words := logs.words
  cursor := logs.cursor

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeEnvironmentEffectsSemantics.builtin name type arguments state.runtime = some (result, final)) :
      Builtin name type arguments state result {state with runtime := final}
  | logs {name type arguments state result final}
      (computed : LogsSemantics.Builtin name type arguments (logsState state) result final) :
      Builtin name type arguments state result (withLogs state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeLogEffectsSemantics
