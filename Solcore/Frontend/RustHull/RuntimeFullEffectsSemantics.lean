import Solcore.Frontend.RustHull.RuntimeLogEffectsSemantics
import Solcore.Frontend.RustHull.TerminationSemantics

/-! Explicit message termination joins event capture and existing runtime
operations without introducing another copy of the source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeFullEffectsSemantics

abbrev State := RuntimeLogEffectsSemantics.State

def withRuntime (state : State) (runtime : RuntimeEffectsSemantics.State) : State :=
  {state with runtime := {state.runtime with runtime := runtime}}

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeLogEffectsSemantics.Builtin name type arguments state result final) :
      Builtin name type arguments state result final
  | termination {name type arguments state result final}
      (computed : TerminationSemantics.builtin name type arguments state.runtime.runtime = some (result, final)) :
      Builtin name type arguments state result (withRuntime state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeFullEffectsSemantics
